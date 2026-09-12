(* Axiom policy (DESIGN.md section 7).

   The assumption set is computed by the kernel-level traversal behind
   [Print Assumptions] and classified by constructor: names are never parsed
   out of printed text, and axioms are matched fully qualified.

   Every name handled here is the CANONICAL kernel name (see
   src/rocqapi/kernel_assumptions.ml for why): [permitted_axioms] entries are
   therefore matched against canonical names.  For library constants the user
   name and the canonical name coincide, so a permitted-axiom list written the
   obvious way ("Stdlib.Logic.Classical_Prop.classic") keeps working; only an
   object re-exported under a different user name by [Include] is reported
   under a name the solution could not choose. *)

open Names

type item =
  | Axiom of string
  | Primitive of string
  | Symbol of string
  | Variable of string
  | Positive of string
  | Guarded of string
  | Type_in_type of string
  | Uip of string

let item_kind = function
  | Axiom _ -> "axiom"
  | Primitive _ -> "kernel primitive"
  | Symbol _ -> "rewrite-rule symbol"
  | Variable _ -> "section variable"
  | Positive _ -> "inductive assumed positive"
  | Guarded _ -> "(co)fixpoint assumed guarded"
  | Type_in_type _ -> "constant relying on type-in-type"
  | Uip _ -> "inductive using definitional UIP"

let item_name = function
  | Axiom s | Primitive s | Symbol s | Variable s | Positive s | Guarded s | Type_in_type s
  | Uip s -> s

let of_constant (c : Constant.t) : item list =
  Kernel_assumptions.collect (GlobRef.ConstRef c)
  |> List.map (fun (k, n) ->
      match k with
      | `Axiom -> Axiom n
      | `Primitive -> Primitive n
      | `Symbol -> Symbol n
      | `Variable -> Variable n
      | `Positive -> Positive n
      | `Guarded -> Guarded n
      | `Type_in_type -> Type_in_type n
      | `Uip -> Uip n)

(* exact name, or a "Prefix.*" wildcard *)
let permitted_matches ~(permitted : string list) (name : string) =
  List.exists
    (fun p ->
       if String.length p >= 2 && String.sub p (String.length p - 2) 2 = ".*" then
         let pre = String.sub p 0 (String.length p - 1) in
         String.length name >= String.length pre && String.sub name 0 (String.length pre) = pre
       else String.equal p name)
    permitted

let check ~(permitted : string list) (targets : (string * Constant.t) list)
    (reports : Verdict.target_report list) :
  ( Verdict.target_report list,
    Verdict.reason * string * Verdict.target_report list )
  result =
  let error = ref None in
  let reports = ref reports in
  let update name f =
    reports :=
      List.map (fun (r : Verdict.target_report) -> if String.equal r.Verdict.name name then f r else r) !reports
  in
  List.iter
    (fun (name, kn) ->
       let items = of_constant kn in
       let used = ref [] in
       List.iter
         (fun it ->
            match it with
            | Primitive _ ->
              (* A kernel primitive (Uint63.add, PrimFloat.mul, ...) is not an
                 assumption: the kernel gives it its meaning, and only a
                 trusted library can declare one (the [Primitive] vernacular
                 is denied to solutions).  Ignore it entirely. *)
              ()
            | Axiom a ->
              if permitted_matches ~permitted a then used := a :: !used
              else if !error = None then begin
                error := Some (Verdict.Forbidden_axiom, name ^ " uses the forbidden axiom " ^ a);
                update name (fun r -> { r with Verdict.target_detail = Some ("forbidden axiom " ^ a) })
              end
            | Variable v ->
              if !error = None then begin
                error := Some (Verdict.Forbidden_axiom, name ^ " depends on the section variable " ^ v);
                update name (fun r -> { r with Verdict.target_detail = Some ("section variable " ^ v) })
              end
            | Symbol _ | Positive _ | Guarded _ | Type_in_type _ | Uip _ ->
              if !error = None then begin
                error :=
                  Some (Verdict.Unsafe_flags,
                        name ^ " depends on a " ^ item_kind it ^ ": " ^ item_name it);
                update name (fun r ->
                    { r with Verdict.target_detail = Some (item_kind it ^ ": " ^ item_name it) })
              end)
         items;
       let sorted = List.sort_uniq String.compare !used in
       update name (fun r -> { r with Verdict.assumptions = sorted }))
    targets;
  match !error with
  | None -> Result.Ok !reports
  | Some (r, d) -> Result.Error (r, d, !reports)
