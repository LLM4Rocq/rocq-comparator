(* Axiom policy (DESIGN.md section 7).

   The assumption set is computed by the kernel-level traversal behind
   [Print Assumptions] and classified by constructor: names are never parsed
   out of printed text, and axioms are matched fully qualified. *)

open Names

type item =
  | Axiom of string
  | Variable of string
  | Positive of string
  | Guarded of string
  | Type_in_type of string
  | Uip of string

let item_kind = function
  | Axiom _ -> "axiom"
  | Variable _ -> "section variable"
  | Positive _ -> "inductive assumed positive"
  | Guarded _ -> "(co)fixpoint assumed guarded"
  | Type_in_type _ -> "constant relying on type-in-type"
  | Uip _ -> "inductive using definitional UIP"

let item_name = function
  | Axiom s | Variable s | Positive s | Guarded s | Type_in_type s | Uip s -> s

let of_constant (c : Constant.t) : item list =
  Kernel_assumptions.collect (GlobRef.ConstRef c)
  |> List.map (fun (k, n) ->
      match k with
      | `Axiom -> Axiom n
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
            | Positive _ | Guarded _ | Type_in_type _ | Uip _ ->
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
