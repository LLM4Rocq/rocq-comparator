(* The single JSON verdict printed on stdout (DESIGN.md section 10). *)

(* The comparator's own version.  It lives in the library (not only in the CLI)
   so it can be stamped into the reproducibility manifest and reported by
   [version], and so the CLI and the manifest can never disagree. *)
let comparator_version = "0.1.0"

type reason =
  | Statement_mismatch
  | Dependency_mismatch
  | Not_proved
  | Target_not_found
  | Kind_mismatch
  | Forbidden_axiom
  | Unsafe_flags
  | Forbidden_command
  | Compile_error
  | Challenge_error
  | Timeout
  | Rocqchk_failed
  | Library_violation
  | Config_error
  | Sandbox_error
  | Internal_error

let reason_to_string = function
  | Statement_mismatch -> "statement_mismatch"
  | Dependency_mismatch -> "dependency_mismatch"
  | Not_proved -> "not_proved"
  | Target_not_found -> "target_not_found"
  | Kind_mismatch -> "kind_mismatch"
  | Forbidden_axiom -> "forbidden_axiom"
  | Unsafe_flags -> "unsafe_flags"
  | Forbidden_command -> "forbidden_command"
  | Compile_error -> "compile_error"
  | Challenge_error -> "challenge_error"
  | Timeout -> "timeout"
  | Rocqchk_failed -> "rocqchk_failed"
  | Library_violation -> "library_violation"
  | Config_error -> "config_error"
  | Sandbox_error -> "sandbox_error"
  | Internal_error -> "internal_error"

let all_reasons =
  [ Statement_mismatch; Dependency_mismatch; Not_proved; Target_not_found;
    Kind_mismatch; Forbidden_axiom; Unsafe_flags; Forbidden_command;
    Compile_error; Challenge_error; Timeout; Rocqchk_failed; Library_violation;
    Config_error; Sandbox_error; Internal_error ]

let reason_of_string s =
  List.find_opt (fun r -> String.equal (reason_to_string r) s) all_reasons

(* Exit code 2 = infrastructure problem (nothing was judged); 1 = rejected. *)
let is_infrastructure = function
  | Challenge_error | Config_error | Sandbox_error | Internal_error -> true
  | _ -> false

type check_status = Ok | Fail of string | Skipped

type target_report = {
  name : string;
  status : string;  (** "proved" | "not_proved" | "missing" | "mismatch" | "unchecked" *)
  assumptions : string list;  (** fully qualified names of permitted axioms used *)
  target_detail : string option;
}

(* Reproducibility manifest (DESIGN-audit tier 4, feature 1).

   A stored verdict records only [rocq_version]; that is not enough to audit
   the run later.  The manifest captures the rest of the ambient inputs the
   pipeline already has in hand and used to throw away: the OCaml compiler the
   kernel was built with, the comparator's own version, the trusted load-path
   roots, and every .vo the run loaded with its on-disk digest.  With this, a
   third party can tell whether a re-run would see the same libraries.  It is
   kept compact and deterministic (libraries sorted by name) so two identical
   runs produce byte-identical manifests. *)
type library_entry = {
  lib_name : string;  (** logical dirpath, e.g. "Stdlib.Arith.Arith" *)
  lib_path : string;  (** absolute .vo path, or "" if it could not be located *)
  lib_digest : string;  (** hex MD5 of the .vo, or "" if unavailable *)
  lib_trust : string;
      (** "installed" (from the switch), "trusted" (a project file in the
          challenge's closure, compiled by this run) or "checked" (a project
          file in the solution's closure, compiled by this run under the
          strict filter and re-checked) *)
}

type manifest = {
  ocaml_version : string;
  comparator_version : string;
  trusted_roots : string list;
  libraries : library_entry list;
}

type t = {
  ok : bool;
  reason : reason option;
  detail : string option;
  sandboxed : bool;
  sandbox : string;
  rocq_version : string;
  manifest : manifest option;
  targets : target_report list;
  checks : (string * check_status) list;
  timing : (string * float) list;
  solution : string option;  (** set in batch mode *)
}

let empty =
  { ok = false; reason = None; detail = None; sandboxed = false; sandbox = "none";
    rocq_version = ""; manifest = None; targets = []; checks = []; timing = []; solution = None }

let fail ?(checks = []) ?(targets = []) ?(timing = []) reason detail =
  { empty with ok = false; reason = Some reason; detail = Some detail; checks; targets; timing }

let pass ?(checks = []) ?(targets = []) ?(timing = []) () =
  { empty with ok = true; reason = None; detail = None; checks; targets; timing }

let exit_code v =
  if v.ok then 0
  else match v.reason with
    | Some r when is_infrastructure r -> 2
    | _ -> 1

let status_to_json = function
  | Ok -> `String "ok"
  | Skipped -> `String "skipped"
  | Fail msg -> `Assoc [ ("fail", `String msg) ]

let status_of_json = function
  | `String "ok" -> Ok
  | `String "skipped" -> Skipped
  | `Assoc [ ("fail", `String msg) ] -> Fail msg
  | j -> Fail ("unparseable status: " ^ Yojson.Safe.to_string j)

let opt_string = function None -> `Null | Some s -> `String s

let manifest_to_json (m : manifest) : Yojson.Safe.t =
  `Assoc
    [ ("ocaml_version", `String m.ocaml_version);
      ("comparator_version", `String m.comparator_version);
      ("trusted_roots", `List (List.map (fun s -> `String s) m.trusted_roots));
      ("libraries",
       `List
         (List.map
            (fun (l : library_entry) ->
               `Assoc
                 [ ("name", `String l.lib_name); ("path", `String l.lib_path);
                   ("digest", `String l.lib_digest); ("trust", `String l.lib_trust) ])
            m.libraries)) ]

let target_to_json (t : target_report) : Yojson.Safe.t =
  `Assoc
    [ ("name", `String t.name);
      ("status", `String t.status);
      ("assumptions", `List (List.map (fun s -> `String s) t.assumptions));
      ("detail", opt_string t.target_detail) ]

let to_json (v : t) : Yojson.Safe.t =
  `Assoc
    ([ ("ok", `Bool v.ok);
       ("reason", (match v.reason with None -> `Null | Some r -> `String (reason_to_string r)));
       ("detail", opt_string v.detail);
       ("sandboxed", `Bool v.sandboxed);
       ("sandbox", `String v.sandbox);
       ("rocq_version", `String v.rocq_version);
       ("manifest", (match v.manifest with None -> `Null | Some m -> manifest_to_json m));
       ("targets", `List (List.map target_to_json v.targets));
       ("checks", `Assoc (List.map (fun (k, s) -> (k, status_to_json s)) v.checks));
       ("timing_s", `Assoc (List.map (fun (k, f) -> (k, `Float f)) v.timing)) ]
     @ match v.solution with None -> [] | Some s -> [ ("solution", `String s) ])

let member k (j : Yojson.Safe.t) = match j with `Assoc l -> List.assoc_opt k l | _ -> None
let str_opt = function Some (`String s) -> Some s | _ -> None
let str_or d j = match str_opt j with Some s -> s | None -> d
let strings_of = function
  | Some (`List l) -> List.filter_map (function `String s -> Some s | _ -> None) l
  | _ -> []

(* Tolerant: an absent or [`Null] manifest yields [None]; a present one is
   parsed field by field so an old verdict missing a sub-field still loads. *)
let manifest_of_json (j : Yojson.Safe.t option) : manifest option =
  match j with
  | None | Some `Null -> None
  | Some m ->
    Some
      { ocaml_version = str_or "" (member "ocaml_version" m);
        comparator_version = str_or "" (member "comparator_version" m);
        trusted_roots = strings_of (member "trusted_roots" m);
        libraries =
          (match member "libraries" m with
           | Some (`List l) ->
             List.map
               (fun e ->
                  { lib_name = str_or "" (member "name" e);
                    lib_path = str_or "" (member "path" e);
                    lib_digest = str_or "" (member "digest" e);
                    lib_trust = str_or "installed" (member "trust" e) })
               l
           | _ -> []) }

let of_json (j : Yojson.Safe.t) : (t, string) result =
  try
    let ok = match member "ok" j with Some (`Bool b) -> b | _ -> failwith "missing ok" in
    let reason = match member "reason" j with
      | Some (`String s) -> (match reason_of_string s with Some r -> Some r | None -> failwith ("unknown reason " ^ s))
      | _ -> None in
    let targets = match member "targets" j with
      | Some (`List l) -> List.map (fun t ->
          { name = (match str_opt (member "name" t) with Some s -> s | None -> "");
            status = (match str_opt (member "status" t) with Some s -> s | None -> "");
            assumptions = (match member "assumptions" t with Some (`List a) -> List.filter_map (function `String s -> Some s | _ -> None) a | _ -> []);
            target_detail = str_opt (member "detail" t) }) l
      | _ -> [] in
    let checks = match member "checks" j with
      | Some (`Assoc l) -> List.map (fun (k, s) -> (k, status_of_json s)) l | _ -> [] in
    let timing = match member "timing_s" j with
      | Some (`Assoc l) -> List.filter_map (fun (k, f) -> match f with `Float x -> Some (k, x) | `Int n -> Some (k, float_of_int n) | _ -> None) l | _ -> [] in
    Result.Ok
      { ok; reason; detail = str_opt (member "detail" j);
        sandboxed = (match member "sandboxed" j with Some (`Bool b) -> b | _ -> false);
        sandbox = (match str_opt (member "sandbox" j) with Some s -> s | None -> "");
        rocq_version = (match str_opt (member "rocq_version" j) with Some s -> s | None -> "");
        manifest = manifest_of_json (member "manifest" j);
        targets; checks; timing; solution = str_opt (member "solution" j) }
  with Failure m -> Result.Error m | Yojson.Json_error m -> Result.Error m

let to_string ?(pretty = false) v =
  if pretty then Yojson.Safe.pretty_to_string (to_json v) else Yojson.Safe.to_string (to_json v)

let print ?pretty v = print_string (to_string ?pretty v); print_newline ()

(* ------------------------------------------------------------------ *)
(* Dry-run / validate-challenge report (DESIGN-audit tier 4, feature 2).

   [rocq-comparator validate] compiles the challenge alone and describes what
   an operator would be publishing: for each declared target whether it
   resolves, its kind and its pretty-printed type, plus the axioms the
   challenge itself declares.  It is a sibling of [t] rather than a reuse of it
   because there is no solution to judge and no pass/fail verdict to render --
   only a description. *)

type validation_target = {
  vt_name : string;
  vt_resolves : bool;
  vt_kind : string;  (** "theorem" | "definition_hole" | "unresolved" *)
  vt_type : string option;  (** pretty-printed statement, [None] if unresolved *)
}

type validation = {
  v_ok : bool;  (** the challenge compiled and every declared target resolved *)
  v_error : string option;
  v_rocq_version : string;
  v_top : string;
  v_targets : validation_target list;
  v_challenge_axioms : string list;  (** fully qualified names the challenge assumes *)
  v_manifest : manifest option;
}

let validation_target_to_json (t : validation_target) : Yojson.Safe.t =
  `Assoc
    [ ("name", `String t.vt_name);
      ("resolves", `Bool t.vt_resolves);
      ("kind", `String t.vt_kind);
      ("type", opt_string t.vt_type) ]

let validation_to_json (v : validation) : Yojson.Safe.t =
  `Assoc
    [ ("validate", `Bool true);
      ("ok", `Bool v.v_ok);
      ("error", opt_string v.v_error);
      ("rocq_version", `String v.v_rocq_version);
      ("top", `String v.v_top);
      ("targets", `List (List.map validation_target_to_json v.v_targets));
      ("challenge_axioms", `List (List.map (fun s -> `String s) v.v_challenge_axioms));
      ("manifest", (match v.v_manifest with None -> `Null | Some m -> manifest_to_json m)) ]

let validation_of_json (j : Yojson.Safe.t) : (validation, string) result =
  try
    Result.Ok
      { v_ok = (match member "ok" j with Some (`Bool b) -> b | _ -> failwith "missing ok");
        v_error = str_opt (member "error" j);
        v_rocq_version = str_or "" (member "rocq_version" j);
        v_top = str_or "" (member "top" j);
        v_targets =
          (match member "targets" j with
           | Some (`List l) ->
             List.map
               (fun t ->
                  { vt_name = str_or "" (member "name" t);
                    vt_resolves =
                      (match member "resolves" t with Some (`Bool b) -> b | _ -> false);
                    vt_kind = str_or "" (member "kind" t);
                    vt_type = str_opt (member "type" t) })
               l
           | _ -> []);
        v_challenge_axioms = strings_of (member "challenge_axioms" j);
        v_manifest = manifest_of_json (member "manifest" j) }
  with Failure m -> Result.Error m | Yojson.Json_error m -> Result.Error m

let validation_to_string ?(pretty = false) v =
  if pretty then Yojson.Safe.pretty_to_string (validation_to_json v)
  else Yojson.Safe.to_string (validation_to_json v)

let validation_exit_code (v : validation) = if v.v_ok then 0 else 2

let print_validation ?pretty v =
  print_string (validation_to_string ?pretty v); print_newline ()
