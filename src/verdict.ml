(* The single JSON verdict printed on stdout (DESIGN.md section 10). *)

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

type t = {
  ok : bool;
  reason : reason option;
  detail : string option;
  sandboxed : bool;
  sandbox : string;
  rocq_version : string;
  targets : target_report list;
  checks : (string * check_status) list;
  timing : (string * float) list;
  solution : string option;  (** set in batch mode *)
}

let empty =
  { ok = false; reason = None; detail = None; sandboxed = false; sandbox = "none";
    rocq_version = ""; targets = []; checks = []; timing = []; solution = None }

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
       ("targets", `List (List.map target_to_json v.targets));
       ("checks", `Assoc (List.map (fun (k, s) -> (k, status_to_json s)) v.checks));
       ("timing_s", `Assoc (List.map (fun (k, f) -> (k, `Float f)) v.timing)) ]
     @ match v.solution with None -> [] | Some s -> [ ("solution", `String s) ])

let member k (j : Yojson.Safe.t) = match j with `Assoc l -> List.assoc_opt k l | _ -> None
let str_opt = function Some (`String s) -> Some s | _ -> None

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
        targets; checks; timing; solution = str_opt (member "solution" j) }
  with Failure m -> Result.Error m | Yojson.Json_error m -> Result.Error m

let to_string ?(pretty = false) v =
  if pretty then Yojson.Safe.pretty_to_string (to_json v) else Yojson.Safe.to_string (to_json v)

let print ?pretty v = print_string (to_string ?pretty v); print_newline ()
