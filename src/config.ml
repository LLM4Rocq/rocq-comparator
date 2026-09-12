(* Configuration (DESIGN.md section 10). All paths are made absolute relative
   to the directory of the config file (or the cwd for command-line flags). *)

type loadpath_entry =
  | Q of string * string  (** -Q dir logical *)
  | R of string * string  (** -R dir logical *)
  | I of string  (** -I dir (ML path) *)

type sandbox_mode =
  | Auto
  | No_sandbox
  | Sandbox_exec
  | Landrun
  | Bwrap
  | Custom of string list

type t = {
  challenge : string;
  solution : string;
  theorem_names : string list;
  definition_names : string list;
  permitted_axioms : string list;  (** exact kernel names, or "Prefix.*" wildcards *)
  loadpath : loadpath_entry list;
  coqproject : string option;
  top : string option;  (** logical name of the library; derived when None *)
  timeout_s : float;
  sandbox : sandbox_mode;
  rocqchk : bool;
  vm : bool;
  impredicative_set : bool;
  indices_matter : bool;
  noinit : bool;  (** compile with -noinit (no prelude); rarely wanted *)
  permitted_plugins : string list;  (** extra VernacExtend plugin names allowed *)
  permitted_libraries : string list;  (** if non-empty, dirpath prefixes the solution may Require *)
  permit_challenge_axioms : bool;
      (** default true: every constant the challenge itself declares [Undef]
          (a [Parameter]/[Axiom], or an [Admitted] helper lemma other than
          the targets) is automatically added to the permitted-axiom set and
          pinned to its challenge-side type, so a solution may either use it
          as an assumption or supply a proof for it. The semantics live in
          Check (this agent owns only the field, its JSON and its default). *)
  config_dir : string;
}

let default_timeout_s = 600.

let default =
  { challenge = "Challenge.v"; solution = "Solution.v"; theorem_names = []; definition_names = [];
    permitted_axioms = []; loadpath = []; coqproject = None; top = None; timeout_s = default_timeout_s;
    sandbox = Auto; rocqchk = true; vm = true; impredicative_set = false; indices_matter = false;
    noinit = false; permitted_plugins = []; permitted_libraries = []; permit_challenge_axioms = true;
    config_dir = Sys.getcwd () }

let absolute ~dir p = if Filename.is_relative p then Filename.concat dir p else p

let sandbox_mode_of_string = function
  | "auto" -> Result.Ok Auto
  | "none" -> Result.Ok No_sandbox
  | "sandbox-exec" -> Result.Ok Sandbox_exec
  | "landrun" -> Result.Ok Landrun
  | "bwrap" -> Result.Ok Bwrap
  | s -> Result.Error ("unknown sandbox mode: " ^ s)

let sandbox_mode_to_string = function
  | Auto -> "auto" | No_sandbox -> "none" | Sandbox_exec -> "sandbox-exec"
  | Landrun -> "landrun" | Bwrap -> "bwrap" | Custom l -> "custom:" ^ String.concat " " l

(* -Q/-R/-I lines of a _CoqProject / _RocqProject file; other lines ignored. *)
let parse_coqproject ~dir (text : string) : loadpath_entry list =
  let toks =
    text |> String.split_on_char '\n'
    |> List.filter (fun l -> not (String.length (String.trim l) > 0 && (String.trim l).[0] = '#'))
    |> List.concat_map (fun l -> String.split_on_char ' ' l)
    |> List.concat_map (String.split_on_char '\t')
    |> List.filter (fun s -> s <> "")
  in
  let rec go acc = function
    | "-Q" :: d :: l :: tl -> go (Q (absolute ~dir d, l) :: acc) tl
    | "-R" :: d :: l :: tl -> go (R (absolute ~dir d, l) :: acc) tl
    | "-I" :: d :: tl -> go (I (absolute ~dir d) :: acc) tl
    | _ :: tl -> go acc tl
    | [] -> List.rev acc
  in
  go [] toks

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

(* Load path with the _CoqProject entries appended, all dirs absolute. *)
let resolve_loadpath (c : t) : loadpath_entry list =
  let own = List.map (function
      | Q (d, l) -> Q (absolute ~dir:c.config_dir d, l)
      | R (d, l) -> R (absolute ~dir:c.config_dir d, l)
      | I d -> I (absolute ~dir:c.config_dir d)) c.loadpath in
  let proj = match c.coqproject with
    | None -> []
    | Some p ->
      let p = absolute ~dir:c.config_dir p in
      if Sys.file_exists p then parse_coqproject ~dir:(Filename.dirname p) (read_file p) else []
  in
  own @ proj

let loadpath_args (c : t) : string list =
  List.concat_map (function
      | Q (d, l) -> [ "-Q"; d; l ]
      | R (d, l) -> [ "-R"; d; l ]
      | I d -> [ "-I"; d ]) (resolve_loadpath c)

(* Arguments for Coqinit.parse_arguments. *)
let rocq_args (c : t) : string list =
  loadpath_args c
  @ [ "-native-compiler"; "no" ]
  @ (if c.vm then [] else [ "-bytecode-compiler"; "no" ])
  @ (if c.impredicative_set then [ "-impredicative-set" ] else [])
  @ (if c.indices_matter then [ "-indices-matter" ] else [])
  @ (if c.noinit then [ "-noinit" ] else [])

let normalize_path p =
  (* collapse ./ and ../ without touching the filesystem *)
  let parts = String.split_on_char '/' p in
  let rec go acc = function
    | [] -> List.rev acc
    | "." :: tl | "" :: tl -> go acc tl
    | ".." :: tl -> (match acc with _ :: acc' -> go acc' tl | [] -> go acc tl)
    | x :: tl -> go (x :: acc) tl
  in
  (if String.length p > 0 && p.[0] = '/' then "/" else "") ^ String.concat "/" (go [] parts)

let is_under ~root p =
  let root = normalize_path root and p = normalize_path p in
  let lr = String.length root in
  String.length p >= lr && String.sub p 0 lr = root
  && (String.length p = lr || p.[lr] = '/' || root = "/")

(* Logical name of the challenge library, as coqdep would derive it. *)
let top_name (c : t) : string =
  match c.top with
  | Some t -> t
  | None ->
    let file = absolute ~dir:c.config_dir c.challenge in
    let base = Filename.remove_extension (Filename.basename file) in
    let dir = Filename.dirname file in
    let candidates = List.filter_map (function
        | Q (d, l) | R (d, l) when is_under ~root:d dir ->
          let rel = String.sub (normalize_path dir) (String.length (normalize_path d))
              (String.length (normalize_path dir) - String.length (normalize_path d)) in
          let rel = String.split_on_char '/' rel |> List.filter (fun s -> s <> "") in
          let comps = (if l = "" then [] else String.split_on_char '.' l) @ rel @ [ base ] in
          Some (String.length (normalize_path d), String.concat "." comps)
        | _ -> None) (resolve_loadpath c) in
    match List.sort (fun (a, _) (b, _) -> compare b a) candidates with
    | (_, name) :: _ -> name
    | [] -> base

let challenge_path c = absolute ~dir:c.config_dir c.challenge
let solution_path c = absolute ~dir:c.config_dir c.solution

(* ---- JSON ---- *)

let member k = function `Assoc l -> List.assoc_opt k l | _ -> None
let str k j = match member k j with Some (`String s) -> Some s | _ -> None
let bool_ ~default k j = match member k j with Some (`Bool b) -> b | _ -> default
let strings k j = match member k j with
  | Some (`List l) -> List.filter_map (function `String s -> Some s | _ -> None) l | _ -> []

let loadpath_of_json (j : Yojson.Safe.t) : (loadpath_entry list, string) result =
  match j with
  | `List l ->
    let rec go acc = function
      | [] -> Result.Ok (List.rev acc)
      | `Assoc [ ("Q", `List [ `String d; `String l ]) ] :: tl -> go (Q (d, l) :: acc) tl
      | `Assoc [ ("R", `List [ `String d; `String l ]) ] :: tl -> go (R (d, l) :: acc) tl
      | `Assoc [ ("I", `List [ `String d ]) ] :: tl -> go (I d :: acc) tl
      | `Assoc [ ("I", `String d) ] :: tl -> go (I d :: acc) tl
      | `List [ `String "-Q"; `String d; `String l ] :: tl -> go (Q (d, l) :: acc) tl
      | `List [ `String "-R"; `String d; `String l ] :: tl -> go (R (d, l) :: acc) tl
      | `List [ `String "-I"; `String d ] :: tl -> go (I d :: acc) tl
      | x :: _ -> Result.Error ("bad loadpath entry: " ^ Yojson.Safe.to_string x)
    in
    go [] l
  | _ -> Result.Error "loadpath must be a list"

(* Expand "@preset" entries of [permitted_axioms] (DESIGN.md section 10) via
   Presets.expand; every other entry (a fully qualified kernel name, or a
   "Prefix.*" wildcard) passes through unchanged. An unknown "@name" is a
   config error rather than a silently-empty permitted list, since a typo
   here would otherwise fail closed in the wrong direction (nothing
   permitted) but a copy-paste of the wrong preset name would fail open in
   the *right* direction and could go unnoticed until a specific proof
   needed the real axiom name. *)
let expand_axioms (names : string list) : (string list, string) result =
  let rec go acc = function
    | [] -> Result.Ok (List.rev acc)
    | name :: tl ->
      if String.length name > 0 && name.[0] = '@' then
        match Presets.expand name with
        | Some expanded -> go (List.rev_append expanded acc) tl
        | None ->
          Result.Error
            (Printf.sprintf "unknown axiom preset %s (known: %s)" name Presets.known_names)
      else go (name :: acc) tl
  in
  go [] names

let of_json ~config_dir (j : Yojson.Safe.t) : (t, string) result =
  let ( let* ) = Result.bind in
  let* loadpath = match member "loadpath" j with None -> Result.Ok [] | Some l -> loadpath_of_json l in
  let* permitted_axioms = expand_axioms (strings "permitted_axioms" j) in
  let* sandbox = match member "sandbox" j with
    | None -> Result.Ok Auto
    | Some (`String s) -> sandbox_mode_of_string s
    | Some (`Assoc [ ("command", `List cmd) ]) ->
      Result.Ok (Custom (List.filter_map (function `String s -> Some s | _ -> None) cmd))
    | Some x -> Result.Error ("bad sandbox: " ^ Yojson.Safe.to_string x) in
  let timeout_s = match member "timeout_s" j with
    | Some (`Int n) -> float_of_int n | Some (`Float f) -> f | _ -> default_timeout_s in
  let theorem_names = strings "theorem_names" j in
  let definition_names = strings "definition_names" j in
  if theorem_names = [] && definition_names = [] then
    Result.Error "theorem_names (or definition_names) must be non-empty"
  else
    Result.Ok
      { challenge = Stdlib.Option.value (str "challenge" j) ~default:"Challenge.v";
        solution = Stdlib.Option.value (str "solution" j) ~default:"Solution.v";
        theorem_names; definition_names;
        permitted_axioms;
        loadpath; coqproject = str "coqproject" j; top = str "top" j; timeout_s; sandbox;
        rocqchk = bool_ ~default:true "rocqchk" j;
        vm = bool_ ~default:true "vm" j;
        impredicative_set = bool_ ~default:false "impredicative_set" j;
        indices_matter = bool_ ~default:false "indices_matter" j;
        noinit = bool_ ~default:false "noinit" j;
        permitted_plugins = strings "permitted_plugins" j;
        permitted_libraries = strings "permitted_libraries" j;
        permit_challenge_axioms = bool_ ~default:true "permit_challenge_axioms" j;
        config_dir }

let of_json_file (path : string) : (t, string) result =
  match Yojson.Safe.from_file path with
  | exception Sys_error m -> Result.Error m
  | exception Yojson.Json_error m -> Result.Error ("invalid JSON in " ^ path ^ ": " ^ m)
  | j -> of_json ~config_dir:(Filename.dirname (absolute ~dir:(Sys.getcwd ()) path)) j

let to_json (c : t) : Yojson.Safe.t =
  `Assoc
    [ ("challenge", `String c.challenge); ("solution", `String c.solution);
      ("theorem_names", `List (List.map (fun s -> `String s) c.theorem_names));
      ("definition_names", `List (List.map (fun s -> `String s) c.definition_names));
      ("permitted_axioms", `List (List.map (fun s -> `String s) c.permitted_axioms));
      ("loadpath", `List (List.map (function
           | Q (d, l) -> `Assoc [ ("Q", `List [ `String d; `String l ]) ]
           | R (d, l) -> `Assoc [ ("R", `List [ `String d; `String l ]) ]
           | I d -> `Assoc [ ("I", `List [ `String d ]) ]) c.loadpath));
      ("coqproject", (match c.coqproject with None -> `Null | Some s -> `String s));
      ("top", (match c.top with None -> `Null | Some s -> `String s));
      ("timeout_s", `Float c.timeout_s);
      ("sandbox", (match c.sandbox with
           | Custom l -> `Assoc [ ("command", `List (List.map (fun s -> `String s) l)) ]
           | m -> `String (sandbox_mode_to_string m)));
      ("rocqchk", `Bool c.rocqchk); ("vm", `Bool c.vm);
      ("impredicative_set", `Bool c.impredicative_set); ("indices_matter", `Bool c.indices_matter);
      ("noinit", `Bool c.noinit);
      ("permitted_plugins", `List (List.map (fun s -> `String s) c.permitted_plugins));
      ("permitted_libraries", `List (List.map (fun s -> `String s) c.permitted_libraries));
      ("permit_challenge_axioms", `Bool c.permit_challenge_axioms) ]
