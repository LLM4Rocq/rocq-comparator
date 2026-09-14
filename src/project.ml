(* Project discovery (DESIGN.md section 16).

   A .v file's project is the nearest ancestor directory holding a
   _CoqProject or a dune-project (the config's "coqproject" field overrides
   the search, and "" disables it).  A project is a list of BINDINGS, each a
   physical directory bound to a logical prefix, together with the .v files
   it contains and their logical names.  The comparator reads project files;
   it never runs dune, make or rocq.

   This module is pure filesystem and string work with no Rocq state, so it
   can run in the outer process (Config.top_name needs it before Rocq is
   initialised) as well as in the sandboxed inner one. *)

type binding = {
  dir : string;  (** absolute physical directory *)
  logical : string;  (** logical prefix, "" for [-Q . ""] *)
  implicit : bool;  (** -R (and dune theories): unqualified names resolve *)
  files : (string * string) list;  (** absolute .v path, logical name *)
}

type t = {
  root : string;  (** directory of the project file *)
  project_file : string;
  bindings : binding list;
  theories : string list;  (** dune [(theories ...)] names, checked after init *)
}

type flags = { impredicative_set : bool; indices_matter : bool; noinit : bool }

let ( let* ) = Result.bind

let skip_entry name =
  String.length name = 0 || name.[0] = '.' || name = "_build" || name = "_opam"

let valid_id s = match Names.Id.of_string s with _ -> true | exception _ -> false

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let split_logical l = List.filter (fun s -> s <> "") (String.split_on_char '.' l)

(* Every .v file under [dir], with the relative directory components of each.
   Walked with [lstat]: a symbolic link anywhere below a binding directory is
   refused, so a submitted project cannot reach outside its own tree. *)
let enumerate (dir : string) : ((string * string list) list, string) result =
  let rec walk acc dir rel =
    match Sys.readdir dir with
    | exception Sys_error m -> Result.Error m
    | entries ->
      Array.sort String.compare entries;
      Array.fold_left
        (fun acc e ->
           let* acc = acc in
           if skip_entry e then Result.Ok acc
           else
             let p = Filename.concat dir e in
             match Unix.lstat p with
             | exception Unix.Unix_error _ -> Result.Ok acc
             | { Unix.st_kind = Unix.S_LNK; _ } ->
               Result.Error ("symbolic link " ^ p ^ " inside a project directory is not allowed")
             | { Unix.st_kind = Unix.S_DIR; _ } ->
               if valid_id e then walk acc p (rel @ [ e ]) else Result.Ok acc
             | { Unix.st_kind = Unix.S_REG; _ } when Filename.check_suffix e ".v" ->
               let base = Filename.chop_suffix e ".v" in
               if valid_id base then Result.Ok ((Config.normalize_path p, rel @ [ base ]) :: acc)
               else Result.Ok acc
             | _ -> Result.Ok acc)
        (Result.Ok acc) entries
  in
  let* l = walk [] dir [] in
  Result.Ok (List.rev l)

let make_binding ~dir ~logical ~implicit =
  let* files = enumerate dir in
  let prefix = split_logical logical in
  Result.Ok
    { dir = Config.normalize_path dir; logical; implicit;
      files = List.map (fun (p, comps) -> (p, String.concat "." (prefix @ comps))) files }

(* A file under nested bindings belongs to the deepest one (its logical name
   there is the one coqdep would use); the other binding forgets it. *)
let assign_nested (bs : binding list) : binding list =
  let owner p =
    List.fold_left
      (fun best b ->
         if List.mem_assoc p b.files then
           match best with
           | Some o when String.length o.dir >= String.length b.dir -> best
           | _ -> Some b
         else best)
      None bs
  in
  List.map
    (fun b -> { b with files = List.filter (fun (p, _) -> match owner p with Some o -> o == b | None -> false) b.files })
    bs

let duplicate_names (bs : binding list) =
  let names = List.concat_map (fun b -> List.map snd b.files) bs in
  let sorted = List.sort String.compare names in
  let rec go = function
    | a :: (b :: _ as tl) -> if a = b then Some a else go tl
    | _ -> None
  in
  go sorted

(* One flag policy for _CoqProject [-arg] and dune [(flags ...)]: warning
   selectors are accepted (and ignored, warnings are swallowed anyway), the
   kernel flags only when they equal the config's, anything else is refused. *)
let check_flags ~(flags : flags) (tokens : string list) : (unit, string) result =
  let tokens = List.concat_map (String.split_on_char ' ') tokens |> List.filter (( <> ) "") in
  let rec go = function
    | [] -> Result.Ok ()
    | ":standard" :: tl -> go tl
    | "-w" :: _ :: tl -> go tl
    | "-impredicative-set" :: tl when flags.impredicative_set -> go tl
    | "-indices-matter" :: tl when flags.indices_matter -> go tl
    | "-noinit" :: tl when flags.noinit -> go tl
    | x :: _ ->
      Result.Error
        ("the project file passes the flag " ^ x
         ^ ", which the comparator does not accept (only -w selectors, and the kernel flags \
            when they match the config)")
  in
  go tokens

(* ---- _CoqProject ------------------------------------------------------- *)

(* A few argument arms of Rocq's parser [CoqProject_file.process_cmd_line]
   call [exit 1] instead of raising: a bare -impredicative-set (it wants -arg
   -impredicative-set), an unknown -native-compiler value (on its own line, or
   under -arg where the values are re-split and parsed again), and a repeated
   -docroot or -generate-meta-for-package.  Inside the sandbox that exit would
   surface as a sandbox_error (exit 2) for what is a malformed submission, so
   these arms are refused before the parser runs.  Its tokenizer is not
   exported; [tokens] mirrors it: whitespace separates, # starts a comment to
   the end of the line, "..." quotes. *)
let tokens (s : string) : (string list, string) result =
  let n = String.length s in
  let rec go acc i =
    if i >= n then Result.Ok (List.rev acc)
    else
      match s.[i] with
      | ' ' | '\n' | '\r' | '\t' -> go acc (i + 1)
      | '#' -> go acc (comment i)
      | '"' -> (
        match String.index_from_opt s (i + 1) '"' with
        | None -> Result.Error "unterminated string"
        | Some j -> go (String.sub s (i + 1) (j - i - 1) :: acc) (j + 1))
      | _ ->
        let j = ref i in
        while !j < n && not (List.mem s.[!j] [ ' '; '\n'; '\r'; '\t'; '#' ]) do incr j done;
        go (String.sub s i (!j - i) :: acc) !j
  and comment i = if i >= n || s.[i] = '\n' then i + 1 else comment (i + 1) in
  go [] 0

let check_exit_arms (toks : string list) : (unit, string) result =
  let rec go seen = function
    | [] -> Result.Ok ()
    | "-impredicative-set" :: _ ->
      Result.Error "-impredicative-set is only accepted as -arg -impredicative-set"
    | ("-Q" | "-R") :: _ :: _ :: r -> go seen r
    | "-native-compiler" :: v :: r when List.mem v [ "yes"; "no"; "ondemand" ] -> go seen r
    | "-native-compiler" :: v :: _ -> Result.Error ("invalid -native-compiler value " ^ v)
    | "-arg" :: a :: r ->
      let unquoted = String.concat "" (String.split_on_char '\'' a) in
      if CString.string_contains ~where:unquoted ~what:"-native-compiler" then
        Result.Error "-native-compiler is not accepted under -arg"
      else go seen r
    | (("-docroot" | "-generate-meta-for-package") as o) :: _ :: r ->
      if List.mem o seen then Result.Error ("option " ^ o ^ " given more than once")
      else go (o :: seen) r
    | _ :: r -> go seen r
  in
  go [] toks

(* Rocq's own parser [CoqProject_file.read_project_file] resolves paths
   relative to the project file's directory; [.path] (not [.canonical_path])
   keeps symlinks unresolved so directories compare verbatim. *)
let coqproject ~(flags : flags) (path : string) : (t, string) result =
  let open CoqProject_file in
  let* toks =
    match tokens (read_file path) with
    | Result.Ok t -> Result.Ok t
    | Result.Error m -> Result.Error ("cannot parse " ^ path ^ ": " ^ m)
    | exception Sys_error m -> Result.Error ("cannot open " ^ path ^ ": " ^ m)
  in
  let* () = Result.map_error (fun m -> path ^ ": " ^ m) (check_exit_arms toks) in
  match read_project_file ~warning_fn:(fun _ -> ()) path with
  | exception Parsing_error m -> Result.Error ("cannot parse " ^ path ^ ": " ^ m)
  | exception UnableToOpenProjectFile m -> Result.Error ("cannot open " ^ path ^ ": " ^ m)
  | proj ->
    let* () =
      match proj.ml_includes with
      | [] -> Result.Ok ()
      | { thing = { path = d; _ }; _ } :: _ ->
        Result.Error (path ^ " adds the ML path " ^ d ^ " with -I, which is not allowed")
    in
    let* () =
      match proj.native_compiler with
      | None | Some NativeNo -> Result.Ok ()
      | Some (NativeYes | NativeOndemand) ->
        Result.Error (path ^ " enables the native compiler, which is not allowed")
    in
    let* () = check_flags ~flags (List.map (fun a -> a.thing) proj.extra_args) in
    let mk implicit { thing = ({ path = d; _ }, l); _ } = make_binding ~dir:d ~logical:l ~implicit in
    let* q = List.fold_right (fun e acc -> let* acc = acc in let* b = mk false e in Result.Ok (b :: acc)) proj.q_includes (Result.Ok []) in
    let* r = List.fold_right (fun e acc -> let* acc = acc in let* b = mk true e in Result.Ok (b :: acc)) proj.r_includes (Result.Ok []) in
    let bindings = assign_nested (q @ r) in
    match duplicate_names bindings with
    | Some n -> Result.Error (path ^ ": two files have the logical name " ^ n)
    | None ->
      Result.Ok
        { root = Config.normalize_path (Filename.dirname path);
          project_file = Config.normalize_path path; bindings; theories = [] }

(* ---- dune ---------------------------------------------------------------- *)

type sexp = Atom of string | List of sexp list

(* Atoms, "quoted strings" with backslash escapes, ; comments.  Enough for
   the stanzas we read; anything fancier fails to parse and is refused. *)
let parse_sexps (s : string) : (sexp list, string) result =
  let n = String.length s in
  let i = ref 0 in
  let rec skip_ws () =
    if !i < n then
      match s.[!i] with
      | ' ' | '\t' | '\n' | '\r' -> incr i; skip_ws ()
      | ';' ->
        while !i < n && s.[!i] <> '\n' do incr i done;
        skip_ws ()
      | _ -> ()
  in
  let rec value () =
    skip_ws ();
    if !i >= n then Result.Error "unexpected end of file"
    else
      match s.[!i] with
      | '(' ->
        incr i;
        let* l = items [] in
        Result.Ok (List l)
      | ')' -> Result.Error "unexpected )"
      | '"' ->
        incr i;
        let b = Buffer.create 16 in
        let rec go () =
          if !i >= n then Result.Error "unterminated string"
          else
            match s.[!i] with
            | '"' -> incr i; Result.Ok (Atom (Buffer.contents b))
            | '\\' when !i + 1 < n -> Buffer.add_char b s.[!i + 1]; i := !i + 2; go ()
            | c -> Buffer.add_char b c; incr i; go ()
        in
        go ()
      | _ ->
        let start = !i in
        while !i < n && (match s.[!i] with ' ' | '\t' | '\n' | '\r' | '(' | ')' | '"' | ';' -> false | _ -> true) do
          incr i
        done;
        Result.Ok (Atom (String.sub s start (!i - start)))
  and items acc =
    skip_ws ();
    if !i >= n then Result.Error "missing )"
    else if s.[!i] = ')' then (incr i; Result.Ok (List.rev acc))
    else
      let* v = value () in
      items (v :: acc)
  in
  let rec top acc =
    skip_ws ();
    if !i >= n then Result.Ok (List.rev acc)
    else
      let* v = value () in
      top (v :: acc)
  in
  top []

type theory = {
  th_dir : string;
  th_name : string;
  th_modules : string list option;
  th_theories : string list;
}

type include_subdirs = No | Qualified

let atoms (l : sexp list) = List.filter_map (function Atom a -> Some a | List _ -> None) l

let has_variable a =
  let n = String.length a in
  let rec go i = i + 1 < n && ((a.[i] = '%' && a.[i + 1] = '{') || go (i + 1)) in
  go 0

(* The stanzas of one dune file we care about: the include_subdirs mode it
   declares, and its coq.theory / rocq.theory stanzas.  Unknown stanzas and
   fields are ignored; the ones that would change what gets compiled or how
   are refused. *)
let read_dune ~(flags : flags) (path : string) :
  (include_subdirs option * theory list, string) result =
  let dir = Config.normalize_path (Filename.dirname path) in
  let* sexps =
    match parse_sexps (read_file path) with
    | Result.Ok l -> Result.Ok l
    | Result.Error m -> Result.Error ("cannot parse " ^ path ^ ": " ^ m)
    | exception Sys_error m -> Result.Error m
  in
  let refuse what = Result.Error (path ^ ": " ^ what) in
  List.fold_left
    (fun acc stanza ->
       let* mode, ths = acc in
       match stanza with
       | List (Atom "include_subdirs" :: rest) -> (
         match atoms rest with
         | [ "no" ] -> Result.Ok (Some No, ths)
         | [ "qualified" ] -> Result.Ok (Some Qualified, ths)
         | _ -> refuse "only (include_subdirs no) and (include_subdirs qualified) are supported")
       | List (Atom ("include" | "subdir") :: _) ->
         refuse "(include ...) and (subdir ...) stanzas are not supported"
       | List (Atom ("coq.theory" | "rocq.theory") :: fields) ->
         let field k =
           List.find_map
             (function List (Atom k' :: v) when k = k' -> Some v | _ -> None)
             fields
         in
         let* () =
           if List.exists (fun f -> has_variable (String.concat " " (atoms (match f with List l -> l | Atom a -> [ Atom a ])))) fields
           then refuse "%{...} variables are not supported"
           else Result.Ok ()
         in
         let* name =
           match field "name" with
           | Some [ Atom n ] -> Result.Ok n
           | _ -> refuse "a theory needs a (name ...)"
         in
         let* () =
           match field "flags" with
           | None -> Result.Ok ()
           | Some l -> (
             match check_flags ~flags (atoms l) with
             | Result.Ok () when List.length (atoms l) = List.length l -> Result.Ok ()
             | Result.Ok () -> refuse "unsupported (flags ...) form"
             | Result.Error m -> refuse m)
         in
         let* () =
           match field "modules_flags" with
           | None -> Result.Ok ()
           | Some _ -> refuse "(modules_flags ...) is not supported"
         in
         let* () =
           match field "stdlib", field "boot" with
           | (None | Some [ Atom "yes" ]), None -> Result.Ok ()
           | _ when flags.noinit -> Result.Ok ()
           | _ -> refuse "(stdlib no) / (boot) need \"noinit\": true in the config"
         in
         let* modules =
           match field "modules" with
           | None -> Result.Ok None
           | Some l ->
             let ms = atoms l in
             if List.length ms <> List.length l
                || List.exists (fun m -> m = "\\" || m = ":standard" || String.contains m '*') ms
             then refuse "(modules ...) must be a plain list of module names"
             else Result.Ok (Some ms)
         in
         let theories = match field "theories" with Some l -> atoms l | None -> [] in
         Result.Ok (mode, { th_dir = dir; th_name = name; th_modules = modules; th_theories = theories } :: ths)
       | _ -> Result.Ok (mode, ths))
    (Result.Ok (None, [])) sexps

(* All dune files under [root], skipping hidden/_build/_opam directories and
   directories that start another dune project. *)
let dune_files (root : string) : string list =
  let rec walk acc dir =
    match Sys.readdir dir with
    | exception Sys_error _ -> acc
    | entries ->
      Array.sort String.compare entries;
      Array.fold_left
        (fun acc e ->
           if skip_entry e then acc
           else
             let p = Filename.concat dir e in
             match Unix.lstat p with
             | exception Unix.Unix_error _ -> acc
             | { Unix.st_kind = Unix.S_DIR; _ } ->
               if Sys.file_exists (Filename.concat p "dune-project") then acc else walk acc p
             | { Unix.st_kind = Unix.S_REG; _ } when e = "dune" -> p :: acc
             | _ -> acc)
        acc entries
  in
  List.rev (walk [] root)

let dune_project ~(flags : flags) (root : string) : (t, string) result =
  let root = Config.normalize_path root in
  let files = dune_files root in
  let* parsed =
    List.fold_right
      (fun f acc ->
         let* acc = acc in
         let* mode, ths = read_dune ~flags f in
         Result.Ok ((Config.normalize_path (Filename.dirname f), mode, ths) :: acc))
      files (Result.Ok [])
  in
  let dirs_with_dune = List.map (fun (d, _, _) -> d) parsed in
  let declared d = List.find_map (fun (d', m, _) -> if d = d' then m else None) parsed in
  let theory_dirs = List.concat_map (fun (_, _, ths) -> List.map (fun t -> t.th_dir) ths) parsed in
  (* the include_subdirs mode in effect at [d]: its own declaration, else the
     nearest ancestor's inside the project *)
  let rec mode_at d =
    match declared d with
    | Some m -> m
    | None -> if d = root || String.length d <= String.length root then No else mode_at (Filename.dirname d)
  in
  let theories = List.concat_map (fun (_, _, ths) -> ths) parsed in
  let* bindings =
    List.fold_right
      (fun th acc ->
         let* acc = acc in
         let* all = enumerate th.th_dir in
         let in_scope (_, comps) =
           match mode_at th.th_dir with
           | No -> List.length comps = 1
           | Qualified ->
             (* every directory between the theory root and the file must keep
                the qualified mode and must not start another theory *)
             let rec ok d = function
               | [] | [ _ ] -> true
               | c :: tl ->
                 let d' = Filename.concat d c in
                 (not (List.mem d' theory_dirs))
                 && (not (List.mem d' dirs_with_dune && declared d' = Some No))
                 && ok d' tl
             in
             ok th.th_dir comps
         in
         let files = List.filter in_scope all in
         let files =
           match th.th_modules with
           | None -> files
           | Some ms ->
             List.filter
               (fun (_, comps) ->
                  List.mem (String.concat "." comps) ms
                  || List.mem (List.nth comps (List.length comps - 1)) ms)
               files
         in
         let prefix = split_logical th.th_name in
         Result.Ok
           ({ dir = th.th_dir; logical = th.th_name; implicit = true;
              files = List.map (fun (p, comps) -> (p, String.concat "." (prefix @ comps))) files }
            :: acc))
      theories (Result.Ok [])
  in
  match duplicate_names bindings with
  | Some n -> Result.Error (root ^ ": two files have the logical name " ^ n)
  | None ->
    Result.Ok
      { root; project_file = Filename.concat root "dune-project"; bindings;
        theories = List.sort_uniq String.compare (List.concat_map (fun t -> t.th_theories) theories) }

(* ---- discovery ------------------------------------------------------------ *)

let find_file (p : t) (path : string) : (binding * string) option =
  let path = Config.normalize_path path in
  List.find_map
    (fun b -> match List.assoc_opt path b.files with Some l -> Some (b, l) | None -> None)
    p.bindings

let of_project_file ~flags path =
  if Filename.basename path = "dune-project" then dune_project ~flags (Filename.dirname path)
  else coqproject ~flags path

(* The project of [file]: the override if given ("" disables discovery), else
   the nearest ancestor directory with a _CoqProject (preferred) or a
   dune-project.  [None] when there is no project file, or when the file is
   not covered by any of the project's bindings: then the file is a plain
   single file, exactly as before this feature. *)
let discover ~(flags : flags) ?override (file : string) : (t option, string) result =
  let covering p = if find_file p file <> None then Some p else None in
  match override with
  | Some "" -> Result.Ok None
  | Some pf ->
    if not (Sys.file_exists pf) then Result.Error ("project file not found: " ^ pf)
    else
      let* p = of_project_file ~flags pf in
      Result.Ok (covering p)
  | None ->
    let rec up dir =
      let cp = Filename.concat dir "_CoqProject" and dp = Filename.concat dir "dune-project" in
      if Sys.file_exists cp then
        let* p = coqproject ~flags cp in
        Result.Ok (covering p)
      else if Sys.file_exists dp then
        let* p = dune_project ~flags dir in
        Result.Ok (covering p)
      else
        let parent = Filename.dirname dir in
        if parent = dir then Result.Ok None else up parent
    in
    up (Filename.dirname (Config.normalize_path file))

(* The logical name of the challenge library: the explicit [top], else the
   name the challenge's project gives the file, else Config's load-path
   derivation.  Called in the outer process before Rocq is initialised. *)
let top_name (c : Config.t) : string =
  match c.Config.top with
  | Some t -> t
  | None -> (
    let flags =
      { impredicative_set = c.Config.impredicative_set; indices_matter = c.Config.indices_matter;
        noinit = c.Config.noinit }
    in
    let override =
      match c.Config.coqproject with
      | None -> None
      | Some "" -> Some ""
      | Some p -> Some (Config.absolute ~dir:c.Config.config_dir p)
    in
    let file = Config.challenge_path c in
    match discover ~flags ?override file with
    | Result.Ok (Some p) -> (
      match find_file p file with Some (_, l) -> l | None -> Config.top_name c)
    | Result.Ok None | Result.Error _ -> Config.top_name c)
