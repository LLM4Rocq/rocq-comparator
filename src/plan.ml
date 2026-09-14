(* The compilation plan for a project run (DESIGN.md section 16).

   From the challenge's and the solution's projects (Project.discover) the
   plan computes, with coqdep's own library (Coqdeplib), the transitive
   Require closure of each side and applies the trust rule literally:

     TRUSTED   = the challenge's closure, restricted to the challenge's own
                 project (the analogue of Lean's assumption 1);
     UNTRUSTED = the solution's closure minus TRUSTED.

   Each helper is compiled by the comparator under its own logical name and
   saved as a .vo into a MIRROR of its binding directory under the run's
   scratch: trusted helpers under scratch/trusted, untrusted ones under
   scratch/untrusted.  Only the mirrors are ever bound on the load path, so
   no .vo the solver shipped (or a stale one next to a source) can be loaded.

   The plan is computed before Rocq is initialised (the mirror bindings are
   part of the init arguments), except [check_installed], which needs the
   switch's load path. *)

open Names

type entry = {
  path : string;  (** absolute .v path *)
  logical : DirPath.t;
  name : string;  (** logical name as a string *)
  binding : int;  (** index into [bindings] *)
  rel : string list;  (** directory components below the binding directory *)
  from_challenge_project : bool;
}

type t = {
  bindings : (Project.binding * bool) list;  (** binding, belongs to the challenge project *)
  challenge_project : Project.t option;
  solution_project : Project.t option;
  trusted : entry list;  (** dependency order *)
  untrusted : entry list;  (** dependency order *)
}

let empty =
  { bindings = []; challenge_project = None; solution_project = None; trusted = []; untrusted = [] }

let is_empty p = p.trusted = [] && p.untrusted = []

(* Untrusted source is compiled with a wall-clock budget, but a dependency
   graph that is merely large can exhaust it late; these caps fail fast. *)
let max_untrusted_files = 100
let max_untrusted_bytes = 8_000_000

let ( let* ) = Result.bind

let flags_of (c : Config.t) : Project.flags =
  { Project.impredicative_set = c.Config.impredicative_set;
    indices_matter = c.Config.indices_matter; noinit = c.Config.noinit }

let override (c : Config.t) =
  match c.Config.coqproject with
  | None -> None
  | Some "" -> Some ""
  | Some p -> Some (Config.absolute ~dir:c.Config.config_dir p)

let dirpath s =
  match Libnames.dirpath_of_string s with
  | dp -> Result.Ok dp
  | exception _ -> Result.Error (s ^ " is not a valid logical name")

(* ---- scratch layout ------------------------------------------------------ *)

let trusted_dir scratch = Filename.concat scratch "trusted"
let untrusted_dir scratch = Filename.concat scratch "untrusted"

let mirror ~scratch ~trusted i =
  Filename.concat (if trusted then trusted_dir scratch else untrusted_dir scratch)
    ("b" ^ string_of_int i)

let vo_dir ~scratch ~trusted (e : entry) =
  List.fold_left Filename.concat (mirror ~scratch ~trusted e.binding) e.rel

let vo_path ~scratch ~trusted (e : entry) =
  let _, base = Libnames.split_dirpath e.logical in
  Filename.concat (vo_dir ~scratch ~trusted e) (Id.to_string base ^ ".vo")

let rec mkdir_p d =
  if not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* Every mirror directory a side's .vo files will live in must exist before
   Rocq is initialised: [Loadpath.add_vo_path] enumerates subdirectories at
   that moment and the result is frozen into the root state. *)
let mkdirs (p : t) ~scratch ~trusted =
  List.iter (fun e -> mkdir_p (vo_dir ~scratch ~trusted e)) (if trusted then p.trusted else p.untrusted)

let sides (p : t) = [ (true, p.trusted); (false, p.untrusted) ]

(* -Q/-R arguments binding the mirrors that hold at least one planned file.
   Untrusted mirrors first, trusted last: Rocq searches the most recently
   added binding first, though with unique names order never decides. *)
let mirror_args ?(trusted_only = false) (p : t) ~scratch : string list =
  List.concat_map
    (fun (trusted, entries) ->
       if (not trusted) && trusted_only then []
       else
         let idxs = List.sort_uniq compare (List.map (fun e -> e.binding) entries) in
         List.concat_map
           (fun i ->
              let b, _ = List.nth p.bindings i in
              [ (if b.Project.implicit then "-R" else "-Q"); mirror ~scratch ~trusted i; b.Project.logical ])
           idxs)
    [ (false, p.untrusted); (true, p.trusted) ]

let mirror_dirs (p : t) ~scratch : string list =
  List.concat_map
    (fun (trusted, entries) ->
       List.sort_uniq compare (List.map (fun e -> mirror ~scratch ~trusted e.binding) entries))
    (sides p)

(* Non-empty logical prefixes of the bindings in use, for permitted_libraries. *)
let binding_logicals (p : t) : string list =
  List.filter_map (fun (b, _) -> if b.Project.logical = "" then None else Some b.Project.logical) p.bindings
  |> List.sort_uniq String.compare

(* ---- the closure ---------------------------------------------------------- *)

(* The Require statements of a file, read with coqdep's own lexer
   (Rocqdep_lexer, the one unit of that library that can be linked into a
   Rocq process): [(from, qualids)] per Require.  Load / Declare ML Module /
   Extra Dependency are ignored here; the filter refuses them anyway. *)
let requires (path : string) : ((string list option * string list list) list, string) result =
  match open_in_bin path with
  | exception Sys_error m -> Result.Error m
  | ic ->
    let lb = Lexing.from_channel ~with_positions:false ic in
    let rec loop acc =
      match Rocqdep_lexer.coq_action lb with
      | Rocqdep_lexer.Require (from, l) -> loop ((from, l) :: acc)
      | Rocqdep_lexer.Declare _ | Rocqdep_lexer.Load _ | Rocqdep_lexer.External _ -> loop acc
      | exception Rocqdep_lexer.Fin_fichier -> Result.Ok (List.rev acc)
      | exception Rocqdep_lexer.Syntax_error _ -> Result.Error ("cannot lex " ^ path)
    in
    let r = loop [] in
    close_in ic;
    r

let rec is_suffix a b =
  (* [a] is a suffix of [b] *)
  let la = List.length a and lb = List.length b in
  la <= lb && (la = lb && a = b || is_suffix a (List.tl b))

let rec is_prefix a b = match a, b with
  | [], _ -> true
  | x :: a, y :: b -> x = y && is_prefix a b
  | _ :: _, [] -> false

let rec drop n l = if n = 0 then l else match l with [] -> [] | _ :: tl -> drop (n - 1) tl

(* Which planned files a Require names, with Rocq's own rule
   (Loadpath.locate_qualified_library): [from @ dir] equal to the directory's
   logical path is an exact match; under an implicit (-R) binding a suffix
   match is enough.  Exact matches win; two candidates in the same class are
   an ambiguity Rocq would reject too, so the plan rejects it first.  A
   Require that names no planned file is an installed library: Rocq resolves
   it at compile time from the trusted load path, or fails. *)
type closure_error =
  | Unreadable of string  (** a file that cannot be read or lexed *)
  | Cycle of string
  | Sink of entry * entry  (** a file requires one of the two top files *)
  | Ambiguous of entry * string * entry list  (** a Require matching several project files *)

let resolve (bindings : (Project.binding * bool) list) (entries : entry list) (e : entry)
    ((from, qid) : string list option * string list) : (entry option, closure_error) result =
  (* a challenge-project file sees only its own project (its Requires are
     resolved while the solution's mirrors are still empty); a solution-side
     file sees both projects, as it will at compile time *)
  let entries =
    if e.from_challenge_project then List.filter (fun (d : entry) -> d.from_challenge_project) entries
    else entries
  in
  match List.rev qid with
  | [] -> Result.Ok None
  | base :: rdir ->
    let dir = List.rev rdir in
    let candidates =
      List.filter_map
        (fun (e : entry) ->
           let b, _ = List.nth bindings e.binding in
           let comps = Project.split_logical e.name in
           match List.rev comps with
           | b' :: rlog when b' = base ->
             let log = List.rev rlog in
             let exact = log = (match from with Some f -> f @ dir | None -> dir) in
             let implicit =
               b.Project.implicit
               && (match from with
                   | None -> is_suffix dir log
                   | Some f -> is_prefix f log && is_suffix dir (drop (List.length f) log))
             in
             if exact then Some (0, e) else if implicit then Some (1, e) else None
           | _ -> None)
        entries
    in
    let pick k = List.filter_map (fun (k', e) -> if k = k' then Some e else None) candidates in
    let name =
      (match from with Some f -> "From " ^ String.concat "." f ^ " " | None -> "")
      ^ "Require " ^ String.concat "." qid
    in
    match pick 0 with
    | [ d ] -> Result.Ok (Some d)
    | _ :: _ :: _ as l -> Result.Error (Ambiguous (e, name, l))
    | [] -> (
      match pick 1 with
      | [ d ] -> Result.Ok (Some d)
      | _ :: _ :: _ as l -> Result.Error (Ambiguous (e, name, l))
      | [] -> Result.Ok None)

let dependencies (bindings : (Project.binding * bool) list) (entries : entry list) :
  (entry -> (entry list, closure_error) result) =
  fun e ->
    let* reqs = match requires e.path with Result.Ok r -> Result.Ok r | Result.Error m -> Result.Error (Unreadable m) in
    List.fold_left
      (fun acc (from, qids) ->
         let* acc = acc in
         List.fold_left
           (fun acc q ->
              let* acc = acc in
              let* r = resolve bindings entries e (from, q) in
              Result.Ok (match r with Some d when not (List.memq d acc) -> acc @ [ d ] | _ -> acc))
           (Result.Ok acc) qids)
      (Result.Ok []) reqs

(* Depth-first postorder from [start]: the files [start] transitively
   Requires, dependencies first, [start] itself excluded.  [stop] marks files
   the walk does not enter (already classified); [sink] files may not be
   Required at all (the two top files). *)
let closure ~deps ~stop ~sink (start : entry) : (entry list, closure_error) result =
  let visiting = Hashtbl.create 16 and done_ = Hashtbl.create 16 in
  let order = ref [] in
  let rec visit (e : entry) : (unit, closure_error) result =
    if Hashtbl.mem done_ e.path || stop e then Result.Ok ()
    else if Hashtbl.mem visiting e.path then Result.Error (Cycle e.name)
    else begin
      Hashtbl.replace visiting e.path ();
      let* ds = deps e in
      let* () =
        List.fold_left
          (fun acc (d : entry) ->
             let* () = acc in
             if sink d then Result.Error (Sink (e, d)) else visit d)
          (Result.Ok ()) ds
      in
      Hashtbl.remove visiting e.path;
      Hashtbl.replace done_ e.path ();
      if e != start then order := e :: !order;
      Result.Ok ()
    end
  in
  let* () = visit start in
  Result.Ok (List.rev !order)

let overlaps = Shadowing.overlaps

let file_size p = try (Unix.stat p).Unix.st_size with _ -> 0

(* ---- the plan --------------------------------------------------------------- *)

let entries_of (bindings : (Project.binding * bool) list) : (entry list, string) result =
  List.fold_left
    (fun acc (i, (b, from_challenge_project)) ->
       let* acc = acc in
       List.fold_left
         (fun acc (path, name) ->
            let* acc = acc in
            let* logical = dirpath name in
            let rel =
              let d = Filename.dirname path in
              let n = String.length b.Project.dir in
              let r = if String.length d > n then String.sub d (n + 1) (String.length d - n - 1) else "" in
              List.filter (( <> ) "") (String.split_on_char '/' r)
            in
            Result.Ok ({ path; logical; name; binding = i; rel; from_challenge_project } :: acc))
         (Result.Ok acc) b.Project.files)
    (Result.Ok []) (List.mapi (fun i b -> (i, b)) bindings)
  |> Result.map List.rev

(* Errors on the challenge's side are the operator's (exit 2); errors on the
   solution's side are a verdict about the solution (exit 1), so that a
   malformed submission can never look like an infrastructure failure. *)
let make ?(with_solution = true) (cfg : Config.t) : (t, Verdict.reason * string) result =
  let flags = flags_of cfg in
  let override = override cfg in
  let challenge = Config.normalize_path (Config.challenge_path cfg) in
  let solution = Config.normalize_path (Config.solution_path cfg) in
  let* cp =
    match Project.discover ~flags ?override challenge with
    | Result.Ok p -> Result.Ok p
    | Result.Error m -> Result.Error (Verdict.Config_error, "the challenge's project: " ^ m)
  in
  let* sp =
    if not with_solution then Result.Ok None
    else
      match cp with
      | Some p when Project.find_file p solution <> None -> Result.Ok (Some p)
      | _ -> (
        match Project.discover ~flags ?override solution with
        | Result.Ok p -> Result.Ok p
        | Result.Error m -> Result.Error (Verdict.Compile_error, "the solution's project: " ^ m))
  in
  if cp = None && sp = None then Result.Ok empty
  else
    let shared = match cp, sp with Some a, Some b -> a.Project.root = b.Project.root | _ -> false in
    let bindings =
      (match cp with Some p -> List.map (fun b -> (b, true)) p.Project.bindings | None -> [])
      @ (match sp with Some p when not shared -> List.map (fun b -> (b, false)) p.Project.bindings | _ -> [])
    in
    let* entries =
      match entries_of bindings with
      | Result.Ok e -> Result.Ok e
      | Result.Error m -> Result.Error (Verdict.Config_error, m)
    in
    let find path = List.find_opt (fun e -> e.path = path) entries in
    let challenge_e = find challenge and solution_e = find solution in
    let tops = List.filter_map (fun x -> x) [ challenge_e; solution_e ] in
    let is_top (e : entry) = List.exists (fun (t : entry) -> t.path = e.path) tops in
    let deps = dependencies bindings entries in
    let* top = match dirpath (Project.top_name cfg) with
      | Result.Ok t -> Result.Ok t
      | Result.Error m -> Result.Error (Verdict.Config_error, m) in
    let where (e : entry) = e.name ^ " (" ^ e.path ^ ")" in
    let describe = function
      | Unreadable m -> m
      | Cycle n -> "circular Require through " ^ n
      | Sink (e, d) -> where e ^ " requires " ^ d.name ^ ", which is one of the two files under comparison"
      | Ambiguous (e, name, l) ->
        where e ^ ": " ^ name ^ " matches several project files: "
        ^ String.concat ", " (List.map (fun (d : entry) -> d.path) l)
    in
    (* trusted: the challenge's closure inside its own project *)
    let* trusted =
      match challenge_e with
      | None -> Result.Ok []
      | Some c -> (
        match closure ~deps ~stop:(fun _ -> false) ~sink:is_top c with
        | Result.Error err -> Result.Error (Verdict.Challenge_error, describe err)
        | Result.Ok l ->
          match List.find_opt (fun e -> not e.from_challenge_project) l with
          | Some e ->
            Result.Error
              (Verdict.Challenge_error,
               "the challenge requires " ^ e.name ^ ", which comes from the solution's project (" ^ e.path
               ^ ") and cannot be trusted")
          | None -> Result.Ok l)
    in
    let is_trusted e = List.exists (fun t -> t.path = e.path) trusted in
    (* on the solution's side an unreadable file or a cycle is the solver's
       compile error; requiring a top file, or a Require that could name a
       trusted file as well as the solver's own, is a library violation *)
    let* untrusted =
      match solution_e with
      | None -> Result.Ok []
      | Some s -> (
        match closure ~deps ~stop:is_trusted ~sink:is_top s with
        | Result.Error ((Unreadable _ | Cycle _) as err) -> Result.Error (Verdict.Compile_error, describe err)
        | Result.Error (Sink _ as err) -> Result.Error (Verdict.Library_violation, describe err)
        | Result.Error (Ambiguous (_, _, l) as err) ->
          if List.exists (fun (d : entry) -> is_trusted d || d.from_challenge_project) l then
            Result.Error (Verdict.Library_violation, describe err)
          else Result.Error (Verdict.Compile_error, describe err)
        | Result.Ok l -> Result.Ok l)
    in
    let violation m = Result.Error (Verdict.Library_violation, m) in
    (* a helper may not carry a name that collides with the two top files *)
    let* () =
      List.fold_left
        (fun acc (e : entry) ->
           let* () = acc in
           if overlaps e.logical top then
             let m = e.name ^ " (" ^ e.path ^ ") collides with the top library name " ^ DirPath.to_string top in
             if is_trusted e then Result.Error (Verdict.Config_error, m) else violation m
           else Result.Ok ())
        (Result.Ok ()) (trusted @ untrusted)
    in
    (* an untrusted file may never share, or nest under, a trusted name: the
       imported axiom policy is a prefix rule over library names *)
    let* () =
      List.fold_left
        (fun acc (u : entry) ->
           let* () = acc in
           match List.find_opt (fun (t : entry) -> overlaps u.logical t.logical) trusted with
           | None -> Result.Ok ()
           | Some t when DirPath.equal u.logical t.logical ->
             violation ("the untrusted file " ^ u.path ^ " has the logical name " ^ u.name
                        ^ ", which is also the name of the trusted file " ^ t.path)
           | Some t ->
             violation ("the untrusted file " ^ u.path ^ " (" ^ u.name ^ ") overlaps the trusted library "
                        ^ t.name ^ " (" ^ t.path ^ ")"))
        (Result.Ok ()) untrusted
    in
    (* two projects: no solution binding may overlap a challenge binding *)
    let* () =
      if shared then Result.Ok ()
      else
        List.fold_left
          (fun acc (bu, from_c) ->
             let* () = acc in
             if from_c || bu.Project.logical = "" then Result.Ok ()
             else
               match
                 List.find_opt
                   (fun (bt, from_c) -> from_c && bt.Project.logical <> ""
                                        && (match dirpath bu.Project.logical, dirpath bt.Project.logical with
                                            | Result.Ok a, Result.Ok b -> overlaps a b
                                            | _ -> false))
                   bindings
               with
               | None -> Result.Ok ()
               | Some (bt, _) ->
                 violation ("the solution's project binds " ^ bu.Project.dir ^ " to " ^ bu.Project.logical
                            ^ ", which shadows the challenge project's namespace " ^ bt.Project.logical
                            ^ " (" ^ bt.Project.dir ^ ")"))
          (Result.Ok ()) bindings
    in
    let* () =
      let n = List.length untrusted in
      let bytes = List.fold_left (fun a e -> a + file_size e.path) 0 untrusted in
      if n > max_untrusted_files then
        Result.Error (Verdict.Compile_error, Printf.sprintf "the solution requires %d project files, more than the limit of %d" n max_untrusted_files)
      else if bytes > max_untrusted_bytes then
        Result.Error (Verdict.Compile_error, Printf.sprintf "the solution's project files total %d bytes, more than the limit of %d" bytes max_untrusted_bytes)
      else Result.Ok ()
    in
    Result.Ok { bindings; challenge_project = cp; solution_project = sp; trusted; untrusted }

(* ---- after Driver.init ------------------------------------------------------ *)

(* Every planned name and binding is checked against the namespaces the
   switch itself owns (Shadowing's list-free rule), before anything is
   compiled; and every dune (theories ...) name must be a project binding or
   an installed logical path. *)
let check_installed (p : t) : (unit, Verdict.reason * string) result =
  let switch = Shadowing.switch_logical () in
  let clash (dp : DirPath.t) = List.find_opt (fun s -> overlaps dp s) switch in
  let* () =
    List.fold_left
      (fun acc (trusted, entries) ->
         List.fold_left
           (fun acc (e : entry) ->
              let* () = acc in
              match clash e.logical with
              | None -> Result.Ok ()
              | Some s ->
                Result.Error
                  (Verdict.Library_violation,
                   Printf.sprintf
                     "the %s file %s has the logical name %s, which shadows the installed namespace %s; \
                      an installed library must be provided by the switch, not by a project"
                     (if trusted then "project" else "solution's") e.path e.name (DirPath.to_string s)))
           acc entries)
      (Result.Ok ()) (sides p)
  in
  let* () =
    List.fold_left
      (fun acc (b, _) ->
         let* () = acc in
         if b.Project.logical = "" then Result.Ok ()
         else
           match dirpath b.Project.logical with
           | Result.Error _ -> Result.Ok ()
           | Result.Ok dp -> (
             match clash dp with
             | None -> Result.Ok ()
             | Some s ->
               Result.Error
                 (Verdict.Library_violation,
                  Printf.sprintf "the project directory %s is bound to %s, which shadows the installed namespace %s"
                    b.Project.dir b.Project.logical (DirPath.to_string s))))
      (Result.Ok ()) p.bindings
  in
  let installed name =
    match dirpath name with
    | Result.Error _ -> false
    | Result.Ok dp ->
      let roots = Shadowing.switch_roots () in
      List.exists
        (fun e -> List.exists (fun r -> Config.is_under ~root:r (Loadpath.physical e)) roots)
        (Loadpath.find_with_logical_path dp)
  in
  let known = List.map (fun (b, _) -> b.Project.logical) p.bindings in
  List.fold_left
    (fun acc (proj, reason) ->
       let* () = acc in
       match proj with
       | None -> Result.Ok ()
       | Some pr ->
         List.fold_left
           (fun acc th ->
              let* () = acc in
              if List.mem th known || installed th then Result.Ok ()
              else
                Result.Error
                  (reason, pr.Project.project_file ^ " depends on the theory " ^ th
                           ^ ", which is neither installed nor part of the project"))
           (Result.Ok ()) pr.Project.theories)
    (Result.Ok ())
    [ (p.challenge_project, Verdict.Config_error);
      ((if p.solution_project == p.challenge_project then None else p.solution_project), Verdict.Compile_error) ]
