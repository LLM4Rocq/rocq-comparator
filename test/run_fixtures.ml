(* Runs the built rocq-comparator over every directory in test/fixtures/ and
   checks the verdict against that fixture's expected.json (DESIGN.md 11).

   expected.json keys:
     exit_code        (int, required)
     reason           (string, optional)
     detail_contains  (string, optional)
     checks           (object name -> "ok" | "skipped" | "fail", optional)
     manifest_trust   (object library name -> "installed" | "trusted" | "checked", optional)
     batch            (list of solution files; runs `batch` instead of `check`)
     oks              (list of bools, one per batch solution)
     note             (free text, ignored) *)

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic; s

(* Run argv, return (exit code, stdout, stderr). stderr goes to a temp file so
   that a chatty child cannot deadlock us by filling a pipe we are not
   reading yet. *)
let run ?(env = [||]) (argv : string list) =
  let prog = List.hd argv in
  let args = Array.of_list argv in
  let env = Array.append (Unix.environment ()) env in
  let out_r, out_w = Unix.pipe () in
  let err_path = Filename.temp_file "rcfix" ".err" in
  let err_fd = Unix.openfile err_path [ Unix.O_WRONLY; Unix.O_TRUNC ] 0o600 in
  let pid = Unix.create_process_env prog args env Unix.stdin out_w err_fd in
  Unix.close out_w;
  Unix.close err_fd;
  let b = Buffer.create 4096 and chunk = Bytes.create 65536 in
  let rec go () =
    match Unix.read out_r chunk 0 (Bytes.length chunk) with
    | 0 -> ()
    | n -> Buffer.add_subbytes b chunk 0 n; go ()
    | exception _ -> ()
  in
  go ();
  Unix.close out_r;
  let code = match snd (Unix.waitpid [] pid) with
    | Unix.WEXITED n -> n
    | Unix.WSIGNALED n | Unix.WSTOPPED n -> 128 + n
  in
  let err = read_file err_path in
  (try Sys.remove err_path with _ -> ());
  (code, Buffer.contents b, err)

let member k = function `Assoc l -> List.assoc_opt k l | _ -> None
let str k j = match member k j with Some (`String s) -> Some s | _ -> None
let int_ k j = match member k j with Some (`Int n) -> Some n | _ -> None

(* --- prebuild support (for the stdlib-shadowing fixture) --------------------
   A fixture may list, under "prebuild" in expected.json, .v files that must be
   compiled before the comparator runs (e.g. a fake Stdlib/Arith.v that the
   config then maps over the real one with -Q . "").  We never compile inside
   the repository -- that would drop .vo/.glob files into test/fixtures -- so
   the whole fixture is copied to a temporary directory, the prebuild files are
   compiled there with the switch's own rocq, and the comparator is pointed at
   the copy.  Returns the directory the fixture should actually run in. *)

let rec copy_tree src dst =
  match Sys.is_directory src with
  | true ->
    (try Unix.mkdir dst 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
    Array.iter (fun e -> copy_tree (Filename.concat src e) (Filename.concat dst e))
      (Sys.readdir src)
  | false ->
    let ic = open_in_bin src and oc = open_out_bin dst in
    let n = in_channel_length ic in
    output_string oc (really_input_string ic n);
    close_in ic; close_out oc
  | exception _ -> ()

(* the switch's rocq binary sits next to the comparator's opam bin; fall back
   to PATH (correct under `dune test` in the project switch) *)
let rocq_bin exe =
  let guess =
    try
      let root = Filename.(dirname (dirname (dirname (dirname exe)))) in
      let c = Filename.concat (Filename.concat root "_opam/bin") "rocq" in
      if Sys.file_exists c then Some c else None
    with _ -> None
  in
  match guess with Some p -> p | None -> "rocq"

(* A prebuild entry is either a file name (compiled in place with
   -Q <copy> "" so the fake library gets its intended logical name) or
   {"src", "top", "out"}: [src] compiled under the logical name [top] into
   the .vo [out], which makes a stale .vo next to a different source. *)
let prebuild ~exe ~dir files =
  let scratch = Filename.temp_file "rcfix_pb" "" in
  Sys.remove scratch;
  Unix.mkdir scratch 0o755;
  copy_tree dir scratch;
  let rocq = rocq_bin exe in
  List.iter
    (function
      | `String f ->
        let path = Filename.concat scratch f in
        ignore (run [ rocq; "compile"; "-Q"; scratch; ""; path ])
      | j -> (
        match str "src" j, str "top" j, str "out" j with
        | Some src, Some top, Some out ->
          ignore
            (run [ rocq; "compile"; "-top"; top; "-o"; Filename.concat scratch out;
                   Filename.concat scratch src ])
        | _ -> ()))
    files;
  scratch

let contains ~needle s =
  let n = String.length needle and m = String.length s in
  if n = 0 then true
  else
    let rec go i = i + n <= m && (String.sub s i n = needle || go (i + 1)) in
    go 0

let verdict_of_stdout out =
  let lines = String.split_on_char '\n' out in
  List.fold_left
    (fun acc l ->
       let l = String.trim l in
       if String.length l > 1 && l.[0] = '{' then
         match Yojson.Safe.from_string l with j -> Some j | exception _ -> acc
       else acc)
    None lines

type result = { name : string; pass : bool; why : string }

let check_one ~exe ~dir ~name ~expected ~env ~label =
  let cfg = Filename.concat dir "config.json" in
  let code, out, err = run ~env [ exe; "check"; cfg ] in
  match verdict_of_stdout out with
  | None ->
    { name = name ^ label; pass = false;
      why = Printf.sprintf "no JSON verdict on stdout (exit %d); stderr: %s" code
          (String.trim err) }
  | Some j ->
    let problems = ref [] in
    let add p = problems := p :: !problems in
    (match int_ "exit_code" expected with
     | Some want when want <> code ->
       add (Printf.sprintf "exit code %d, expected %d" code want)
     | _ -> ());
    (match str "reason" expected with
     | Some want ->
       let got = match str "reason" j with Some s -> s | None -> "null" in
       if got <> want then add (Printf.sprintf "reason %s, expected %s" got want)
     | None -> ());
    (match str "detail_contains" expected with
     | Some needle ->
       let d = match str "detail" j with Some s -> s | None -> "" in
       if not (contains ~needle d) then
         add (Printf.sprintf "detail %S does not contain %S" d needle)
     | None -> ());
    (match member "checks" expected with
     | Some (`Assoc wanted) ->
       let got = match member "checks" j with Some (`Assoc l) -> l | _ -> [] in
       List.iter
         (fun (k, want) ->
            let g = match List.assoc_opt k got with Some v -> v | None -> `Null in
            let same =
              match (want, g) with
              | `String "fail", `Assoc [ ("fail", _) ] -> true
              | w, g -> Yojson.Safe.equal w g
            in
            if not same then
              add (Printf.sprintf "check %s = %s, expected %s" k (Yojson.Safe.to_string g)
                     (Yojson.Safe.to_string want)))
         wanted
     | _ -> ());
    (match member "manifest_trust" expected with
     | Some (`Assoc wanted) ->
       let libs =
         match member "manifest" j with
         | Some m -> ( match member "libraries" m with Some (`List l) -> l | _ -> [])
         | None -> []
       in
       List.iter
         (fun (name, want) ->
            match List.find_opt (fun l -> str "name" l = Some name) libs with
            | None -> add (Printf.sprintf "library %s missing from the manifest" name)
            | Some l ->
              let got = match str "trust" l with Some s -> s | None -> "" in
              if `String got <> want then
                add (Printf.sprintf "library %s: trust=%s, expected %s" name got
                       (Yojson.Safe.to_string want)))
         wanted
     | _ -> ());
    (* optional per-target status assertions: [{"name":..,"status":..}, ..] *)
    (match member "targets" expected with
     | Some (`List wanted) ->
       let got = match member "targets" j with Some (`List l) -> l | _ -> [] in
       List.iter
         (fun wt ->
            match str "name" wt with
            | None -> ()
            | Some nm -> (
              match List.find_opt (fun t -> str "name" t = Some nm) got with
              | None -> add (Printf.sprintf "target %s missing from the verdict" nm)
              | Some gt -> (
                match str "status" wt with
                | Some ws ->
                  let gs = match str "status" gt with Some s -> s | None -> "" in
                  if gs <> ws then
                    add (Printf.sprintf "target %s: status=%s, expected %s" nm gs ws)
                | None -> ())))
         wanted
     | _ -> ());
    let why = String.concat "; " (List.rev !problems) in
    { name = name ^ label; pass = why = ""; why }

let check_batch ~exe ~dir ~name ~expected sols =
  let cfg = Filename.concat dir "config.json" in
  let paths = List.map (fun s -> Filename.concat dir s) sols in
  let code, out, _err = run ([ exe; "batch"; cfg ] @ paths) in
  let all_lines =
    String.split_on_char '\n' out
    |> List.filter_map (fun l ->
        let l = String.trim l in
        if String.length l > 1 && l.[0] = '{' then
          match Yojson.Safe.from_string l with j -> Some j | exception _ -> None
        else None)
  in
  (* batch prints a trailing tagged summary line ("summary":true) after the
     per-solution lines; the per-solution assertions below run over the
     solution lines only, and the summary is checked separately. *)
  let is_summary j = member "summary" j = Some (`Bool true) in
  let summary = List.find_opt is_summary all_lines in
  let lines = List.filter (fun j -> not (is_summary j)) all_lines in
  let problems = ref [] in
  let add p = problems := p :: !problems in
  (match int_ "exit_code" expected with
   | Some want when want <> code -> add (Printf.sprintf "exit code %d, expected %d" code want)
   | _ -> ());
  if List.length lines <> List.length sols then
    add (Printf.sprintf "%d JSON lines, expected %d" (List.length lines) (List.length sols));
  (match member "oks" expected with
   | Some (`List wanted) ->
     List.iteri
       (fun i w ->
          match List.nth_opt lines i with
          | None -> ()
          | Some j ->
            let got = match member "ok" j with Some (`Bool b) -> b | _ -> false in
            let want = match w with `Bool b -> b | _ -> false in
            if got <> want then
              add (Printf.sprintf "solution %d: ok=%b, expected %b" i got want);
            if member "solution" j = None then
              add (Printf.sprintf "solution %d: missing the \"solution\" field" i))
       wanted
   | _ -> ());
  (* the trailing summary line must be present and its total must match *)
  (match summary with
   | None -> add "no trailing summary line"
   | Some s ->
     (match int_ "total" s with
      | Some t when t <> List.length sols ->
        add (Printf.sprintf "summary total %d, expected %d" t (List.length sols))
      | _ -> ());
     (match member "oks" expected with
      | Some (`List wanted) ->
        let want_ok = List.length (List.filter (function `Bool b -> b | _ -> false) wanted) in
        (match int_ "ok" s with
         | Some got when got <> want_ok ->
           add (Printf.sprintf "summary ok=%d, expected %d" got want_ok)
         | _ -> ())
      | _ -> ()));
  let why = String.concat "; " (List.rev !problems) in
  { name; pass = why = ""; why }

(* A fixture with {"validate": true, ...} in expected.json is run through the
   `validate` subcommand (challenge only, no solution). Recognised keys:
     exit_code                 (int)
     v_ok                      (bool: the reported "ok")
     error_contains            (string)
     targets                   (list of {name, resolves?, kind?, type_contains?})
     challenge_axioms_contains (list of fully qualified names) *)
let check_validate ~exe ~dir ~name ~expected =
  let cfg = Filename.concat dir "config.json" in
  let code, out, err = run [ exe; "validate"; cfg ] in
  match verdict_of_stdout out with
  | None ->
    { name; pass = false;
      why = Printf.sprintf "no JSON on stdout (exit %d); stderr: %s" code (String.trim err) }
  | Some j ->
    let problems = ref [] in
    let add p = problems := p :: !problems in
    (match int_ "exit_code" expected with
     | Some want when want <> code -> add (Printf.sprintf "exit code %d, expected %d" code want)
     | _ -> ());
    (match member "v_ok" expected with
     | Some (`Bool want) ->
       let got = match member "ok" j with Some (`Bool b) -> b | _ -> false in
       if got <> want then add (Printf.sprintf "ok=%b, expected %b" got want)
     | _ -> ());
    (match str "error_contains" expected with
     | Some needle ->
       let d = match str "error" j with Some s -> s | None -> "" in
       if not (contains ~needle d) then add (Printf.sprintf "error %S does not contain %S" d needle)
     | None -> ());
    let got_targets = match member "targets" j with Some (`List l) -> l | _ -> [] in
    let find_target nm = List.find_opt (fun t -> str "name" t = Some nm) got_targets in
    (match member "targets" expected with
     | Some (`List wanted) ->
       List.iter
         (fun wt ->
            match str "name" wt with
            | None -> ()
            | Some nm -> (
              match find_target nm with
              | None -> add (Printf.sprintf "target %s missing from validation output" nm)
              | Some gt ->
                (match member "resolves" wt with
                 | Some (`Bool wb) ->
                   let gb = match member "resolves" gt with Some (`Bool b) -> b | _ -> false in
                   if gb <> wb then
                     add (Printf.sprintf "target %s: resolves=%b, expected %b" nm gb wb)
                 | _ -> ());
                (match str "kind" wt with
                 | Some wk ->
                   let gk = match str "kind" gt with Some s -> s | None -> "" in
                   if gk <> wk then add (Printf.sprintf "target %s: kind=%s, expected %s" nm gk wk)
                 | None -> ());
                (match str "type_contains" wt with
                 | Some needle ->
                   let ty = match str "type" gt with Some s -> s | None -> "" in
                   if not (contains ~needle ty) then
                     add (Printf.sprintf "target %s: type %S does not contain %S" nm ty needle)
                 | None -> ())))
         wanted
     | _ -> ());
    (match member "challenge_axioms_contains" expected with
     | Some (`List wanted) ->
       let got_ax =
         match member "challenge_axioms" j with
         | Some (`List l) -> List.filter_map (function `String s -> Some s | _ -> None) l
         | _ -> []
       in
       List.iter
         (function
           | `String nm ->
             if not (List.mem nm got_ax) then
               add (Printf.sprintf "challenge axiom %s missing (got: %s)" nm
                      (String.concat ", " got_ax))
           | _ -> ())
         wanted
     | _ -> ());
    let why = String.concat "; " (List.rev !problems) in
    { name; pass = why = ""; why }

let () =
  let exe = Sys.argv.(1) in
  let root = if Array.length Sys.argv > 2 then Sys.argv.(2) else "fixtures" in
  let dirs =
    Sys.readdir root |> Array.to_list |> List.sort String.compare
    |> List.filter (fun d -> Sys.is_directory (Filename.concat root d))
  in
  let results =
    List.concat_map
      (fun name ->
         let dir = Filename.concat root name in
         let exp_path = Filename.concat dir "expected.json" in
         if not (Sys.file_exists exp_path) then
           [ { name; pass = false; why = "no expected.json" } ]
         else
           let expected = Yojson.Safe.from_string (read_file exp_path) in
           (* a "prebuild" fixture is compiled and run in a scratch copy *)
           let dir =
             match member "prebuild" expected with
             | Some (`List l) -> prebuild ~exe ~dir l
             | _ -> dir
           in
           let main =
             match member "validate" expected with
             | Some (`Bool true) -> check_validate ~exe ~dir ~name ~expected
             | _ -> (
               match member "batch" expected with
               | Some (`List l) ->
                 let sols = List.filter_map (function `String s -> Some s | _ -> None) l in
                 check_batch ~exe ~dir ~name ~expected sols
               | _ -> check_one ~exe ~dir ~name ~expected ~env:[||] ~label:"")
           in
           let nofilter = Filename.concat dir "expected_nofilter.json" in
           if Sys.file_exists nofilter then
             [ main;
               check_one ~exe ~dir ~name
                 ~expected:(Yojson.Safe.from_string (read_file nofilter))
                 ~env:[| "ROCQ_COMPARATOR_UNSAFE_NO_FILTER=1" |] ~label:" [no filter]" ]
           else [ main ])
      dirs
  in
  List.iter
    (fun r ->
       if r.pass then Printf.printf "PASS %s\n" r.name
       else Printf.printf "FAIL %s: %s\n" r.name r.why)
    results;
  let failed = List.filter (fun r -> not r.pass) results in
  Printf.printf "\n%d/%d fixtures passed\n%!" (List.length results - List.length failed)
    (List.length results);
  if failed <> [] then exit 1
