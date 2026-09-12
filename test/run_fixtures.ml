(* Runs the built rocq-comparator over every directory in test/fixtures/ and
   checks the verdict against that fixture's expected.json (DESIGN.md 11).

   expected.json keys:
     exit_code        (int, required)
     reason           (string, optional)
     detail_contains  (string, optional)
     checks           (object name -> "ok" | "skipped" | "fail", optional)
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
    let why = String.concat "; " (List.rev !problems) in
    { name = name ^ label; pass = why = ""; why }

let check_batch ~exe ~dir ~name ~expected sols =
  let cfg = Filename.concat dir "config.json" in
  let paths = List.map (fun s -> Filename.concat dir s) sols in
  let code, out, _err = run ([ exe; "batch"; cfg ] @ paths) in
  let lines =
    String.split_on_char '\n' out
    |> List.filter_map (fun l ->
        let l = String.trim l in
        if String.length l > 1 && l.[0] = '{' then
          match Yojson.Safe.from_string l with j -> Some j | exception _ -> None
        else None)
  in
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
           let main =
             match member "batch" expected with
             | Some (`List l) ->
               let sols = List.filter_map (function `String s -> Some s | _ -> None) l in
               check_batch ~exe ~dir ~name ~expected sols
             | _ -> check_one ~exe ~dir ~name ~expected ~env:[||] ~label:""
           in
           let nofilter = Filename.concat dir "expected_nofilter.json" in
           if Sys.file_exists nofilter then
             [ main;
               check_one ~exe ~dir ~name
                 ~expected:(Yojson.Safe.from_string (read_file nofilter))
                 ~env:[| "ROCQ_COMPARATOR_NO_FILTER=1" |] ~label:" [no filter]" ]
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
