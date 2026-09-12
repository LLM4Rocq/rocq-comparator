(* Unit tests for the infrastructure modules: configuration handling, the
   verdict's JSON shape, and the sandbox wrapper. *)

module RC = Rocq_comparator

let tmpdir () =
  let d =
    Filename.concat (Filename.get_temp_dir_name ())
      (Printf.sprintf "rcinfra-%d-%d" (Unix.getpid ()) (Random.int 1_000_000))
  in
  Unix.mkdir d 0o700; d

let write path s =
  let oc = open_out_bin path in
  output_string oc s; close_out oc

(* --- Config --- *)

let t_is_under () =
  Alcotest.(check bool) "plain prefix" true (RC.Config.is_under ~root:"/a/b" "/a/b/c");
  Alcotest.(check bool) "equal" true (RC.Config.is_under ~root:"/a/b" "/a/b");
  Alcotest.(check bool) "not a path prefix" false (RC.Config.is_under ~root:"/a/b" "/a/bc");
  Alcotest.(check bool) "sibling" false (RC.Config.is_under ~root:"/a/b" "/a/c");
  Alcotest.(check bool) "dot-dot escapes" false (RC.Config.is_under ~root:"/a/b" "/a/b/../c");
  Alcotest.(check bool) "root contains everything" true (RC.Config.is_under ~root:"/" "/a/b")

let t_json_roundtrip () =
  let dir = tmpdir () in
  let json =
    {|{ "challenge": "C.v", "solution": "S.v", "theorem_names": ["foo","bar"],
        "permitted_axioms": ["A.b.c", "D.*"],
        "loadpath": [ {"Q": ["theories", "Comp"]}, {"R": ["r", "R"]}, {"I": ["ml"]} ],
        "timeout_s": 42, "sandbox": "none", "rocqchk": false, "vm": false,
        "impredicative_set": true, "permitted_plugins": ["elpi"] }|}
  in
  let path = Filename.concat dir "config.json" in
  write path json;
  match RC.Config.of_json_file path with
  | Result.Error m -> Alcotest.fail ("config rejected: " ^ m)
  | Result.Ok c ->
    Alcotest.(check (list string)) "theorems" [ "foo"; "bar" ] c.RC.Config.theorem_names;
    Alcotest.(check (float 0.001)) "timeout" 42. c.RC.Config.timeout_s;
    Alcotest.(check bool) "rocqchk off" false c.RC.Config.rocqchk;
    Alcotest.(check bool) "vm off" false c.RC.Config.vm;
    Alcotest.(check bool) "impredicative set" true c.RC.Config.impredicative_set;
    Alcotest.(check bool) "sandbox none" true (c.RC.Config.sandbox = RC.Config.No_sandbox);
    Alcotest.(check string) "challenge is absolute" (Filename.concat dir "C.v")
      (RC.Config.challenge_path c);
    Alcotest.(check (list string)) "rocq args carry the load path"
      [ "-Q"; Filename.concat dir "theories"; "Comp"; "-R"; Filename.concat dir "r"; "R";
        "-I"; Filename.concat dir "ml" ]
      (RC.Config.loadpath_args c);
    Alcotest.(check bool) "native compiler is always off" true
      (List.exists (( = ) "-native-compiler") (RC.Config.rocq_args c));
    (* a round trip through to_json must preserve the essentials *)
    (match RC.Config.of_json ~config_dir:dir (RC.Config.to_json c) with
     | Result.Error m -> Alcotest.fail ("round trip failed: " ^ m)
     | Result.Ok c' ->
       Alcotest.(check (list string)) "theorems survive" c.RC.Config.theorem_names
         c'.RC.Config.theorem_names;
       Alcotest.(check (list string)) "axioms survive" c.RC.Config.permitted_axioms
         c'.RC.Config.permitted_axioms;
       Alcotest.(check (float 0.001)) "timeout survives" c.RC.Config.timeout_s
         c'.RC.Config.timeout_s;
       Alcotest.(check bool) "rocqchk survives" c.RC.Config.rocqchk c'.RC.Config.rocqchk)

let t_no_targets () =
  let dir = tmpdir () in
  let path = Filename.concat dir "config.json" in
  write path {|{ "challenge": "C.v" }|};
  Alcotest.(check bool) "a config without targets is rejected" true
    (Result.is_error (RC.Config.of_json_file path))

let t_top_name () =
  let dir = tmpdir () in
  Unix.mkdir (Filename.concat dir "theories") 0o700;
  Unix.mkdir (Filename.concat dir "theories/sub") 0o700;
  let base =
    { RC.Config.default with
      RC.Config.config_dir = dir; challenge = "theories/sub/Problem.v";
      theorem_names = [ "foo" ] }
  in
  Alcotest.(check string) "no load path: the basename" "Problem" (RC.Config.top_name base);
  let c = { base with RC.Config.loadpath = [ RC.Config.Q ("theories", "Comp") ] } in
  Alcotest.(check string) "derived like coqdep" "Comp.sub.Problem" (RC.Config.top_name c);
  let c = { c with RC.Config.top = Some "Explicit.Name" } in
  Alcotest.(check string) "an explicit top wins" "Explicit.Name" (RC.Config.top_name c)

let t_coqproject () =
  let dir = tmpdir () in
  write (Filename.concat dir "_CoqProject")
    "# a comment\n-Q theories Comp\n-R other Other\n-I ml\nfoo.v\n";
  let c =
    { RC.Config.default with
      RC.Config.config_dir = dir; coqproject = Some "_CoqProject"; theorem_names = [ "foo" ] }
  in
  Alcotest.(check (list string)) "the _CoqProject load path is merged"
    [ "-Q"; Filename.concat dir "theories"; "Comp";
      "-R"; Filename.concat dir "other"; "Other";
      "-I"; Filename.concat dir "ml" ]
    (RC.Config.loadpath_args c)

(* --- Verdict --- *)

let t_verdict_roundtrip () =
  let v =
    { (RC.Verdict.fail RC.Verdict.Forbidden_axiom "foo uses Challenge.magic") with
      RC.Verdict.sandboxed = true; sandbox = "sandbox-exec"; rocq_version = "9.2";
      targets =
        [ { RC.Verdict.name = "foo"; status = "proved"; assumptions = [ "A.b" ];
            target_detail = Some "why" } ];
      checks = [ ("challenge_compile", RC.Verdict.Ok); ("axioms", RC.Verdict.Fail "bad");
                 ("rocqchk", RC.Verdict.Skipped) ];
      timing = [ ("init", 0.5) ];
      solution = Some "S.v" }
  in
  match RC.Verdict.of_json (RC.Verdict.to_json v) with
  | Result.Error m -> Alcotest.fail ("verdict round trip failed: " ^ m)
  | Result.Ok v' ->
    Alcotest.(check bool) "ok" v.RC.Verdict.ok v'.RC.Verdict.ok;
    Alcotest.(check bool) "reason" true (v.RC.Verdict.reason = v'.RC.Verdict.reason);
    Alcotest.(check (option string)) "detail" v.RC.Verdict.detail v'.RC.Verdict.detail;
    Alcotest.(check bool) "sandboxed" true v'.RC.Verdict.sandboxed;
    Alcotest.(check string) "sandbox" "sandbox-exec" v'.RC.Verdict.sandbox;
    Alcotest.(check (option string)) "solution" (Some "S.v") v'.RC.Verdict.solution;
    Alcotest.(check int) "targets" 1 (List.length v'.RC.Verdict.targets);
    Alcotest.(check bool) "checks" true (v.RC.Verdict.checks = v'.RC.Verdict.checks)

let t_exit_codes () =
  Alcotest.(check int) "accepted" 0 (RC.Verdict.exit_code (RC.Verdict.pass ()));
  Alcotest.(check int) "rejected" 1
    (RC.Verdict.exit_code (RC.Verdict.fail RC.Verdict.Statement_mismatch "x"));
  Alcotest.(check int) "not proved is a rejection" 1
    (RC.Verdict.exit_code (RC.Verdict.fail RC.Verdict.Not_proved "x"));
  Alcotest.(check int) "a broken challenge is infrastructure" 2
    (RC.Verdict.exit_code (RC.Verdict.fail RC.Verdict.Challenge_error "x"));
  Alcotest.(check int) "a broken sandbox is infrastructure" 2
    (RC.Verdict.exit_code (RC.Verdict.fail RC.Verdict.Sandbox_error "x"));
  Alcotest.(check int) "an internal error is infrastructure" 2
    (RC.Verdict.exit_code (RC.Verdict.fail RC.Verdict.Internal_error "x"));
  Alcotest.(check int) "a timeout is a rejection" 1
    (RC.Verdict.exit_code (RC.Verdict.fail RC.Verdict.Timeout "x"))

let t_unparseable_is_never_ok () =
  Alcotest.(check bool) "garbage does not parse as a verdict" true
    (Result.is_error (RC.Verdict.of_json (`Assoc [ ("nonsense", `Int 1) ])))

(* --- Sandbox --- *)

let t_detect () =
  let k, reason = RC.Sandbox.detect RC.Config.No_sandbox in
  Alcotest.(check bool) "none is honoured" true (k = RC.Sandbox.No_sandbox);
  Alcotest.(check bool) "with a reason" true (String.length reason > 0);
  let k, _ = RC.Sandbox.detect (RC.Config.Custom [ "mywrap" ]) in
  Alcotest.(check bool) "custom is honoured" true (k = RC.Sandbox.Custom [ "mywrap" ]);
  let k, reason = RC.Sandbox.detect RC.Config.Auto in
  Alcotest.(check bool) "auto explains itself" true (String.length reason > 0);
  if Sys.file_exists "/usr/bin/sandbox-exec" then
    Alcotest.(check string) "auto picks sandbox-exec on macOS" "sandbox-exec"
      (RC.Sandbox.name k)

let t_wrap () =
  let scratch = tmpdir () in
  let argv = [ "/bin/echo"; "hi" ] in
  Alcotest.(check (list string)) "no sandbox is the identity" argv
    (RC.Sandbox.wrap RC.Sandbox.No_sandbox ~scratch ~argv);
  let w = RC.Sandbox.wrap (RC.Sandbox.Custom [ "wrapper"; "-x" ]) ~scratch ~argv in
  Alcotest.(check (list string)) "custom gets the scratch dir and --"
    [ "wrapper"; "-x"; scratch; "--"; "/bin/echo"; "hi" ] w;
  let w = RC.Sandbox.wrap RC.Sandbox.Sandbox_exec ~scratch ~argv in
  (match w with
   | "sandbox-exec" :: "-f" :: profile :: rest ->
     Alcotest.(check (list string)) "the command is appended" argv rest;
     Alcotest.(check bool) "the profile was written" true (Sys.file_exists profile);
     let ic = open_in_bin profile in
     let s = really_input_string ic (in_channel_length ic) in
     close_in ic;
     let has needle =
       let n = String.length needle and m = String.length s in
       let rec go i = i + n <= m && (String.sub s i n = needle || go (i + 1)) in
       go 0
     in
     Alcotest.(check bool) "denies by default" true (has "(deny default)");
     Alcotest.(check bool) "denies the network" true (has "(deny network*)");
     Alcotest.(check bool) "allows writing into the scratch dir" true
       (has (Unix.realpath scratch))
   | _ -> Alcotest.fail "unexpected sandbox-exec argv")

let t_run () =
  let r = RC.Sandbox.run ~timeout_s:20. [ "/bin/echo"; "hello" ] in
  Alcotest.(check int) "exit code" 0 r.RC.Sandbox.exit_code;
  Alcotest.(check bool) "not timed out" false r.RC.Sandbox.timed_out;
  Alcotest.(check string) "stdout captured" "hello\n" r.RC.Sandbox.stdout;
  let r = RC.Sandbox.run ~timeout_s:20. [ "/bin/sh"; "-c"; "echo oops 1>&2; exit 3" ] in
  Alcotest.(check int) "exit code is reported" 3 r.RC.Sandbox.exit_code;
  Alcotest.(check string) "stderr captured" "oops\n" r.RC.Sandbox.stderr;
  let r = RC.Sandbox.run ~timeout_s:20. [ "/definitely/not/a/program" ] in
  Alcotest.(check int) "a missing program exits 127" 127 r.RC.Sandbox.exit_code

let t_timeout () =
  let t0 = Unix.gettimeofday () in
  let r = RC.Sandbox.run ~timeout_s:0.5 [ "/bin/sh"; "-c"; "sleep 30" ] in
  let dt = Unix.gettimeofday () -. t0 in
  Alcotest.(check bool) "timed out" true r.RC.Sandbox.timed_out;
  Alcotest.(check bool) "and quickly" true (dt < 10.)

let t_kills_the_group () =
  (* the child's own children must die with it, or the run would hang *)
  let t0 = Unix.gettimeofday () in
  let r = RC.Sandbox.run ~timeout_s:0.5 [ "/bin/sh"; "-c"; "sleep 30 & sleep 30" ] in
  let dt = Unix.gettimeofday () -. t0 in
  Alcotest.(check bool) "timed out" true r.RC.Sandbox.timed_out;
  Alcotest.(check bool) "without waiting for the grandchild" true (dt < 10.)

(* The inner process must not inherit anything that can redirect Rocq's load
   path or plugin search (ROCQLIB, COQPATH, OCAMLPATH, XDG_*, ...): its
   environment is built from an allow-list. *)
let t_inner_env () =
  let dangerous =
    [ "ROCQLIB"; "COQLIB"; "ROCQPATH"; "COQPATH"; "OCAMLPATH"; "OCAMLFIND_CONF";
      "CAML_LD_LIBRARY_PATH"; "XDG_DATA_HOME"; "XDG_DATA_DIRS"; "XDG_CONFIG_HOME";
      "ROCQ_COLORS"; "LD_PRELOAD"; "DYLD_INSERT_LIBRARIES" ]
  in
  List.iter (fun k -> Unix.putenv k "/tmp/evil") dangerous;
  Unix.putenv "ROCQ_COMPARATOR_UNSAFE_NO_FILTER" "1";
  let env = Array.to_list (RC.Sandbox.inner_env ()) in
  let key kv = match String.index_opt kv '=' with Some i -> String.sub kv 0 i | None -> kv in
  let keys = List.map key env in
  List.iter
    (fun k ->
       Alcotest.(check bool) (k ^ " is not forwarded") false (List.mem k keys))
    dangerous;
  Alcotest.(check bool) "PATH is forwarded" true (List.mem "PATH" keys);
  Alcotest.(check bool) "the test-only escape hatch is forwarded" true
    (List.mem "ROCQ_COMPARATOR_UNSAFE_NO_FILTER" keys);
  (* no marker selects the inner side any more: only the --inner flag does *)
  Unix.putenv "ROCQ_COMPARATOR_INNER" "1";
  Alcotest.(check bool) "no inner marker is forwarded" false
    (List.mem "ROCQ_COMPARATOR_INNER" (List.map key (Array.to_list (RC.Sandbox.inner_env ()))))

let () =
  Random.self_init ();
  Alcotest.run "rocq-comparator/infra"
    [ ( "config",
        [ Alcotest.test_case "is_under" `Quick t_is_under;
          Alcotest.test_case "json round trip" `Quick t_json_roundtrip;
          Alcotest.test_case "no targets" `Quick t_no_targets;
          Alcotest.test_case "top name" `Quick t_top_name;
          Alcotest.test_case "_CoqProject" `Quick t_coqproject ] );
      ( "verdict",
        [ Alcotest.test_case "json round trip" `Quick t_verdict_roundtrip;
          Alcotest.test_case "exit codes" `Quick t_exit_codes;
          Alcotest.test_case "unparseable" `Quick t_unparseable_is_never_ok ] );
      ( "sandbox",
        [ Alcotest.test_case "detect" `Quick t_detect;
          Alcotest.test_case "wrap" `Quick t_wrap;
          Alcotest.test_case "run" `Quick t_run;
          Alcotest.test_case "timeout" `Quick t_timeout;
          Alcotest.test_case "kills the process group" `Quick t_kills_the_group;
          Alcotest.test_case "inner env allow-list" `Quick t_inner_env ] ) ]
