(* OS sandbox selection and child-process execution (DESIGN.md section 3 and
   CONTRACTS.md "Sandbox").  Defence in depth: the inner process compiles an
   adversarial file, so it runs with no network and (essentially) no write
   access outside its scratch directory. *)

type kind =
  | Sandbox_exec
  | Landrun
  | Bwrap
  | Custom of string list
  | No_sandbox

let name = function
  | Sandbox_exec -> "sandbox-exec"
  | Landrun -> "landrun"
  | Bwrap -> "bwrap"
  | Custom _ -> "custom"
  | No_sandbox -> "none"

(* --- the child's environment ---------------------------------------------

   CRITICAL.  The inner process links the Rocq kernel and loads .vo files; a
   whole family of environment variables can redirect what it loads and from
   where:

     ROCQLIB / COQLIB            where the standard library lives
     ROCQPATH / COQPATH          extra load-path roots, prepended to user-contrib
     ROCQ_* / COQ_*              other Rocq knobs (e.g. COQ_COLORS, and any
                                 future one we do not know about)
     XDG_DATA_HOME / XDG_DATA_DIRS / XDG_CONFIG_HOME
                                 searched by Rocq for user-contrib and rc files
     OCAMLPATH / OCAMLFIND_CONF / CAML_LD_LIBRARY_PATH / LD_LIBRARY_PATH /
     DYLD_* / LD_PRELOAD         where findlib/the dynamic loader look for the
                                 plugins (.cmxs) a Require can load

   Anything on that list turns "the load path is trusted" (DESIGN assumption 1)
   into a lie: a caller's stray COQPATH, or an attacker who can set one
   variable in the environment of the judge, would get adversarial .vo files or
   OCaml plugins loaded by the trusted inner process.  So the child's
   environment is built from an ALLOW-LIST instead of being filtered: whatever
   we forget to deny is simply not forwarded.

   The list is deliberately tiny:
     PATH                  we exec the sandbox wrapper and rocqchk by name
     HOME, TMPDIR          scratch files, and enough of a home for the
                           OCaml/Unix runtime not to misbehave
     LANG, LC_ALL, LC_CTYPE, TERM, USER
                           locale/tty/user niceties with no effect on loading
     ROCQ_COMPARATOR_UNSAFE_NO_FILTER
                           the test-only escape hatch (CONTRACTS.md); it is
                           recorded in the verdict's "filter" check, so a run
                           made with it set can never be mistaken for a normal
                           one, and the fixture suite needs it in the child. *)
let inner_env_allowlist =
  [ "PATH"; "HOME"; "TMPDIR"; "LANG"; "LC_ALL"; "LC_CTYPE"; "TERM"; "USER";
    "ROCQ_COMPARATOR_UNSAFE_NO_FILTER" ]

let inner_env () : string array =
  Unix.environment ()
  |> Array.to_list
  |> List.filter (fun kv ->
      match String.index_opt kv '=' with
      | None -> false
      | Some i -> List.mem (String.sub kv 0 i) inner_env_allowlist)
  |> Array.of_list

(* --- locating the wrapper binaries --- *)

let which prog =
  if String.contains prog '/' then (if Sys.file_exists prog then Some prog else None)
  else
    let path = match Sys.getenv_opt "PATH" with Some p -> p | None -> "/usr/bin:/bin" in
    let rec go = function
      | [] -> None
      | d :: tl ->
        let p = Filename.concat d prog in
        if Sys.file_exists p then Some p else go tl
    in
    go (String.split_on_char ':' path)

let is_darwin () = Sys.file_exists "/usr/bin/sandbox-exec" || Sys.file_exists "/System/Library"

(* [detect mode] -> the sandbox actually used and a one-line explanation. *)
let detect (mode : Config.sandbox_mode) : kind * string =
  match mode with
  | Config.No_sandbox -> (No_sandbox, "sandbox disabled by configuration")
  | Config.Custom l -> (Custom l, "custom sandbox command from configuration")
  | Config.Sandbox_exec ->
    (Sandbox_exec,
     match which "sandbox-exec" with
     | Some p -> "sandbox-exec requested (" ^ p ^ ")"
     | None -> "sandbox-exec requested but not found in PATH")
  | Config.Landrun ->
    (Landrun,
     match which "landrun" with
     | Some p -> "landrun requested (" ^ p ^ ")"
     | None -> "landrun requested but not found in PATH")
  | Config.Bwrap ->
    (Bwrap,
     match which "bwrap" with
     | Some p -> "bwrap requested (" ^ p ^ ")"
     | None -> "bwrap requested but not found in PATH")
  | Config.Auto ->
    if is_darwin () then
      match which "sandbox-exec" with
      | Some p -> (Sandbox_exec, "auto: macOS, using sandbox-exec (" ^ p ^ ")")
      | None -> (No_sandbox, "auto: macOS but sandbox-exec not found; running UNSANDBOXED")
    else (
      match which "landrun" with
      | Some p -> (Landrun, "auto: using landrun (" ^ p ^ ")")
      | None ->
        (match which "bwrap" with
         | Some p -> (Bwrap, "auto: using bwrap (" ^ p ^ ")")
         | None -> (No_sandbox, "auto: no landrun/bwrap found; running UNSANDBOXED")))

(* Resolve symlinks so the profile talks about the same paths the kernel sees
   (/tmp is a symlink to /private/tmp on macOS). *)
let real_path p =
  match Unix.realpath p with exception _ -> p | r -> r

let sandbox_exec_profile ~scratch =
  let tmp = real_path (Filename.get_temp_dir_name ()) in
  let scratch = real_path scratch in
  String.concat "\n"
    [ "(version 1)";
      "(deny default)";
      "(allow process*)";
      "(allow sysctl-read)";
      "(allow mach-lookup)";
      "(allow file-read*)";
      Printf.sprintf "(allow file-write* (subpath %S))" scratch;
      Printf.sprintf "(allow file-write* (subpath %S))" tmp;
      "(allow file-write* (literal \"/dev/null\"))";
      "(allow file-write* (literal \"/dev/tty\"))";
      "(allow file-write* (literal \"/dev/dtracehelper\"))";
      "(deny network*)";
      "" ]

let write_file path s =
  let oc = open_out_bin path in
  output_string oc s;
  close_out oc

(* Full argv, wrapper included. *)
let wrap (k : kind) ~scratch ~argv : string list =
  match k with
  | No_sandbox -> argv
  | Custom l -> l @ [ scratch ] @ [ "--" ] @ argv
  | Sandbox_exec ->
    let profile = Filename.concat scratch "sandbox.sb" in
    write_file profile (sandbox_exec_profile ~scratch);
    [ "sandbox-exec"; "-f"; profile ] @ argv
  | Landrun ->
    [ "landrun"; "--best-effort"; "--ro"; "/"; "--rw"; "/dev"; "--rwx"; scratch;
      "--rw"; Filename.get_temp_dir_name (); "--ldd"; "--add-exec"; "--" ] @ argv
  | Bwrap ->
    [ "bwrap"; "--ro-bind"; "/"; "/"; "--dev"; "/dev";
      "--bind"; scratch; scratch;
      "--bind"; Filename.get_temp_dir_name (); Filename.get_temp_dir_name ();
      "--unshare-net"; "--die-with-parent"; "--" ] @ argv

(* --- running a child --- *)

type run_result = {
  exit_code : int;
  timed_out : bool;
  signaled : bool;
  stdout : string;
  stderr : string;
}

(* fork+exec is not thread safe in general; batch mode may call [run] from
   several threads, so serialise the fork/exec window. *)
let fork_mutex = Mutex.create ()

let read_all_with_deadline ~deadline ~pid (fds : (Unix.file_descr * Buffer.t) list) =
  let buf = Bytes.create 65536 in
  let open_fds = ref fds in
  let timed_out = ref false in
  let killed = ref false in
  while !open_fds <> [] && not !timed_out do
    let now = Unix.gettimeofday () in
    let remaining = deadline -. now in
    if remaining <= 0. then begin
      (* grace: kill the group, then drain for a moment so we keep the output *)
      if not !killed then begin
        killed := true;
        (try Unix.kill (-pid) Sys.sigkill with _ -> ());
        (try Unix.kill pid Sys.sigkill with _ -> ())
      end;
      timed_out := true
    end else begin
      let wait = if remaining > 0.5 then 0.5 else remaining in
      let r, _, _ = try Unix.select (List.map fst !open_fds) [] [] wait with
        | Unix.Unix_error (Unix.EINTR, _, _) -> ([], [], [])
      in
      List.iter
        (fun fd ->
           let n = try Unix.read fd buf 0 (Bytes.length buf) with _ -> 0 in
           if n = 0 then open_fds := List.filter (fun (f, _) -> f <> fd) !open_fds
           else
             match List.assoc_opt fd !open_fds with
             | Some b -> Buffer.add_subbytes b buf 0 n
             | None -> ())
        r
    end
  done;
  (* if we timed out, drain whatever is buffered without blocking *)
  if !timed_out then
    List.iter
      (fun (fd, b) ->
         let rec drain () =
           match Unix.select [ fd ] [] [] 0.05 with
           | [ _ ], _, _ ->
             let n = try Unix.read fd buf 0 (Bytes.length buf) with _ -> 0 in
             if n > 0 then (Buffer.add_subbytes b buf 0 n; drain ())
           | _ -> ()
           | exception _ -> ()
         in
         drain ())
      !open_fds;
  !timed_out

let run ?env ~timeout_s (argv : string list) : run_result =
  match argv with
  | [] -> { exit_code = 2; timed_out = false; signaled = false; stdout = ""; stderr = "empty argv" }
  | prog :: _ ->
    let args = Array.of_list argv in
    let env = match env with Some e -> e | None -> Unix.environment () in
    let out_r, out_w = Unix.pipe () in
    let err_r, err_w = Unix.pipe () in
    let devnull = Unix.openfile "/dev/null" [ Unix.O_RDONLY ] 0 in
    Mutex.lock fork_mutex;
    let pid =
      match Unix.fork () with
      | 0 ->
        (try
           ignore (Unix.setsid ());
           Unix.dup2 devnull Unix.stdin;
           Unix.dup2 out_w Unix.stdout;
           Unix.dup2 err_w Unix.stderr;
           Unix.close out_r; Unix.close err_r;
           Unix.close out_w; Unix.close err_w; Unix.close devnull;
           Unix.execvpe prog args env
         with _ -> Unix._exit 127)
      | pid -> pid
    in
    Mutex.unlock fork_mutex;
    Unix.close out_w; Unix.close err_w; Unix.close devnull;
    let ob = Buffer.create 4096 and eb = Buffer.create 4096 in
    let deadline = Unix.gettimeofday () +. timeout_s in
    let timed_out = read_all_with_deadline ~deadline ~pid [ (out_r, ob); (err_r, eb) ] in
    (try Unix.close out_r with _ -> ());
    (try Unix.close err_r with _ -> ());
    let status =
      let rec wait () =
        match Unix.waitpid [] pid with
        | _, st -> st
        | exception Unix.Unix_error (Unix.EINTR, _, _) -> wait ()
        | exception _ -> Unix.WEXITED 2
      in
      (* if the pipes closed but the child lingers, enforce the deadline *)
      if not timed_out then begin
        let rec poll () =
          match Unix.waitpid [ Unix.WNOHANG ] pid with
          | 0, _ ->
            if Unix.gettimeofday () > deadline then begin
              (try Unix.kill (-pid) Sys.sigkill with _ -> ());
              (try Unix.kill pid Sys.sigkill with _ -> ());
              wait ()
            end else (ignore (Unix.select [] [] [] 0.02); poll ())
          | _, st -> st
          | exception Unix.Unix_error (Unix.EINTR, _, _) -> poll ()
          | exception _ -> Unix.WEXITED 2
        in
        poll ()
      end else wait ()
    in
    (match status with
     | Unix.WEXITED n ->
       { exit_code = n; timed_out; signaled = false;
         stdout = Buffer.contents ob; stderr = Buffer.contents eb }
     | Unix.WSIGNALED n | Unix.WSTOPPED n ->
       { exit_code = 128 + n; timed_out; signaled = true;
         stdout = Buffer.contents ob; stderr = Buffer.contents eb })
