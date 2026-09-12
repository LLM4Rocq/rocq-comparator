(* Optional replay of the compiled library through rocqchk, Rocq's independent
   checker (DESIGN.md section 9).

   The .vo is produced by this very process, so unmarshalling it in rocqchk is
   not an adversarial input; rocqchk runs inside the same sandbox because the
   inner process is already sandboxed. *)

open Names

(* The bin/ directory of the Rocq installation this binary is linked against.
   [Boot.Env.rocqbin] is derived from argv.(0), which points at our own build
   tree, and the first rocqchk on PATH may well come from another switch (with
   another .vo version): go through the compiled-in coqlib instead. *)
let switch_bin () : string option =
  let lib = try Boot.Env.relocate Coq_config.coqlib with _ -> "" in
  if lib = "" then None
  else
    let suffix = Coq_config.coqlibsuffix in
    let n = String.length lib and m = String.length suffix in
    if n > m + 1 && String.sub lib (n - m) m = suffix then
      Some (Filename.concat (String.sub lib 0 (n - m - 1)) "bin")
    else Some (Filename.concat (Filename.dirname (Filename.dirname lib)) "bin")

let find_rocqchk () : string option =
  let candidates =
    let of_bin b = [ Filename.concat b "rocqchk"; Filename.concat b "coqchk" ] in
    (match switch_bin () with Some b -> of_bin b | None -> [])
    @ (match (try Boot.Env.rocqbin with _ -> "") with "" -> [] | b -> of_bin b)
    @ [ "rocqchk"; "coqchk" ]
  in
  let rec go = function
    | [] -> None
    | c :: tl -> (
      if String.contains c '/' then if Sys.file_exists c then Some c else go tl
      else
        match Sandbox.which c with Some p -> Some p | None -> go tl)
  in
  go candidates

(* [top] as a (logical prefix, base name) pair: with "-Q dir PREFIX" the
   library PREFIX.BASE is looked up as dir/BASE.vo. *)
let split_top (top : DirPath.t) =
  match List.rev (String.split_on_char '.' (DirPath.to_string top)) with
  | [] -> ("", "Top")
  | base :: rev_prefix -> (String.concat "." (List.rev rev_prefix), base)

let save_vo ~(top : DirPath.t) ~(dir : string) : (string, string) result =
  let _, base = split_top top in
  let path = Filename.concat dir (base ^ ".vo") in
  match Library.save_library_to Library.ProofsTodoNone ~output_native_objects:false top path with
  | () -> Result.Ok path
  | exception e when CErrors.noncritical e ->
    let e, info = Exninfo.capture e in
    Result.Error ("cannot save the library: " ^ Pp.string_of_ppcmds (CErrors.iprint (e, info)))

let tail n s =
  let len = String.length s in
  if len <= n then s else "..." ^ String.sub s (len - n) n

let run ~(rocqchk : string) ~(top : DirPath.t) ~(vo_dir : string)
    ~(loadpath_args : string list) ~(deadline : float) : (unit, string) result =
  let prefix, _ = split_top top in
  let argv =
    [ rocqchk; "-silent"; "-Q"; vo_dir; prefix ] @ loadpath_args
    @ [ "-norec"; DirPath.to_string top ]
  in
  let timeout = deadline -. Unix.gettimeofday () in
  if timeout <= 0. then Result.Error "no time budget left for rocqchk"
  else
    let r = Sandbox.run ~timeout_s:timeout argv in
    if r.Sandbox.timed_out then Result.Error "rocqchk timed out"
    else if r.Sandbox.exit_code = 0 then Result.Ok ()
    else
      Result.Error
        (Printf.sprintf "rocqchk exited with %d: %s" r.Sandbox.exit_code
           (tail 600 (String.trim (r.Sandbox.stderr ^ "\n" ^ r.Sandbox.stdout))))
