(* In-process compilation of one .v file as a library (DESIGN.md sections 3-4).

   The Rocq runtime is initialised once; every library is compiled from the
   frozen root state, so the challenge cannot be influenced by the solution
   and vice versa. *)

type sentence_error = {
  msg : string;
  line : int option;
  bp : int;
  ep : int;
  text : string;
}

type outcome =
  | Done of Vernacstate.t
  | Error of sentence_error
  | Parse_error of sentence_error
  | Timeout of string
  | Forbidden of string * sentence_error

let pp = Pp.string_of_ppcmds

(* --- initialisation (idempotent) --- *)

let opts_ref : Coqargs.t option ref = ref None
let root_ref : Vernacstate.t option ref = ref None
let messages : string list ref = ref []

let last_messages () = List.rev !messages
let clear_messages () = messages := []

let rocq_version () = Coq_config.version

let init ~(args : string list) : unit =
  match !opts_ref with
  | Some _ -> ()
  | None ->
    Coqinit.init_ocaml ();
    let usage =
      Boot.Usage.{ executable_name = "rocq-comparator"; extra_args = ""; extra_options = "" }
    in
    let opts, () =
      Coqinit.parse_arguments ~parse_extra:(fun _ e -> ((), e)) ~initial_args:Coqargs.default args
    in
    Coqinit.init_runtime ~usage opts;
    Coqinit.init_document opts;
    (* enable memprof-based allocation-point interruption (see compile_library) *)
    Memprof_limits.start_memprof_limits ();
    (* Swallow feedback; keep the last messages for error reporting. *)
    ignore
      (Feedback.add_feeder (fun fb ->
           match fb.Feedback.contents with
           | Feedback.Message (_, _, _, m) ->
             let s = pp m in
             if String.length s > 0 then begin
               messages := s :: !messages;
               (* bound the buffer *)
               if List.length !messages > 50 then
                 messages := List.filteri (fun i _ -> i < 50) !messages
             end
           | _ -> ()));
    (* Native compilation compiles and dlopens generated OCaml: never enable it. *)
    Global.set_native_compiler false;
    opts_ref := Some opts;
    root_ref := Some (Vernacstate.freeze_full_state ())

let opts () = match !opts_ref with Some o -> o | None -> failwith "Driver.init not called"
let root () = match !root_ref with Some r -> r | None -> failwith "Driver.init not called"

let with_state (st : Vernacstate.t) (f : unit -> 'a) : 'a =
  let saved = Vernacstate.freeze_full_state () in
  Vernacstate.unfreeze_full_state st;
  match f () with
  | v -> Vernacstate.unfreeze_full_state saved; v
  | exception e ->
    let e, info = Exninfo.capture e in
    Vernacstate.unfreeze_full_state saved;
    Exninfo.iraise (e, info)

(* --- compiling one library --- *)

(* coqc reads .v files with [open_utf8_file_in], which skips a leading UTF-8
   byte-order mark. We read the file as bytes (offsets must match the ones the
   parser reports), so we strip the BOM ourselves: without this a solution
   saved by a BOM-emitting editor is rejected as a parse error, which is a
   verdict about the editor and not about the proof. *)
let utf8_bom = "\xef\xbb\xbf"

let strip_bom s =
  let n = String.length utf8_bom in
  if String.length s >= n && String.equal (String.sub s 0 n) utf8_bom then
    String.sub s n (String.length s - n)
  else s

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  strip_bom s

let sentence_text src bp ep =
  let n = String.length src in
  let bp = if bp < 0 then 0 else if bp > n then n else bp in
  let ep = if ep < bp then bp else if ep > n then n else ep in
  let s = String.sub src bp (ep - bp) in
  let s = String.trim s in
  if String.length s > 300 then String.sub s 0 300 ^ "..." else s

let err_of_loc src (loc : Loc.t option) msg =
  match loc with
  | Some l -> { msg; line = Some l.Loc.line_nb; bp = l.Loc.bp; ep = l.Loc.ep;
                text = sentence_text src l.Loc.bp l.Loc.ep }
  | None -> { msg; line = None; bp = 0; ep = 0; text = "" }

let proof_open (st : Vernacstate.t) =
  st.Vernacstate.interp.Vernacstate.Interp.lemmas <> None

exception Outcome_exn of outcome

let compile_library ?(filter = fun _ -> Result.Ok ())
    ?(deadline = infinity) ~(top : Names.DirPath.t) ~(file : string) () : outcome =
  clear_messages ();
  let src = read_file file in
  (* [Vernacstate.unfreeze_full_state] restores the Interp half through
     [do_if_not_cached], which skips the restore when the state it is asked
     for is *physically* the one the cache last saw. The isolation between the
     challenge and the solution rests entirely on this restore actually
     happening, so we drop the cache first and pay one extra summary unfreeze
     rather than trust a pointer comparison. (Flagged "do not use" in
     vernacstate.mli, but it is the documented way to force a reset and is
     used for the same purpose by coq-lsp and rocq-tools.) *)
  Vernacstate.Interp.invalidate_cache ();
  Vernacstate.unfreeze_full_state (root ());
  Coqinit.start_library ~intern:Vernacinterp.fs_intern ~top (Coqargs.injection_commands (opts ()));
  let pa =
    Procq.Parsable.make
      ~loc:(Loc.initial (Loc.InFile { dirpath = None; file }))
      (Gramlib.Stream.of_string src)
  in
  let text_of = function
    | Some (l : Loc.t) -> sentence_text src l.Loc.bp l.Loc.ep
    | None -> ""
  in
  let rec loop st =
    (* When a proof is open, parse the next sentence in the current proof mode.
       [get_default_proof_mode] is a synterp-stage option that tracks the file's
       own [Set Default Proof Mode] and the mode a plugin sets on import (e.g.
       [From Ltac2 Require Import Ltac2] switches it to "Ltac2"), so for a
       whole-file compile it is the same mode coqc would parse with. Verified on
       Classic, ssreflect and Ltac2 solutions. *)
    let pm = if proof_open st then Some (Synterp.get_default_proof_mode ()) else None in
    let next =
      match Procq.Entry.parse (Pvernac.main_entry pm) pa with
      | v -> v
      | exception e when CErrors.noncritical e ->
        let e, info = Exninfo.capture e in
        raise
          (Outcome_exn
             (Parse_error (err_of_loc src (Loc.get_loc info) (pp (CErrors.iprint (e, info))))))
    in
    match next with
    | None -> Done (Vernacstate.freeze_full_state ())
    | Some vc ->
      let loc = vc.CAst.loc in
      (match filter vc with
       | Result.Error what -> raise (Outcome_exn (Forbidden (what, err_of_loc src loc what)))
       | Result.Ok () -> ());
      let remaining = deadline -. Unix.gettimeofday () in
      if deadline <> infinity && remaining <= 0. then
        raise (Outcome_exn (Timeout (text_of loc)));
      let run () = Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~st vc in
      let on_error e =
        let e, info = Exninfo.capture e in
        let loc = match Loc.get_loc info with Some l -> Some l | None -> loc in
        raise (Outcome_exn (Error (err_of_loc src loc (pp (CErrors.iprint (e, info))))))
      in
      if deadline = infinity then
        (match run () with
         | st' -> loop st'
         | exception e when CErrors.noncritical e -> on_error e)
      else begin
        (* Two interruption layers guard the solution. [Control.timeout] fires
           at the prover's own checkpoints; a [memprof-limits] token, tripped by
           a watchdog thread at the deadline, fires at allocation points, which
           is what stops an allocation-heavy loop that never reaches a
           Control.timeout checkpoint (e.g. a runaway [vm_compute]). Same
           combination coq-lsp and rocq-tools use. *)
        let token = Memprof_limits.Token.create () in
        let watchdog =
          Thread.create
            (fun () ->
               let dl = Unix.gettimeofday () +. remaining +. 0.5 in
               while (not (Memprof_limits.Token.is_set token)) && Unix.gettimeofday () < dl do
                 Thread.delay 0.05
               done;
               if Unix.gettimeofday () >= dl then Memprof_limits.Token.set token)
            ()
        in
        let stop () = Memprof_limits.Token.set token; Thread.join watchdog in
        let timed_out () =
          Vernacstate.Interp.invalidate_cache ();
          raise (Outcome_exn (Timeout (text_of loc)))
        in
        match Memprof_limits.limit_with_token ~token (fun () -> Control.timeout remaining run ()) with
        | Ok (Ok st') -> stop (); loop st'
        | Ok (Error _) (* wall-clock timeout *) | Error _ (* token interrupt *) ->
          stop (); timed_out ()
        | exception e when CErrors.noncritical e -> stop (); on_error e
      end
  in
  let out =
    try loop (Vernacstate.freeze_full_state ()) with Outcome_exn o -> o
  in
  (match out with Done st -> Vernacstate.unfreeze_full_state st | _ -> ());
  out
