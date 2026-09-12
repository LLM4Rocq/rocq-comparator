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

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

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
      let r =
        try if deadline = infinity then Result.Ok (run ()) else Control.timeout remaining run ()
        with e when CErrors.noncritical e ->
          let e, info = Exninfo.capture e in
          let loc = match Loc.get_loc info with Some l -> Some l | None -> loc in
          raise (Outcome_exn (Error (err_of_loc src loc (pp (CErrors.iprint (e, info))))))
      in
      (match r with
       | Result.Ok st' -> loop st'
       | Result.Error _ -> raise (Outcome_exn (Timeout (text_of loc))))
  in
  let out =
    try loop (Vernacstate.freeze_full_state ()) with Outcome_exn o -> o
  in
  (match out with Done st -> Vernacstate.unfreeze_full_state st | _ -> ());
  out
