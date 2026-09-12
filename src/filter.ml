(* Vernacular AST filter (DESIGN.md section 6).

   Every constructor of [vernac_control_gen], [control_flag],
   [synterp_vernac_expr] and [synpure_vernac_expr] is listed explicitly: the
   matches below are exhaustive on purpose, so that a new constructor in a
   future Rocq breaks the build instead of silently slipping through. *)

[@@@warning "+8"]

open Vernacexpr

type mode = Strict | Lenient

type policy = {
  mode : mode;
  permitted_plugins : string list;
  permitted_libraries : string list;
}

let default_plugins =
  [ "ltac"; "ltac2"; "ltac2_ltac1"; "ssreflect"; "ssrmatching"; "micromega";
    "ring"; "nsatz"; "zify"; "btauto"; "cc"; "firstorder"; "rtauto"; "tauto";
    "derive"; "funind"; "number_string_notation" ]

let ok = Result.Ok ()
let deny what = Result.Error what

(* "rocq-runtime.plugins.ltac" / "coq-core.plugins.ltac" / "ltac" -> "ltac" *)
let plugin_basename s =
  match List.rev (String.split_on_char '.' s) with [] -> s | last :: _ -> last

let lowercase_path (p : string list) = String.lowercase_ascii (String.concat " " p)

(* Options whose value changes what the kernel checks. *)
let denied_options =
  [ "guard checking"; "positivity checking"; "universe checking";
    "definitional uip"; "allow rewrite rules"; "extraction output directory";
    "printing universes file" ]

let classify_option (name : Goptions.option_name) : [ `Allow | `Deny ] =
  if List.mem (lowercase_path name) denied_options then `Deny else `Allow

let check_option_setting p name =
  match p.mode with
  | Lenient -> ok
  | Strict -> (
    match classify_option name with
    | `Allow -> ok
    | `Deny -> deny ("option " ^ String.concat " " name))

(* #[bypass_check(...)] and friends. *)
let rec check_attributes p (flags : Attributes.vernac_flags) =
  match p.mode with
  | Lenient -> ok
  | Strict ->
    let rec go = function
      | [] -> ok
      | { CAst.v = key, value; _ } :: tl ->
        if String.lowercase_ascii key = "bypass_check" then
          deny "attribute bypass_check"
        else (
          match value with
          | Attributes.VernacFlagList sub -> (
            match check_attributes p sub with Result.Error e -> Result.Error e | Result.Ok () -> go tl)
          | Attributes.VernacFlagEmpty | Attributes.VernacFlagLeaf _ -> go tl)
    in
    go flags

let check_control p (c : control_flag) =
  match c.CAst.v with
  | ControlRedirect _ -> deny "Redirect"
  | ControlTime | ControlInstructions | ControlProfile _ | ControlTimeout _
  | ControlFail | ControlSucceed ->
    ignore p; ok

let check_require p (l : (Libnames.qualid * import_filter_expr) list) =
  match p.permitted_libraries with
  | [] -> ok
  | allowed ->
    let bad =
      List.filter
        (fun (q, _) ->
           let s = Libnames.string_of_qualid q in
           not (List.exists (fun a -> s = a || String.length s > String.length a
                                              && String.sub s 0 (String.length a + 1) = a ^ ".") allowed))
        l
    in
    (match bad with
     | [] -> ok
     | (q, _) :: _ -> deny ("Require of non-permitted library " ^ Libnames.string_of_qualid q))

let check_synterp p (e : synterp_vernac_expr) =
  match e with
  (* always denied: these break the comparator's own invariants *)
  | VernacLoad _ -> deny "Load"
  | VernacChdir _ -> deny "Cd"
  | VernacDeclareMLModule _ -> deny "Declare ML Module"
  | VernacExtraDependency _ -> deny "Extra Dependency"
  (* restricted *)
  | VernacRequire (_, _, l) -> check_require p l
  | VernacSetOption (_, name, _) -> check_option_setting p name
  | VernacExtend (ext, _) -> (
    match p.mode with
    | Lenient -> ok
    | Strict ->
      let plug = plugin_basename ext.ext_plugin in
      if List.mem plug default_plugins || List.mem plug p.permitted_plugins
         || List.mem ext.ext_plugin p.permitted_plugins
      then ok
      else deny ("plugin command from " ^ ext.ext_plugin ^ " (" ^ ext.ext_entry ^ ")"))
  (* allowed *)
  | VernacReservedNotation _ | VernacNotation _ | VernacDeclareCustomEntry _
  | VernacBeginSection _ | VernacEndSegment _ | VernacImport _
  | VernacDeclareModule _ | VernacDefineModule _ | VernacDeclareModuleType _
  | VernacInclude _ | VernacProofMode _ -> ok

let check_synpure p (e : synpure_vernac_expr) =
  match e with
  (* always denied *)
  | VernacResetName _ -> deny "Reset"
  | VernacResetInitial -> deny "Reset Initial"
  | VernacBack _ -> deny "Back"
  | VernacUndo _ -> deny "Undo"
  | VernacUndoTo _ -> deny "Undo To"
  | VernacRestart -> deny "Restart"
  | VernacAbortAll -> deny "Abort All"
  | VernacRegister _ -> deny "Register"
  | VernacPrimitive _ -> deny "Primitive"
  | VernacSymbol _ -> deny "Symbol"
  | VernacAddRewRule _ -> deny "Rewrite Rule"
  | VernacPrint (PrintUniverses { file = Some _; _ }) -> deny "Print Universes to a file"
  (* restricted *)
  | VernacAddOption (name, _) -> check_option_setting p name
  | VernacRemoveOption (name, _) -> check_option_setting p name
  (* allowed *)
  | VernacOpenCloseScope _ | VernacDeclareScope _ | VernacDelimiters _
  | VernacBindScope _ | VernacEnableNotation _ | VernacDefinition _
  | VernacStartTheoremProof _ | VernacEndProof _ | VernacExactProof _
  | VernacAssumption _ | VernacInductive _ | VernacFixpoint _
  | VernacCoFixpoint _ | VernacSchemeAll _ | VernacScheme _
  | VernacSchemeEquality _ | VernacCombinedScheme _ | VernacUniverse _
  | VernacSort _ | VernacConstraint _ | VernacCanonical _ | VernacCoercion _
  | VernacIdentityCoercion _ | VernacNameSectionHypSet _ | VernacInstance _
  | VernacDeclareInstance _ | VernacContext _ | VernacExistingInstance _
  | VernacExistingClass _ | VernacCreateHintDb _ | VernacRemoveHints _
  | VernacHints _ | VernacAbbreviation _ | VernacArguments _ | VernacReserve _
  | VernacGeneralizable _ | VernacSetOpacity _ | VernacSetStrategy _
  | VernacMemOption _ | VernacPrintOption _ | VernacCheckMayEval _
  | VernacGlobalCheck _ | VernacDeclareReduction _ | VernacPrint _
  | VernacSearch _ | VernacLocate _ | VernacComments _ | VernacAttributes _
  | VernacAbort | VernacFocus _ | VernacUnfocus | VernacUnfocused
  | VernacBullet _ | VernacSubproof _ | VernacEndSubproof | VernacShow _
  | VernacCheckGuard | VernacValidateProof | VernacProof _ ->
    ignore p; ok

let ( let* ) = Result.bind

let check (p : policy) (vc : vernac_control) : (unit, string) result =
  let { control; attrs; expr } = vc.CAst.v in
  let* () =
    List.fold_left (fun acc c -> match acc with Result.Error _ -> acc | Result.Ok () -> check_control p c)
      ok control
  in
  let* () = check_attributes p attrs in
  match expr with
  | VernacSynterp e -> check_synterp p e
  | VernacSynPure e -> check_synpure p e
