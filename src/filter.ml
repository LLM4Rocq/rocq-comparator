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

(* [VernacExtend] is how Rocq represents BOTH an ordinary tactic call (Ltac,
   Ltac2, ssreflect, lia, ...) and a handful of extension *commands*, all as
   one AST node tagged with the plugin that defined it.  We do not police
   tactics: whatever proof term a tactic builds is checked by the kernel, and
   any axiom or disabled kernel check it relies on is caught by the
   assumptions and typing-flag checks (the two `[no filter]` fixtures show
   those rejections happen with this filter switched off).  So instead of
   maintaining a list of *blessed* tactic plugins, we deny only the extensions
   that act outside the kernel.

   Today that is just extraction: it writes source files and can drive an
   external compiler, and has no place in a proof.  The in-process
   code-loading vectors (`Declare ML Module`, `Load`, `Cd`) are dedicated
   constructors, denied below; `Add LoadPath` / `Add ML Path` were removed in
   Rocq 9.2.  A challenge may per-problem re-allow a denied plugin through
   [permitted_plugins]. *)
let denied_plugins = [ "extraction" ]

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
  | ControlProfile (Some _) -> deny "Profile to a file"
  | ControlTime | ControlInstructions | ControlProfile None | ControlTimeout _
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
      (* a per-problem override always wins *)
      if List.mem plug p.permitted_plugins || List.mem ext.ext_plugin p.permitted_plugins
      then ok
      else if List.mem plug denied_plugins then
        deny ("command from the " ^ plug ^ " plugin (" ^ ext.ext_entry
              ^ "), which acts outside the kernel")
      else ok)
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
