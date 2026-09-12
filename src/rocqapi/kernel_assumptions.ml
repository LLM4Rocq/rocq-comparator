(* Thin wrapper around Rocq's [Assumptions] module.

   It lives in its own (unwrapped) dune library because the main library
   defines a module called [Assumptions] too, which would shadow Rocq's
   inside the wrapped library. *)

open Names

(* --- naming -------------------------------------------------------------

   Every name reported here is the CANONICAL kernel name, not the user name.

   Why: [Include M] (and module aliasing in general) re-declares an object
   under a *user* name in the including module while the kernel keeps the
   original *canonical* name; [Constant.to_string] prints the user name.  Two
   different user names can therefore denote the very same kernel object, so a
   permitted-axiom list matched against user names could be defeated by
   aliasing an axiom into a module whose name happens to be permitted (and,
   symmetrically, a legitimately permitted axiom reached through an alias
   would be reported under a name the list does not mention).  The canonical
   name is the kernel's identity of the object and cannot be chosen by the
   solution for an object it did not declare itself.

   For constants and inductives that come from a library, user = canonical, so
   nothing changes for the usual fully qualified names
   ("Stdlib.Logic.Classical_Prop.classic"). *)

(* [KerName.to_string] is flagged "not to be used for user-facing messages",
   because it is the raw internal encoding rather than a pretty-printed name.
   That raw encoding is exactly what we want here: it is the stable, canonical,
   fully-qualified dotted string ("Stdlib.Logic.Classical_Prop.classic") that
   [permitted_axioms] entries are written as, so it doubles as the matching key
   and the reported name.  There is no better-fit "safe name" API for the
   canonical name of a constant, and [permitted_axioms] are user-provided
   strings of precisely this shape, so this is the pragmatic and correct choice. *)
let const_name (c : Constant.t) = KerName.to_string (Constant.canonical c)

(* The canonical name of the [i]th inductive type of the block [m]: the
   canonical module path of the block, with that packet's own type name. *)
let ind_name ((m, i) : Ind.t) =
  let mp = KerName.modpath (MutInd.canonical m) in
  match (Global.lookup_mind m).Declarations.mind_packets with
  | packets when i >= 0 && i < Array.length packets ->
    KerName.to_string (KerName.make mp packets.(i).Declarations.mind_typename)
  | _ | (exception _) -> KerName.to_string (MutInd.canonical m)

let mind_name (m : MutInd.t) = ind_name (m, 0)

let construct_name (((m, i), k) : Construct.t) =
  match (Global.lookup_mind m).Declarations.mind_packets with
  | packets when i >= 0 && i < Array.length packets
                 && k >= 1 && k <= Array.length packets.(i).Declarations.mind_consnames ->
    ind_name (m, i) ^ "." ^ Id.to_string packets.(i).Declarations.mind_consnames.(k - 1)
  | _ | (exception _) -> ind_name (m, i) ^ "#" ^ string_of_int k

let glob_name (g : GlobRef.t) =
  match g with
  | GlobRef.ConstRef c -> const_name c
  | GlobRef.IndRef i -> ind_name i
  | GlobRef.ConstructRef c -> construct_name c
  | GlobRef.VarRef id -> Id.to_string id

(* --- classification ----------------------------------------------------- *)

type tag =
  [ `Axiom | `Primitive | `Symbol | `Variable | `Positive | `Guarded | `Type_in_type | `Uip ]

(* [Assumptions.assumptions] reports every body-less constant as
   [Axiom (Constant c, _)] (see [Declareops.constant_has_body], which answers
   false for [Undef], [Primitive] and [Symbol] alike).  Split them apart by
   looking the constant up in the kernel:

   - [Primitive _] is a kernel primitive *operation* (Uint63.add, PrimFloat.mul,
     PArray.get, ...).  It is *not* an assumption: its meaning is fixed by the
     kernel, not by an unproved declaration, and the [Primitive] vernacular is
     denied to solutions, so only a trusted library can introduce one.
   - [Symbol _] is a rewrite-rule symbol: unsafe, it makes the kernel's
     conversion depend on user-supplied rules.
   - [Undef _] is a real axiom -- with one exception: a primitive *type*
     ([int], [float], [string], [array]) is stored as [Undef None] and
     recorded in the kernel's retroknowledge instead
     (kernel/constant_typing.ml: [OT_type _ -> Undef None], and
     kernel/safe_typing.ml registers [Register_type]).  Those four constants
     are primitives too, so recognise them through [Environ.retroknowledge];
     the kernel refuses to register a primitive type more than once and forbids
     it inside a section, so this cannot be spoofed by a solution. *)
let is_primitive_type (env : Environ.env) (c : Constant.t) =
  let r = Environ.retroknowledge env in
  let is = function Some c' -> Constant.CanOrd.equal c c' | None -> false in
  is r.Retroknowledge.retro_int63 || is r.Retroknowledge.retro_float64
  || is r.Retroknowledge.retro_string || is r.Retroknowledge.retro_array

let classify_constant (env : Environ.env) (c : Constant.t) : tag =
  match (Global.lookup_constant c).Declarations.const_body with
  | Declarations.Primitive _ -> `Primitive
  | Declarations.Symbol _ -> `Symbol
  | Declarations.Undef _ -> if is_primitive_type env c then `Primitive else `Axiom
  (* cannot happen (a constant with a body is not reported as an axiom); stay
     on the safe side and treat it as an axiom if it ever does *)
  | Declarations.Def _ | Declarations.OpaqueDef _ -> `Axiom
  | exception _ -> `Axiom

(* [Assumptions.uses_uip] (vernac/assumptions.ml) is *shape*-based: it flags
   every inductive that looks like an equality-with-UIP (irrelevant, not
   squashed, one constructor with no real arguments), whether or not the
   definitional-UIP rule was ever enabled for it.  That over-reports ordinary
   library inductives such as [SProp]-valued records.  What actually weakens
   the kernel is the [allow_uip] typing flag, so report [Uip] only when the
   inductive was really declared with definitional UIP allowed.  (A *local*
   inductive with [allow_uip] is rejected outright by Envcheck, so this can
   only ever concern library inductives.) *)
let really_uses_uip (m : MutInd.t) =
  match (Global.lookup_mind m).Declarations.mind_typing_flags with
  | flags -> flags.Declarations.allow_uip
  | exception _ -> true

let collect (gr : GlobRef.t) : (tag * string) list =
  let env = Global.env () in
  let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
  let acc = (Library.indirect_accessor [@alert "-deprecated"]) in
  let m = Assumptions.assumptions acc ts ~add_opaque:false ~add_transparent:false [ gr ] in
  Printer.ContextObjectMap.fold
    (fun obj _ty acc ->
       match obj with
       | Printer.Variable id -> (`Variable, Id.to_string id) :: acc
       | Printer.Axiom (Printer.Constant c, _) -> (classify_constant env c, const_name c) :: acc
       | Printer.Axiom (Printer.Positive m, _) -> (`Positive, mind_name m) :: acc
       | Printer.Axiom (Printer.Guarded g, _) -> (`Guarded, glob_name g) :: acc
       | Printer.Axiom (Printer.TypeInType g, _) -> (`Type_in_type, glob_name g) :: acc
       | Printer.Axiom (Printer.UIP m, _) ->
         if really_uses_uip m then (`Uip, mind_name m) :: acc else acc
       | Printer.Opaque c -> (`Axiom, const_name c) :: acc
       | Printer.Transparent _ -> acc)
    m []
