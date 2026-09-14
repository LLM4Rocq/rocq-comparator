# rocq-comparator — design

A trustworthy judge for Rocq proofs, modelled on
[leanprover/comparator](https://github.com/leanprover/comparator), built as a
single OCaml executable linked against the installed `rocq-runtime` (no
source changes to Rocq, no `coqc` subprocess on the trusted path).

## 1. Goal and guarantee

Input: a trusted **challenge** `.v` file containing one or more theorems whose
proofs are missing (`Admitted.`, or any proof), a possibly adversarial
**solution** `.v` file, a list of `theorem_names`, optional
`definition_names` (definition holes), and a list of `permitted_axioms`
(fully qualified kernel names, e.g. `Stdlib.Logic.Classical_Prop.classic`).

Assumptions (mirroring Lean's comparator):

1. The installed load path (every `.vo` the challenge or solution can
   `Require` from the switch), the challenge file, its project file and its
   transitive `Require` closure inside that project are controlled by you or
   trustworthy (section 16).
2. You have not previously compiled the solution (or any adversarial file) in
   a way that could have modified the challenge or the load path.
3. The sandbox (`sandbox-exec` on macOS, `landrun`/`bwrap` on Linux, or your
   own wrapper) works and the solution does not escape it.
4. The Rocq kernel of the linked `rocq-runtime` is correct.
5. You are not running as a privileged user.

If `rocq-comparator check config.json` exits 0, then for every name in
`theorem_names` the solution's constant:

1. **proves the same statement** as the challenge's: its type is identical to
   the challenge's type (structurally, modulo a bijective renaming of
   library-local universe levels, with universe constraints on those levels
   no stronger than the challenge's), and every constant / inductive that the
   statement transitively depends on is identical in both environments
   (kind, type, body, universes, typing flags);
2. **uses no more axioms than `permitted_axioms`**: the transitive closure of
   its proof term contains no `Undef` constant outside the permitted list, no
   section variable, no `Symbol` (rewrite rule), and no constant or inductive
   declared with a kernel check bypassed (guard, positivity, universes,
   definitional UIP);
3. **is accepted by the Rocq kernel**: the proof term was type-checked by
   `Safe_typing` in this process, with default typing flags, the environment
   is joined (no delayed opaque proof), and (optionally, on by default) the
   library was re-checked by `rocqchk`, Rocq's independent checker.

Definition holes (`definition_names`) get the weaker Lean guarantee: name,
kind (must be a definition, not an assumption), type and universes match, and
the body obeys the axiom policy. As in Lean, definition-hole solutions can be
gamed semantically and must be reviewed by an additional verifier.

## 2. Why this design (vs rocq-mcp's `rocq_verify`)

`rocq_verify` (rocq-mcp) wraps the solution source in `Module M. ... End M.`,
re-states the challenge, closes it with `exact M.foo || apply ...`, and parses
the text of `Print Assumptions`. It needs two `coqc` subprocesses, regex-based
forbidden-command filtering, text surgery to share definitions across the
module boundary (nominal types), and a short-name axiom whitelist. It has
missed `#[bypass_check]` (see rocq-mcp-evolve audit A130).

This project does the comparison **at the kernel level**:

- the challenge and the solution are compiled **in-process**, one after the
  other, from **source text** (never from a `.vo` produced by an adversary —
  the analogue of Lean's "never load oleans" policy; Rocq `.vo` files are
  `Marshal` blobs, which is an even larger attack surface than mmapped
  oleans);
- both are compiled under the **same logical library name** (the `-top`
  dirpath), so kernel names coincide and statements can be compared as
  `Constr.t` trees, Lean-style, including their dependency closure;
- assumptions are computed with `Assumptions.assumptions` (the function behind
  `Print Assumptions`) and classified **by constructor**, never by parsing
  printed text; axiom names are matched **fully qualified**;
- dangerous vernaculars are rejected on the **parsed AST** with a
  default-deny classification of every `Vernacexpr` constructor (the OCaml
  exhaustiveness check guarantees no constructor is forgotten) and a plugin
  allow-list for `VernacExtend`;
- the whole run happens under an OS sandbox as defence in depth.

Per-solution cost is dominated by proof checking itself: one process, no
`coqc` spawn, no text surgery, and `.vo` loading only for trusted libraries.

## 3. Pipeline

```
rocq-comparator check config.json
  │
  ├─ (outer) parse config, resolve load path, pick sandbox, create scratch dir
  ├─ (outer) re-exec self under the sandbox with ROCQ_COMPARATOR_INNER=1,
  │          wall-clock timeout enforced by the outer process (kill on expiry)
  │
  └─ (inner)
     0. plan (section 16): discover the two files' projects, compute the
        Require closures, classify trusted / untrusted, refuse collisions;
        with a project the trusted helpers were compiled by a separate
        trusted phase into scratch/trusted before this process started
     1. init Rocq once (Coqinit.init_ocaml / parse_arguments / init_runtime /
        init_document) with: the trusted load path (-Q/-R/-I) plus the scratch
        mirrors, -noinit only if the config says so, native compiler OFF, VM
        per config (default on), -impredicative-set / -indices-matter from
        config (both files share them)
        → freeze ROOT = Vernacstate.freeze_full_state ()
     2. CHALLENGE: unfreeze ROOT; Coqinit.start_library ~top; parse+run every
        sentence of Challenge.v (AST filter applied in *lenient* mode: only
        commands that would break the comparator itself are rejected, e.g.
        Load/Chdir/AddLoadPath; the challenge is trusted);
        → extract SPEC (section 5) from Global.env ()
     3. UNTRUSTED HELPERS, then SOLUTION: for each, unfreeze ROOT;
        start_library (a helper under its own name, the solution under ~top);
        parse+run every sentence with the *strict* AST filter (section 6) and
        per-sentence Control.timeout under one deadline; a helper is scanned
        by the hygiene check and saved to scratch/untrusted
        → env_s = Global.env ()
     4. CHECKS on env_s (all run, all reported; verdict ok iff all pass):
        a. joined: Safe_typing.is_joined_environment (Global.safe_env ())
        b. targets: each theorem name resolves to a constant; kind is
           Def/OpaqueDef (Undef → "not_proved")
        c. statement match + dependency closure vs SPEC (section 5)
        d. assumptions (section 7)
        e. environment hygiene (section 8)
        f. loaded libraries all resolve under the trusted load path roots
        f'. every library loaded from scratch is one this run wrote, unchanged
        g. optional: save Challenge.vo to scratch, run `rocqchk -silent
           -norec <helper> (one each) -norec <top>` in the sandbox (section 9)
     5. print one JSON verdict on stdout (section 10); exit 0 / 1 / 2
```

Order matters: the challenge is compiled **before** the solution so the
solution cannot influence the extraction of SPEC. SPEC is a plain immutable
OCaml value that survives `Vernacstate.unfreeze_full_state ROOT`.

Precedents for "several libraries in one process by unfreezing a root state":
coq-lsp (`coq/init.ml: doc_init`), rocq-mcp-evolve's `rocq_driver.ml`.

## 4. Driver (src/driver.ml)

Startup mirrors `rocq-tools/src/audit/rocq_assumptions.ml` (known to work on
9.1; verify signatures against the local switch's 9.2 `.mli`s):

```ocaml
Coqinit.init_ocaml ();
let opts, () = Coqinit.parse_arguments ~parse_extra:(fun _ e -> ((), e))
    ~initial_args:Coqargs.default args in      (* args: -Q/-R/-I ..., -native-compiler no, ... *)
Coqinit.init_runtime ~usage opts;
Coqinit.init_document opts;
let root = Vernacstate.freeze_full_state () in
(* per library: *)
Vernacstate.unfreeze_full_state root;
Coqinit.start_library ~intern:Vernacinterp.fs_intern ~top (Coqargs.injection_commands opts);
```

Parsing: `Procq.Parsable.make` over the whole file with a real `Loc.t`
(file name + offsets), `Procq.Entry.parse (Pvernac.main_entry None)` in a loop
until `None`. Keep the proof-mode-aware entry (`Pvernac.main_entry
(Some pm)`) behaviour identical to `coqc`: use `Vernacstate.Synterp` /
`Pvernac` the way `Ccompile`/`Vernac.load_vernac_core` does (read that file
in `rocq-runtime`'s `toplevel/vernac.ml` and copy its loop rather than
reinventing it).

Execution: `Vernacinterp.interp ~intern:Vernacinterp.fs_intern ~st vc`, with
the returned state threaded. Every sentence of the solution runs under
`Control.timeout remaining_budget`; `memprof-limits` token interruption as the
outer layer (same combination as rocq-mcp-evolve / coq-lsp) so that
allocation-heavy loops that never hit `Control.timeout` checkpoints are still
interrupted. Feedback messages are collected (not printed) and attached to the
verdict on error.

Error handling: any `CErrors.noncritical` exception while running a solution
sentence → verdict `compile_error` with `Loc`, message and the sentence text.
`Sys.Break`/anomalies → `internal_error` (exit 2) — never `ok`.

Native compute is disabled at init (`-native-compiler no`, and additionally
`Global.set_native_compiler false` after init, verified with
`Environ.typing_flags`), because `native_compute` compiles and `dlopen`s
generated OCaml code.

## 5. SPEC extraction and comparison (src/spec.ml, src/compare.ml)

SPEC is extracted from the challenge environment:

```ocaml
type const_spec = { kn : Constant.t; body : cbody; typ : Constr.t;
                    univs : Declarations.universes; flags : typing_flags }
and cbody = Undef | Def of Constr.t | Opaque of Constr.t (* forced *) | Primitive of CPrimitives.t
type ind_spec  = { mind : MutInd.t; body : mutual_inductive_body }
type target    = { name : string; kn : Constant.t; kind : [`Theorem | `Definition_hole];
                   typ : Constr.t; univs : universes }
type spec = { targets : target list; closure : (const_spec list * ind_spec list);
              graph : UGraph.t; top : DirPath.t }
```

Targets are resolved with `Smartlocate.global_with_alias (qualid_of_string
name)` in the challenge state (also try `top.name`); the result must be a
`ConstRef` whose `ModPath` is `MPfile top` or an `MPdot` chain rooted there.

Dependency closure (Lean's `getUsedConstants` worklist): starting from every
target's **type** (and, for definition holes, the type only), traverse
`Constr.t` collecting `Const`, `Ind`, `Construct`, `Proj` (its inductive and
its projection constant), `Case` (its `ci_ind`), and `Var` (→ immediate
error: statements must be closed, section variables are not allowed). For
every collected constant/inductive, add its type, its body (for `Def` and
forced `OpaqueDef`), and for inductives all arities and constructor types, and
continue until the worklist is empty. Only **library-local** objects
(`ModPath` rooted at `MPfile top`) go into `closure`; objects from
`Require`d libraries are compared *by presence and shape* in a lighter way:
their `Constant.t`/`MutInd.t` must resolve in the solution env to a constant
with `Constr.equal` type (they come from the same trusted `.vo`, so this is
belt-and-braces — Lean compares them fully; we compare type + body for
constants and the packet shapes for inductives, which is cheap since these
are already-loaded values).

Also add to the closure every permitted axiom that exists in the challenge
env (Lean adds `legalAxioms` to the compare targets), and check in the
solution env that each permitted axiom name resolving to a constant is `Undef`
with an equal type.

Comparison, per target: solution constant must exist, must be `Def` or
`OpaqueDef` (definition holes: `Def` or `OpaqueDef`; theorem targets:
`Def` or `OpaqueDef` — a `Definition foo : T := proof` is acceptable),
`typ` equal modulo universe renaming (below), `univs` equal: both
`Monomorphic`, or both `Polymorphic` with `AbstractContext.size` equal and
constraints equal (compare `UVars.AbstractContext.repr` → `UContext`
constraints with `Univ.Constraints.equal`; names are irrelevant).

Per closure constant: kind equal (`Undef`/`Def`/`OpaqueDef`/`Primitive`),
type and body equal modulo universe renaming, `univs` as above, and the
safety-relevant typing flags equal (section 8). Per closure inductive:
compare `mind_finite`, `mind_ntypes`, `mind_nparams`, `mind_nparams_rec`,
`mind_params_ctxt`, `mind_record` (constructor of `record_info`, and for
`PrimRecord` the projection labels), `mind_universes`, `mind_template`
(presence + structure), `mind_variance`, `mind_private`, `mind_hyps` (must be
empty), safety flags, and per packet `mind_typename`, `mind_arity_ctxt`,
`mind_user_arity`, `mind_sort`, `mind_consnames`, `mind_user_lc`,
`mind_nrealargs`, `mind_nrealdecls`, `mind_squashed`, `mind_relevance` —
everything that determines the kernel object; derived/cache fields
(`mind_nf_lc`, `mind_recargs`, `mind_reloc_tbl`, `mind_nb_*`) are skipped.

### Equality modulo universe renaming

Anonymous monomorphic universes are named `<top>.<n>` in creation order, so a
solution that declares one extra `Type`-using definition before the target
shifts every later level name. Comparison therefore uses
`Constr.compare_head_gen` (kernel/constr.mli) with custom instance and sort
comparators over a stateful bijection `ren : Level.t ↔ Level.t`:

- `Level.is_set` or `Level.var_index` (polymorphic bound var) → `Level.equal`;
- global level with `Level.name = Some g`, `UGlobal.repr g = (dp,_,_)`: if
  `dp` equals `top` on both sides → look up / extend `ren` (fail if either
  side is already mapped to something else); if neither is local →
  `Level.equal`; mixed → not equal;
- `Universe.t` compared as sorted `(level, n)` lists through the above;
- `Sorts.t`: constructor-wise; `QSort` qualities compared by `QVar.equal`
  (sort-polymorphic variables live in the abstract context); `Type u` via
  universes.

Traversal order is deterministic and identical on both sides, so the
bijection is well defined. Terms are compared with the *same* `ren`
accumulated across the whole SPEC (targets first, then closure).

Constraint entailment: let `L` be the set of local levels in `ren`'s domain.
For every pair `(a, b)` in `(L ∪ {Set})²` with `a ≠ b`, if
`UGraph.check_leq env_s (Universe.make a') (Universe.make b')` holds in the
**solution** graph (with `a', b'` the solution-side names), then
`UGraph.check_leq spec.graph (Universe.make a) (Universe.make b)` must hold
in the **challenge** graph; likewise for strict `<` (`check_leq` of
`Universe.super`). Any solution-only constraint means the solution proved a
weaker (more constrained) statement → `statement_mismatch` with the offending
pair in `detail`. `spec.graph = Global.universes ()` captured at SPEC time.

## 6. Vernacular filter (src/filter.ml)

Applied to every parsed `Vernacexpr.vernac_control` **before** execution.
Implemented as a total function over `vernac_control_gen`, `control_flag`,
`synterp_vernac_expr`, `synpure_vernac_expr` and attributes, with `[@warning
"+8"]` so a new constructor in a future Rocq breaks the build rather than
silently passing. Two modes: `Strict` (solution) and `Lenient` (challenge).

Denied in both modes (they break the comparator's own invariants):
`VernacLoad`, `VernacChdir`, `VernacDeclareMLModule`, `VernacExtraDependency`,
`VernacAddLoadPath`/`VernacRemoveLoadPath`/`VernacAddMLPath` (find their
9.2 spelling; they may live in `VernacExtend` or `synterp`), `ControlRedirect`,
`VernacResetName`, `VernacResetInitial`, `VernacBack`, `VernacUndo`,
`VernacUndoTo`, `VernacRestart`, `VernacAbortAll`, `VernacWriteState`,
`VernacRestoreState` (if present), `VernacPrint` of `PrintUniverses` with a
file name, `VernacRegister`, `VernacPrimitive`, `VernacSymbol`,
`VernacAddRewRule`.

Denied only in `Strict` mode (in addition): `VernacSetOption`/`VernacAddOption`/
`VernacRemoveOption` on option names in the deny-list below,
`VernacDeclareModule`/`VernacDeclareModuleType` are allowed but
`VernacInclude` is allowed too — module tricks are caught at the kernel level
(the target's canonical constant is what gets checked); `VernacAbort` allowed
(the target will simply be missing); `VernacProofMode` allowed;
`VernacExtend (ext, _)`: this one node is both every tactic call and a few
extension *commands*. Tactics are not policed — the kernel checks whatever
term they build, and a disabled check or stray axiom is caught by the
assumptions / typing-flag checks — so there is no allow-list of blessed
plugins. Instead `Strict` denies only the extensions that act *outside* the
kernel: the `denied_plugins` set, today just `extraction` (writes source
files, can drive an external compiler), and the elpi entries that define,
extend or query an elpi program (section 16). Every other extension is
allowed. The
in-process code-loading vectors (`Declare ML Module`, `Load`, `Cd`) are
dedicated constructors denied above; `Add LoadPath` / `Add ML Path` no longer
exist in Rocq 9.2. A challenge may re-allow a denied plugin per problem via
`permitted_plugins`. Attributes: `bypass_check(...)` denied in `Strict` mode
(also caught later by the typing-flag check).

Option deny-list (name paths as strings): `Guard Checking`,
`Positivity Checking`, `Universe Checking`, `Definitional UIP`,
`Allow Rewrite Rules`, `Allow StrictProp` is allowed, `Extraction Output
Directory`, `Native Compiler`? (not an option; ignore), `Cumulative
StrictProp`? (ignore). `Set`/`Unset` of anything else is allowed.

Everything else (`Definition`, `Theorem`, tactics via `VernacExtend ltac`,
`Notation`, `Require`, `Import`, `Section`, `Module`, `Hint`, `Print`,
`Search`, `Fail`, `Time`, `Timeout`, `Succeed`, ...) is allowed.

`Require` is allowed because the load path is trusted (assumption 1); the
optional config `permitted_libraries` (list of dirpath prefixes) restricts it
further, checked both on the AST (`VernacRequire` qualids after resolution)
and post hoc on `Library.loaded_libraries ()`.

## 7. Assumptions (src/assumptions.ml)

Exactly `rocq-tools/src/audit/rocq_assumptions.ml`'s core: for each target
`gr`, `Assumptions.assumptions (Library.indirect_accessor) ts
~add_opaque:false ~add_transparent:false gr cstr` → `ContextObjectMap`;
classify every key by constructor:

| object | verdict |
|---|---|
| `Variable id` | reject (`forbidden_axiom`, "section variable") |
| `Axiom (Constant c, _)` | ok iff `Constant.to_string c` matches `permitted_axioms` (exact, or a `Prefix.*` wildcard) |
| `Axiom (Positive m, _)` / `Guarded gr` / `TypeInType gr` / `UIP m` | reject (`unsafe_flags`) |
| `Opaque`/`Transparent` | not produced (flags false) |

The verdict lists, per target, the fully qualified assumptions it depends on
(so a consumer sees exactly which permitted axioms were used).

Additionally, for each target, if its own body is `Undef` → `not_proved`
(covers `Admitted.`, `Parameter`, `Abort` + `Axiom`, `Include` of an
axiomatised module, etc.). Rewrite-rule `Symbol`s are rejected by section 8.

## 8. Environment hygiene (src/envcheck.ml)

After the solution compiles:

- `Global.rewrite_rules_allowed ()` must be false; no library-local constant
  may have `const_body = Symbol _`.
- Every library-local constant and inductive (`Environ.fold_constants`,
  `fold_inductives`, filtered on `ModPath` rooted at `MPfile top`) must have
  safety flags `check_guarded = true`, `check_positive = true`,
  `check_universes = true`, `allow_uip = false`, and `impredicative_set` /
  `indices_matter` equal to the challenge's (they are process-wide init
  flags, so this is a consistency assertion).
- `Safe_typing.is_joined_environment (Global.safe_env ())` must be true.
- `Environ.typing_flags (Global.env ())` must still have
  `enable_native_compiler = false`.
- Every `Library.loaded_libraries ()` entry located via
  `Loadpath.locate_absolute_library` must be under one of the trusted roots
  (the switch's `coqlib`, `user-contrib`, and the configured `-Q/-R` dirs).

## 9. rocqchk replay (src/rocqchk.ml)

If `rocqchk` is found (same `bin/` as the running switch: derive from
`Boot.Env`/`Envars.coqbin` or `Sys.executable_name`'s switch) and
`config.rocqchk` is true (default):
`Declaremods.end_library ~output_native_objects:false top` then
`Library.save_library_to` (see `toplevel/ccompile.ml` in rocq-runtime for the
exact call sequence in 9.2) into `<scratch>/<Top>.vo`, then run
`rocqchk -silent -norec <top> -Q <scratch> <top-prefix>` plus the trusted
`-Q/-R` flags, inside the same sandbox, with the remaining time budget.
Non-zero exit → `rocqchk_failed`. The `.vo` is produced by *this* process, so
unmarshalling it in `rocqchk` is not an adversarial input. With a project,
one `-norec` per untrusted helper is added and the scratch mirrors are on
rocqchk's load path: every library the solver's side produced is replayed,
and the trusted helpers and installed libraries are admitted from `.vo`
files the comparator itself wrote or the switch installed.

## 10. Config, CLI, output

Config (JSON; all paths relative to the config file's directory):

```json
{
  "challenge": "Challenge.v",
  "solution": "Solution.v",
  "theorem_names": ["foo"],
  "definition_names": [],
  "permitted_axioms": ["Stdlib.Logic.Classical_Prop.classic",
                       "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep",
                       "Stdlib.Reals.ClassicalDedekindReals.*"],
  "loadpath": [ {"Q": ["theories", "Comp"]}, {"R": ["dir", "Logical"]}, {"I": ["mlpath"]} ],
  "coqproject": null,
  "top": "Challenge",
  "timeout_s": 600,
  "sandbox": "auto",
  "rocqchk": true,
  "vm": true,
  "impredicative_set": false,
  "indices_matter": false,
  "permitted_plugins": [],
  "permitted_libraries": [],
  "permit_challenge_axioms": true
}
```

Each entry of `permitted_axioms` is a fully qualified kernel name (e.g.
`Stdlib.Logic.Classical_Prop.classic`) or a prefix wildcard
(`"Some.Dir.Path.*"`). There is deliberately **no built-in list of "known"
axioms to maintain**: the permitted set is stated per challenge, exactly as
Lean's comparator does it. To discover the names a given challenge or a
reference proof actually needs, run `rocq-comparator validate` (or
`Print Assumptions`) and copy the fully qualified names it reports; the
`validate` verdict lists them. (Note for anyone porting the old DESIGN
example: `"Stdlib.Reals.Raxioms.*"` matches nothing — in Rocq 9.x `R` is
built from Dedekind cuts, so the real Reals axioms live under
`Stdlib.Reals.ClassicalDedekindReals.*` and
`Stdlib.Logic.FunctionalExtensionality.*`.)

`permit_challenge_axioms` (default `true`): every constant the challenge
itself leaves `Undef` (a `Parameter`/`Axiom`, or a helper lemma left
`Admitted` other than the targets) is automatically added to the permitted
set and pinned to its challenge-side statement, so a solution may either
rely on it as given or supply its own proof; set to `false` to require such
helpers to be listed in `permitted_axioms` explicitly like any other axiom.

`loadpath` names directories of already compiled, trusted `.vo` files.
`coqproject` is not a load-path source any more: it overrides project
discovery (section 16), naming the `_CoqProject` or `dune-project` of both
files, and `""` disables discovery; the default is to discover a project from
each file's path. `top` defaults to the challenge file's logical name in its
project, else the name derived from the load path (as `coqdep` would), else
the basename. `sandbox` ∈ `auto | none |
sandbox-exec | landrun | bwrap | {"command": ["...", "..."]}`; `auto` picks
the first available for the platform and falls back to `none` **with
`"sandboxed": false` in the verdict and a warning on stderr** (never silently).
The custom form gets the scratch dir and the inner command appended.

CLI (cmdliner):

```
rocq-comparator check CONFIG.json [--json|--pretty]
rocq-comparator check --challenge C.v --solution S.v --theorem foo [--theorem bar]
                      [--axiom NAME]... [-Q dir Logical]... [--timeout N] [--sandbox MODE] [--no-rocqchk]
rocq-comparator batch CONFIG.json SOLUTION.v... [-j N]     # one JSON line per solution (challenge compiled once, one forked child per solution)
rocq-comparator sandbox-info                                # which sandbox would be used, and why
```

Verdict (stdout, one JSON object; stderr is free-form):

```json
{ "ok": false, "reason": "statement_mismatch",
  "detail": "foo: type differs at ...",
  "sandboxed": true, "sandbox": "sandbox-exec", "rocq_version": "9.2.0",
  "targets": { "foo": { "status": "proved|not_proved|missing|mismatch",
                        "assumptions": ["Stdlib.Logic.Classical_Prop.classic"] } },
  "checks": { "challenge_compile": "ok", "solution_compile": "ok", "joined": "ok",
              "statements": "fail", "closure": "ok", "axioms": "ok",
              "hygiene": "ok", "libraries": "ok", "rocqchk": "skipped" },
  "timing_s": { "init": 0.1, "challenge": 0.3, "solution": 1.2, "compare": 0.0, "rocqchk": 0.8 } }
```

`reason` ∈ `statement_mismatch | dependency_mismatch | not_proved |
target_not_found | kind_mismatch | forbidden_axiom | unsafe_flags |
forbidden_command | compile_error | challenge_error | timeout |
rocqchk_failed | library_violation | internal_error`. Exit code: 0 ok, 1
rejected, 2 infrastructure error (bad config, challenge does not compile,
sandbox failure).

## 11. Tests (test/)

Fixture directories `test/fixtures/<name>/` with `Challenge.v`, `Solution.v`,
`config.json` (may omit `challenge`/`solution`, defaulting to those names),
and `expected.json` (`{"exit_code": 0}` or `{"exit_code": 1, "reason":
"statement_mismatch"}`). A dune `test` runs the built binary over every
fixture and diff-checks `ok`/`reason`. Fixtures (each documents one
capability or one attack):

| fixture | expects |
|---|---|
| simple_match | ok |
| simple_mismatch (statement `0 + n` vs `n + 0`) | statement_mismatch |
| admitted_solution | not_proved |
| custom_axiom (`Axiom magic : False`) | forbidden_axiom (`Challenge.magic`) |
| permitted_axiom (`classic`, permitted) | ok |
| unpermitted_stdlib_axiom (`classic`, not permitted) | forbidden_axiom |
| def_redefinition (`Definition f := 3` → `5`) | dependency_mismatch |
| inductive_redefinition (extra constructor) | dependency_mismatch |
| bypass_check_guard (`#[bypass_check(guard)] Fixpoint` proving False) | forbidden_command (filter) — and `unsafe_flags` when run with the filter disabled via a test-only env var |
| unset_guard_checking | forbidden_command |
| module_include_admitted (`Module M0 ... Admitted ... Include M0`) | forbidden_axiom (`Include` re-declares the constant as an alias definition of `M0.foo`, whose admitted proof is caught by the axiom check) |
| section_variable (`Section` + `Variable H : False`) | statement_mismatch |
| def_hole (`Definition large : nat. Admitted.` + `37 < large`) | ok |
| def_hole_type_mismatch | statement_mismatch |
| universe_shift (extra `Definition helper (A : Type) := A.` before a `Type`-quantified target) | ok |
| universe_polymorphic_match | ok |
| forbidden_command (`Declare ML Module`, `Redirect`, `Load`) | forbidden_command |
| compile_error | compile_error |
| timeout (tiny `timeout_s`, slow `vm_compute`/`cbv`) | timeout |
| reals_axioms (`Reals`, `Stdlib.Reals.Raxioms.*` permitted) | ok |
| batch (3 solutions → 2 ok, 1 fail, JSONL) | — |
| rocqchk_runs (verdict has `"rocqchk": "ok"`) | ok |
| project_shared (shared `_CoqProject`, trusted `Defs`, checked `theories/Lib`) | ok, manifest labels |
| project_dune (solution in its own dune project, `include_subdirs qualified`) | ok |
| project_helper_axiom (`Axiom` in an untrusted helper) | forbidden_axiom |
| project_helper_unset_guard (`Unset Guard Checking` in an untrusted helper) | forbidden_command |
| project_shadow_binding (solution binding `Proj.Extra` under the challenge's `Proj`) | library_violation |
| project_name_collision (solution ships its own `Proj.Defs`) | library_violation |
| project_stale_vo (stale `Helper.vo` next to the untrusted `Helper.v`) | forbidden_axiom (the `.v` wins) |

Plus a handful of unit tests (alcotest) for `compare.ml`'s universe renaming
and `filter.ml`'s classification. No exhaustive unit-test drowning.

## 12. Layout

```
dune-project, rocq-comparator.opam, LICENSE (Apache-2.0), README.md, DESIGN.md
bin/main.ml                 cmdliner CLI → rocq-comparator
src/ (library rocq_comparator)
  config.ml  project.ml  plan.ml  rocqdep_lexer.mll  driver.ml  filter.ml
  spec.ml  compare.ml  assumptions.ml  envcheck.ml  shadowing.ml  sandbox.ml
  rocqchk.ml  check.ml  verdict.ml
examples/projects/{coqproject,dune}/   runnable project examples
test/fixtures/<name>/...   test/run_fixtures.ml   test/unit/*.ml   test/infra/*.ml
```

Build: `opam exec --switch=<project dir> -- dune build @all @runtest` in the
project-local switch (`./_opam`, OCaml 5.5.1, rocq-core 9.2.0).

## 13. Rocq 9.2 API notes (verified in the local switch, `_opam/lib/rocq-runtime`)

A prototype of the pipeline (sections 3–4, statement match, assumptions) was
built and run against Rocq 9.2 / OCaml 5.5.1; whole runs take ~0.2 s with
`Arith`+`Lia` loaded. Verified facts:

- `Coqinit.init_ocaml (); parse_arguments ~parse_extra ~initial_args args;
  init_runtime ~usage opts; init_document opts` then
  `root = Vernacstate.freeze_full_state ()`. For each library:
  `Vernacstate.unfreeze_full_state root; Coqinit.start_library
  ~intern:Vernacinterp.fs_intern ~top (Coqargs.injection_commands opts)`.
  Starting the same `top` twice this way works (challenge then solution).
- Parsing loop: `Procq.Parsable.make ~loc:(Loc.initial (Loc.InFile
  {dirpath=None; file})) (Gramlib.Stream.of_string src)`; per sentence
  `Procq.Entry.parse (Pvernac.main_entry pm) pa` with `pm = Some
  (Synterp.get_default_proof_mode ())` iff
  `st.interp.lemmas <> None` (a proof is open), else `None`; `None` result =
  end of file. Execute with `Vernacinterp.interp ~intern:Vernacinterp.fs_intern
  ~st vc` (returns the new `Vernacstate.t`).
- `Assumptions.assumptions ?add_opaque ?add_transparent
  (Library.indirect_accessor) ts [gr]` — takes a **list** of `GlobRef.t` in
  9.2 (no separate constr). Keys are `Printer.context_object`:
  `Variable | Axiom of axiom * ... | Opaque | Transparent`, with `axiom =
  Constant of Constant.t | Positive of MutInd.t | Guarded of GlobRef.t |
  TypeInType of GlobRef.t | UIP of MutInd.t`. A `#[bypass_check(guard)]`
  fixpoint used by the proof shows up as `Guarded`; an `Admitted` target
  shows up as `Axiom (Constant Challenge.foo)` with the target itself `Undef`.
- `Names.Constant.to_string` gives the fully qualified name
  (`Challenge.magic`, `Stdlib.Logic.Classical_Prop.classic`).
- `Library.save_library_to Library.ProofsTodoNone ~output_native_objects:false
  top path_dot_vo` calls `Declaremods.end_library` itself and asserts
  `Safe_typing.is_joined_environment`; call it once per library, last.
- `Vernacexpr.extend_name = { ext_plugin : string; ext_entry : string;
  ext_index : int }`; control flags: `ControlTime | ControlInstructions |
  ControlProfile | ControlRedirect | ControlTimeout | ControlFail |
  ControlSucceed`. The full constructor lists of `synterp_vernac_expr` and
  `synpure_vernac_expr` are in `vernac/vernacexpr.mli` (9.2 adds
  `VernacSchemeAll`, `VernacAbbreviation`).
- `Envars.coqpath ()`, `Boot.Env` give the install dirs; `rocqchk` lives next
  to `rocq` in the switch's `bin/`.

## 14. Roadmap (deferred)

Two audit-identified features are intentionally not implemented yet:

- **Independent second kernel.** Lean's comparator can cross-check with an
  independently-authored kernel (`nanoda`). We run `rocqchk` (Rocq's own
  `coqchk`), which is a differently-implemented replay but developed inside
  the Rocq project, not an independent implementation. Rocq also has no
  `lean4export`-equivalent serialization to feed a foreign kernel. Adding a
  genuine second kernel is high-value but large and partly blocked by the
  ecosystem.
- **Batch challenge-amortization.** `batch` recompiles the challenge once per
  solution (one sandboxed process each). Sharing a single compiled challenge
  across many solutions to the same problem — by forking after the challenge
  is compiled and running each solution in a child — would cut per-solution
  cost substantially. It needs care around Rocq global state across `fork`
  (the memprof watchdog thread, open file descriptors) and per-child
  re-sandboxing.

## 15. Web front-end (separate project)

A client-side browser front-end lives in the sibling project
`rocq-comparator-web` (kept out of this repo). It runs the whole check in the
browser on a WebAssembly Rocq, modelled on comparator.live.lean-lang.org. The
backend spike found the full build feasible via js_of_ocaml/wasm_of_ocaml with
jsCoq/wacoq's `coerce-32bit` patch to the Rocq kernel (the only real blocker
is the kernel's 63-bit-int assumption; zarith stubs are not needed — Rocq 9.2
uses native int63/float64). See `rocq-comparator-web/BACKEND.md`. The browser
build uses `Check.run_inner` with `rocqchk = None` and no OS sandbox (the
browser origin is the sandbox); the strict AST filter, kernel comparison,
assumptions, envcheck and shadowing all run as compiled OCaml in the worker.

## 16. Projects

A challenge or a solution may be one file of a project. This section is the
design of that support; the rule it implements is the Lean comparator's
assumption 1 (the challenge, its import closure and the project file are
trusted) taken literally, and nothing the solver ships is ever trusted.

### Discovery

A file's project is found from its path: the nearest ancestor directory
holding a `_CoqProject` (preferred) or a `dune-project`. The config's
`coqproject` field overrides the search for both files; `""` disables it. A
`_CoqProject` contributes its `-Q`/`-R` lines as bindings (directory,
logical prefix, implicit or not), parsed by Rocq's own
`CoqProject_file.read_project_file`. A `dune-project` contributes one binding
per `coq.theory` / `rocq.theory` stanza found in the `dune` files below the
root (skipping `_build`, `_opam`, hidden directories and nested projects),
read with a small S-expression reader: `name`, `theories`, `modules`,
`flags`, `stdlib`/`boot` and `include_subdirs` are interpreted, everything
else is ignored. A dune theory is an implicit (`-R`) binding whose files are
the stanza directory's `.v` files, plus the subdirectories' files with
qualified names under `(include_subdirs qualified)` (cut by a nested
`(include_subdirs no)` or a nested theory).

The `.v` files of every binding are enumerated by the comparator with
`lstat`; a symbolic link inside a bound directory is refused, so a project
cannot reach outside its tree. A file that no binding covers has no project
and is judged exactly as before this feature (the repository's own
`dune-project` above the test fixtures is such a case: no stanza covers
them). The comparator never runs `dune`, `make` or `rocq`; a source a dune
`(rule ...)` would generate is simply absent, and a `Require` of it fails to
compile.

A project file may not: add ML paths (`-I`); pass flags other than `-w`
selectors and the kernel flags (`-impredicative-set`, `-indices-matter`,
`-noinit`) when they equal the config's; enable the native compiler; use
`(stdlib no)` or `(boot)` without `noinit`; use `%{...}` variables,
`(include ...)`, `(subdir ...)`, `(modules_flags ...)` or a set-language
`(modules ...)`; give two files the same logical name. Problems in the
challenge's project are `config_error` (exit 2, the operator's); problems in
a solution's own project are `compile_error` (exit 1, a verdict about the
solution), so that a malformed submission can never look like an
infrastructure failure. `_CoqProject` file lists are accepted and ignored
(they do not change what is bound or compiled). Rocq's `_CoqProject` parser
exits the process, rather than raising, on a few malformed arms (a bare
`-impredicative-set`, an unknown `-native-compiler` value, a repeated
`-docroot` or `-generate-meta-for-package`); inside the sandbox that exit
would read as a `sandbox_error`, so the comparator tokenizes the file first
(the parser's tokenizer is not exported; `Project.tokens` mirrors it) and
refuses those arms with the verdict above before the parser runs.

### The plan

`Plan.make` (src/plan.ml), computed in each inner process before Rocq is
initialised:

1. discover the challenge's project, then the solution's (the same one when
   it covers the solution file);
2. read every planned file's `Require` statements with coqdep's own lexer
   (`Rocqdep_lexer`, vendored from Rocq: the `coqdeplib` library registers a
   warning name that the Rocq library already owns, so the two cannot be
   linked into one process) and resolve each with Rocq's rule: `From F
   Require D.B` names the file whose logical directory is `F.D` (exact), and
   under an implicit binding a suffix match is enough; a challenge-project
   file resolves only inside its project. A `Require` that names no planned
   file is an installed library, resolved by Rocq at compile time from the
   trusted load path or failing there. A `Require` that could name two
   planned files is refused (a `library_violation` when one of them is the
   challenge's, else the solver's `compile_error`);
3. TRUSTED = the challenge's transitive closure, restricted to files of the
   challenge's project (the challenge requiring a file of the solver's
   project is a `challenge_error`); UNTRUSTED = the solution's closure minus
   TRUSTED, whichever project a file belongs to. Both in dependency order
   (depth-first postorder); a cycle is an error of its side; no file may
   require either of the two top files;
4. collisions: an untrusted file whose logical name equals, extends or is
   extended by a trusted file's name is a `library_violation` (the imported
   axiom policy is a prefix rule over library names, so nesting matters as
   much as equality); when the two projects differ, a solution binding whose
   logical prefix overlaps a challenge binding's is a `library_violation`;
   any helper whose name overlaps `top` is refused; and, after `Driver.init`,
   every planned name and binding is checked against the namespaces the
   switch owns with Shadowing's list-free rule, and every dune `(theories
   ...)` name must be a project binding or an installed logical path;
5. caps: at most 100 untrusted files and 8 MB of untrusted source, so a
   large dependency graph fails fast instead of at the outer kill.

### Scratch layout and the two phases

```
<scratch>/config.json         the resolved config
<scratch>/trusted/            written by the TRUSTED phase only
   libraries.json             what it wrote: name, path, digest per .vo
   b<i>/<rel>/<Base>.vo       mirror of binding i, trusted files
<scratch>/untrusted/          written by the SOLUTION phase only
   b<i>/<rel>/<Base>.vo       mirror of binding i, untrusted files
   top/<Base>.vo              the solution top, for rocqchk only
   verdict.json
```

When the challenge has a project, the outer process first runs the
comparator in a sandbox that may write only `scratch/trusted`: it computes
the plan, initialises Rocq with the trusted mirrors bound, runs the
shadowing checks, compiles the trusted helpers under the lenient filter
(each under its own name, with a deadline mapped to `challenge_error`),
saves each `.vo` into its mirror and records the digests. Then the solution
phase runs in a sandbox that may write only `scratch/untrusted` (its
`TMPDIR` is that directory; the system temp dir, under which the scratch
itself lives, is not writable). It reads `libraries.json`, checks that the
trusted phase produced exactly the planned files with unchanged digests,
creates the untrusted mirror directories (every directory a `.vo` will land
in must exist before `Driver.init`, because `Loadpath.add_vo_path`
enumerates subdirectories at that moment and the result is frozen into the
root state), initialises Rocq with all mirrors bound, and proceeds as in
section 3: challenge top, SPEC, untrusted helpers under the strict filter
(each scanned by the hygiene check under its own name before being saved),
solution top, the checks, rocqchk.

Only the mirrors are ever bound on the load path, never a source directory,
so a `.vo` the solver shipped, or a stale one next to a source, cannot be
loaded. The untrusted mirrors are empty while the challenge compiles, so the
challenge cannot resolve a `Require` to the solver's side even if the names
were confusable. Every library loaded from anywhere under the scratch must
be one this run wrote and must still have the digest recorded at save time;
this gate runs after each untrusted helper, after the challenge, and before
rocqchk, which then admits only those very files.

The manifest labels each loaded library `installed`, `trusted` or
`checked` from the plan's record, not from a path prefix. Axioms declared in
trusted helpers are challenge axioms (permitted under
`permit_challenge_axioms` and pinned to their types); the imported policy
covers the libraries the challenge loaded, which include the trusted helpers
and never the untrusted ones, so an axiom in an untrusted helper is always
forbidden. A non-empty `permitted_libraries` implicitly includes the
project's binding prefixes. `validate` runs the trusted phase and then the
challenge alone; `batch` discovers each solution's project in its own run.

The elpi plugin deserves a word. Its runtime exposes `system`, `open_out`
and friends, so a solution that could define or extend an elpi program (or
run one inline with `Elpi Query`) could write files inside the sandbox. In
strict mode the filter now refuses `Elpi Program/Command/Tactic/Db/File`,
`Elpi Accumulate` and `Elpi Query`, while calls to installed programs
(`HB.instance`, exported commands, elpi tactics) stay allowed; a challenge
can re-allow the rest with `permitted_plugins: ["elpi"]`, which lifts this
rule exactly as it lifts the `extraction` one. The rule is not tied to
projects: a single-file solution goes through the same strict filter, and
its own file is the first place a solver would write an `Elpi Command` or
`Elpi Query`, so the denial applies there too. The plugin model
remains deny-list based (`extraction`, and elpi program definition), backed
by the sandbox for everything else.

### Threat model additions

The invariants of section 1 survive: every untrusted `.v` goes through the
strict filter and the kernel inside the comparator; no solver-produced `.vo`
is ever loaded; the challenge and its closure are trusted, nothing else from
a submission is; the solution never runs a build system; rocqchk replays only
what the comparator compiled on the solver's side; trusted libraries are
never re-checked; there are no maintained lists. What the feature adds to
the attack surface, and how each item is closed:

- a writable directory holding trusted `.vo` files during the untrusted
  phase: closed by the two sandboxed phases (write access to one side each)
  and by the digest gate over everything loaded from scratch;
- name confusion between the two sides: closed by the collision rules
  (equal, nested, overlapping bindings, installed namespaces), applied before
  anything is compiled, and by the empty untrusted mirrors while the
  challenge compiles;
- a project file that changes how Rocq runs: closed by refusing every
  option other than `-w` and the kernel flags the config already sets;
- a project tree that reaches outside itself: closed by `lstat` enumeration
  with symbolic links refused, and by binding mirrors only;
- a large graph exhausting the wall clock late: closed by the caps and by
  one absolute deadline over the whole untrusted side.

The two design reviews disagreed on three points; the more conservative
choice was taken each time. Trusted `.vo` files live in their own directory
with their own sandboxed writer (not one mirror per binding shared by both
sides). Plan failures caused by the solver's files are exit 1 verdicts
(never exit 2 retries). The full `coqdeplib` was dropped for its lexer plus
the comparator's own resolution over the planned files, which also avoids
coqdep's symlink-following directory walk.

### Comparison with the Lean comparator

| Lean | Here | Verdict |
|---|---|---|
| Assumption 1: the challenge, its import closure and the lakefile are trusted | The challenge, its Require closure inside its project, and its project file; installed libraries as before | Equal for files and imports. Stronger for the project file: a lakefile is a build program Lean's comparator runs through lake, our project file is read by the comparator and may only bind directories and select warnings |
| Assumption 2: no adversarial file compiled earlier into the environment | Same, plus a fresh scratch per run and a frozen root state per library | Stronger: nothing on disk is reused between runs, and the solution's side is rebuilt from source every time |
| Assumptions 3 and 4: the sandbox holds | sandbox-exec, landrun or bwrap, one writable directory per phase, no network; `sandboxed: false` reported honestly | Weaker on process and IPC restrictions (Lean's landrun invocation is tighter and their README adds a systemd-run guard); comparable on file writes now that the trusted side is read-only during the untrusted phase |
| Assumption 5: the kernel is correct, reducible to "one of the kernels" with external kernels | The linked Rocq kernel, plus the rocqchk replay | Weaker: rocqchk is a separate implementation inside the Rocq project, not an independent kernel; see section 14 |
| Assumption 6: not root | Same | Equal |
| Never load oleans; export the solution and compare the export | Never load a solver-produced `.vo`; compile the solver's side in-process; trusted `.vo` files (installed and the trusted mirrors this run wrote) are unmarshalled | Equal or stronger on the untrusted side (no solver artefact is unmarshalled at all); weaker on the trusted side (Marshal is a larger surface than mmapped oleans, as section 2 notes) |
| Guarantee 1: same statement | Kernel-term comparison of the statement and its full closure, modulo universe renaming with constraint entailment | Stronger: the closure includes bodies, universes, typing flags and inductive layout |
| Guarantee 2: no more axioms than permitted | Assumptions by constructor, fully qualified; the imported policy over the libraries the challenge loaded; trusted helpers' axioms pinned; untrusted helpers' axioms never permitted | Equal to stronger: the same mechanism, plus the pinning of challenge-side assumptions |
| Guarantee 3: accepted by the kernel | Safe_typing in-process, joined environment, default typing flags re-asserted on every solver-side constant, rocqchk replay of every solver-side library | Equal on the builtin replay; weaker on independent replay |
| Definition holes need human review | Same | Equal |
| Re-check of kernel-magic constants (Quot, primitive Nat) | Primitives are compared as part of the closure when the statement reaches them; no dedicated re-pin | Weaker: no named check that the prelude's primitives are the installed ones beyond the load-path and shadowing rules |
