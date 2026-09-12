# rocq-comparator

A trustworthy judge for Rocq proofs, modelled on
[leanprover/comparator](https://github.com/leanprover/comparator): a single
OCaml executable, linked in-process against `rocq-runtime` 9.2 (no `rocqc`
subprocess on the trusted path), that decides whether a possibly adversarial
**solution** `.v` file proves the same theorems as a trusted **challenge**
`.v` file, using no more axioms than a permitted list, with the proof
accepted by the Rocq kernel. It is meant to be the scoring function for an
autoformalization benchmark or an RL environment: fast (no `coqc` spawn per
attempt), and hard to game (see the guarantee below).

See `DESIGN.md` for the full threat model and pipeline, and `CONTRACTS.md`
for the module interfaces.

## The guarantee, and its assumptions

If `rocq-comparator check config.json` exits `0`, then for every name in
`theorem_names` the solution's constant:

1. **proves the same statement** as the challenge's: its type is identical
   to the challenge's type (structurally, modulo a bijective renaming of
   library-local universe levels, with universe constraints on those levels
   no stronger than the challenge's), and every constant / inductive that
   the statement transitively depends on is identical in both environments
   (kind, type, body, universes, typing flags);
2. **uses no more axioms than `permitted_axioms`**: the transitive closure
   of its proof term contains no `Undef` constant outside the permitted
   list, no section variable, no `Symbol` (rewrite rule), and no constant or
   inductive declared with a kernel check bypassed (guard, positivity,
   universes, definitional UIP);
3. **is accepted by the Rocq kernel**: the proof term was type-checked by
   `Safe_typing` in this process, with default typing flags, the
   environment is joined (no delayed opaque proof), and — optionally, on by
   default — the library was re-checked by `rocqchk`, Rocq's independent
   checker.

`definition_names` (definition holes) get the weaker guarantee Lean's
comparator gives them: name, kind (must be a definition, not an assumption),
type and universes match, and the body obeys the axiom policy. As in Lean,
a definition-hole solution can be gamed semantically (see Limitations) and
should be reviewed by an additional verifier when the statement doesn't pin
down the definition's meaning on its own.

This rests on five assumptions, mirroring Lean's comparator:

1. The load path (every `.vo` the challenge or solution can `Require`) and
   the challenge file are controlled by you or trustworthy.
2. You have not previously compiled the solution (or any adversarial file)
   in a way that could have modified the challenge or the load path.
3. The sandbox (`sandbox-exec` on macOS, `landrun`/`bwrap` on Linux, or your
   own wrapper) works and the solution does not escape it.
4. The Rocq kernel of the linked `rocq-runtime` is correct.
5. You are not running as a privileged user.

## Install

A project-local opam switch, as `dune-project`/`rocq-comparator.opam`
declare:

```sh
opam switch create . ocaml-base-compiler.5.5.1
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-core rocq-stdlib dune yojson cmdliner memprof-limits alcotest
dune build
```

Run the test suite (unit tests plus the fixture suite over
`test/fixtures/*`) with:

```sh
dune build @runtest
```

## Usage

```sh
# with a configuration file
rocq-comparator check config.json [--pretty]

# or entirely from flags
rocq-comparator check --challenge Challenge.v --solution Solution.v \
    --theorem foo --theorem bar \
    --axiom Stdlib.Logic.Classical_Prop.classic \
    -Q theories Comp --timeout 600 --sandbox auto

# one JSON verdict per line, one solution per line (challenge recompiled
# once per solution; see Limitations)
rocq-comparator batch config.json Sol1.v Sol2.v Sol3.v [-j 4]

rocq-comparator sandbox-info      # which sandbox would be used, and why
rocq-comparator version
```

A configuration-file flag and its command-line equivalent both work; flags
override the file when both are given. `--pretty` pretty-prints the single
JSON verdict; without it, the verdict is one compact JSON line on stdout
(stderr is free-form: sandbox warnings, the `ROCQ_COMPARATOR_UNSAFE_NO_FILTER`
banner, and nothing else). `check` and `batch` share the same `-Q`/`-R`/`-I`,
`--theorem`, `--definition`, `--axiom`, `--coqproject`, `--top`, `--timeout`,
`--sandbox` and `--no-rocqchk` flags.

For a benchmark harness computing pass@k: a solution counts as **passing**
iff the verdict's top-level `"ok"` field is `true` — never infer pass/fail
from the exit code alone, since exit code `1` (rejected) and exit code `2`
(infrastructure error: bad config, the challenge itself does not compile,
the sandbox failed to start) both mean `"ok": false`, but only the latter
means nothing about the solution was actually judged and the attempt should
usually be retried or excluded rather than scored as a failed proof. In
`batch` mode the process itself exits `0` as long as *every* solution
produced some verdict (whatever it says) and `2` only if the run as a whole
could not judge one of them; read the per-line `"ok"` to score each
solution.

## Configuration

All paths are resolved relative to the configuration file's directory
(command-line-only paths are resolved relative to the current directory).
Every field, with its default (from `src/config.ml`):

```json
{
  "challenge": "Challenge.v",
  "solution": "Solution.v",
  "theorem_names": [],
  "definition_names": [],
  "permitted_axioms": [],
  "loadpath": [],
  "coqproject": null,
  "top": null,
  "timeout_s": 600,
  "sandbox": "auto",
  "rocqchk": true,
  "vm": true,
  "impredicative_set": false,
  "indices_matter": false,
  "noinit": false,
  "permitted_plugins": [],
  "permitted_libraries": [],
  "permit_challenge_axioms": true
}
```

- `challenge` / `solution`: the two `.v` files. `theorem_names` and/or
  `definition_names` must together be non-empty.
- `loadpath`: a list of `{"Q": [dir, logical]}` / `{"R": [dir, logical]}` /
  `{"I": [dir]}` entries, exactly like `rocq`'s `-Q`/`-R`/`-I`. `coqproject`
  additionally merges in the `-Q`/`-R`/`-I` lines of a `_CoqProject` file.
- `top`: the logical library name both files are compiled under; when
  omitted it is derived from the load path the way `coqdep` would (falling
  back to the challenge file's basename).
- `timeout_s`: wall-clock budget for the solution, enforced both per-sentence
  (`Control.timeout`, inner process) and for the sandboxed child as a whole
  (outer process, `timeout_s + 30`).
- `sandbox`: `"auto"` (pick the first available for the platform, falling
  back to `"none"` with `"sandboxed": false` in the verdict and a stderr
  warning — never silently), `"none"`, `"sandbox-exec"`, `"landrun"`,
  `"bwrap"`, or `{"command": ["...", "..."]}` for your own wrapper.
- `rocqchk`: replay the compiled library through `rocqchk` (see below).
- `vm`: the bytecode VM used to evaluate `vm_compute`/`native_compute`-free
  proofs; `false` passes `-bytecode-compiler no`. The native compiler itself
  is always off (`-native-compiler no`, checked again after init), regardless
  of this flag: `native_compute` would `dlopen` code the solution influenced.
- `impredicative_set` / `indices_matter`: passed to `rocq` at init and
  re-checked as safety flags on every solution-side constant (both files
  necessarily share them, since they are process-wide).
- `noinit`: compile with `-noinit` (no prelude); rarely wanted.
- `permitted_plugins`: extra `VernacExtend` plugin names allowed in the
  solution beyond the built-in allow-list (`ltac`, `ltac2`, `ssreflect`,
  `micromega`, `ring`, `firstorder`, ... — see `src/filter.ml`).
- `permitted_libraries`: if non-empty, dirpath prefixes the solution is
  allowed to `Require`, checked both on the parsed `Require` and post hoc
  against `Library.loaded_libraries ()`.
- `permit_challenge_axioms` (default `true`): every constant the *challenge*
  file itself leaves `Undef` — a `Parameter`/`Axiom`, or a helper lemma
  proved with `Admitted` other than the targets themselves — is
  automatically added to the permitted-axiom set and **pinned** to its
  challenge-side statement: the solution may either use it as an assumption
  as-is, or supply its own proof for it (the pinning means it cannot
  restate it with a different, weaker type and prove that instead). Set it
  to `false` to require every such helper to be listed explicitly in
  `permitted_axioms` (or proved) like any other axiom.

## Permitted axioms

`permitted_axioms` entries are one of:

- a fully qualified **kernel name**, e.g.
  `Stdlib.Logic.Classical_Prop.classic` — exactly what
  `Names.Constant.to_string` prints and what an axiom is matched against,
  never a short name or a notation;
- a **prefix wildcard**, `"Some.Dir.Path.*"` — matches any kernel name
  starting with `Some.Dir.Path.`;
- a **preset**, `"@name"` — expanded by `src/presets.ml` before the config
  is used; an unknown `@name` is a `config_error`, not a silently-empty
  list.

Presets currently defined (every name below was verified empirically
against this switch's rocq-core 9.2.0 / rocq-stdlib 9.1.0 with
`_opam/bin/rocq compile` and `Print Assumptions`, not taken from
documentation — see the comments in `src/presets.ml` for the exact probe and
why each *other* similarly-named lemma was deliberately left out because it
turned out to be a derived lemma rather than a real axiom):

- `@stdlib-classical`:
  `Stdlib.Logic.Classical_Prop.classic`,
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`,
  `Stdlib.Logic.PropExtensionality.propositional_extensionality`,
  `Stdlib.Logic.ProofIrrelevance.proof_irrelevance`,
  `Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq`,
  `Stdlib.Logic.ClassicalEpsilon.constructive_indefinite_description`,
  `Stdlib.Logic.Description.constructive_definite_description`,
  `Stdlib.Logic.ClassicalUniqueChoice.dependent_unique_choice`,
  `Stdlib.Logic.RelationalChoice.relational_choice`,
  `Stdlib.Sets.Ensembles.Extensionality_Ensembles`.
- `@stdlib-reals`: what `Print Assumptions` actually reports for typical
  `Reals` lemmas (`Rplus_comm`, `Rinv_l`, `archimed`, `completeness`,
  `Rlt_asym`, `sqrt_sqrt`, `exp_ln`) —
  `Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec`,
  `Stdlib.Reals.ClassicalDedekindReals.sig_not_dec`,
  `Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep`,
  `Stdlib.Logic.Classical_Prop.classic`. Notably **not**
  `Stdlib.Reals.Raxioms.*`: in Rocq 9.x, `R` is built from Dedekind cuts and
  `Raxioms.v` *proves* its axiom-looking statements from
  `ClassicalDedekindReals` plus `FunctionalExtensionality`; it declares no
  axiom of its own, so that wildcard (the design's original, wrong,
  example) would silently permit nothing.
- `@stdlib-all`: the union of the two above.

There is no `@mathcomp-classical` preset: `mathcomp-classical` /
`mathcomp-analysis` (the package that defines `boolp`'s axioms) is not
installed in this project's switch (`_opam/lib/coq/user-contrib/mathcomp`
has only `algebra`, `boot`, `finite_group`, `order`, `ssreflect`). Adding a
preset for axiom names that cannot be verified against the running switch
would violate the same "observed, not guessed" rule; add it, the same way,
the day that package is installed.

## Verdict

One JSON object on stdout; everything on stderr is free-form and not part
of the contract.

```json
{ "ok": false, "reason": "statement_mismatch",
  "detail": "foo: type differs at ...",
  "sandboxed": true, "sandbox": "sandbox-exec", "rocq_version": "9.2.0",
  "targets": [ { "name": "foo", "status": "mismatch",
                 "assumptions": ["Stdlib.Logic.Classical_Prop.classic"],
                 "detail": null } ],
  "checks": { "filter": "ok", "challenge_compile": "ok", "solution_compile": "ok",
              "joined": "ok", "statements": {"fail": "..."}, "closure": "ok",
              "axioms": "ok", "hygiene": "ok", "libraries": "ok", "rocqchk": "skipped" },
  "timing_s": { "init": 0.1, "challenge": 0.3, "solution": 1.2, "compare": 0.0,
                "rocqchk": 0.8 } }
```

- `ok`: `true` iff the solution is accepted. This is the field to score a
  solution on — see Usage above.
- `reason` (only when `ok` is `false`), one of: `statement_mismatch`,
  `dependency_mismatch`, `not_proved`, `target_not_found`, `kind_mismatch`,
  `forbidden_axiom`, `unsafe_flags`, `forbidden_command`, `compile_error`,
  `challenge_error`, `timeout`, `rocqchk_failed`, `library_violation`,
  `config_error`, `sandbox_error`, `internal_error`.
- `sandboxed` / `sandbox`: whether a real OS sandbox was used, and which
  one (`"none"` with `sandboxed: false` means the run had **no** sandbox —
  check this if you rely on the sandbox for defence in depth).
- `targets`: one entry per requested `theorem_names`/`definition_names`
  name, with its `status` (`proved` / `not_proved` / `missing` / `mismatch`
  / `kind_mismatch`), the fully qualified permitted axioms it actually used,
  and an optional human-readable `detail`.
- `checks`: the fixed, ordered list of pipeline stages — `filter`
  (`{"fail": "..."}` only when `ROCQ_COMPARATOR_UNSAFE_NO_FILTER` disabled
  it), `challenge_compile`, `solution_compile`, `joined`, `statements`,
  `closure`, `axioms`, `hygiene`, `libraries`, `rocqchk` — each `"ok"`,
  `"skipped"` (a later stage never ran, or `rocqchk` was unavailable/off),
  or `{"fail": "..."}`. A stage after the first failure is generally
  `"skipped"`, not run.
- `timing_s`: wall-clock seconds per pipeline stage, for profiling a
  harness's throughput.

Exit code: **0** accepted, **1** rejected (a real verdict on the proof
itself), **2** infrastructure error (bad config, the challenge does not
compile, the sandbox could not be started, an internal anomaly) — nothing
about the solution was actually judged.

## Sandboxing

`sandbox: "auto"` (the default) picks `sandbox-exec` on macOS or the first
of `landrun`/`bwrap` found on Linux; if none is available it falls back to
`"none"`, which is reported honestly as `"sandboxed": false` in the verdict
plus a warning on stderr — it is never silently treated as sandboxed.
`{"command": [...]}` runs your own wrapper, given the scratch directory and
the inner command appended.

The sandbox denies network access and file writes everywhere except the
per-run scratch directory (and, for `sandbox-exec`, the process temp
directory, needed for `.lia.cache`/`.nra.cache` and similar tactic caches);
reads are otherwise unrestricted, since `.vo` files under the trusted load
path must be readable. There is intentionally **no memory limit on macOS**
(`sandbox-exec` has no such primitive) — a solution that allocates without
ever hitting a `Control.timeout` checkpoint is stopped only by the outer
process's wall-clock kill of the whole process group, not by memory
pressure.

## How it works

1. Rocq is initialised once in this process (`Coqinit.init_ocaml` /
   `parse_arguments` / `init_runtime` / `init_document`), then the state is
   frozen (`Vernacstate.freeze_full_state`).
2. The frozen root is unfrozen, the **challenge** is parsed and run
   sentence-by-sentence under a *lenient* vernacular filter (only commands
   that would break the comparator itself, e.g. `Load`/`Chdir`, are
   rejected — the challenge is trusted), and a plain-OCaml **specification**
   (target statements plus their full dependency closure) is extracted from
   `Global.env ()`.
3. The root is unfrozen again and the **solution** is parsed and run under
   a *strict* filter — every `Vernacexpr` constructor is classified with a
   default-deny match, exhaustive by construction (`[@warning "+8"]`), so a
   new Rocq constructor breaks the build rather than silently passing
   through; a plugin allow-list gates `VernacExtend`.
4. The two environments are compared **at the kernel level**: statements
   and their closures as `Constr.t` trees (universes compared modulo a
   bijective renaming plus constraint entailment, never by pretty-printing);
   assumptions computed by `Assumptions.assumptions` — the function behind
   `Print Assumptions` — and classified by constructor, never by parsing
   text; environment hygiene (typing flags, joined state, no rewrite rules,
   loaded libraries under a trusted root); optionally, the compiled library
   is saved to the scratch directory and replayed through `rocqchk`, Rocq's
   independent checker, as a second, differently-implemented judge of the
   same `.vo`.
5. One JSON verdict is printed; the whole run happens inside an OS sandbox
   as defence in depth.

| | rocq-comparator | rocq-mcp's `rocq_verify` |
|---|---|---|
| comparison | kernel-level `Constr.t` equality + dependency closure | text of `Print Assumptions`, regex-parsed |
| isolation | in-process, same logical library name for both files | `Module M. ... End M.` text wrapping + name surgery |
| processes per solution | 1 (no `coqc` spawn) | 2 `coqc` subprocesses |
| axiom matching | fully qualified kernel name, by constructor | short name, string match |
| `#[bypass_check]` | rejected by the filter and, independently, by the typing-flag check | missed (rocq-mcp-evolve audit A130) |

And, since this project is explicitly modelled on it:

| | rocq-comparator | Lean's `leanprover/comparator` |
|---|---|---|
| loads | source only, never a `.vo` produced by an adversary | source only, never an `.olean` |
| statement equality | `Constr.t` modulo universe renaming | `Expr` modulo universe renaming |
| axiom classification | by `Printer.context_object` constructor | by Lean's axiom constructor |

## Limitations

- **Section-based challenges**: `Admitted` inside a `Section` discharges
  *all* section variables into the constant's type, while `Qed` discharges
  only the ones the proof actually used; a challenge and solution that
  otherwise match can end up with genuinely different closed types purely
  because of this asymmetry. Prefer toplevel statements, or an explicit
  `Proof using` clause in both files, over relying on section discharge to
  line up.
- **HB / mathcomp-generated names**: Hierarchy-Builder instance names are
  numbered per file (`HB_unnamed_mixin_12`, ...); if a target's statement
  depends on a challenge-local HB instance, an extra HB declaration in the
  solution before that point can renumber later instances and break the
  closure comparison even though nothing semantically changed.
- **Statement equality is syntactic**, modulo universe renaming only: two
  statements that are equal after `unfold`ing a `Notation` or an
  abbreviation but differ as raw terms are treated as a mismatch. Write the
  challenge's target type the way you want solutions to have to match it
  syntactically.
- **Definition holes can be gamed** semantically (the same caveat Lean's
  comparator documents): a solution can supply a definition whose *type*
  matches but whose *value* trivializes what the definition was meant to
  capture; only the type is compared, plus the same axiom policy as
  theorems. Use a theorem target (whose *statement* pins down the meaning)
  wherever the semantics matter, and treat definition-hole results as
  needing a second, semantic review.
- **`batch` recompiles the challenge per solution**: each solution gets its
  own sandboxed process and its own from-scratch challenge compile; sharing
  one compiled challenge across solutions (forking after the challenge
  compiles) is future work, so batch throughput is not better per-solution
  than repeated `check` calls, only more convenient.
- **`memprof-limits` is declared as a dependency but not yet used for
  interruption**: the solution's wall-clock budget is enforced only via
  `Control.timeout` at Rocq's own checkpoints (per sentence) plus the outer
  process's kill of the whole sandboxed process group at `timeout_s + 30`;
  an allocation-heavy loop that never reaches a `Control.timeout`
  checkpoint is stopped only by that outer kill, not by an allocation
  budget.
- **`ROCQ_COMPARATOR_UNSAFE_NO_FILTER`** is a test-only escape hatch (set to
  run the solution through the *lenient* filter instead of the strict one)
  used by the fixture suite to demonstrate that the kernel-level checks
  (typing flags, assumptions) reject things like `#[bypass_check(guard)]`
  and `Unset Guard Checking` on their own, independently of the AST filter.
  It must never be set in production; when it is set, the verdict's
  `checks.filter` is `{"fail": "DISABLED by ROCQ_COMPARATOR_UNSAFE_NO_FILTER"}`
  rather than `"ok"`, so a verdict produced with it can never be mistaken
  for a normal one, and `bin/main.ml` prints a stderr warning every time.

## Development

```sh
opam exec --switch=$PWD -- dune build
opam exec --switch=$PWD -- dune test --force   # unit tests + test/fixtures/*
```

To add a fixture: create `test/fixtures/<name>/` with `Challenge.v`,
`Solution.v` (both default to those names if omitted from `config.json`),
`config.json`, and `expected.json` (`{"exit_code": 0}`, or
`{"exit_code": 1, "reason": "...", "detail_contains": "..."}`; see
`test/run_fixtures.ml` for every recognised key, including `checks`,
`batch`/`oks` for a batch fixture, and the `expected_nofilter.json`
companion for a fixture that also runs once under
`ROCQ_COMPARATOR_UNSAFE_NO_FILTER`). Validate every `.v` file against the
switch's `rocq` directly first (`_opam/bin/rocq compile -top Challenge
Challenge.v`) in a scratch copy, and never commit the resulting `.vo`/`.glob`
files. `dune test --force` runs the built binary over every fixture
directory and diffs the verdict against `expected.json`.

See `DESIGN.md` for the full pipeline and threat model, and `CONTRACTS.md`
for the module-by-module interfaces used to build this in parallel.
