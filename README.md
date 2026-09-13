# rocq-comparator

A trustworthy judge for Rocq proofs, modelled on
[leanprover/comparator](https://github.com/leanprover/comparator): one OCaml
executable linked in-process against `rocq-runtime` 9.2 (no `coqc` on the
trusted path) that decides whether an adversarial **solution** `.v` proves the
same theorems as a trusted **challenge** `.v`, using no more axioms than a
permitted list, with the proof accepted by the Rocq kernel.

**Guarantee.** If `check` exits `0`, then for every name in `theorem_names`
the solution's theorem: (1) has the same statement as the challenge (the same
type, and the same definitions behind it, up to renaming of internal universe
levels); (2) uses no axiom you did not permit, no section variable, no rewrite
rule, and no disabled kernel check; (3) is accepted by the Rocq kernel.
Guarantee (3) means the proof term type-checks, no part of it was left
deferred or unchecked, and by default the whole library is re-checked by
`rocqchk`, Rocq's separate checker.

This rests on the same assumptions as Lean's comparator: the load path and
challenge are trusted, no adversarial file was compiled earlier into them, the
sandbox holds, the Rocq kernel is correct, and you do not run as root. See
`DESIGN.md` for the threat model and pipeline.

**Status.** This is a prototype. It was produced by Claude Fable 5.1
(Anthropic) under the direction of the project authors, and is inspired by the
[Lean comparator](https://github.com/leanprover/comparator). Expect rough
edges, and read `DESIGN.md` before relying on it for anything that matters.

## Install

Project-local opam switch (`./_opam`, OCaml 5.5.1, rocq-core 9.2):

```sh
opam switch create . ocaml-base-compiler.5.5.1
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-core rocq-stdlib dune yojson cmdliner memprof-limits alcotest
opam exec --switch=$PWD -- dune build
opam exec --switch=$PWD -- dune test   # unit tests + test/fixtures/*
```

## Quickstart

`config.json` (paths relative to the file's directory):

```json
{ "challenge": "Challenge.v", "solution": "Solution.v",
  "theorem_names": ["add_n_0"], "top": "Challenge" }
```

```sh
rocq-comparator check config.json            # one JSON verdict on stdout
rocq-comparator check config.json --pretty
rocq-comparator validate config.json         # dry-run: challenge only, no solution
rocq-comparator batch config.json S1.v S2.v [-j N]   # one verdict line per solution
rocq-comparator sandbox-info                 # which sandbox would run, and why
rocq-comparator version
```

Every flag has a config-file equivalent; flags win when both are given. `check`
/ `batch` / `validate` also accept `--challenge`, `--solution`, `--theorem`,
`--definition`, `--axiom`, `-Q/-R/-I`, `--coqproject`, `--top`, `--timeout`,
`--sandbox`, `--no-rocqchk` (and `batch` takes `-j`). Verdict (manifest and
`timing_s` abbreviated):

```json
{ "ok": true, "reason": null, "detail": null,
  "sandboxed": true, "sandbox": "sandbox-exec", "rocq_version": "9.2",
  "targets": [ { "name": "add_n_0", "status": "proved",
                 "assumptions": [], "detail": null } ],
  "checks": { "filter": "ok", "challenge_compile": "ok", "solution_compile": "ok",
              "joined": "ok", "statements": "ok", "closure": "ok", "axioms": "ok",
              "hygiene": "ok", "libraries": "ok", "rocqchk": "ok" },
  "manifest": { "ocaml_version": "5.5.1", "comparator_version": "0.1.0",
                "trusted_roots": ["/home/you/proj/_opam/lib/coq/user-contrib"],
                "libraries": [ {"name":"Corelib.Init.Logic",
                                "path":"/home/you/proj/_opam/lib/coq/theories/Init/Logic.vo",
                                "digest":"9f86d081884c7d65"} ] },
  "timing_s": { "init": 0.02, "challenge": 0.11, "solution": 0.10, "compare": 0.02, "rocqchk": 0.13 } }
```

To score a benchmark, use the top-level `"ok"` field, not the exit code alone.
Exit 1 and exit 2 both mean `ok: false`, but only 2 means nothing was judged
and the attempt should be retried rather than scored as a failed proof.

## Configuration

| field | default | meaning |
|---|---|---|
| `challenge` / `solution` | `Challenge.v` / `Solution.v` | the two `.v` files |
| `theorem_names` / `definition_names` | `[]` / `[]` | targets; together must be non-empty |
| `permitted_axioms` | `[]` | fully-qualified axiom names or `Prefix.*` wildcards; see below |
| `axiom_policy` | `"imported"` | `imported`: also allow axioms from libraries the challenge imports. `listed`: only `permitted_axioms` |
| `loadpath` | `[]` | `{"Q":[dir,log]}` / `{"R":[dir,log]}` / `{"I":[dir]}`, like `-Q`/`-R`/`-I` |
| `coqproject` | `null` | merge `-Q`/`-R`/`-I` from a `_CoqProject` |
| `top` | derived | logical library name both files compile under (`coqdep`-style, else basename) |
| `timeout_s` | `600` | wall-clock budget (per-sentence `Control.timeout` + outer kill at `+30`) |
| `sandbox` | `"auto"` | `auto`, `none`, `sandbox-exec`, `landrun`, `bwrap`, or `{"command":["prog","arg"]}` |
| `rocqchk` | `true` | replay the compiled library through `rocqchk` |
| `vm` | `true` | bytecode VM for `vm_compute`; `false` passes `-bytecode-compiler no`. `native_compute` is always off |
| `impredicative_set` / `indices_matter` | `false` | init flags, re-checked on every solution constant |
| `noinit` | `false` | compile with `-noinit` (no prelude); rarely wanted |
| `permitted_plugins` | `[]` | plugins to re-allow past the deny set (only `extraction` is denied) |
| `permitted_libraries` | `[]` | if non-empty, dirpath prefixes the solution may `Require` |
| `permit_challenge_axioms` | `true` | axioms/`Admitted` helpers in the challenge are auto-permitted, pinned to their challenge-side type (solution may assume or prove them); `false` requires listing them |

## Verdict

- `ok`: the field to score on.
- `reason` (when `ok` is `false`): `statement_mismatch`, `dependency_mismatch`,
  `not_proved`, `target_not_found`, `kind_mismatch`, `forbidden_axiom`,
  `unsafe_flags`, `forbidden_command`, `compile_error`, `challenge_error`,
  `timeout`, `rocqchk_failed`, `library_violation`, `config_error`,
  `sandbox_error`, `internal_error`.
- `sandboxed` / `sandbox`: whether a real OS sandbox ran, and which. `"none"`
  with `sandboxed: false` means no sandbox.
- `targets`: per requested name, a `status` (`proved`, `not_proved`,
  `missing`, `mismatch`, or `unchecked`), the permitted axioms it used, and a
  `detail`. On a `mismatch` the detail shows both statements, and their kernel
  forms when the two print the same.
- `checks`: fixed ordered stages `filter`, `challenge_compile`,
  `solution_compile`, `joined`, `statements`, `closure`, `axioms`, `hygiene`,
  `libraries`, `rocqchk`; each `"ok"`, `"skipped"`, or `{"fail": "<message>"}`.
  Stages after the first failure are `"skipped"`.
- `manifest`: reproducibility snapshot: OCaml/comparator versions, trusted
  roots, and every loaded `.vo` with its digest.
- `timing_s`: wall-clock seconds per stage.

**Exit codes:** `0` accepted, `1` rejected (a real verdict), `2` infrastructure
error (nothing judged). `batch` exits `0` if every solution produced a verdict,
`2` otherwise; read each line's `ok`. `validate` exits `0`/`2`.

## Permitted axioms

By default (`axiom_policy: "imported"`) the solution may use any axiom that
comes from a library the challenge imports. A challenge that opens `Require
Import Reals` or `From mathcomp Require Import classical_sets` accepts that
library's axioms (functional extensionality, choice, the classical Reals
axioms, and so on) with nothing to list. What is still rejected is an axiom the
solution declares itself, or one from a library the challenge did not import.
This is read from the challenge's own imports at run time, so there is no list
to keep in sync with the libraries.

For a strict challenge, for example a constructive one, set `axiom_policy:
"listed"`. Then the solution may use only the axioms in `permitted_axioms`.
Each entry is a fully qualified kernel name (what `Print Assumptions` reports,
for example `Stdlib.Logic.Classical_Prop.classic`) or a prefix wildcard
(`Some.Dir.Path.*`). `permitted_axioms` is additive under both policies. To see
which axioms a proof uses, run `rocq-comparator validate` or `Print
Assumptions` and copy the names. There are no presets and no built-in list.

## Sandboxing

`check`/`batch`/`validate` run inside an OS sandbox as defence in depth.
`auto` picks `sandbox-exec` on macOS or the first of `landrun`/`bwrap` on
Linux, falling back to `none` reported honestly as `sandboxed: false` plus a
stderr warning, never silently. The sandbox denies network and all writes
except the per-run scratch directory; reads stay open (trusted `.vo` files must
be readable). A solution that spins in an allocation-heavy loop is interrupted
in-process by a `memprof-limits` token tripped at the deadline (allocation
points, which `Control.timeout`'s checkpoints may never reach), with the outer
wall-clock kill as a final backstop. There is no memory-size limit on macOS
(`sandbox-exec` has no such primitive).

## How it works

1. Rocq is initialised once, then the root state is frozen.
2. The frozen root is unfrozen and the **challenge** runs under a lenient
   filter; a plain-OCaml spec (target statements + dependency closure) is
   extracted from its environment.
3. The root is unfrozen again and the **solution** runs under a strict filter
   (a default-deny match over every `Vernacexpr` constructor; the plugin deny
   set is just `extraction`, tactics are left to the kernel).
4. The two environments are compared at the kernel level: statements and
   closures as `Constr.t`, assumptions via `Assumptions.assumptions` classified
   by constructor, environment hygiene, and optionally a `rocqchk` replay.

## Limitations

- **Statement equality is syntactic** (modulo universe renaming only): terms
  equal after unfolding a notation still count as a mismatch. Write the target
  type the way solutions must match it.
- **Definition holes can be gamed** semantically, because only the type is
  compared. Use theorem targets where meaning matters, and second-review hole
  results.
- **Sections**: `Admitted` in a `Section` discharges all section variables,
  `Qed` only the used ones, so types can genuinely differ. Prefer toplevel
  statements or an explicit `Proof using` in both files.
- **HB / mathcomp names**: an extra Hierarchy-Builder declaration can renumber
  later instance names and break a closure comparison over a challenge-local
  HB instance.
- **`batch` recompiles the challenge per solution** (one sandboxed process
  each); it is more convenient than repeated `check`, not faster per solution.
- `ROCQ_COMPARATOR_UNSAFE_NO_FILTER` is a test-only escape hatch: it runs the
  solution through the lenient filter and marks `checks.filter` as failed so
  such a verdict can never be mistaken for a normal one. Never set it in
  production.

A client-side (WebAssembly) web front-end lives in the sibling project
`rocq-comparator-web`. See `DESIGN.md` and `CONTRACTS.md` for internals.
