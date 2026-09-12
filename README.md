# rocq-comparator

A trustworthy judge for Rocq proofs, modelled on
[leanprover/comparator](https://github.com/leanprover/comparator): one OCaml
executable linked in-process against `rocq-runtime` 9.2 (no `coqc` on the
trusted path) that decides whether an adversarial **solution** `.v` proves the
same theorems as a trusted **challenge** `.v`, using no more axioms than a
permitted list, with the proof accepted by the Rocq kernel.

**Guarantee.** If `check` exits `0`, then for every `theorem_names` entry the
solution's constant (1) has a type identical to the challenge's, with an
identical dependency closure (modulo universe renaming); (2) uses no axiom
outside `permitted_axioms`, no section variable, no rewrite rule, and no
kernel check bypassed; (3) was type-checked by `Safe_typing`, is joined, and —
by default — re-checked by `rocqchk`. `definition_names` (holes) get the
weaker Lean guarantee: kind/type/universes match and the body obeys the axiom
policy, but only the type is compared (a hole can be gamed semantically).

This rests on the same assumptions as Lean's comparator: the load path and
challenge are trusted, no adversarial file was compiled earlier into them, the
sandbox holds, the Rocq kernel is correct, and you do not run as root. See
`DESIGN.md` for the threat model and pipeline.

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
                "trusted_roots": ["..."], "libraries": [ {"name":"...","path":"...","digest":"..."} ] },
  "timing_s": { "init": 0.02, "challenge": 0.11, "solution": 0.10, "compare": 0.02, "rocqchk": 0.13 } }
```

To score a benchmark, use the top-level `"ok"` field — never the exit code
alone (exit 1 and exit 2 both mean `ok: false`, but only 2 means nothing was
judged and the attempt should be retried, not scored as a failed proof).

## Configuration

| field | default | meaning |
|---|---|---|
| `challenge` / `solution` | `Challenge.v` / `Solution.v` | the two `.v` files |
| `theorem_names` / `definition_names` | `[]` / `[]` | targets; together must be non-empty |
| `permitted_axioms` | `[]` | see below |
| `loadpath` | `[]` | `{"Q":[dir,log]}` / `{"R":[dir,log]}` / `{"I":[dir]}`, like `-Q`/`-R`/`-I` |
| `coqproject` | `null` | merge `-Q`/`-R`/`-I` from a `_CoqProject` |
| `top` | derived | logical library name both files compile under (`coqdep`-style, else basename) |
| `timeout_s` | `600` | wall-clock budget (per-sentence `Control.timeout` + outer kill at `+30`) |
| `sandbox` | `"auto"` | `auto` / `none` / `sandbox-exec` / `landrun` / `bwrap` / `{"command":[...]}` |
| `rocqchk` | `true` | replay the compiled library through `rocqchk` |
| `vm` | `true` | bytecode VM for `vm_compute`; `false` → `-bytecode-compiler no`. `native_compute` is always off |
| `impredicative_set` / `indices_matter` | `false` | init flags, re-checked on every solution constant |
| `noinit` | `false` | compile with `-noinit` (no prelude); rarely wanted |
| `permitted_plugins` | `[]` | plugins to re-allow past the deny set (only `extraction` is denied) |
| `permitted_libraries` | `[]` | if non-empty, dirpath prefixes the solution may `Require` |
| `permit_challenge_axioms` | `true` | axioms/`Admitted` helpers in the challenge are auto-permitted, pinned to their challenge-side type (solution may assume or prove them); `false` requires listing them |

## Verdict

- `ok` — the field to score on.
- `reason` (when `ok` is `false`): `statement_mismatch`, `dependency_mismatch`,
  `not_proved`, `target_not_found`, `kind_mismatch`, `forbidden_axiom`,
  `unsafe_flags`, `forbidden_command`, `compile_error`, `challenge_error`,
  `timeout`, `rocqchk_failed`, `library_violation`, `config_error`,
  `sandbox_error`, `internal_error`.
- `sandboxed` / `sandbox` — whether a real OS sandbox ran, and which; `"none"`
  + `sandboxed: false` means no sandbox.
- `targets` — per requested name: `status` (`proved` / `not_proved` /
  `missing` / `mismatch` / `unchecked`), the permitted axioms it used, a
  `detail`.
- `checks` — fixed ordered stages `filter`, `challenge_compile`,
  `solution_compile`, `joined`, `statements`, `closure`, `axioms`, `hygiene`,
  `libraries`, `rocqchk`; each `"ok"`, `"skipped"`, or `{"fail": "..."}`.
  Stages after the first failure are `"skipped"`.
- `manifest` — reproducibility snapshot: OCaml/comparator versions, trusted
  roots, and every loaded `.vo` with its digest.
- `timing_s` — wall-clock seconds per stage.

**Exit codes:** `0` accepted, `1` rejected (a real verdict), `2` infrastructure
error (nothing judged). `batch` exits `0` if every solution produced a verdict,
`2` otherwise; read each line's `ok`. `validate` exits `0`/`2`.

## Permitted axioms

Each `permitted_axioms` entry is a **fully qualified kernel name** (exactly
what `Names.Constant.to_string` prints, e.g.
`Stdlib.Logic.Classical_Prop.classic`) or a **prefix wildcard**
(`"Some.Dir.Path.*"`). There are **no presets and no built-in blessed list** —
the permitted set is stated per challenge. To discover the names a challenge or
reference proof needs, run `rocq-comparator validate` (its `challenge_axioms`
field) or `Print Assumptions`, and copy the qualified names verbatim.

## Sandboxing

`check`/`batch`/`validate` run inside an OS sandbox as defence in depth.
`auto` picks `sandbox-exec` on macOS or the first of `landrun`/`bwrap` on
Linux, falling back to `none` reported honestly as `sandboxed: false` plus a
stderr warning — never silently. The sandbox denies network and all writes
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
4. The two environments are compared at the kernel level — statements and
   closures as `Constr.t`, assumptions via `Assumptions.assumptions` classified
   by constructor, environment hygiene, and optionally a `rocqchk` replay.

## Limitations

- **Statement equality is syntactic** (modulo universe renaming only): terms
  equal after unfolding a notation still count as a mismatch. Write the target
  type the way solutions must match it.
- **Definition holes can be gamed** semantically — only the type is compared.
  Use theorem targets where meaning matters, and second-review hole results.
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
