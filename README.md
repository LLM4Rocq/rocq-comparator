# rocq-comparator

A trustworthy judge for Rocq proofs, modelled on
[leanprover/comparator](https://github.com/leanprover/comparator): a single
OCaml executable linked against `rocq-runtime` 9.2 that decides whether a
possibly adversarial **solution** file proves the same theorems as a trusted
**challenge** file, using no more axioms than permitted, with the proof
accepted by the Rocq kernel.

The comparison happens at the kernel level — both files are compiled
in-process from source under the same logical library name, statements are
compared as `Constr.t` trees together with their dependency closure, and
assumptions are classified by constructor rather than by parsing the output of
`Print Assumptions`. See `DESIGN.md` for the guarantee and the threat model,
and `CONTRACTS.md` for the module interfaces.

## Build

```sh
opam exec --switch=$PWD -- dune build
opam exec --switch=$PWD -- dune build @runtest
```

## Use

```sh
# with a configuration file
rocq-comparator check config.json [--pretty]

# or entirely from flags
rocq-comparator check --challenge Challenge.v --solution Solution.v \
    --theorem foo --theorem bar \
    --axiom Stdlib.Logic.Classical_Prop.classic \
    -Q theories Comp --timeout 600 --sandbox auto

# one JSON verdict per line, one solution per line
rocq-comparator batch config.json Sol1.v Sol2.v Sol3.v [-j 4]

rocq-comparator sandbox-info      # which sandbox would be used, and why
rocq-comparator version
```

Flags override the configuration file when both are given. Exit code: **0**
accepted, **1** rejected, **2** infrastructure error (bad config, the
challenge does not compile, the sandbox failed). A run that produces no
parseable verdict is never accepted.

```json
{
  "challenge": "Challenge.v",
  "solution": "Solution.v",
  "theorem_names": ["foo"],
  "definition_names": [],
  "permitted_axioms": ["Stdlib.Logic.Classical_Prop.classic",
                       "Stdlib.Reals.Raxioms.*"],
  "loadpath": [{"Q": ["theories", "Comp"]}],
  "top": "Challenge",
  "timeout_s": 600,
  "sandbox": "auto",
  "rocqchk": true
}
```

## How a run is structured

The process runs twice. The **outer** process resolves the configuration,
picks an OS sandbox (`sandbox-exec` on macOS, `landrun`/`bwrap` on Linux),
writes the fully resolved configuration into a scratch directory and re-execs
itself inside the sandbox with `ROCQ_COMPARATOR_INNER=1`. It owns the
wall-clock timeout and kills the whole process group when it expires. The
**inner** process initialises Rocq once, compiles the challenge, extracts the
specification, compiles the solution from the same frozen root state, runs
every check, and prints one JSON verdict on stdout.

## Layout

```
bin/main.ml                  the CLI, the outer/inner split
src/config.ml   src/verdict.ml     configuration and the JSON verdict
src/driver.ml                in-process compilation of one .v file
src/filter.ml                the vernacular AST filter (default deny)
src/spec.ml     src/compare.ml     specification extraction and comparison
src/assumptions.ml           the axiom policy
src/envcheck.ml              environment hygiene after the solution compiles
src/rocqchk.ml               the optional rocqchk replay
src/sandbox.ml               sandbox selection and child-process execution
src/check.ml                 the inner pipeline
src/rocqapi/                 a thin unwrapped wrapper around Rocq's Assumptions
test/run_fixtures.ml         runs the binary over test/fixtures/*
test/unit/  test/infra/      alcotest unit tests
```
