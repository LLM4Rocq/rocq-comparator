# Project examples

Two copies of the same small project, laid out like the Lean comparator's
Navier-Stokes repository: a `Defs.v` both sides share, a `Challenge.v` whose
theorems are `Admitted`, and a `Solution.v` that proves them with the help of
its own library `theories/Lib.v`.

- `coqproject/` describes the project with a `_CoqProject` (`-R . Nse`).
- `dune/` describes it with a `dune-project` and a `dune` file holding a
  `coq.theory` stanza plus `(include_subdirs qualified)`.

The comparator discovers the project from the file paths, so the config
files name only the two `.v` files and the targets. Nothing is built ahead of
time: the comparator never runs `dune` or `make`, it compiles the files it
needs itself.

From the repository root, with the switch built:

```sh
opam exec --switch=$PWD -- dune build
./_build/default/bin/main.exe check examples/projects/coqproject/config.json
./_build/default/bin/main.exe check examples/projects/dune/config.json
```

Both print a verdict with `"ok": true`, `"rocqchk": "ok"`, and a manifest that
lists `Nse.Defs` as `trusted` (the challenge's closure, compiled in the
trusted phase) and `Nse.theories.Lib` as `checked` (the solution's closure,
compiled under the strict filter and replayed by `rocqchk`).

`validate` works the same way and needs no solution:

```sh
./_build/default/bin/main.exe validate examples/projects/coqproject/config.json --pretty
```
