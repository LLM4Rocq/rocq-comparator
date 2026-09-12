(lang dune 3.8)
(name rocq-comparator)
(generate_opam_files true)
(source (github LLM4Rocq/rocq-comparator))
(license Apache-2.0)
(authors "LLM4Rocq")
(maintainers "guillaume.baudart@gmail.com")

(package
 (name rocq-comparator)
 (synopsis "A trustworthy judge for Rocq proofs")
 (description
  "Checks that a solution file proves the same statements as a trusted challenge file, using no more axioms than permitted, with the proof accepted by the Rocq kernel. Kernel-level comparison in-process (linked against rocq-runtime), modelled on leanprover/comparator.")
 (depends
  (ocaml (>= 5.3))
  dune
  (rocq-runtime (>= 9.2))
  rocq-core
  rocq-stdlib
  yojson
  cmdliner
  memprof-limits
  (alcotest :with-test)))
