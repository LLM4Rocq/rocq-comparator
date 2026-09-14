# Module contracts (for parallel implementation)

All modules live in `src/` inside the dune library `rocq_comparator`
(wrapped: refer to siblings as `Verdict`, `Config`, ... — dune's default
wrapping makes them available under those names inside the library).
`Verdict` and `Config` already exist and are the source of truth for their
types; do not change their public types without updating every user.

Rocq's `clib` shadows a few Stdlib modules (`Option`, `List`, `String`,
`Int`, `Array` get extra functions, and `Option.value` does not exist —
use `Stdlib.Option.value` or Rocq's `Option.default`). When in doubt,
prefix with `Stdlib.`.

Build: `cd <checkout> && opam exec --switch=/Users/gbaudart/Project/llm4rocq/rocq-comparator -- dune build 2>&1`
(the local opam switch is at that absolute path; worktrees must reference it
by path). Rocq binaries for experiments:
`/Users/gbaudart/Project/llm4rocq/rocq-comparator/_opam/bin/{rocq,rocqchk}`.
Rocq 9.2 OCaml API: `/Users/gbaudart/Project/llm4rocq/rocq-comparator/_opam/lib/rocq-runtime/**/*.mli`
(and `.ml` for most modules). A working prototype of init / two-library
compile / statement compare / assumptions is at
`/private/tmp/claude-501/-Users-gbaudart-Project-llm4rocq-rocq-comparator/c11b0c08-a53c-40e0-9ad7-6586edde1e54/scratchpad/proto/bin/proto.ml`
— copy from it freely.

## Verdict (exists)

```ocaml
type reason = Statement_mismatch | Dependency_mismatch | Not_proved | Target_not_found
            | Kind_mismatch | Forbidden_axiom | Unsafe_flags | Forbidden_command | Compile_error
            | Challenge_error | Timeout | Rocqchk_failed | Library_violation | Config_error
            | Sandbox_error | Internal_error
type check_status = Ok | Fail of string | Skipped
type target_report = { name : string; status : string; assumptions : string list; target_detail : string option }
type library_entry = { lib_name; lib_path; lib_digest; lib_trust : string (* installed | trusted | checked *) }
type t = { ok : bool; reason : reason option; detail : string option; sandboxed : bool; sandbox : string;
           rocq_version : string; targets : target_report list; checks : (string * check_status) list;
           timing : (string * float) list; solution : string option }
val fail : ?checks -> ?targets -> ?timing -> reason -> string -> t
val pass : ?checks -> ?targets -> ?timing -> unit -> t
val to_json / of_json / to_string ?pretty / print ?pretty / exit_code / reason_to_string / reason_of_string
```

Check names used in `checks` (fixed strings, in this order):
`challenge_compile`, `solution_compile`, `joined`, `statements`, `closure`,
`axioms`, `hygiene`, `libraries`, `rocqchk`.

## Config (exists)

```ocaml
type loadpath_entry = Q of string * string | R of string * string | I of string
type sandbox_mode = Auto | No_sandbox | Sandbox_exec | Landrun | Bwrap | Custom of string list
type t = { challenge; solution; theorem_names; definition_names; permitted_axioms; loadpath;
           coqproject : string option; top : string option; timeout_s : float; sandbox : sandbox_mode;
           rocqchk : bool; vm : bool; impredicative_set : bool; indices_matter : bool; noinit : bool;
           permitted_plugins : string list; permitted_libraries : string list; config_dir : string }
val of_json_file : string -> (t, string) result
val of_json : config_dir:string -> Yojson.Safe.t -> (t, string) result
val to_json : t -> Yojson.Safe.t
val resolve_loadpath : t -> loadpath_entry list      (* absolute dirs; the project file is NOT merged *)
val loadpath_args : t -> string list                 (* -Q d l -R d l -I d ... *)
val rocq_args : t -> string list                     (* loadpath_args @ -native-compiler no [...] *)
val top_name : t -> string                           (* from loadpath, e.g. "Challenge" or "Comp.Problem"; Project.top_name refines it *)
val challenge_path / solution_path : t -> string     (* absolute *)
val is_under : root:string -> string -> bool
```

## Project and Plan (projects, DESIGN section 16)

```ocaml
(* Project: pure filesystem work, usable before Rocq is initialised *)
type binding = { dir : string; logical : string; implicit : bool; files : (string * string) list }
type t = { root : string; project_file : string; bindings : binding list; theories : string list }
type flags = { impredicative_set : bool; indices_matter : bool; noinit : bool }
val discover : flags:flags -> ?override:string -> string -> (t option, string) result
    (* nearest _CoqProject (preferred) or dune-project above the file; None when no binding covers it;
       override "" disables discovery *)
val find_file : t -> string -> (binding * string) option     (* the file's binding and logical name *)
val coqproject : flags:flags -> string -> (t, string) result  (* strict: -I, unknown -arg, native refused *)
val dune_project : flags:flags -> string -> (t, string) result
val top_name : Config.t -> string                            (* explicit top, else the project's name, else Config.top_name *)

(* Plan: the closure and the scratch layout; Plan.make before Driver.init, check_installed after *)
type entry = { path; logical : Names.DirPath.t; name : string; binding : int; rel : string list; from_challenge_project : bool }
type t = { bindings; challenge_project; solution_project; trusted : entry list; untrusted : entry list }
val make : ?with_solution:bool -> Config.t -> (t, Verdict.reason * string) result
val trusted_dir / untrusted_dir : string -> string           (* scratch/trusted, scratch/untrusted *)
val mkdirs : t -> scratch:string -> trusted:bool -> unit      (* every mirror dir, before init *)
val mirror_args : ?trusted_only:bool -> t -> scratch:string -> string list   (* -Q/-R of the mirrors *)
val mirror_dirs : t -> scratch:string -> string list
val vo_dir / vo_path : scratch:string -> trusted:bool -> entry -> string
val check_installed : t -> (unit, Verdict.reason * string) result   (* shadowing of switch namespaces, (theories) *)
```

`Rocqdep_lexer` is `tools/coqdep/lib/lexer.mll` of Rocq 9.2, vendored
because `rocq-runtime.coqdeplib` cannot be linked into a process that links
the Rocq library (a duplicate warning name at initialisation).

## Driver (CORE-A)

```ocaml
type sentence_error = { msg : string; line : int option; bp : int; ep : int; text : string }
type outcome =
  | Done of Vernacstate.t                       (* Global.env () is the library's final env *)
  | Error of sentence_error                     (* Rocq error while running a sentence *)
  | Parse_error of sentence_error
  | Timeout of string                           (* sentence text *)
  | Forbidden of string * sentence_error        (* Filter rejection: what, where *)
val init : args:string list -> unit               (* Coqinit sequence; idempotent; sets the root state *)
val rocq_version : unit -> string
val compile_library :
  ?filter:(Vernacexpr.vernac_control -> (unit, string) result) ->
  ?deadline:float ->                            (* Unix.gettimeofday () absolute; per-sentence Control.timeout on the remainder *)
  top:Names.DirPath.t -> file:string -> unit -> outcome
val with_state : Vernacstate.t -> (unit -> 'a) -> 'a   (* unfreeze st, run, restore previous *)
```

`compile_library` unfreezes the root, calls `Coqinit.start_library`, parses
with proof-mode tracking and runs each sentence through `filter` (before
execution) then `Vernacinterp.interp`. Feedback messages are swallowed
(collected into a buffer exposed as `val last_messages : unit -> string list`).
Anomalies and `Sys.Break` are re-raised (the caller maps them to
`Internal_error`).

## Filter (FILTER)

```ocaml
type mode = Strict | Lenient
type policy = { mode : mode; permitted_plugins : string list; permitted_libraries : string list }
val denied_plugins : string list  (* plugins denied in Strict mode; today just "extraction" *)
val check : policy -> Vernacexpr.vernac_control -> (unit, string) result
(* Error "Declare ML Module" / "Unset Guard Checking" / "plugin extraction" / ... — short, names the offending command *)
val classify_option : string list -> [ `Allow | `Deny ]     (* option name path, e.g. ["Guard"; "Checking"] *)
```

Total over every constructor of `vernac_control_gen`, `control_flag`,
`synterp_vernac_expr`, `synpure_vernac_expr` (compile with warning 8 as an
error for this module), attributes (`bypass_check`), options, and
`VernacExtend` by `ext_plugin` (normalise: the plugin string may look like
`rocq-runtime.plugins.ltac` or `coq-core.plugins.ltac` or just `ltac` — accept
the last dot-component). `Lenient` mode still denies what breaks the
comparator (see DESIGN §6).

## Spec (CORE-A)

```ocaml
type target = { name : string; kn : Names.Constant.t; hole : bool; typ : Constr.t; univs : Declarations.universes }
type const_entry = { c : Names.Constant.t; cb : Declarations.constant_body; body : Constr.t option }
type ind_entry = { m : Names.MutInd.t; mb : Declarations.mutual_inductive_body }
type t = { top : Names.DirPath.t; targets : target list;
           local_consts : const_entry list; local_inds : ind_entry list;
           external_consts : const_entry list; external_inds : ind_entry list;
           graph : UGraph.t; permitted_present : (Names.Constant.t * Constr.t) list }
val extract : ?trusted:Names.DirPath.t list -> top:Names.DirPath.t -> theorem_names:string list
           -> definition_names:string list -> permitted_axioms:string list
           -> permit_challenge_axioms:bool -> unit -> (t, Verdict.reason * string) result
   (* [trusted]: the trusted helpers' names; their Undef constants are challenge axioms too *)
val is_local : top:Names.DirPath.t -> Names.ModPath.t -> bool
```

Runs in the challenge state (after `compile_library` returned `Done`).

## Compare (CORE-A)

```ocaml
val check : Spec.t -> Environ.env -> (Verdict.target_report list, Verdict.reason * string) result
(* statement match (modulo universe renaming + constraint entailment), kinds, closure *)
val eq_constr_mod_univ : top:Names.DirPath.t -> ren:(Univ.Level.t * Univ.Level.t) list ref -> Constr.t -> Constr.t -> bool
```

Runs in the solution state. Target statuses: `"proved"` when kind ok and
statement matches (assumptions filled in later by `Assumptions`),
`"not_proved"` (Undef), `"missing"`, `"mismatch"`, `"kind_mismatch"`.

## Assumptions (CORE-B)

```ocaml
type item = Axiom of string | Variable of string | Positive of string | Guarded of string
          | Type_in_type of string | Uip of string
val of_constant : Names.Constant.t -> item list         (* Assumptions.assumptions [ConstRef c], fully qualified names *)
val permitted_matches : permitted:string list -> string -> bool   (* exact or "Prefix.*" *)
val check : permitted:string list -> (string * Names.Constant.t) list -> Verdict.target_report list
         -> (Verdict.target_report list, Verdict.reason * string * Verdict.target_report list) result
(* inputs: (target name, its Constant.t) for every target whose report status is "proved", and the reports so far;
   fills report.assumptions with the permitted axioms each target uses (sorted, fully qualified);
   first offending item → Error (Forbidden_axiom | Unsafe_flags, detail, reports-with-status-updated) *)
```

`Assumptions` must not depend on `Spec` (owned by another agent); it only
needs `Names`, `Verdict`.

## Envcheck (CORE-B)

```ocaml
val check : top:Names.DirPath.t -> trusted_roots:string list -> permitted_libraries:string list
         -> impredicative_set:bool -> indices_matter:bool
         -> (unit, Verdict.reason * string) result
(* rewrite rules off; no Symbol; safe typing flags on every local const/ind; joined; native off;
   every Library.loaded_libraries () located under a trusted root (Loadpath.locate_absolute_library or
   Library.library_full_filename); permitted_libraries prefixes if non-empty *)
val trusted_roots : Config.t -> string list   (* coqlib, coqlib/user-contrib, configured -Q/-R dirs; absolute *)
```

## Rocqchk (CORE-B)

```ocaml
val save_vo : top:Names.DirPath.t -> dir:string -> (string (* .vo path *), string) result
val run : rocqchk:string -> top:Names.DirPath.t -> norec:Names.DirPath.t list -> vo_dir:string
       -> loadpath_args:string list -> deadline:float -> (unit, string) result
       (* one -norec per untrusted helper and for top; exit code + stderr tail on failure *)
val find_rocqchk : unit -> string option               (* next to Sys.executable_name's switch bin, or PATH *)
```

## Sandbox (INFRA)

```ocaml
type kind = Sandbox_exec | Landrun | Bwrap | Custom of string list | No_sandbox
val detect : Config.sandbox_mode -> kind * string          (* chosen kind and a one-line reason *)
val name : kind -> string
val wrap : kind -> scratch:string -> argv:string list -> string list
    (* full argv incl. wrapper; [scratch] is the ONE writable directory (a phase's side of the scratch) *)
val inner_env : ?tmpdir:string -> unit -> string array   (* allow-listed env; TMPDIR replaced by [tmpdir] *)
type run_result = { exit_code : int; timed_out : bool; signaled : bool; stdout : string; stderr : string }
val run : ?env:string array -> timeout_s:float -> string list -> run_result
  (* spawns argv in its own process group, kills the group on timeout, captures both streams *)
val inner_marker : string        (* "ROCQ_COMPARATOR_INNER" *)
val is_inner : unit -> bool
```

`wrap` for `Sandbox_exec` builds a profile: deny default; allow process*,
sysctl-read, mach-lookup, file-read* everywhere; file-write* only under
`scratch` (the writable side) and `/dev/null`, `/dev/tty`; deny network*.
The system temp dir is not writable: the child's `TMPDIR` is the writable
side. For `Landrun`:
`landrun --best-effort --ro / --rw /dev --rwx <scratch> --ldd --add-exec -- argv`.
For `Bwrap`:
`bwrap --ro-bind / / --dev /dev --bind <scratch> <scratch> --unshare-net --die-with-parent -- argv`.
`Custom l` → `l @ [scratch] @ ["--"] @ argv`.

## Check (CORE-A)

The pipeline orchestrator. The modules owned by other agents are injected as
a record of functions so that CORE-A builds and tests on its own:

```ocaml
type hooks = {
  filter : strict:bool -> permitted_plugins:string list -> permitted_libraries:string list
           -> Vernacexpr.vernac_control -> (unit, string) result;
  assumptions : permitted:string list -> (string * Names.Constant.t) list -> Verdict.target_report list
                -> (Verdict.target_report list, Verdict.reason * string * Verdict.target_report list) result;
  envcheck : top:Names.DirPath.t -> trusted_roots:string list -> permitted_libraries:string list
             -> impredicative_set:bool -> indices_matter:bool -> (unit, Verdict.reason * string) result;
  trusted_roots : Config.t -> string list;
  rocqchk : (top:Names.DirPath.t -> norec:Names.DirPath.t list -> vo_dir:string
             -> loadpath_args:string list -> deadline:float
             -> (unit, string) result) option;     (* None = rocqchk unavailable → check "rocqchk" Skipped *)
  filter_status : Verdict.check_status;
}
val permissive_hooks : hooks    (* filter allows all, assumptions/envcheck pass, no rocqchk — local testing only *)
val run_inner : hooks -> Config.t -> scratch:string -> Verdict.t
(* the whole inner pipeline (DESIGN §3 steps 1–5, plus the project steps of section 16) with timing;
   never raises; sets rocq_version; sandboxed/sandbox fields are filled by the caller.
   [scratch] is the run's scratch ROOT: scratch/trusted holds what run_trusted wrote (read here),
   scratch/untrusted is this phase's writable side. Without a project the layout is not touched. *)
val run_trusted : hooks -> Config.t -> scratch:string -> Verdict.t
(* the trusted phase: compiles the challenge's project closure into scratch/trusted and records
   the .vo digests in scratch/trusted/libraries.json; ok = true means "go on" *)
val validate_inner : hooks -> Config.t -> scratch:string -> Verdict.validation
```

The browser front-end constructs the `hooks` record literally with
`rocqchk = None` and calls `run_inner`, so hook FIELDS must not be added;
changing the type inside the `rocqchk` option is safe.

`bin/main.ml` (integration) builds the real `hooks` from `Filter`,
`Assumptions`, `Envcheck`, `Rocqchk`.

## bin/main.ml (INTEGRATION, later)

Subcommands `check`, `batch`, `sandbox-info`; outer/inner re-exec; JSONL
batch with a forked child per solution.

## Implementation notes (integration)

The interfaces above were implemented as specified, with three deliberate
deviations, all additive:

1. **`src/rocqapi/` (library `rocq_comparator_rocqapi`, module
   `Kernel_assumptions`).** Our `Assumptions` module would shadow Rocq's
   `Assumptions` inside the wrapped `rocq_comparator` library (dune opens the
   alias module in every unit), so the one call to
   `Assumptions.assumptions` lives in a tiny separate unwrapped library.
   `Assumptions.of_constant` has exactly the contracted signature.

2. **`Compare.check_targets`** — `Spec.t -> Environ.env -> target_report list
   * (reason * string) option` — is the function the pipeline actually uses,
   so that per-target statuses are reported even when the comparison fails.
   `Compare.check` is defined in terms of it and keeps the contracted type.

3. **Targets are excluded from the closure comparison.** A target constant
   reachable from another target's statement must not have its *body*
   compared (the whole point is that the solution supplies a different proof),
   and a definition hole must not have its *kind* compared (`Undef` in the
   challenge, `Def` in the solution). Both are checked as targets instead,
   which is what DESIGN section 5 asks for.

`bin/main.ml` honours `ROCQ_COMPARATOR_UNSAFE_NO_FILTER=1` as a **test-only** escape
hatch: the solution is then run through the lenient filter, so the fixture
suite can show that the kernel-level checks reject `#[bypass_check(guard)]`
and `Unset Guard Checking` on their own (`unsafe_flags`) even when the AST
filter is out of the way. It prints a warning on stderr and must never be set
in production.
