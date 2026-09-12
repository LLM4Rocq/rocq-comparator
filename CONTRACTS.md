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
val resolve_loadpath : t -> loadpath_entry list      (* absolute dirs, _CoqProject merged *)
val loadpath_args : t -> string list                 (* -Q d l -R d l -I d ... *)
val rocq_args : t -> string list                     (* loadpath_args @ -native-compiler no [...] *)
val top_name : t -> string                           (* e.g. "Challenge" or "Comp.Problem" *)
val challenge_path / solution_path : t -> string     (* absolute *)
val is_under : root:string -> string -> bool
```

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
val default_plugins : string list
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
val extract : top:Names.DirPath.t -> theorem_names:string list -> definition_names:string list
           -> permitted_axioms:string list -> (t, Verdict.reason * string) result
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
val run : rocqchk:string -> top:Names.DirPath.t -> vo_dir:string -> loadpath_args:string list
       -> deadline:float -> (unit, string) result       (* exit code + stderr tail on failure *)
val find_rocqchk : unit -> string option               (* next to Sys.executable_name's switch bin, or PATH *)
```

## Sandbox (INFRA)

```ocaml
type kind = Sandbox_exec | Landrun | Bwrap | Custom of string list | No_sandbox
val detect : Config.sandbox_mode -> kind * string          (* chosen kind and a one-line reason *)
val name : kind -> string
val wrap : kind -> scratch:string -> argv:string list -> string list   (* full argv incl. wrapper *)
type run_result = { exit_code : int; timed_out : bool; signaled : bool; stdout : string; stderr : string }
val run : ?env:string array -> timeout_s:float -> string list -> run_result
  (* spawns argv in its own process group, kills the group on timeout, captures both streams *)
val inner_marker : string        (* "ROCQ_COMPARATOR_INNER" *)
val is_inner : unit -> bool
```

`wrap` for `Sandbox_exec` builds a profile: deny default; allow process*,
sysctl-read, mach-lookup, file-read* everywhere; file-write* only under
`scratch`, `/dev/null`, `/dev/tty`?, and the process's temp dir
(`Filename.get_temp_dir_name ()`); deny network*. For `Landrun`:
`landrun --best-effort --ro / --rw /dev --rwx <scratch> --ldd --add-exec -- argv`
(check `landrun --help` spelling). For `Bwrap`:
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
  rocqchk : (top:Names.DirPath.t -> scratch:string -> loadpath_args:string list -> deadline:float
             -> (unit, string) result) option;     (* None = rocqchk unavailable → check "rocqchk" Skipped *)
}
val permissive_hooks : hooks    (* filter allows all, assumptions/envcheck pass, no rocqchk — local testing only *)
val run_inner : hooks -> Config.t -> scratch:string -> Verdict.t
(* the whole inner pipeline (DESIGN §3 steps 1–5) with timing; never raises; sets rocq_version;
   sandboxed/sandbox fields are filled by the caller *)
```

`bin/main.ml` (integration) builds the real `hooks` from `Filter`,
`Assumptions`, `Envcheck`, `Rocqchk`.

## bin/main.ml (INTEGRATION, later)

Subcommands `check`, `batch`, `sandbox-info`; outer/inner re-exec; JSONL
batch with a forked child per solution.
