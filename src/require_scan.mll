(* require_scan.mll: the Require statements of a .v file.
 *
 * The plan needs one thing from a source file: which libraries it Requires,
 * as written.  Rocq's own scanner for this lives in coqdeplib, which cannot
 * be linked here: that library's Args module registers the warning name
 * "unknown-option", which library/goptions.ml registers too, and Rocq raises
 * "Already used warning name" as soon as both initialisers run (reported
 * upstream).  Running `rocq dep` instead is not an option either: on an
 * ambiguous Require it picks one file, prints a warning and exits 0, so the
 * ambiguity the plan must reject would have to be recovered from prose.
 *
 * This scanner follows the lexical rules of the reference manual: comments
 * (* ... *) nest and may contain strings, a "..." string escapes a quote by
 * doubling it, and a sentence ends at a '.' followed by a blank or by the end
 * of the file (the '.' of a qualified name is always followed by an
 * identifier).  Every other token is skipped, so a Require written inside a
 * comment or a string is not one.
 *
 * Deliberately conservative: an unexpected token ends the module list.  A
 * missed Require cannot become a false accept, only a compile error, because
 * a file the plan does not know is never compiled and so is never on the load
 * path either. *)

{
  (* the modules of one Require, and the library it comes From, each as the
     dot-separated components the source wrote *)
  type t = { from : string list option; mods : string list list }
}

let blank = [' ' '\t' '\r' '\n']
let first = ['a'-'z' 'A'-'Z' '_' '\128'-'\255']
let next = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'' '\128'-'\255']
let ident = first next*

rule scan acc = parse
  | "(*"            { comment 1 lexbuf; scan acc lexbuf }
  | '"'             { str lexbuf; scan acc lexbuf }
  | "From" blank+   { let f =
                        match ident_or_empty lexbuf with
                        | None -> []
                        | Some i -> i :: qualid_rest lexbuf
                      in
                      if from_require lexbuf then
                        let m = mods [] lexbuf in
                        scan ({ from = Some f; mods = m } :: acc) lexbuf
                      else scan acc lexbuf }
  | "Require"       { let m = mods [] lexbuf in
                      scan ({ from = None; mods = m } :: acc) lexbuf }
  | ident           { scan acc lexbuf }
  | eof             { List.rev acc }
  | _               { scan acc lexbuf }

(* the first identifier of a qualified name, if the next token is one;
   blanks and comments may precede it *)
and ident_or_empty = parse
  | blank+          { ident_or_empty lexbuf }
  | "(*"            { comment 1 lexbuf; ident_or_empty lexbuf }
  | ident           { Some (Lexing.lexeme lexbuf) }
  | ""              { None }

(* the dotted tail of a qualified name: a '.' starts one only when an
   identifier follows, so the '.' that ends a sentence is left alone *)
and qualid_rest = parse
  | '.' (ident as i) { i :: qualid_rest lexbuf }
  | ""               { [] }

(* between "From <qualid>" and the modules: the keyword Require, or not *)
and from_require = parse
  | blank+          { from_require lexbuf }
  | "(*"            { comment 1 lexbuf; from_require lexbuf }
  | "Require"       { true }
  | ""              { false }

(* the modules of a Require, up to the end of the sentence.  Import and Export
   are skipped, as is an import filter (...) or -(...); anything else ends the
   list. *)
and mods acc = parse
  | blank+                   { mods acc lexbuf }
  | "(*"                     { comment 1 lexbuf; mods acc lexbuf }
  | "Import" | "Export"      { mods acc lexbuf }
  | '-'? '('                 { paren 1 lexbuf; mods acc lexbuf }
  | '.'                      { List.rev acc }
  | ident                    { (* bind the lexeme before qualid_rest moves the
                                  lexbuf: :: evaluates right to left *)
                               let i = Lexing.lexeme lexbuf in
                               let q = i :: qualid_rest lexbuf in
                               mods (q :: acc) lexbuf }
  | eof                      { List.rev acc }
  | _                        { List.rev acc }

and comment depth = parse
  | "(*"            { comment (depth + 1) lexbuf }
  | "*)"            { if depth > 1 then comment (depth - 1) lexbuf }
  | '"'             { str lexbuf; comment depth lexbuf }
  | eof             { () }
  | _               { comment depth lexbuf }

and str = parse
  | "\"\""          { str lexbuf }   (* a doubled quote, not the end *)
  | '"'             { () }
  | eof             { () }
  | _               { str lexbuf }

and paren depth = parse
  | '('             { paren (depth + 1) lexbuf }
  | ')'             { if depth > 1 then paren (depth - 1) lexbuf }
  | '"'             { str lexbuf; paren depth lexbuf }
  | eof             { () }
  | _               { paren depth lexbuf }

{
  (* the Require statements of [path], in source order *)
  let file (path : string) : (t list, string) result =
    match open_in_bin path with
    | exception Sys_error m -> Result.Error m
    | ic ->
      let r =
        try Result.Ok (scan [] (Lexing.from_channel ~with_positions:false ic))
        with e -> Result.Error (Printexc.to_string e)
      in
      close_in ic; r
}
