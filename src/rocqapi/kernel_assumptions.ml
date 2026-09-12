(* Thin wrapper around Rocq's [Assumptions] module.

   It lives in its own (unwrapped) dune library because the main library
   defines a module called [Assumptions] too, which would shadow Rocq's
   inside the wrapped library. *)

let collect (gr : Names.GlobRef.t) :
  ([ `Axiom | `Variable | `Positive | `Guarded | `Type_in_type | `Uip ] * string) list =
  let env = Global.env () in
  let ts = Conv_oracle.get_transp_state (Environ.oracle env) in
  let acc = (Library.indirect_accessor [@alert "-deprecated"]) in
  let m = Assumptions.assumptions acc ts ~add_opaque:false ~add_transparent:false [ gr ] in
  Printer.ContextObjectMap.fold
    (fun obj _ty acc ->
       match obj with
       | Printer.Variable id -> (`Variable, Names.Id.to_string id) :: acc
       | Printer.Axiom (Printer.Constant c, _) -> (`Axiom, Names.Constant.to_string c) :: acc
       | Printer.Axiom (Printer.Positive m, _) -> (`Positive, Names.MutInd.to_string m) :: acc
       | Printer.Axiom (Printer.Guarded g, _) ->
         (`Guarded, Names.GlobRef.print g |> Pp.string_of_ppcmds) :: acc
       | Printer.Axiom (Printer.TypeInType g, _) ->
         (`Type_in_type, Names.GlobRef.print g |> Pp.string_of_ppcmds) :: acc
       | Printer.Axiom (Printer.UIP m, _) -> (`Uip, Names.MutInd.to_string m) :: acc
       | Printer.Opaque c -> (`Axiom, Names.Constant.to_string c) :: acc
       | Printer.Transparent _ -> acc)
    m []
