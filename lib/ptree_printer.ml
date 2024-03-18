open Why3

type 'a t = Format.formatter -> 'a -> unit

let pp_expr = (Mlw_printer.pp_expr ~attr:true).closed
let pp_term = (Mlw_printer.pp_term ~attr:true).closed
let pp_pty = (Mlw_printer.pp_pty ~attr:true).closed
let pp_decl = Mlw_printer.pp_decl ~attr:true
