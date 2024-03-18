open Why3
open Ptree

type 'a t = Format.formatter -> 'a -> unit

val pp_expr : expr t
val pp_term : term t
val pp_pty : pty t
val pp_decl : decl t
