(** Sorts for the FOL theory used as the assertion language *)

type t =
  (* core data types *)
  | S_string
  | S_nat
  | S_int
  | S_bytes
  | S_bool
  | S_unit
  | S_list of t
  | S_pair of t * t
  | S_tuple of t list
  | S_option of t
  | S_or of t * t
  | S_set of t
  | S_map of t * t
  | S_big_map of t * t
  (* domain specific data types *)
  | S_lambda of t * t
  | S_timestamp
  | S_mutez
  | S_address
  | S_contract of t
  | S_operation
  | S_key
  | S_key_hash
  | S_signature
  | S_chain_id
  | S_any of string

(* Other Michelson types but not implemented yet *)
(* | S_never
 * | S_ticket of t
 * | S_bls12_381_g1
 * | S_bls12_381_g2
 * | S_bls12_381_fr
 * | S_sapling_transaction of int
 * | S_sapling_state of int *)

val compare : t -> t -> int

val pp_sort : Format.formatter -> t -> unit
(** Pretty printer *)

val string_of_sort : t -> string

val sort_of_pty : Why3.Ptree.pty -> t Error_monad.iresult
(** Parse a [Why3.Ptree.pty] value as a Michelson type and convert into a [Sort.t] value. *)

val pty_of_sort : t -> Why3.Ptree.pty
(** Convert [t] value into [Why3.Ptree.pty] value.  *)
