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
  | S_lambda of t * t
  (* domain specific data types *)
  | S_timestamp
  | S_mutez
  | S_address
  | S_contract
  | S_operation
  | S_key
  | S_key_hash
  | S_signature
  | S_chain_id

(* Other Michelson types but not implemented yet *)
(* | S_never
 * | S_ticket of t
 * | S_bls12_381_g1
 * | S_bls12_381_g2
 * | S_bls12_381_fr
 * | S_sapling_transaction of int
 * | S_sapling_state of int *)

let compare (t1 : t) (t2 : t) = compare t1 t2

let rec pp_sort fmt (ty : t) =
  let open Format in
  match ty with
  | S_string -> fprintf fmt "string"
  | S_nat -> fprintf fmt "nat"
  | S_int -> fprintf fmt "int"
  | S_bytes -> fprintf fmt "bytes"
  | S_bool -> fprintf fmt "bool"
  | S_unit -> fprintf fmt "unit"
  | S_list ty -> fprintf fmt "(@[list@ %a@])" pp_sort ty
  | S_pair (ty1, ty2) ->
      fprintf fmt "(@[pair@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_tuple tys ->
      fprintf fmt "(@[%a@])"
        (pp_print_list ~pp_sep:(fun fmt () -> pp_print_string fmt ",") pp_sort)
        tys
  | S_option ty -> fprintf fmt "(@[option@ %a@])" pp_sort ty
  | S_or (ty1, ty2) -> fprintf fmt "(@[or@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_set ty -> fprintf fmt "(@[set@ %a@])" pp_sort ty
  | S_map (ty1, ty2) -> fprintf fmt "(@[map@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_big_map (ty1, ty2) ->
      fprintf fmt "(@[big_map@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_lambda (ty1, ty2) ->
      fprintf fmt "(@[lambda@ %a@ %a@])" pp_sort ty1 pp_sort ty2
  | S_timestamp -> fprintf fmt "timestamp"
  | S_mutez -> fprintf fmt "mutez"
  | S_address -> fprintf fmt "address"
  | S_contract -> fprintf fmt "contract"
  | S_operation -> fprintf fmt "operation"
  | S_key -> fprintf fmt "key"
  | S_key_hash -> fprintf fmt "key_hash"
  | S_signature -> fprintf fmt "signature"
  | S_chain_id -> fprintf fmt "chain_id"

let string_of_sort (ty : t) : string =
  let open Format in
  asprintf "%a"
    (fun ppf ty ->
      (* ignore newlines and indents automatically inserted by pretty printing *)
      pp_set_formatter_out_functions ppf
        {
          (pp_get_formatter_out_functions ppf ()) with
          out_newline = ignore;
          out_indent = ignore;
        };
      pp_sort ppf ty)
    ty

open Error_monad
open Why3
open Ptree
open Ptree_helpers

let rec sort_of_pty (pty : pty) : t iresult =
  let elt1 l =
    match l with
    | [ pty ] -> sort_of_pty pty
    | _ -> error_with "expected 1 parameter"
  in
  let elt2 l =
    match l with
    | [ pty1; pty2 ] ->
        let* s1 = sort_of_pty pty1 in
        let* s2 = sort_of_pty pty2 in
        return (s1, s2)
    | _ -> error_with "expected 2 parameter"
  in
  match pty with
  | PTtyapp (Qident id, pl) -> (
      match id.id_str with
      | "string" -> return S_string
      | "nat" -> return S_nat
      | "int" -> return S_int
      | "bytes" -> return S_bytes
      | "bool" -> return S_bool
      | "unit" -> return S_unit
      | "timestamp" -> return S_timestamp
      | "mutez" -> return S_mutez
      | "address" -> return S_address
      | "key" -> return S_key
      | "key_hash" -> return S_key_hash
      | "signature" -> return S_signature
      | "chain_id" -> return S_chain_id
      | "operation" -> return S_operation
      | "list" ->
          let* s = elt1 pl in
          return @@ S_list s
      | "option" ->
          let* s = elt1 pl in
          return @@ S_option s
      | "or" ->
          let* s1, s2 = elt2 pl in
          return @@ S_or (s1, s2)
      | "set" ->
          let* s = elt1 pl in
          return @@ S_set s
      | "map" ->
          let* s1, s2 = elt2 pl in
          return @@ S_map (s1, s2)
      | "big_map" ->
          let* s1, s2 = elt2 pl in
          return @@ S_big_map (s1, s2)
      | "lambda" ->
          let* s1, s2 = elt2 pl in
          return @@ S_lambda (s1, s2)
      | "contract" -> return S_contract
      | s -> error_with "unknown sort %s" s)
  | PTtuple [] -> return @@ S_unit
  | PTtuple [ pty ] -> sort_of_pty pty
  | PTtuple ([ _; _ ] as pl) ->
      let* s1, s2 = elt2 pl in
      return @@ S_pair (s1, s2)
  | PTtuple ptys ->
      let* sl = List.map_e sort_of_pty ptys in
      return @@ S_tuple sl
  | PTparen pty -> sort_of_pty pty
  | _ -> error_with "unknown sort %a" Ptree_printer.pp_pty pty

let rec pty_of_sort (s : t) : Ptree.pty =
  let ty s = PTtyapp (qualid [ s ], []) in
  match s with
  | S_string -> ty "string"
  | S_nat -> ty "nat"
  | S_int -> ty "int"
  | S_bytes -> ty "bytes"
  | S_bool -> ty "bool"
  | S_unit -> ty "unit"
  | S_list s -> PTtyapp (qualid [ "list" ], [ pty_of_sort s ])
  | S_pair (s1, s2) -> PTtuple [ pty_of_sort s1; pty_of_sort s2 ]
  | S_tuple sl -> PTtuple (List.map pty_of_sort sl)
  | S_option s -> PTtyapp (qualid [ "option" ], [ pty_of_sort s ])
  | S_or (s1, s2) ->
      PTtyapp (qualid [ "or" ], [ pty_of_sort s1; pty_of_sort s2 ])
  | S_set s -> PTtyapp (qualid [ "set" ], [ pty_of_sort s ])
  | S_map (s1, s2) ->
      PTtyapp (qualid [ "map" ], [ pty_of_sort s1; pty_of_sort s2 ])
  | S_big_map (s1, s2) ->
      PTtyapp (qualid [ "map" ], [ pty_of_sort s1; pty_of_sort s2 ])
  | S_lambda (s1, s2) ->
      PTtyapp (qualid [ "lambda" ], [ pty_of_sort s1; pty_of_sort s2 ])
  | S_timestamp -> ty "timestamp"
  | S_mutez -> ty "mutez"
  | S_address -> ty "address"
  | S_contract -> ty "contract"
  | S_operation -> ty "operation"
  | S_key -> ty "key"
  | S_key_hash -> ty "key_hash"
  | S_signature -> ty "signature"
  | S_chain_id -> ty "chain_id"
