type error = Why3.Loc.position option * exn
type 'a iresult = ('a, error list) result

val return : 'a -> ('a, 'b) result
val error : error -> 'a iresult

val error_with :
  ?loc:Why3.Loc.position ->
  ('a, Format.formatter, unit, 'b iresult) format4 ->
  'a

val error_of_fmt :
  ?loc:Why3.Loc.position -> ('a, Format.formatter, unit, error) format4 -> 'a

val trace : err:error -> 'a iresult -> 'a iresult
val error_unless : bool -> err:error -> unit iresult
val ( >>= ) : ('a, 'b) result -> ('a -> ('c, 'b) result) -> ('c, 'b) result
val ( let* ) : ('a, 'b) result -> ('a -> ('c, 'b) result) -> ('c, 'b) result
val raise_error : 'a iresult -> 'a

module StringMap : sig
  include Map.S with type key = string

  val fold_e : (key -> 'a -> 'b -> 'b iresult) -> 'a t -> 'b -> 'b iresult
end

module Option : sig
  include module type of struct
    include Option
  end

  val to_iresult : 'a option -> none:error -> 'a iresult
  val map_e : ('a -> 'b iresult) -> 'a option -> 'b option iresult
end

module List : sig
  include module type of struct
    include List
  end

  val fold_left_e :
    ('a -> 'b -> 'a iresult) -> 'a -> 'b list -> ('a, error list) result

  val map_e : ('a -> 'b iresult) -> 'a list -> 'b list iresult
  val iter_e : ('a -> unit iresult) -> 'a list -> unit iresult
  val concat_map_e : ('a -> 'b list iresult) -> 'a list -> 'b list iresult
end
