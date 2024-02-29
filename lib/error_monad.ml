open Why3

type error = Loc.position option * exn
type trace = error list

exception Trace of trace

let () =
  Exn_printer.register (fun ppf -> function
    | Failure s -> Format.pp_print_string ppf s
    | Trace errors ->
        let open Format in
        fprintf ppf "@[<v>%a@]"
          (pp_print_list
             ~pp_sep:(fun ppf () -> fprintf ppf ",@ ")
             (fun ppf -> function
               | Some loc, e ->
                   fprintf ppf "@[<2>File %a:@ %a@]" Loc.pp_position loc
                     Exn_printer.exn_printer e
               | None, e -> Exn_printer.exn_printer ppf e))
          errors
    | e -> raise e)

type 'a iresult = ('a, trace) Result.t

let return = Result.ok
let error (e : error) : 'a iresult = Result.error [ e ]

let error_with ?loc msg =
  Format.kasprintf (fun s -> error @@ (loc, Failure s)) msg

let error_of_fmt ?loc msg = Format.kasprintf (fun s -> (loc, Failure s)) msg

let trace ~(err : error) (m : 'a iresult) : 'a iresult =
  match m with Ok v -> return v | Error tr -> Error (err :: tr)

let error_unless (b : bool) ~(err : error) : unit iresult =
  if b then return () else error err

let ( >>= ) = Result.bind
let ( let* ) = Result.bind

let raise_error (m : 'a iresult) : 'a =
  match m with Ok v -> v | Error tr -> raise (Trace tr)

module StringMap = struct
  include Map.Make (String)

  let fold_e (f : key -> 'a -> 'b -> 'b iresult) (m : 'a t) (acc : 'b) :
      'b iresult =
    fold
      (fun k e acc ->
        let* acc = acc in
        f k e acc)
      m (return acc)
end

module Option = struct
  include Option

  let to_iresult (o : 'a option) ~(none : error) : 'a iresult =
    match o with Some v -> return v | None -> error none

  let map_e (f : 'a -> 'b iresult) (o : 'a option) : 'b option iresult =
    match o with
    | None -> return None
    | Some x ->
        let* x = f x in
        return @@ Some x
end

module List = struct
  include List

  let fold_left_e (f : 'a -> 'b -> 'a iresult) (acc : 'a) (l : 'b list) =
    fold_left
      (fun acc x ->
        let* acc = acc in
        f acc x)
      (return acc) l

  let map_e (f : 'a -> 'b iresult) (l : 'a list) : 'b list iresult =
    let* l =
      fold_left_e
        (fun tl x ->
          let* x = f x in
          return @@ (x :: tl))
        [] l
    in
    return @@ List.rev l

  let iter_e (f : 'a -> unit iresult) (l : 'a list) : unit iresult =
    fold_left_e (fun () x -> f x) () l

  let concat_map_e f l =
    let* xs = map_e f l in
    return @@ concat xs
end
