(** tzw program parser *)

module Regexp = Re
open Why3
open Ptree
open Error_monad

let is_id_type (pty : Ptree.pty) (id : ident) : bool =
  match pty with
  | PTtyapp (Qident { id_str; _ }, []) when id_str = id.id_str -> true
  | _ -> false

let is_step_type (pty : Ptree.pty) : bool = is_id_type pty Id.step_ty
let is_storage_type (pty : Ptree.pty) : bool = is_id_type pty Id.storage_ty

type entrypoint_params = {
  epp_step : param;
  epp_param : param list;
  epp_old_s : param;
  epp_new_s : param;
  epp_ops : param;
}

type entrypoint = {
  ep_loc : Loc.position;
  ep_name : ident;
  ep_params : entrypoint_params;
  ep_body : term;
}

type contract = {
  c_name : ident;
  c_entrypoints : entrypoint list;
  c_num_kont : int;
  c_pre : logic_decl;
  c_post : logic_decl;
  c_other_decls : decl list;
}

type t = {
  tzw_preambles : decl list;
  tzw_postambles : decl list;
  tzw_knowns : contract list;
  tzw_epp : Sort.t list StringMap.t StringMap.t;
  tzw_unknown_pre : logic_decl;
  tzw_unknown_post : logic_decl;
}

(** entrypoint params are "(st : step) (p1 : t1) ... (pn : tn) (s : store) (ops : list operation) (s' : store)", where "t1 ... tn" must be a michelson type. *)
let parse_entrypoint_params (params : param list) =
  let param_loc (l, _, _, _) = l in
  let param_pty (_, _, _, pty) = pty in
  let* st, params =
    match params with
    | x :: xs -> return (x, xs)
    | _ -> error_with "invalid format: parameters"
  in
  let* s, s', op, params =
    let rec aux params = function
      | [ s; op; s' ] -> return (s, s', op, List.rev params)
      | x :: (_ :: _ :: _ :: _ as xs) -> aux (x :: params) xs
      | _ -> error_with "invalid format: parameters"
    in
    aux [] params
  in
  let* () =
    error_unless
      (is_step_type @@ param_pty st)
      ~err:
        (error_of_fmt ~loc:(param_loc st)
           "invalid format: step type is expected")
  in
  let* () =
    error_unless
      (is_storage_type @@ param_pty s)
      ~err:
        (error_of_fmt ~loc:(param_loc s)
           "invalid format: storage type is expected")
  in
  let* () =
    error_unless
      (is_storage_type @@ param_pty s')
      ~err:
        (error_of_fmt ~loc:(param_loc s')
           "invalid format: storage type is expected")
  in
  let* op_ty =
    trace
      ~err:
        (error_of_fmt ~loc:(param_loc op)
           "invalid format: list operation type is expected")
    @@ Sort.sort_of_pty @@ param_pty op
  in
  let* () =
    error_unless
      (op_ty = Sort.(S_list S_operation))
      ~err:
        (error_of_fmt ~loc:(param_loc op)
           "invalid format: list operation type is expected")
  in
  let* () =
    List.fold_left_e
      (fun () p ->
        let* _ =
          trace
            ~err:
              (error_of_fmt ~loc:(param_loc p)
                 "invalid format: Michelson type is expected")
          @@ Sort.sort_of_pty @@ param_pty p
        in
        return ())
      () params
  in
  return
    {
      epp_step = st;
      epp_param = params;
      epp_old_s = s;
      epp_new_s = s';
      epp_ops = op;
    }

let parse_entrypoint_pred (ld : logic_decl) : entrypoint iresult =
  let ep_loc = ld.ld_loc in
  let ep_name = ld.ld_ident in
  let* ep_params = parse_entrypoint_params ld.ld_params in
  let* () =
    error_unless (ld.ld_type = None)
      ~err:(error_of_fmt ~loc:ep_loc "invalid format: predicate is expected")
  in
  let* ep_body =
    Option.to_iresult ld.ld_def
      ~none:(error_of_fmt ~loc:ep_loc "invalid format: spec body is missing")
  in
  return { ep_loc; ep_name; ep_params; ep_body }

let parse_entrypoint_scope (lds : decl list) =
  List.fold_left_e
    (fun tl d ->
      match d with
      | Dlogic [ ld ] ->
          let* ep = parse_entrypoint_pred ld in
          return @@ (ep :: tl)
      | _ -> error_with "invalid format: unexpected decl in Spec scope")
    [] lds

let check_storage_type_decl (td : type_decl) : type_decl iresult =
  let loc = td.td_loc in
  let* () =
    error_unless (td.td_params = [])
      ~err:(error_of_fmt ~loc "storage type cannot have type parameters")
  in
  let* () =
    error_unless (td.td_vis = Public) ~err:(error_of_fmt ~loc "public")
  in
  let* () =
    error_unless (td.td_mut = false) ~err:(error_of_fmt ~loc "immutable")
  in
  let* () =
    error_unless (td.td_inv = []) ~err:(error_of_fmt ~loc "pure record")
  in
  let* () =
    error_unless (td.td_wit = None) ~err:(error_of_fmt ~loc "pure record")
  in
  return td

let parse_upper_ops (e : expr) =
  let loc = e.expr_loc in
  match e.expr_desc with
  | Econst (ConstInt i) -> (
      try return @@ BigInt.to_int i.il_int
      with Failure _ ->
        error_with ~loc "upper bound length of operation lists is too large")
  | _ -> error_with ~loc "upper_ops_len shall be an integer constant"

let parse_contract loc id ds =
  let* _ostore, okont, oeps, opre, opost =
    List.fold_left_e
      (fun (ostore, okont, oeps, opre, opost) -> function
        (* TODO: storage can be defined with other types *)
        | Dtype [ td ] when td.td_ident.id_str = Id.storage_ty.id_str ->
            let* () =
              error_unless (ostore = None)
                ~err:
                  (error_of_fmt ~loc:td.td_loc
                     "multiple declaration of storage type")
            in
            let* store = check_storage_type_decl td in
            return (Some store, okont, oeps, opre, opost)
        | Dtype _tds -> return (ostore, okont, oeps, opre, opost)
        | Dlet (id, _, _, e) when id.id_str = Id.upper_ops.id_str ->
            let* () =
              error_unless (okont = None)
                ~err:
                  (error_of_fmt ~loc:id.id_loc
                     "multiple declaration of upper_ops")
            in
            let* kont = parse_upper_ops e in
            return (ostore, Some kont, oeps, opre, opost)
        | Dscope (loc, _, id, dls) when id.id_str = Id.spec_scope.id_str ->
            let* () =
              error_unless (oeps = None)
                ~err:(error_of_fmt ~loc "multiple declaration of Spec")
            in
            let* eps = parse_entrypoint_scope dls in
            return (ostore, okont, Some eps, opre, opost)
        | Dlogic [ ld ] when ld.ld_ident.id_str = Id.pre.id_str ->
            let* () =
              error_unless (opre = None)
                ~err:(error_of_fmt ~loc:ld.ld_loc "multiple declaration of pre")
            in
            return (ostore, okont, oeps, Some ld, opost)
        | Dlogic [ ld ] when ld.ld_ident.id_str = Id.post.id_str ->
            let* () =
              error_unless (opost = None)
                ~err:(error_of_fmt ~loc:ld.ld_loc "multiple declaration of pre")
            in
            return (ostore, okont, oeps, opre, Some ld)
        | Dlogic _ -> return (ostore, okont, oeps, opre, opost)
        | decl ->
            error_with ~loc "@[<2>unexpected declaration:@ %a@]"
              (Mlw_printer.pp_decl ~attr:true)
              decl)
      (None, None, None, None, None)
      ds
  in
  let* c_num_kont =
    Option.to_iresult okont ~none:(error_of_fmt ~loc "upper_ops is missing")
  in
  let* c_entrypoints =
    Option.to_iresult oeps ~none:(error_of_fmt ~loc "Spec is missing")
  in
  let* c_pre =
    Option.to_iresult opre ~none:(error_of_fmt ~loc "pre is missing")
  in
  let* c_post =
    Option.to_iresult opost ~none:(error_of_fmt ~loc "post is missing")
  in
  let c_other_decls =
    List.filter
      (function
        | Dlet (id, _, _, _) when id.id_str = Id.upper_ops.id_str ->
            (* skip let upper_ops = _ *)
            false
        | Dlogic [ ld ] when ld.ld_ident.id_str = Id.pre.id_str ->
            (* skip predicate pre = _ *)
            false
        | Dlogic [ ld ] when ld.ld_ident.id_str = Id.post.id_str ->
            (* skip predicate post = _ *)
            false
        | Dscope (_loc, _, id, _dls) when id.id_str = Id.spec_scope.id_str ->
            (* skip Spec *)
            false
        | _ -> true)
      ds
  in
  return
    { c_name = id; c_entrypoints; c_num_kont; c_pre; c_post; c_other_decls }

let parse_unknown (loc : Loc.position) (ds : decl list) =
  let parse_entrypoint_type (ds : decl list) =
    List.fold_left_e
      (fun m -> function
        | Dlogic [ ld ] ->
            let* s =
              List.map_e
                (fun (loc, _, _, pty) ->
                  trace ~err:(error_of_fmt ~loc "Michelson type is expected")
                  @@ Sort.sort_of_pty pty)
                ld.ld_params
            in
            return @@ StringMap.add ld.ld_ident.id_str s m
        | _ ->
            error_with ~loc "invalid format: predicate declaration is expected")
      StringMap.empty ds
  in
  let* oep, opre, opost =
    List.fold_left_e
      (fun (oep, opre, opost) -> function
        | Dscope (loc, _, id, ds) when id.id_str = "Entrypoint" ->
            let* () =
              error_unless (oep = None)
                ~err:(error_of_fmt ~loc "multiple declaration of Entrypoint")
            in
            let* ep = parse_entrypoint_type ds in
            return (Some ep, opre, opost)
        | Dlogic [ ld ] when ld.ld_ident.id_str = Id.pre.id_str ->
            let* () =
              error_unless (opre = None)
                ~err:(error_of_fmt ~loc:ld.ld_loc "multiple declaration of pre")
            in
            return (oep, Some ld, opost)
        | Dlogic [ ld ] when ld.ld_ident.id_str = Id.post.id_str ->
            let* () =
              error_unless (opost = None)
                ~err:(error_of_fmt ~loc:ld.ld_loc "multiple declaration of pre")
            in
            return (oep, opre, Some ld)
        | _ -> error_with "invalid format: unexpected declaration")
      (None, None, None) ds
  in
  let ep = Option.value oep ~default:StringMap.empty in
  let* pre =
    Option.to_iresult opre ~none:(error_of_fmt ~loc "pre is missing")
  in
  let* post =
    Option.to_iresult opost ~none:(error_of_fmt ~loc "post is missing")
  in
  return @@ (ep, pre, post)

let parse_mlw (mlw : mlw_file) =
  let* scopes =
    match mlw with
    | Decls ds ->
        List.fold_left_e
          (fun m -> function
            | Dscope (loc, _, id, ds) ->
                if StringMap.exists (fun k _ -> k = id.id_str) m then
                  error_with ~loc "%s has been declared" id.id_str
                else return @@ StringMap.add id.id_str (loc, id, ds) m
            | _ -> error_with "invalid format: top level must consist of scopes")
          StringMap.empty ds
    | _ -> error_with "invalid format: top level must consist of scopes"
  in
  let preambles =
    match StringMap.find_opt Id.preambles_scope.id_str scopes with
    | None -> []
    | Some (_, _, ds) -> ds
  in
  let scopes = StringMap.remove Id.preambles_scope.id_str scopes in
  let postambles =
    match StringMap.find_opt Id.postambles_scope.id_str scopes with
    | None -> []
    | Some (_, _, ds) -> ds
  in
  let scopes = StringMap.remove Id.postambles_scope.id_str scopes in
  let* loc, _id, ds =
    StringMap.find_opt "Unknown" scopes
    |> Option.to_iresult ~none:(error_of_fmt "Unknown scope must be declared")
  in
  let* ep, pre, post = parse_unknown loc ds in
  let scopes = StringMap.remove "Unknown" scopes in
  let* cs, epp =
    StringMap.fold_e
      (fun name (loc, id, ds) (cs, eps) ->
        let* c = parse_contract loc id ds in
        let* epp =
          List.fold_left_e
            (fun m ep ->
              let* s =
                List.map_e
                  (fun (_, _, _, pty) -> Sort.sort_of_pty pty)
                  ep.ep_params.epp_param
              in
              return @@ StringMap.add ep.ep_name.id_str s m)
            StringMap.empty c.c_entrypoints
        in
        return @@ (c :: cs, StringMap.add name epp eps))
      scopes
      ([], StringMap.singleton "Unknown" ep)
  in
  return
    {
      tzw_preambles = preambles;
      tzw_postambles = postambles;
      tzw_knowns = cs;
      tzw_epp = epp;
      tzw_unknown_pre = pre;
      tzw_unknown_post = post;
    }
