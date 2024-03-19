module Regexp = Re
open Why3
open Ptree
open Ptree_helpers
open Error_monad
module StringSet = Set.Make (String)

let fresh_id =
  let count = ref 0 in
  fun ?(x = "x") () ->
    incr count;
    ident @@ Format.sprintf "%s%d" x !count

type contract = {
  cn_name : string;
  (* cn_param_ty : Sort.t; *)
  (* cn_store_ty : Sort.t; *)
  cn_num_kont : int;
      (* cn_index : int; *)
      (* cn_spec : logic_decl; *)
      (* cn_pre : logic_decl; *)
      (* cn_post : logic_decl; *)
}

type desc = {
  d_contracts : contract list;
  (* d_inv_pre : logic_decl; *)
  (* d_inv_post : logic_decl; *)
  d_whyml : decl list;
}

(* id definitions
   Magical words should be defined here. *)

let ctx_ty_ident = ident "ctx"
let ctx_wf_ident = ident "ctx_wf"
let step_ty_ident = ident "step"
let step_wf_ident = ident "step_wf"
let spec_ident = ident "spec"
let addr_ident = ident "addr"
let param_wf_ident = ident "param_wf"
let storage_ty_ident = ident "storage"
let storage_wf_ident = ident "is_storage_wf"
let gparam_ty_ident = ident "gparam"
let operation_ty_ident = ident "operation"
let operation_wf_ident = ident "is_operation_wf"
let entrypoint_ty_ident = ident "entrypoint"
let contract_ty_ident = ident "contract"
let contract_wf_ident = ident "is_contract_wf"
let gas_ident = ident "g"
let terminate_ident = ident "Terminate"
let insufficient_mutez_ident = ident "Insufficient_mutez"
let unknown_ident = ident "unknown"
let _unknown_param_ctr_ident = ident "Punknown"
let xfer_cstr_ident = ident "Xfer"
let sdel_cstr_ident = ident "Sdel"

let qid_of (c : contract) (id : ident) =
  qualid [ String.capitalize_ascii c.cn_name; id.id_str ]

let _id_contract_of (c : contract) : ident = ident c.cn_name
let id_func_of (c : contract) : ident = ident @@ c.cn_name ^ "_func"
let id_pre_of (c : contract) : ident = ident @@ c.cn_name ^ "_pre"
let id_post_of (c : contract) : ident = ident @@ c.cn_name ^ "_post"
let id_balance_of (c : contract) : ident = ident @@ c.cn_name ^ "_balance"
let id_store_of (c : contract) : ident = ident @@ c.cn_name ^ "_storage"

let id_is_param_of (c : contract) : ident =
  ident @@ "is_" ^ c.cn_name ^ "_param"

let _constr_of_sort (s : Sort.t) : string =
  let re = Regexp.(compile @@ alt [ char ' '; char '('; char ')' ]) in
  Sort.string_of_sort s |> String.capitalize_ascii
  |> Regexp.replace re ~f:(fun g ->
         match Regexp.Group.get g 0 with
         | " " -> "_"
         | "(" -> "'0"
         | ")" -> "'1"
         | _ -> assert false)
  |> Format.sprintf "P%s"

let qid (id : ident) : qualid = Qident id

let _binder_id (x : binder) : ident =
  match x with _, Some x, _, _ -> x | _ -> assert false

let _param_id (x : param) : ident =
  match x with _, Some x, _, _ -> x | _ -> assert false

let _mk_internal_id s = s
let mk_binder ?pty id : binder = (Loc.dummy_position, Some id, false, pty)
let mk_param x pty = (Loc.dummy_position, Some (ident x), false, pty)

let mk_post t : post =
  (Loc.dummy_position, [ (pat @@ Pvar (ident "result"), t) ])

let mk_xpost id : xpost = (Loc.dummy_position, [ (qid id, None) ])

module T = struct
  let mk_not (t : term) : term = term @@ Tnot t

  let _mk_imply (t1 : term) (t2 : term) : term =
    term @@ Tbinnop (t1, Dterm.DTimplies, t2)

  let mk_and (t1 : term) (t2 : term) : term =
    term @@ Tbinnop (t1, Dterm.DTand, t2)

  let mk_applys f ts = List.fold_left (fun a b -> term @@ Tapply (a, b)) f ts

  (** convert expression to term *)
  let rec of_expr (e : expr) : term =
    let term_desc =
      match e.expr_desc with
      | Etrue -> Ttrue
      | Efalse -> Tfalse
      | Econst c -> Tconst c
      | Eident qid -> Tident qid
      | Eidapp (f, l) -> Tidapp (f, List.map of_expr l)
      | Einnfix (e1, o, e2) -> Tinnfix (of_expr e1, o, of_expr e2)
      | Etuple el -> Ttuple (List.map of_expr el)
      | Ematch (e, cls, []) ->
          Tcase (of_expr e, List.map (fun (p, e) -> (p, of_expr e)) cls)
      | Eapply
          ( {
              expr_desc = Efun ([ (_, Some id, _, _) ], None, _ (*p?*), _, _, e);
              _;
            },
            e' ) ->
          Tlet (id, of_expr e', of_expr e)
      | Eand (e1, e2) ->
          (* Hack: && => /\ *)
          Tbinnop (of_expr e1, Dterm.DTand, of_expr e2)
      | Eapply (e1, e2) -> Tapply (of_expr e1, of_expr e2)
      | _ ->
          Format.eprintf "T.of_expr: unsupported: %a@." Ptree_printer.pp_expr e;
          assert false
    in
    { term_desc; term_loc = e.expr_loc }
end

module E = struct
  let mk_var (x : ident) : expr = evar @@ qid x

  let var_of_binder (x : binder) : expr =
    match x with _, Some x, _, _ -> mk_var x | _ -> assert false

  let var_of_param (x : param) : expr =
    match x with _, Some x, _, _ -> mk_var x | _ -> assert false

  let mk_let (x : ident) (e1 : expr) (e2 : expr) : expr =
    expr @@ Elet (x, false, RKnone, e1, e2)

  let mk_seq (e1 : expr) (e2 : expr) : expr = expr @@ Esequence (e1, e2)
  let mk_if (e1 : expr) (e2 : expr) (e3 : expr) : expr = expr @@ Eif (e1, e2, e3)

  let mk_any ?ensure (pty : pty) : expr =
    let sp_post =
      match ensure with
      | None -> []
      | Some t ->
          [ (Loc.dummy_position, [ (pat @@ Pvar (ident "result"), t) ]) ]
    in
    expr
    @@ Eany
         ( [],
           RKnone,
           Some pty,
           pat Pwild,
           Ity.MaskVisible,
           { empty_spec with sp_post } )

  let mk_bin (e1 : expr) (o : string) (e2 : expr) : expr =
    expr @@ Einnfix (e1, ident @@ Ident.op_infix o, e2)

  let _mk_tuple (el : expr list) : expr = expr @@ Etuple el
  let mk_record (el : (qualid * expr) list) : expr = expr @@ Erecord el

  let _mk_proj (e : expr) (m : int) (n : int) : expr =
    assert (m > 0 && m > n);
    let p =
      pat
      @@ Ptuple
           (List.init m (fun i ->
                if i = n then pat @@ Pvar (ident "x") else pat Pwild))
    in
    expr @@ Ematch (e, [ (p, mk_var @@ ident "x") ], [])

  let _mk_update (e1 : expr) (m : int) (n : int) (e2 : expr) : expr =
    assert (m > 0 && m > n);
    let p =
      pat
      @@ Ptuple
           (List.init m (fun i ->
                pat @@ Pvar (ident @@ Format.sprintf "_x%d" i)))
    in
    let e =
      expr
      @@ Etuple
           (List.init m (fun i ->
                if i = n then e2 else mk_var (ident @@ Format.sprintf "_x%d" i)))
    in
    expr @@ Ematch (e1, [ (p, e) ], [])

  let mk_assume (t : term) : expr = expr @@ Eassert (Expr.Assume, t)
  let mk_raise (x : ident) : expr = expr @@ Eraise (qid x, None)
  let mk_idapp id es = expr @@ Eidapp (qid id, es)
end

module Step_constant = struct
  let mk ~source ~sender ~self ~entrypoint ~amount ~level ~now : expr =
    E.mk_record
      [
        (qualid [ "source" ], source);
        (qualid [ "sender" ], sender);
        (qualid [ "self" ], self);
        (qualid [ "entrypoint" ], entrypoint);
        (qualid [ "amount" ], amount);
        (qualid [ "level" ], level);
        (qualid [ "now" ], now);
      ]

  let source st : expr = eapp (qualid [ "source" ]) [ st ]
  let sender st : expr = eapp (qualid [ "sender" ]) [ st ]
  let self st : expr = eapp (qualid [ "self" ]) [ st ]
  let amount st : expr = eapp (qualid [ "amount" ]) [ st ]
  let level st : expr = eapp (qualid [ "level" ]) [ st ]
  let now st : expr = eapp (qualid [ "now" ]) [ st ]
  let entrypoint st : expr = eapp (qualid [ "entrypoint" ]) [ st ]
end

module Is_type_wf = struct
  let pred_name = Printf.sprintf "is_%s_wf"

  (* Build a term for the well-foundness of [pty], [is_<type>_wf is_'a_wf ..].

     We need to pre-define [is__tupleX_wf], since [term] cannot have lambdas
     and therefore we cannot write [fun (x, y) -> is_x_wf x /\ is_y_wf y].
     "__" of [is__tupleX_wf] is intentional to avoid name clashes.
  *)
  let rec gen_expr (pty : pty) : term =
    let fun_id id = ident @@ pred_name id.id_str in
    let fun_qualid = function
      | Qident id -> Qident (fun_id id)
      | Qdot (qualid, id) -> Qdot (qualid, fun_id id)
    in
    match pty with
    | PTtyvar id -> tvar @@ qualid [ pred_name ("'" ^ id.id_str) ]
    | PTtyapp (qualid, []) -> tvar @@ fun_qualid qualid
    | PTtyapp (qualid, ptys) ->
        let ptys = List.map gen_expr ptys in
        T.mk_applys (tvar @@ fun_qualid qualid) ptys
    | PTtuple [] -> tvar @@ qualid [ "is_unit_wf" ]
    | PTtuple [ pty ] -> gen_expr pty
    | PTtuple ptys ->
        let ptys = List.map gen_expr ptys in
        let fun_tuple =
          (* __ is intentional to avoid name crashes *)
          qualid [ Printf.sprintf "is__tuple%d_wf" (List.length ptys) ]
        in
        T.mk_applys (tvar fun_tuple) ptys
    | PTparen pty -> gen_expr pty
    | _ ->
        failwith
          (Format.asprintf "is_type_wf: Unsupported type %a"
             Ptree_printer.pp_pty pty)

  (* [is_type_wf e] *)
  let gen_apply pty e =
    let f = gen_expr pty in
    T.mk_applys f [ T.of_expr e ]

  (* Auto-generate [let is_<typename>_wf = ...] *)
  let gen_decl (type_decl : type_decl) : logic_decl iresult =
    let loc = type_decl.td_loc in
    let name = pred_name type_decl.td_ident.id_str in
    let decl_id = ident name in
    let v_id = ident "_v" in
    let* body =
      match type_decl.td_def with
      | TDalias pty -> return @@ gen_apply pty @@ evar @@ qid v_id
      | TDrecord flds ->
          (* predicate is_type_wf _s =
             is_type1_wf _s.field1 /\
             is_type2_wf _s.field2 ...
          *)
          List.fold_left_e
            (fun t f ->
              let p =
                gen_apply f.f_pty @@ E.mk_idapp f.f_ident [ evar @@ qid v_id ]
              in
              return @@ T.mk_and p t)
            (Ptree_helpers.term Ttrue) flds
      | TDalgebraic cs ->
          (* predicate is_type_wf _s =
             match _s with
             | C1 (a1, a2, ..) ->
             is_type1_wf a1 /\ is_type2_wf a2 ..
             | ..
             end
          *)
          let* cases =
            List.map_e
              (fun (_loc, c, params) ->
                let param_ids =
                  List.mapi (fun i _ -> ident @@ Printf.sprintf "_a%d" i) params
                in
                let pats = List.map (fun i -> pat @@ Pvar i) param_ids in
                let param_tys = List.map (fun (_, _, _, pty) -> pty) params in
                let p = pat @@ Papp (qid c, pats) in
                let* ts =
                  List.map_e (fun (i, pty) ->
                      let term = gen_apply pty (evar (qid i)) in
                      return term)
                  @@ List.combine param_ids param_tys
                in
                let t = List.fold_left T.mk_and (term Ttrue) ts in
                return (p, t))
              cs
          in
          return @@ term @@ Tcase (term @@ Tident (qid v_id), cases)
      | _ ->
          error_with ~loc "Unsupported %a@." Ptree_printer.pp_decl
            (Dtype [ type_decl ])
    in
    let v_param : param =
      ( Loc.dummy_position,
        Some v_id,
        false,
        PTtyapp
          ( Qident type_decl.td_ident,
            List.map (fun id -> PTtyvar id) type_decl.td_params ) )
    in
    let t_params : param list =
      List.map
        (fun td_param ->
          ( Loc.dummy_position,
            Some (ident (pred_name ("'" ^ td_param.id_str))),
            false,
            PTarrow (PTtyvar td_param, PTtyapp (qualid [ "bool" ], [])) ))
        type_decl.td_params
    in
    return
      {
        ld_loc = Loc.dummy_position;
        ld_ident = decl_id;
        ld_params = t_params @ [ v_param ];
        ld_type = None;
        ld_def = Some body;
      }

  (* let [is_<typename>_wf] = ... *)
  let gen_decls (type_decls : type_decl list) : decl list iresult =
    (* One of type names need to be with attribute [@gen_wf].
       The attribute must be removed since mlw printing has some issue around it *)
    let type_decls, generate =
      let rev_tds, gen =
        List.fold_left
          (fun (rev_tds, gen) td ->
            let gens, others =
              List.partition
                (function
                  | ATstr atr when atr.attr_string = "gen_wf" -> true
                  | _ -> false)
                td.td_ident.id_ats
            in
            ( { td with td_ident = { td.td_ident with id_ats = others } }
              :: rev_tds,
              gen || gens <> [] ))
          ([], false) type_decls
      in
      (List.rev rev_tds, gen)
    in
    if generate then
      let* decls = List.map_e gen_decl type_decls in
      return [ Dlogic decls ]
    else return []

  let add_wfs (decls : decl list) : decl list iresult =
    (* Adds predicate [is_type_wf] for type decls with [@gen_wf] in the preambles *)
    List.concat_map_e
      (function
        | Dtype dts as d ->
            let* xs = gen_decls dts in
            return ([ d ] @ xs)
        | d -> return [ d ])
      decls
end

let sort_wf (s : Sort.t) (p : expr) : term =
  Is_type_wf.gen_apply (Sort.pty_of_sort s) p

module type Desc = sig
  val desc : desc
end

module Generator (D : Desc) = struct
  module M = Map.Make (String)

  let contracts =
    List.fold_left (fun s c -> M.add c.cn_name c s) M.empty D.desc.d_contracts

  (* code fragment makers *)

  let wrap_assume ~(assumption : term) (e : expr) : expr =
    E.mk_seq (E.mk_assume assumption) e

  let wrap_gas_check (e : expr) : expr =
    E.mk_if
      (E.mk_bin (E.mk_var gas_ident) "<" (econst 0))
      (E.mk_raise terminate_ident)
      e

  let gas_decr : expr = E.mk_bin (E.mk_var gas_ident) "-" @@ econst 1
  let gas_variant : variant = [ (tvar @@ qid gas_ident, None) ]
  let ctx_pty = PTtyapp (qid ctx_ty_ident, [])
  let step_pty = PTtyapp (qid step_ty_ident, [])
  let gparam_pty = PTtyapp (qid gparam_ty_ident, [])

  let entrypoint_pty =
    PTscope
      ( Qdot (qid @@ ident "ICon", ident "Contract"),
        PTtyapp (qid entrypoint_ty_ident, []) )

  let contract_pty = PTtyapp (qid contract_ty_ident, [])
  let operation_pty = PTtyapp (qid operation_ty_ident, [])
  let storage_pty_of c = PTtyapp (qid_of c storage_ty_ident, [])
  let qid_param_wf_of (c : contract) : qualid = qid_of c param_wf_ident
  let qid_storage_wf_of (c : contract) : qualid = qid_of c storage_wf_ident
  let call_ctx_wf (ctx : expr) : expr = eapp (qid ctx_wf_ident) [ ctx ]
  let call_step_wf (st : expr) : expr = eapp (qid step_wf_ident) [ st ]
  let call_inv_pre (ctx : expr) : expr = eapp (qualid [ "inv_pre" ]) [ ctx ]

  let call_inv_post (ctx : expr) (ctx' : expr) : expr =
    eapp (qualid [ "inv_post" ]) [ ctx; ctx' ]

  let is_contract_of (c : contract) (e : expr) : expr =
    E.mk_bin e "=" @@ evar @@ qid_of c addr_ident

  let call_param_wf_of (c : contract) (p : expr) (ep : expr) : expr =
    eapp (qid_param_wf_of c) [ p; ep ]

  let call_storage_wf_of (c : contract) (s : expr) : expr =
    eapp (qid_storage_wf_of c) [ s ]

  let call_spec_of (c : contract) (st : expr) (gp : expr) (s : expr)
      (ops : expr) (s' : expr) : expr =
    eapp (qid_of c spec_ident) [ st; gp; s; ops; s' ]

  let call_pre_of (c : contract) (st : expr) (p : expr) (ctx : expr) : expr =
    eapp (qid @@ id_pre_of c) [ st; p; ctx ]

  let call_post_of (c : contract) (st : expr) (p : expr) (ctx : expr)
      (ctx' : expr) : expr =
    eapp (qid @@ id_post_of c) [ st; p; ctx; ctx' ]

  let _call_is_param_of (c : contract) (gp : expr) : expr =
    eapp (qid @@ id_is_param_of c) [ gp ]

  let balance_of (c : contract) (ctx : expr) : expr =
    eapp (qid @@ id_balance_of c) [ ctx ]

  let storage_of (c : contract) (ctx : expr) : expr =
    eapp (qid @@ id_store_of c) [ ctx ]

  let update_balance_of (c : contract) (ctx : expr) (e : expr) : expr =
    expr @@ Eupdate (ctx, [ (qid @@ id_balance_of c, e) ])

  let update_storage_of (c : contract) (ctx : expr) (e : expr) : expr =
    expr @@ Eupdate (ctx, [ (qid @@ id_store_of c, e) ])

  let incr_balance_of (c : contract) (ctx : expr) (amt : expr) : expr =
    update_balance_of c ctx @@ E.mk_bin (balance_of c ctx) "+" amt

  let decr_balance_of (c : contract) (ctx : expr) (amt : expr) : expr =
    update_balance_of c ctx @@ E.mk_bin (balance_of c ctx) "-" amt

  let call_func_of (c : contract) (st : expr) (gp : expr) (ctx : expr) : expr =
    eapp (qid @@ id_func_of c) [ gas_decr; st; gp; ctx ]

  let call_unknown (ctx : expr) : expr =
    eapp (qid unknown_ident) [ gas_decr; ctx ]

  let dispatch_transfer (ctx : expr) (st : expr) (gp : expr) : expr =
    M.fold
      (fun _ c e ->
        E.mk_if
          (is_contract_of c @@ Step_constant.self st)
          (wrap_assume
             ~assumption:
               (T.of_expr
               @@ call_param_wf_of c gp (eapp (qualid [ "entrypoint" ]) [ st ])
               )
          @@ call_func_of c st gp ctx)
          e)
      contracts (call_unknown ctx)

  let ( let+ ) e f =
    let x = fresh_id () in
    E.mk_let x e (f (E.mk_var x))

  let known_contract (contract : contract) : fundef =
    let st = mk_binder @@ ident "st" in
    let gparam = mk_binder @@ ident "gp" in
    let ctx = mk_binder @@ ident "c" in
    let spec =
      {
        empty_spec with
        sp_pre =
          List.map T.of_expr
            [
              is_contract_of contract @@ Step_constant.self
              @@ E.var_of_binder st;
              call_ctx_wf @@ E.var_of_binder ctx;
              call_step_wf @@ E.var_of_binder st;
              call_param_wf_of contract (E.var_of_binder gparam)
                (eapp (qualid [ "entrypoint" ]) [ E.var_of_binder st ]);
              call_pre_of contract (E.var_of_binder st) (E.var_of_binder gparam)
                (E.var_of_binder ctx);
            ];
        sp_post =
          [
            mk_post @@ T.of_expr @@ call_ctx_wf @@ E.mk_var Id.result;
            mk_post @@ T.of_expr
            @@ call_post_of contract (E.var_of_binder st)
                 (E.var_of_binder gparam) (E.var_of_binder ctx)
                 (E.mk_var Id.result);
          ];
        sp_xpost =
          (if contract.cn_num_kont > 0 then
             [ mk_xpost terminate_ident; mk_xpost insufficient_mutez_ident ]
           else [ mk_xpost terminate_ident ]);
        sp_variant = gas_variant;
      }
    in
    let rec mk_ops_pat n acc =
      if n > 0 then
        let o = fresh_id () in
        mk_ops_pat (n - 1)
          ( pat @@ Papp (qualid [ "Cons" ], [ pat_var o; fst acc ]),
            E.mk_var o :: snd acc )
      else acc
    in
    let mk_clause ctx n =
      let ops_p, binders =
        mk_ops_pat n (pat @@ Papp (qualid [ "Nil" ], []), [])
      in
      let rec aux ctx l =
        match l with
        | [] -> ctx
        | o :: tl ->
            let gp = fresh_id () in
            let amt = fresh_id () in
            let dst = fresh_id () in
            let+ ctx =
              expr
              @@ Ematch
                   ( o,
                     [
                       (pat @@ Papp (qualid [ "Sdel" ], [ pat Pwild ]), ctx);
                       ( pat
                         @@ Papp
                              ( qualid [ "Xfer" ],
                                [ pat_var gp; pat_var amt; pat_var dst ] ),
                         wrap_assume
                           ~assumption:(sort_wf Sort.S_mutez @@ E.mk_var amt)
                         @@ E.mk_if
                              (E.mk_bin (balance_of contract ctx) "<"
                              @@ E.mk_var amt)
                              (E.mk_raise insufficient_mutez_ident)
                         @@ let+ ctx =
                              decr_balance_of contract ctx @@ E.mk_var amt
                            in
                            let+ st =
                              Step_constant.(
                                mk
                                  ~source:(source @@ E.var_of_binder st)
                                  ~sender:(self @@ E.var_of_binder st)
                                  ~self:
                                    (eapp (qualid [ "ct_addr" ])
                                       [ E.var_of_binder (mk_binder dst) ])
                                  ~entrypoint:
                                    (eapp (qualid [ "ct_ep" ])
                                       [ E.var_of_binder (mk_binder dst) ])
                                  ~amount:(E.mk_var amt)
                                  ~level:(level @@ E.var_of_binder st)
                                  ~now:(now @@ E.var_of_binder st))
                            in
                            dispatch_transfer ctx st (E.mk_var gp) );
                     ],
                     [] )
            in
            aux ctx tl
      in
      (ops_p, aux ctx binders)
    in
    let body =
      let+ ctx =
        incr_balance_of contract (E.var_of_binder ctx)
          (Step_constant.amount @@ E.var_of_binder st)
      in
      let+ new_s =
        E.mk_any
          ~ensure:
            (T.of_expr
            @@ call_storage_wf_of contract
            @@ E.mk_var @@ ident "result")
        @@ storage_pty_of contract
      in
      let+ ops = E.mk_any @@ Sort.pty_of_sort Sort.(S_list S_operation) in
      wrap_assume
        ~assumption:
          (T.of_expr
          @@ call_spec_of contract (E.var_of_binder st) (E.var_of_binder gparam)
               (storage_of contract ctx) ops new_s)
      @@ let+ ctx = update_storage_of contract ctx new_s in
         let cls =
           (pat @@ Pwild, expr @@ Eabsurd)
           :: List.rev_map
                (fun i -> mk_clause ctx i)
                (List.init (contract.cn_num_kont + 1) Fun.id)
         in
         expr @@ Ematch (ops, List.rev cls, [])
    in
    let body = wrap_gas_check body in
    ( id_func_of contract,
      true,
      Expr.RKnone,
      [ mk_binder gas_ident; st; gparam; ctx ],
      None,
      pat Pwild,
      Ity.MaskVisible,
      spec,
      body )

  let unknown_func_def =
    let ctx = mk_binder @@ ident "c" in
    let spec =
      {
        empty_spec with
        sp_pre =
          [
            T.of_expr @@ call_ctx_wf @@ E.var_of_binder ctx;
            T.of_expr @@ call_inv_pre @@ E.var_of_binder ctx;
          ];
        sp_post =
          [
            mk_post @@ T.of_expr @@ call_ctx_wf @@ E.mk_var @@ ident "result";
            mk_post @@ T.of_expr
            @@ call_inv_post (E.var_of_binder ctx)
            @@ E.mk_var @@ ident "result";
          ];
        sp_xpost =
          [ mk_xpost terminate_ident; mk_xpost insufficient_mutez_ident ];
        sp_variant = gas_variant;
      }
    in
    let wf st =
      M.fold
        (fun _ c t ->
          T.mk_not (T.of_expr @@ is_contract_of c @@ Step_constant.source st)
          :: T.mk_not (T.of_expr @@ is_contract_of c @@ Step_constant.sender st)
          :: t)
        contracts []
      |> List.fold_left T.mk_and @@ term Ttrue
    in
    let body =
      E.mk_if (E.mk_any @@ Sort.pty_of_sort Sort.S_bool) (E.var_of_binder ctx)
      @@ let+ st =
           E.mk_any
             ~ensure:(T.of_expr @@ call_step_wf @@ E.mk_var @@ ident "result")
             step_pty
         in
         let+ p = E.mk_any gparam_pty in
         wrap_assume ~assumption:(wf st)
         @@ let+ ctx = dispatch_transfer (E.var_of_binder ctx) st p in
            call_unknown ctx
    in
    let body = wrap_gas_check body in
    ( unknown_ident,
      true,
      Expr.RKnone,
      [ mk_binder gas_ident; ctx ],
      None,
      pat Pwild,
      Ity.MaskVisible,
      spec,
      body )

  let ctx_ty_def =
    let flds =
      M.fold
        (fun _ c flds ->
          {
            f_loc = Loc.dummy_position;
            f_ident = id_store_of c;
            f_pty = storage_pty_of c;
            f_mutable = false;
            f_ghost = false;
          }
          :: {
               f_loc = Loc.dummy_position;
               f_ident = id_balance_of c;
               f_pty = Sort.pty_of_sort Sort.S_mutez;
               f_mutable = false;
               f_ghost = false;
             }
          :: flds)
        contracts []
    in
    Dtype
      [
        {
          td_loc = Loc.dummy_position;
          td_ident = ctx_ty_ident;
          td_params = [];
          td_vis = Public;
          td_mut = false;
          td_inv = [];
          td_wit = None;
          td_def = TDrecord flds;
        };
      ]

  let operation_ty_def =
    {
      td_loc = Loc.dummy_position;
      td_ident = operation_ty_ident;
      td_params = [];
      td_vis = Public;
      td_mut = false;
      td_inv = [];
      td_wit = None;
      td_def =
        TDalgebraic
          [
            ( Loc.dummy_position,
              xfer_cstr_ident,
              [
                (Loc.dummy_position, None, false, gparam_pty);
                (Loc.dummy_position, None, false, Sort.pty_of_sort Sort.S_mutez);
                (* ( Loc.dummy_position,
                     None,
                     false,
                     Sort.pty_of_sort Sort.S_address );
                   ( Loc.dummy_position,
                     None,
                     false,
                     PTtyapp (qualid [ "ICon"; "Contract"; "entrypoint" ], []) ); *)
                (Loc.dummy_position, None, false, contract_pty);
              ] );
            ( Loc.dummy_position,
              sdel_cstr_ident,
              [
                ( Loc.dummy_position,
                  None,
                  false,
                  Sort.pty_of_sort Sort.(S_option S_key_hash) );
              ] );
          ];
    }

  let ctx_wf_def : decl =
    let ctx : param = mk_param "ctx" ctx_pty in
    let d =
      M.fold
        (fun _ c t ->
          T.mk_and (sort_wf Sort.S_mutez @@ balance_of c @@ E.var_of_param ctx)
          @@ T.mk_and
               (T.of_expr @@ call_storage_wf_of c @@ storage_of c
              @@ E.var_of_param ctx)
               t)
        contracts
      @@ term Ttrue
    in
    Dlogic
      [
        {
          ld_loc = Loc.dummy_position;
          ld_ident = ctx_wf_ident;
          ld_params = [ ctx ];
          ld_type = None;
          ld_def = Some d;
        };
      ]

  let func_def =
    List.map (fun (_, c) -> known_contract c) @@ M.bindings contracts
end

let rec de_qualid = function
  | Qident id -> [ id ]
  | Qdot (qid, id) -> de_qualid qid @ [ id ]

(* Match with paths [ICon.Gp.xxx] *)
let is_icon_gp qid =
  match de_qualid qid with
  | [ { id_str = "ICon"; _ }; { id_str = "Gp"; _ } ] -> true
  | _ -> false

(* Mangle [Sort.t] *)
let mangle_sort (s : Sort.t) : string =
  let re = Regexp.(compile @@ alt [ char ' '; char '('; char ')'; char ',' ]) in
  Sort.string_of_sort s
  |> Regexp.replace re ~f:(fun g ->
         match Regexp.Group.get g 0 with
         | " " -> "0"
         | "(" -> "1"
         | ")" -> "2"
         | "," -> "3"
         | _ -> assert false)

let rec expand_alias env pty =
  match pty with
  | PTtyapp (Qident id, []) -> (
      match List.assoc_opt id.id_str env with None -> pty | Some pty -> pty)
  | PTtyapp (qid, ptys) -> PTtyapp (qid, List.map (expand_alias env) ptys)
  | PTtuple ptys -> PTtuple (List.map (expand_alias env) ptys)
  | PTref ptys -> PTref (List.map (expand_alias env) ptys)
  | PTarrow (pty1, pty2) ->
      PTarrow (expand_alias env pty1, expand_alias env pty2)
  | PTscope (qid, pty) -> PTscope (qid, expand_alias env pty)
  | PTparen pty -> PTparen (expand_alias env pty)
  | PTpure pty -> PTpure (expand_alias env pty)
  | PTtyvar _ -> pty

(* If a type decl is an alias of a sort, returns the sort *)
let type_decl_alias_of_sort env type_decl =
  match (type_decl.td_params, type_decl.td_def) with
  | [], TDalias pty -> (
      (* Skip the decl which defines a sort itself, such as
         [type nat = int]  and  [type address = int]
      *)
      match Sort.sort_of_pty (PTtyapp (Qident type_decl.td_ident, [])) with
      | Ok _ -> None
      | Error _ -> (
          let pty = expand_alias env pty in
          match Sort.sort_of_pty pty with
          | Ok _sort -> Some ((type_decl.td_ident.id_str, pty) :: env)
          | Error _ -> None))
  | _ -> None

let extract_sort_decls decls =
  List.fold_left
    (fun env decl ->
      match decl with
      | Dtype type_decls ->
          List.fold_left
            (fun env type_decl ->
              match type_decl_alias_of_sort env type_decl with
              | None -> env
              | Some env -> env)
            env type_decls
      | _ -> env)
    [] decls

let sort_of_pty' env pty =
  let pty = expand_alias env pty in
  Sort.sort_of_pty pty

(** Generate the global parameter constructor name for entrypoint [ep] of type [s]. *)
let gen_gparam_cstr (s : Sort.t) : string =
  Format.sprintf "Gp'0%s" (mangle_sort s)

let entrypoint_qualid epn =
  qualid [ "ICon"; "Contract"; String.capitalize_ascii epn ]

(* ICon.Gp (e : ty) => ICon.Gp.Ty_ty e *)
module ICon_Gp = struct
  let convert_term (env : (string * pty) list)
      (_epp : Sort.t StringMap.t StringMap.t) (t : term) : term iresult =
    let open Ptree_mapper in
    let convert_term mapper term =
      let convert_icon_gp ~loc t =
        match t.term_desc with
        | Tcast (t, pty) -> (
            match sort_of_pty' env pty with
            | Error _ ->
                raise
                @@ Loc.Located
                     ( loc,
                       Failure
                         (Format.sprintf
                            "The type is not declared or is not a sort") )
            | Ok sort ->
                Ptree_helpers.term
                  (Tidapp (qualid [ gen_gparam_cstr sort ], [ t ])))
        | _ ->
            raise
              (Loc.Located
                 (loc, Failure "ICon.Gp must take a term with a type constraint"))
      in
      match term.term_desc with
      | Tapply ({ term_desc = Tident qid; _ }, t) when is_icon_gp qid ->
          convert_icon_gp ~loc:term.term_loc t
      | Tidapp (qid, ts) when is_icon_gp qid -> (
          match ts with
          | [ t ] -> convert_icon_gp ~loc:term.term_loc t
          | _ ->
              raise
                (Loc.Located
                   (term.term_loc, Failure "ICon.Gp takes only 1 argument")))
      | _ -> default_mapper.term mapper term
    in

    let convert_term : Ptree_mapper.mapper -> term -> term =
      (*
      let string_of_qident qid =
        let rec aux qid s =
          match qid with
          | Qident id -> id.id_str :: s
          | Qdot (qid, id) -> aux qid (id.id_str :: s)
        in
        let s = aux qid [] in
        String.concat "." s
          [@@ocaml.warning "-26"]
      in
      *)
      let convert (sub : Ptree_mapper.mapper) term =
        let gen_contract _cn ep addr =
          (*
          let cn_epp =
            try StringMap.find cn epp
            with Not_found ->
              raise
              @@ Loc.Located
                   ( term.term_loc,
                     Failure (Format.sprintf "%s is not declared" cn) )
          in
          *)
          let ct_ep = Tident (entrypoint_qualid ep) in
          Trecord
            [
              (Qident (ident "ct_ep"), { term with term_desc = ct_ep });
              (Qident (ident "ct_addr"), sub.term sub addr);
            ]
        in
        let term_desc =
          match term.term_desc with
          (*
          | Tidapp (Qdot (Qident icon, contract), terms)
            when icon.id_str = "ICon" && contract.id_str = "Contract" ->
              let cn, ep, addr =
                match terms with
                | [ { term_desc = Tident (Qdot (Qident ct, ep)); _ }; addr ] ->
                    (ct.id_str, ep.id_str, addr)
                | [ addr ] -> ("Unknown", "default", addr)
                | _ ->
                    raise
                    @@ Loc.Located
                         ( term.term_loc,
                           Failure
                             (Format.sprintf
                                "The arguments of Icon.Contract is invalid") )
              in
              gen_contract cn ep addr
          *)
          (*
             | Tapply
              ( {
                  term_desc =
                    Tapply
                      ( { term_desc = Tident (Qdot (Qident icon, contract)); _ },
                        { term_desc = Tident (Qdot (Qident ct, ep)); _ } );
                  _;
                },
                addr )
                *)
          | Tapply
              ( {
                  term_desc = Tident (Qdot (Qdot (Qident icon, contract), ep));
                  _;
                },
                addr )
            when icon.id_str = "ICon" && contract.id_str = "Contract" ->
              Format.eprintf "Debug : Found ICon.Contract \n";
              gen_contract "Unknown" ep.id_str addr
          | Tapply
              ({ term_desc = Tident (Qdot (Qident icon, contract)); _ }, addr)
            when icon.id_str = "ICon" && contract.id_str = "Contract" ->
              Format.eprintf "Debug : Found ICon.Contract default : %a \n"
                Sexplib0.Sexp.pp (Ptree.sexp_of_term addr);
              gen_contract "Unknown" "default" addr
          (*
           | Tidapp (qid, ts) ->
              Format.eprintf "Debug idapp:%s %a\n" (string_of_qident qid)
                (Format.pp_print_list Sexplib0.Sexp.pp) (List.map Ptree.sexp_of_term ts);
              Tidapp (sub.qualid sub qid, List.map (sub.term sub) ts)
          *)
          | _ -> (default_mapper.term sub term).term_desc
        in
        { term with term_desc }
      in

      fun mapper term ->
        let term = convert_term mapper term in
        convert mapper term
    in

    let convert_pattern mapper p =
      let rec convert_icon_gp ~loc p =
        match p.pat_desc with
        | Pcast (p, pty) -> (
            match sort_of_pty' env pty with
            | Error _ ->
                raise
                @@ Loc.Located
                     ( loc,
                       Failure
                         (Format.sprintf
                            "The type is not declared or is not a sort") )
            | Ok sort ->
                Ptree_helpers.pat
                  (Papp (qualid [ gen_gparam_cstr sort ], [ p ])))
        | Pparen p -> convert_icon_gp ~loc p
        | _ ->
            raise
              (Loc.Located
                 ( loc,
                   Failure "ICon.Gp must take a pattern with a type constraint"
                 ))
      in
      match p.pat_desc with
      | Papp (qid, ps) when is_icon_gp qid -> (
          match ps with
          | [ p ] -> convert_icon_gp ~loc:p.pat_loc p
          | _ ->
              raise
                (Loc.Located (p.pat_loc, Failure "ICon.Gp takes only 1 argument"))
          )
      | _ -> default_mapper.pattern mapper p
    in

    try
      return
      @@ apply_term t
           {
             default_mapper with
             term = convert_term;
             pattern = convert_pattern;
           }
    with Loc.Located (loc, Failure s) -> error_with ~loc "%s" s

  let convert_logic_decl sort_env (epp : Sort.t StringMap.t StringMap.t)
      (logic_decl : logic_decl) : logic_decl iresult =
    let* ld_def = Option.map_e (convert_term sort_env epp) logic_decl.ld_def in
    return { logic_decl with ld_def }

  (* Only for functions and predicates for now *)
  let convert_decl sort_env (epp : Sort.t StringMap.t StringMap.t) (decl : decl)
      : decl iresult =
    match decl with
    | Dlogic lds ->
        let* lds = List.map_e (convert_logic_decl sort_env epp) lds in
        return @@ Dlogic lds
    | _ -> return decl
end

let gen_spec (epp : Sort.t StringMap.t) =
  let st : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "st"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "step" ], []) )
  in
  let gp : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "gp"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "gparam" ], []) )
  in
  let s : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "s"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "storage" ], []) )
  in
  let op : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "op"),
      false,
      Sort.pty_of_sort Sort.(S_list S_operation) )
  in
  let s' : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "s'"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "storage" ], []) )
  in
  let args =
    Ptree_helpers.
      [
        tvar @@ qualid [ "st" ];
        tvar @@ qualid [ "s" ];
        tvar @@ qualid [ "op" ];
        tvar @@ qualid [ "s'" ];
      ]
  in
  let cls =
    StringMap.fold
      (fun en (s : Sort.t) cls ->
        (* | "entrypoint", Gp'0... _p -> Spec.entrypoint st s op s' _p *)
        let param = pat_var @@ ident "_p" in
        let args = args @ [ tvar @@ qualid [ "_p" ] ] in
        ( pat
            (Ptuple
               [
                 pat @@ Papp (entrypoint_qualid en, []);
                 pat @@ Papp (qualid [ gen_gparam_cstr s ], [ param ]);
               ]),
          tapp (qualid [ "Spec"; en ]) args )
        :: cls)
      epp
      [ (pat Pwild, term Tfalse) ]
  in
  let body =
    term
    @@ Tcase
         ( term
             (Ttuple
                [
                  T.of_expr (Step_constant.entrypoint (evar @@ qualid [ "st" ]));
                  tvar (qualid [ "gp" ]);
                ]),
           cls )
  in
  let ld_loc = Loc.dummy_position in
  let ld_ident = Ptree_helpers.ident "spec" in
  let ld_params = [ st; gp; s; op; s' ] in
  let ld_type = None in
  let ld_def = Some body in
  { ld_loc; ld_ident; ld_params; ld_type; ld_def }

let gen_param_wf ep =
  let gp_param : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "gp"),
      false,
      PTtyapp (Ptree_helpers.qualid [ "gparam" ], []) )
  in
  let ep_param : Ptree.param =
    ( Loc.dummy_position,
      Some (Ptree_helpers.ident "ep"),
      false,
      PTscope
        ( Qdot (qid @@ ident "ICon", ident "Contract"),
          PTtyapp (qid (ident "entrypoint"), []) ) )
  in
  let cls =
    StringMap.fold
      (fun en (s : Sort.t) cls ->
        let p = ident "_p" in
        let param = pat_var p in
        let pred = sort_wf s @@ E.mk_var p in
        ( pat
          @@ Ptuple
               [
                 pat @@ Papp (qualid [ gen_gparam_cstr s ], [ param ]);
                 pat @@ Papp (entrypoint_qualid en, []);
               ],
          pred )
        :: cls)
      ep
      [ Ptree_helpers.(pat Pwild, term Tfalse) ]
  in
  let body =
    Ptree_helpers.(
      term
      @@ Tcase
           ( term @@ Ttuple [ tvar (qualid [ "gp" ]); tvar (qualid [ "ep" ]) ],
             cls ))
  in
  return
    {
      ld_loc = Loc.dummy_position;
      ld_ident = Ptree_helpers.ident "param_wf";
      ld_params = [ gp_param; ep_param ];
      ld_type = None;
      ld_def = Some body;
    }

(* meta "algebraic:kept" type <ty> *)
let gen_meta_algebraic_kept_type ty = Dmeta (ident "algebraic:kept", [ Mty ty ])

let convert_entrypoint sort_env (epp : Sort.t StringMap.t StringMap.t)
    (ep : Tzw.entrypoint) : logic_decl iresult =
  let* body = ICon_Gp.convert_term sort_env epp ep.ep_body in
  return
    {
      ld_loc = ep.ep_loc;
      ld_ident = ep.ep_name;
      ld_params =
        [
          ep.ep_params.epp_step;
          ep.ep_params.epp_old_s;
          ep.ep_params.epp_ops;
          ep.ep_params.epp_new_s;
          ep.ep_params.epp_param;
        ];
      ld_type = None;
      ld_def = Some body;
    }

let convert_contract sort_env (epp : Sort.t StringMap.t StringMap.t)
    (c : Tzw.contract) =
  let* eps =
    List.fold_left_e
      (fun tl (ep : Tzw.entrypoint) ->
        let meta =
          let _, _, _, pty = ep.ep_params.epp_param in
          gen_meta_algebraic_kept_type pty
        in
        let* ep = convert_entrypoint sort_env epp ep in
        return @@ (meta :: Dlogic [ ep ] :: tl))
      [] c.c_entrypoints
  in
  let* ep =
    StringMap.find_opt c.c_name.id_str epp
    |> Option.to_iresult ~none:(error_of_fmt "")
  in
  let* param_wf = gen_param_wf ep in
  let* other_decls = Is_type_wf.add_wfs c.c_other_decls in
  return
  (* scope Contract .. *)
  @@ Dscope
       ( Loc.dummy_position,
         false,
         c.c_name,
         other_decls
         @ [
             Dlogic
               [
                 {
                   ld_loc = Loc.dummy_position;
                   ld_ident = Ptree_helpers.ident "addr";
                   ld_params = [];
                   ld_type = Some (Sort.pty_of_sort Sort.S_address);
                   ld_def = None;
                 };
               ];
             Dlogic [ param_wf ];
             Dscope (Loc.dummy_position, false, Ptree_helpers.ident "Spec", eps);
             Dlogic [ gen_spec (StringMap.find c.c_name.id_str epp) ];
           ] )

(* type gparam = ... | GpUnknown *)
let gen_gparam (epp : Sort.t StringMap.t StringMap.t) =
  let module S = Set.Make (struct
    type t = Loc.position * ident * param list

    let compare = compare
  end) in
  let td_def =
    TDalgebraic
      (S.elements
      @@ StringMap.fold
           (fun _ (* contract name *) ->
             StringMap.fold (fun _en (* entrypoint name *) (s : Sort.t) cstrs ->
                 S.add
                   ( Loc.dummy_position,
                     ident @@ gen_gparam_cstr s,
                     [ (Loc.dummy_position, None, false, Sort.pty_of_sort s) ]
                   )
                   cstrs))
           epp
      @@ S.singleton (Loc.dummy_position, ident "GpUnknown", []))
  in
  {
    td_loc = Loc.dummy_position;
    td_ident = Ptree_helpers.ident "gparam";
    td_params = [];
    td_vis = Public;
    td_mut = false;
    td_inv = [];
    td_wit = None;
    td_def;
  }

(*
let gen_contract (epp : Sort.t list StringMap.t StringMap.t) =
  let module S = Set.Make (struct
    type t = Loc.position * ident * param list

    let compare = compare
  end) in
  let td_def =
    TDalgebraic
      (S.elements
      @@ StringMap.fold
           (fun ct ->
             StringMap.fold (fun en s cstrs ->
                 S.add
                   ( Loc.dummy_position,
                     Ptree_helpers.ident @@ gen_entrypoint_cstr ct en s,
                     [] )
                   cstrs))
           epp
      @@ S.singleton (Loc.dummy_position, ident "EpUnknown", []))
  in
  {
    td_loc = Loc.dummy_position;
    td_ident = entrypoint_ty_ident;
    td_params = [];
    td_vis = Public;
    td_mut = false;
    td_inv = [];
    td_wit = None;
    td_def;
  }
*)

let parse_string s =
  let lexbuf = Lexing.from_string s in
  Lexer.parse_mlw_file lexbuf

let convert_mlw (tzw : Tzw.t) =
  let epp = tzw.tzw_epp in
  let* preambles =
    match parse_string Preambles.preambles with
    | Decls ds -> return (ds @ tzw.tzw_preambles)
    | _ -> error_with "invalid prembles: preambles must be list of declarations"
  in
  let* preambles = Is_type_wf.add_wfs preambles in
  let entrypoint_def =
    let epns : string list =
      StringSet.elements
      @@ StringMap.fold
           (fun _cn ep acc ->
             StringMap.fold (fun epn _sort acc -> StringSet.add epn acc) ep acc)
           tzw.tzw_epp StringSet.empty
    in
    let td_def =
      TDalgebraic
        (List.map
           (fun epn ->
             ( Loc.dummy_position,
               (match entrypoint_qualid epn with
               | Qdot (_, id) -> id
               | _ -> assert false),
               [] ))
           epns)
    in
    [
      Dtype
        [
          {
            td_loc = Loc.dummy_position;
            td_ident = ident "entrypoint";
            td_params = [];
            td_vis = Public;
            td_mut = false;
            td_inv = [];
            td_wit = None;
            td_def;
          };
        ];
    ]
  in
  let* step =
    match parse_string Preambles.step with
    | Decls ds -> return ds
    | _ ->
        error_with
          "invalid step type definition: step must be list of declarations"
  in
  let sort_env = extract_sort_decls preambles in
  let* ds = List.map_e (convert_contract sort_env epp) tzw.tzw_knowns in
  let* invariants =
    let* lds =
      List.map_e
        (fun (c : Tzw.contract) ->
          let* pre_def =
            Option.map_e (ICon_Gp.convert_term sort_env epp) c.c_pre.ld_def
          in
          let* post_def =
            Option.map_e (ICon_Gp.convert_term sort_env epp) c.c_post.ld_def
          in
          return
            [
              Dlogic
                [
                  {
                    c.c_pre with
                    ld_ident =
                      Ptree_helpers.ident @@ String.uncapitalize_ascii
                      @@ c.c_name.id_str ^ "_pre";
                    ld_def = pre_def;
                  };
                ];
              Dlogic
                [
                  {
                    c.c_post with
                    ld_ident =
                      Ptree_helpers.ident @@ String.uncapitalize_ascii
                      @@ c.c_name.id_str ^ "_post";
                    ld_def = post_def;
                  };
                ];
            ])
        tzw.tzw_knowns
    in
    let* pre_def =
      Option.map_e
        (ICon_Gp.convert_term sort_env epp)
        tzw.tzw_unknown_pre.ld_def
    in
    let* post_def =
      Option.map_e
        (ICon_Gp.convert_term sort_env epp)
        tzw.tzw_unknown_post.ld_def
    in
    return
    @@ Dlogic
         [
           {
             tzw.tzw_unknown_pre with
             ld_ident = Ptree_helpers.ident "inv_pre";
             ld_def = pre_def;
           };
         ]
       :: Dlogic
            [
              {
                tzw.tzw_unknown_post with
                ld_ident = Ptree_helpers.ident "inv_post";
                ld_def = post_def;
              };
            ]
       :: List.flatten lds
  in
  let d_contracts =
    List.map
      (fun (c : Tzw.contract) ->
        {
          cn_name = String.uncapitalize_ascii c.c_name.id_str;
          cn_num_kont = c.c_num_kont;
        })
      tzw.tzw_knowns
  in
  let module G = Generator (struct
    let desc = { d_contracts; d_whyml = [] }
  end) in
  let* postambles =
    List.map_e (ICon_Gp.convert_decl sort_env epp) tzw.tzw_postambles
  in
  let decls =
    List.concat
      [
        (* contents of [scope Preambles] *)
        preambles;
        (* scope ICon
             scope Contract
               type entrypoint =
                 | ...
             end
           end
        *)
        [
          Dscope
            ( Loc.dummy_position,
              false,
              ident "ICon",
              [
                Dscope
                  (Loc.dummy_position, false, ident "Contract", entrypoint_def);
              ] );
        ];
        [
          (* Dtype [ gen_contract epp ]; *)
          (let contract_ty_def =
             {
               td_loc = Loc.dummy_position;
               td_ident = contract_ty_ident;
               td_params = [];
               td_vis = Public;
               td_mut = false;
               td_inv = [];
               td_wit = None;
               td_def =
                 TDrecord
                   [
                     {
                       f_loc = Loc.dummy_position;
                       f_ident = ident "ct_ep";
                       f_pty = G.entrypoint_pty;
                       f_mutable = false;
                       f_ghost = false;
                     };
                     {
                       f_loc = Loc.dummy_position;
                       f_ident = ident "ct_addr";
                       f_pty = Sort.pty_of_sort S_address;
                       f_mutable = false;
                       f_ghost = false;
                     };
                   ];
             }
           in
           Dtype [ contract_ty_def ]);
          Dlogic
            [
              {
                ld_loc = Loc.dummy_position;
                ld_ident = contract_wf_ident;
                ld_params = [ mk_param "cont" G.contract_pty ];
                ld_type = None;
                ld_def = Some (term Ttrue);
              };
            ];
        ];
        step;
        [
          Dtype
            [
              (* type gparam = .. *)
              gen_gparam epp;
              (* type operation = .. *)
              G.operation_ty_def;
            ];
            Dlogic
            [
              {
                ld_loc = Loc.dummy_position;
                ld_ident = operation_wf_ident;
                ld_params = [ mk_param "op" G.operation_pty ];
                ld_type = None;
                ld_def = Some (term Ttrue);
              };
            ];
        ];
        (* Scope Contract .. end *)
        ds;
        (* type ctx = .. *)
        [ G.ctx_ty_def ];
        (* predicate ctx_wf (ctx: ctx) = .. *)
        [ G.ctx_wf_def ];
        (* contents of [scope Postambles] *)
        postambles;
        (* inv_pre, inv_post, contract_pre, contract_post *)
        invariants;
        (* let rec ghost unknown g c .. *)
        [ Drec (G.unknown_func_def :: G.func_def) ];
      ]
  in
  return @@ Modules [ (ident "Top", decls) ]

(* let file desc = *)
(*   let module G = Generator (struct *)
(*     let desc = desc *)
(*   end) in *)
(*   Decls *)
(*     ([ use ~import:false [ "michelson"; "Michelson" ] ] *)
(*     @ [ G.ctx_ty_def; G.operation_ty_def ] *)
(*     (\* @ List.map (fun ld -> Dlogic [ ld ]) G.accessor *\) *)
(*     @ [ G.ctx_wf_def ] *)
(*     @ desc.d_whyml *)
(*     (\* @ List.map (fun ld -> Dlogic [ ld ]) G.spec *\) *)
(*     @ [ Drec (G.unknown_func_def :: G.func_def) ]) *)

let parse_file fn =
  In_channel.with_open_text fn (fun ic ->
      let lexbuf = Lexing.from_channel ic in
      Lexing.set_filename lexbuf fn;
      Lexer.parse_mlw_file lexbuf)

let from_mlw mlw =
  let r = Tzw.parse_mlw mlw >>= convert_mlw in
  raise_error r

let from_file fn = from_mlw (parse_file fn)
