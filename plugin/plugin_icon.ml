module Regexp = Re
open Why3

let find_target (ds : Decl.decl list) : Ident.ident option =
  let is_tuple ty =
    match ty.Ty.ty_node with
    | Tyapp (s, _) ->
        Regexp.(
          execp
            (compile (seq [ bos; alt [ str "tuple"; str "gparam"; str "or" ] ])))
          s.ts_name.id_string
    | _ -> false
  in
  List.find_map
    (fun d ->
      match d.Decl.d_node with
      | Dparam p ->
          Option.bind p.ls_value (fun ty ->
              if is_tuple ty then Some p.ls_name else None)
      | _ -> None)
    ds

let destruct_adt env =
  let rec aux t =
    let x = find_target @@ Task.task_decls t in
    match x with
    | None -> [ t ]
    | Some x ->
        let naming_table = Args_wrapper.build_naming_tables t in
        let x = Ident.id_unique naming_table.printer x in
        Trans.apply_transform_args "destruct_term_subst" env [ x ] naming_table
          Lexer.whyml_format t
        |> List.map aux |> List.flatten
  in
  Trans.store aux

let simplify env : Task.task Trans.tlist =
  let split_vc = Trans.lookup_transform_l "split_vc" env in
  let simplify_computations =
    Trans.singleton @@ Trans.lookup_transform "simplify_computations" env
  in
  let inline_all = Trans.singleton Inlining.all in
  let subst_all = Trans.singleton Subst.subst_all in
  Trans.seq_l
    [ inline_all; split_vc; subst_all; destruct_adt env; simplify_computations ]

let () =
  Trans.register_env_transform_l ~desc:"icon michelson" "icon_simplify" simplify

let read_channel env _path file c =
  let lexbuf = Lexing.from_channel c in
  Lexing.set_filename lexbuf file;
  let f = Lexer.parse_mlw_file lexbuf in
  Typing.type_mlw_file env [] (file ^ ".mlw") @@ Gen_mlw.from_mlw f

let () =
  Env.register_format Pmodule.mlw_language "tzw" [ "tzw" ] read_channel
    ~desc:"iCon project format"
