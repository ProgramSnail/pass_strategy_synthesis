(* (,,) -< Pair.inj _ (Pair.inj _ _) *)

module Relational =
struct
  open GT
  open OCanren
  open OCanren.Std

  @type data_ground = Nat.ground with show, gmap
  @type data_logic = Nat.logic with show, gmap
  type data_injected = Nat.injected

  @type tag_ground = Ref | Value with show, gmap
  @type tag_logic = tag_ground logic with show, gmap
  type tag_injected = tag_ground ilogic

  @type ('d, 'dl) stmt_abs = Call of 'd * 'dl | Read of 'd | Write of 'd with show, gmap
  @type stmt_ground = (data_ground, data_ground List.ground) stmt_abs with show, gmap
  @type stmt_logic = (data_logic, data_logic List.logic) stmt_abs logic with show, gmap
  type stmt_injected = (data_injected, data_injected List.injected) stmt_abs ilogic

  @type body_ground = stmt_ground List.ground with show, gmap
  @type body_logic = stmt_logic List.logic with show, gmap
  type body_injected = stmt_injected List.injected

  @type fun_decl_ground = tag_ground List.ground * body_ground with show, gmap
  @type fun_decl_logic = (tag_logic List.logic * body_logic) logic with show, gmap
  type fun_decl_injected = (tag_injected List.injected * body_injected) ilogic

  @type prog_ground = fun_decl_ground List.ground * fun_decl_ground with show, gmap
  @type prog_logic = (fun_decl_logic List.logic * fun_decl_logic) logic with show, gmap
  type prog_injected = (fun_decl_injected List.injected * fun_decl_injected) ilogic

  @type 'd arg_abs = RValue | LValue of 'd with show, gmap
  @type arg_ground = data_ground arg_abs with show, gmap
  @type arg_logic = data_logic arg_abs logic with show, gmap
  type arg_injected = data_injected arg_abs ilogic

  @type value_ground = UnitV | BotV with show, gmap
  @type value_logic = value_ground logic with show, gmap
  type value_injected = value_ground ilogic

  @type env_ground = (data_ground * data_ground) List.ground with show, gmap
  @type env_logic = (data_logic * data_logic) List.logic with show, gmap
  type env_injected = (data_injected * data_injected) List.injected ilogic

  @type ('env, 'mem, 'last_mem, 'assignments) state_abs =  'env * 'mem * 'last_mem * 'assignments with show, gmap
  @type state_ground = (list_map_ground, value_ground List.ground, data_ground, data_ground List.ground) state_abs with show, gmap
  @type state_logic = (list_map_logic, value_logic List.logic, data_logic, data_logic List.logic) state_abs logic with show, gmap
  type state_injected = (env_injected, value_injected List.injected, data_injected, data_injected List.injected) state_abs ilogic

  (* ocanren type 'a lst = Nil | Cons of 'a * 'a lst *)

  let rec list_replace xs id value ys =
    conde
    [ (xs === Nil) (ys === Nil) (* TODO: error *)
    ; fresh (x xs') (xs === x :: xs') (id === 0) (ys === value :: xs)
    ; fresh (x xs' id' ys') (xs === x :: xs') (id === suc id') (ys === x :: ys')
                            (list_replace xs' id' value ys')
    ]

  let env_get state id state' =
    fresh (env env' mem mem_len assignments)
    (state === (env, mem, mem_len, assignments))
    (state' === (env', mem,  mem_len, assignments))
    (List.assoc id env env')

  let env_add state id mem_id state' =
    fresh (env env' mem mem_len assignments)
    (state === (env, mem, mem_len, assignments))
    (state' === (env', mem,  mem_len, assignments))
    (env' == (id, mem_id) :: env)

  let inv_id mem_len id id' = (id === mem_len - id - 1)

  (* --- *)

  let mem_get state id value' =
    (fresh mem mem_len)
    (state === (_, mem, mem_len, _))
    (fresh mem_len_inv)
    (inv_id mem_len mem_len_inv)
    (fresh mem_id)
    (env_get state id mem_id)
    (List.nth mem mem_len_inv mem_id value')

  let mem_set state id value state'=
    (fresh env mem mem_len assignments)
    (state === (env, mem, mem_len, assignments))
    (fresh mem_id) (env_get state id mem_id)
    (fresh inv_mem_id) (inv_id mem_len mem_id inv_mem_id)
    (fresh mem') (list_replace mem mem_id value mem')
    (state' === (env, mem', mem_len, id :: assignments))

  let mem_add state value state' =
    (fresh env mem mem_len assignments)
    (state === (env, mem, mem_len, assignments))
    (fresh mem') (mem' === value :: mem)
    (state' === (env, mem, suc mem_len, assignments))

  let mem_check state id state' =
    conde
    [ (mem_get state id BotV) (state' === state) (* TODO: error *)
    ; (mem_get state id UnitV) (state' === state)
    ]

  (* --- *)

  let arg_to_value state arg value' =
    conde
    [ (arg === RValue) (value' === UnitV)
    ; (fresh id) (arg === LValue id) (mem_get state id value')
    ]

  let st_mem_len state mem_len' = (state === (_, _, mem_len, _))

  let st_add_arg state state_before id arg_tag arg state'' =
    conde
    [ (arg_tag === Ref) (arg === RValue) (state'' === state) (* TODO: error *) (* TODO: allow later ?? *)
    ; (fresh arg') (arg_tag === Ref) (arg === LValue arg')
      (fresh value') (env_get state_before arg value')
                     (env_add state id value' state'')
    ; (arg_tag === Value)
      (fresh value' state' mem_len_dec')
      (arg_to_value state_before arg value')
      (mem_add state value' state')
      (suc mem_len_dec' === st_mem_len state) (* or ... = ... - 1*)
      (env_add state' id mem_len_dec' state'')
    ]

  let st_spoil_assignments state state' =
    (fresh env mem mem' mem_len assignments)
    (state === (env, mem, mem_len, assignments))
    (List.fold_left (fun mem id -> list_replace mem (inv_id mem_len @@ env_get state id) BotV) mem assignments mem')
    (state') === (env, mem', mem_len, [])

  (* --- *)

  let rec eval_stmt state prog stmt state' =
    conde
    [ (fresh f_id args)
      (stmt === Call (f_id, args))
      (fresh f args')
      (List.nth prog f_id f)
      (List.map (fun arg -> LValue arg) args args')
      (* TODO how, rewrite from scratch ??? *)
      (eval_fun state prog f args')
    ; (fresh id) (stmt === Read id) (mem_check state id state')
    ; (fresh id) (stmt === Write id) (mem_set state it UnitV state')
    ]

  and eval_body state prog body state' =
    (List.fold_left (fun state stmt -> eval_stmt state prog stmt) state body)
    (* TODO how, rewrite from scratch ??? *)

  and eval_fun state prog decl args state' =
    (fresh arg_tags body)
    (fresh env_before mem_before len_before assignments_before)
    (fresh state_clean)
    (state_clean === ([], mem_before, len_before, []))
    (fresh state_with_vars)
    (state_with_vars === List.fold_left2 (fun (state, id) arg_tag arg -> (st_add_arg state state id arg_tag arg, id + 1)) (state, 0) arg_tags args)
    (* TODO how, rewrite from scratch ??? *)
    (fresh state_evaled)
    (eval_body state prog body state_evaled)
    (fresh state_spoiled)
    (st_spoil_assignments state_evaled state_spoiled)
    (fresh mem_updated len_to_drop)
    (len_to_drop === len - len_before)
    (List.drop len_to_drop mem mem_updated)
    (state' === (env_before, mem_updated, len_before, assignments_before))

  and eval_fun_empty_args state prog decl state' =
    (fresh arg_tags)
    (decl === (arg_tags, _))
    (List.map (fun _ -> RValue) arg_tags args) (* TODO how, rewrite from scratch ??? *)
    (eval_fun state prog decl args state')

  (* --- *)

  let empty_state state = (state === ([], [], 0, []))

  let eval_prog all_prog state' =
    (fresh prog main_decl)
    (all_prog == (prog, main_decl))
    (eval_fun_empty_args empty_state prog main_decl state')
end
