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
  @type state_ground = (env_ground, value_ground List.ground, data_ground, data_ground List.ground) state_abs with show, gmap
  @type state_logic = (env_logic, value_logic List.logic, data_logic, data_logic List.logic) state_abs logic with show, gmap
  type state_injected = (env_injected, value_injected List.injected, data_injected, data_injected List.injected) state_abs ilogic

  (* ocanren type 'a lst = Nil | Cons of 'a * 'a lst *)

  let rec list_replace xs id value ys =
    conde
    [ (xs === Std.nil ()) &&& (ys === Std.nil ()) (* TODO: error *)
    ; fresh (x xs') (xs === List.cons x xs') (id === Nat.o) (ys === List.cons value xs)
    ; fresh (x xs' id' ys') (xs === List. cons x xs') (id === Nat.s id') (ys === List.cons x ys')
                            (list_replace xs' id' value ys')
    ]

  let rec list_assoc a xs v' =
    conde
    [ fresh (a' b' xs')
      (xs === List.cons (a', b') xs')
      (a =/= a')
      (list_assoc a xs' v')
    ; fresh (a' b' xs')
      (xs === List.cons (a', b') xs')
      (a === a')
      (v' === b')
    ]
  (* TODO: dofference from List.assoco ?? *)

  let env_get state id mem_id' =
    fresh (env mem mem_len assignments)
    (state === inj (env, mem, mem_len, assignments))
    (list_assoc id env mem_id')
    (* (List.assoco id env mem_id') *)

  let env_add state id mem_id state' =
    fresh (env env' mem mem_len assignments)
    (state === inj (env, mem, mem_len, assignments))
    (state' === inj (env', mem,  mem_len, assignments))
    (env' === List.cons (id, mem_id) env)

  let inv_id mem_len id id' =
    fresh (inv_id_inc)
    (Nat.addo inv_id_inc id mem_len)
    (Nat.addo id' (Nat.s Nat.o) inv_id_inc)

  (* --- *)

  let rec list_nth xs id x' =
   conde
   [ (xs === Std.nil ()) (* TODO: error *)
   ; fresh (y' xs') (id === Nat.o) (List.cons y' xs' === xs) (x' === y')
   ; fresh (id' y' xs') (Nat.s id' === id) (List.cons y' xs' === xs) (list_nth xs' id' x')
   ]

  (* TODO: use real holes *)
  let mem_get state id value' =
    fresh (mem mem_len mem_id mem_id_inv env_ assignments_)
    (state === inj (env_, mem, mem_len, assignments_))
    (env_get state id mem_id)
    (inv_id mem_len mem_id mem_id_inv)
    (list_nth mem mem_id_inv value')

  let mem_set state id value state'=
    fresh (env mem mem_len assignments mem_id inv_mem_id mem')
    (state === inj (env, mem, mem_len, assignments))
    (env_get state id mem_id)
    (inv_id mem_len mem_id inv_mem_id)
    (list_replace mem mem_id value mem')
    (state' === inj (env, mem', mem_len, List.cons id assignments))

  let mem_add state value state' =
    fresh (env mem mem_len assignments mem')
    (state === inj (env, mem, mem_len, assignments))
    (mem' === List.cons value mem)
    (state' === inj (env, mem, Nat.s mem_len, assignments))

  let mem_check state id state' =
    conde
    [ (mem_get state id (inj BotV)) &&& (state' === state) (* TODO: error *)
    ; (mem_get state id (inj UnitV)) &&& (state' === state)
    ]

  (* --- *)

  let rec list_foldl f acc xs acc' =
    conde
    [ (xs === Std.nil ()) &&& (acc' === acc)
    ; fresh (x' xs' acc_upd)
      (xs === List.cons x' xs')
      (list_foldl f acc xs' acc_upd)
      (f acc_upd x' acc')
    ]


  let rec list_foldr2 f acc xs ys acc' =
    conde
    [ (xs === Std.nil ()) &&& (ys === Std.nil ()) &&& (acc' === acc)
    ; fresh (x' xs' y' ys' acc_upd)
      (xs === List.cons x' xs')
      (ys === List.cons y' ys')
      (f acc x' y' acc_upd)
      (list_foldr2 f acc_upd xs' ys' acc')
    ]

  let rec list_foldl2 f acc xs ys acc' =
    conde
    [ (xs === Std.nil ()) &&& (ys === Std.nil ()) &&& (acc' === acc)
    ; fresh (x' xs' y' ys' acc_upd)
      (xs === List.cons x' xs')
      (ys === List.cons y' ys')
      (list_foldl2 f acc xs' ys' acc_upd)
      (f acc_upd x' y' acc')
    ]

  let arg_to_value state arg value' =
    conde
    [ (arg === inj RValue) &&& (value' === inj UnitV)
    ; fresh (id) (arg === inj (LValue id)) (mem_get state id value')
    ]

  let arg_to_rvalue _arg value' = (value' === inj RValue)

  let st_mem_len state mem_len' =
    fresh (env_ mem_ assignments_) (* TODO: replace with real placeholder ? *)
    (state === inj (env_, mem_, mem_len', assignments_))

  let st_add_arg state state_before id arg_tag arg state'' =
    conde
    [ (arg_tag === inj Ref) &&& (arg === inj RValue) &&& (state'' === state)
      (* TODO: error, TODO: allow later ?? *)
    ; fresh (arg' value')
      (arg_tag === inj Ref)
      (arg === inj (LValue arg'))
      (env_get state_before arg' value')
      (env_add state id value' state'')
    ; fresh (value' state' mem_len_dec')
      (arg_tag === inj Value)
      (arg_to_value state_before arg value')
      (mem_add state value' state')
      (st_mem_len state (Nat.s mem_len_dec'))
      (env_add state' id mem_len_dec' state'')
    ]

  let st_spoil_folder mem_len state mem id mem' =
    fresh (mem_id' mem_id_inv')
    (env_get state id mem_id')
    (inv_id mem_len mem_id' mem_id_inv')
    (list_replace mem mem_id_inv' (inj BotV) mem')

  let st_spoil_assignments state state' =
    fresh (env mem mem' mem_len assignments)
    (state === inj (env, mem, mem_len, assignments))
    (list_foldl (st_spoil_folder mem_len state) mem assignments mem')
    (* (List.fold_left (fun mem id -> list_replace mem (inv_id mem_len @@ env_get state id) BotV) mem assignments mem') *)
    (state' === inj (env, mem', mem_len, Std.nil ()))

  (* --- *)

  let arg_to_lvalue arg arg' = (arg' === inj (LValue arg))

  let rec list_drop n xs xs' =
    conde
    [ (xs === Std.nil ()) &&& (xs' === Std.nil ())
    ; n === Nat.o &&& (xs === xs')
    ; fresh (n' y ys) (Nat.s n' === n) (xs === List.cons y ys) (list_drop n' ys xs')
    ]

  let rec eval_stmt state prog stmt state' =
    conde
    [ fresh (f_id args f args')
      (stmt === inj (Call (f_id, args)))
      (list_nth prog f_id f)
      (List.mapo arg_to_lvalue args args')
      (eval_fun state prog f args' state')
    ; fresh (id) (stmt === inj (Read id)) (mem_check state id state')
    ; fresh (id) (stmt === inj (Write id)) (mem_set state id (inj UnitV) state')
    ]

  and eval_body_folder prog state stmt state' = eval_stmt state prog stmt state'

  and eval_body state prog body state' =
    list_foldl (eval_body_folder prog) state body state' 
    (* (List.fold_left (fun state stmt -> eval_stmt state prog stmt) state body) *)

  and add_arg_folder state_before state_c arg_tag arg state_c' =
    fresh (state id state' id')
    (state_c === inj (state, id))
    (st_add_arg state state_before id arg_tag arg state')
    (id' === Nat.s id)
    (state_c' === inj (state', id'))

  and eval_fun state prog decl args state' =
    fresh (arg_tags body
           env_before mem_before len_before assignments_before
           state_clean
           state_with_vars counter_
           state_evaled
           state_spoiled
           env_ mem_spoiled len assignments_
           mem_updated len_to_drop)
    (decl === inj (arg_tags, body))
    (state === inj (env_before, mem_before, len_before, assignments_before))
    (state_clean === inj (Std.nil (), mem_before, len_before, Std.nil ()))
    (list_foldl2 (add_arg_folder state) (inj (state, Nat.o)) arg_tags args (inj (state_with_vars, counter_))) (* TODO: replace with real placeholder *)
    (eval_body state_with_vars prog body state_evaled)
    (st_spoil_assignments state_evaled state_spoiled)
    (state_spoiled === inj (env_, mem_spoiled, len, assignments_))
    (Nat.addo len_to_drop len_before len)
    (list_drop len_to_drop mem_spoiled mem_updated)
    (state' === inj (env_before, mem_updated, len_before, assignments_before))

  and eval_fun_empty_args state prog decl state' =
    fresh (arg_tags args hole_) (* TODO: replace with real placeholder *)
    (decl === inj (arg_tags, hole_))
    (List.mapo arg_to_rvalue arg_tags args)
    (eval_fun state prog decl args state')

  (* --- *)

  let empty_state state = (state === inj (Std.nil (), Std.nil (), Nat.o, Std.nil ()))

  let eval_prog all_prog state' =
    fresh (prog main_decl state)
    (all_prog === inj (prog, main_decl))
    (empty_state state)
    (eval_fun_empty_args state prog main_decl state')
end
