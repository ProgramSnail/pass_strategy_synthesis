(* (,,) -< Pair.inj _ (Pair.inj _ _) *)

module Relational =
struct
  open GT
  open OCanren
  open OCanren.Std

  type data_ground = Nat.ground (* with show, gmap *)
  [@@deriving gt ~options:{ show; gmap }]
  type data_logic = Nat.logic
  [@@deriving gt ~options:{ show; gmap }]
  type data_injected = Nat.injected

  module Tag = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec t = Ref | Value
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]
  end

  module Stmt = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('d, 'dl) t = Call of 'd * 'dl | Read of 'd | Write of 'd
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Nat.ground, Nat.ground List.ground) t
    ]
  end

  module Body = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('stmt, 'l) t = Body of ('stmt, 'l) List.t
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Stmt.ground, Stmt.ground List.ground) t
    ]
  end

  module FunDecl = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('tag, 'lt, 'stmt, 'ls) t = FunDecl of ('tag, 'lt) List.t * ('stmt, 'ls) Body.t
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Tag.ground, Tag.ground List.ground, Stmt.ground, Stmt.ground List.ground) t
    ]
  end

  module Prog = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('fd, 'lf, 'tag, 'lt, 'stmt, 'ls) t = Prog of ('fd, 'lf) List.t * ('tag, 'lt, 'stmt, 'ls) FunDecl.t
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (FunDecl.ground, FunDecl.ground List.ground, Tag.ground, Tag.ground List.ground, Stmt.ground, Stmt.ground List.ground) t
    ]
  end

  module Arg = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec 'd t = RValue | LValue of 'd
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = Nat.ground t
    ]
  end

  module Value = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec t = Unit | Bot
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]
  end

  module Envr = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('d, 'l) t = Envr of ('d * 'd, 'l) List.t
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Nat.ground, Nat.ground List.ground) t
    ]
  end

  module State = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('env, 'mem, 'last_mem, 'assignments) t = State of 'env * 'mem * 'last_mem * 'assignments
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Envr.ground, Value.ground List.ground, Nat.ground, Nat.ground List.ground) t
    ]
  end

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
  (* TODO: difference from List.assoco ?? *)

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
    [ (mem_get state id (inj Value.Bot)) &&& (state' === state) (* TODO: error *)
    ; (mem_get state id (inj Value.Unit)) &&& (state' === state)
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
    [ (arg === inj Arg.RValue) &&& (value' === inj Value.Unit)
    ; fresh (id) (arg === inj (Arg.LValue id)) (mem_get state id value')
    ]

  let arg_to_rvalue _arg value' = (value' === inj Arg.RValue)

  let st_mem_len state mem_len' =
    fresh (env_ mem_ assignments_) (* TODO: replace with real placeholder ? *)
    (state === inj (env_, mem_, mem_len', assignments_))

  let st_add_arg state state_before id arg_tag arg state'' =
    conde
    [ (arg_tag === inj Tag.Ref) &&& (arg === inj Arg.RValue) &&& (state'' === state)
      (* TODO: error, TODO: allow later ?? *)
    ; fresh (arg' value')
      (arg_tag === inj Tag.Ref)
      (arg === inj (Arg.LValue arg'))
      (env_get state_before arg' value')
      (env_add state id value' state'')
    ; fresh (value' state' mem_len_dec')
      (arg_tag === inj Tag.Value)
      (arg_to_value state_before arg value')
      (mem_add state value' state')
      (st_mem_len state (Nat.s mem_len_dec'))
      (env_add state' id mem_len_dec' state'')
    ]

  let st_spoil_folder mem_len state mem id mem' =
    fresh (mem_id' mem_id_inv')
    (env_get state id mem_id')
    (inv_id mem_len mem_id' mem_id_inv')
    (list_replace mem mem_id_inv' (inj Value.Bot) mem')

  let st_spoil_assignments state state' =
    fresh (env mem mem' mem_len assignments)
    (state === inj (env, mem, mem_len, assignments))
    (list_foldl (st_spoil_folder mem_len state) mem assignments mem')
    (* (List.fold_left (fun mem id -> list_replace mem (inv_id mem_len @@ env_get state id) BotV) mem assignments mem') *)
    (state' === inj (env, mem', mem_len, Std.nil ()))

  (* --- *)

  let arg_to_lvalue arg arg' = (arg' === inj (Arg.LValue arg))

  let rec list_drop n xs xs' =
    conde
    [ (xs === Std.nil ()) &&& (xs' === Std.nil ())
    ; n === Nat.o &&& (xs === xs')
    ; fresh (n' y ys) (Nat.s n' === n) (xs === List.cons y ys) (list_drop n' ys xs')
    ]

  let rec eval_stmt state prog stmt state' =
    conde
    [ fresh (f_id args f args')
      (stmt === inj (Stmt.Call (f_id, args)))
      (list_nth prog f_id f)
      (List.mapo arg_to_lvalue args args')
      (eval_fun state prog f args' state')
    ; fresh (id) (stmt === inj (Stmt.Read id)) (mem_check state id state')
    ; fresh (id) (stmt === inj (Stmt.Write id)) (mem_set state id (inj Value.Unit) state')
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

  (* let eval_prog_fwd all_prog = *)
    (* run q (fun q -> eval_prog (inj_state all_prog) q) *)
          (* (fun _ -> ()) *)

  (* let%expect_test "empty" = *)
    (* eval_prog_fwd ([], ([], [])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

end
