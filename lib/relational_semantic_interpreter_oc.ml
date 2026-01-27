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

    let ref = inj Ref
    let value = inj Value
  end

  module Stmt = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('d, 'dl) t = Call of 'd * 'dl | Read of 'd | Write of 'd
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Nat.ground, Nat.ground List.ground) t
    ]

    let call f args = inj (Call (f, args))
    let read id = inj (Read id)
    let write id = inj (Write id)
  end

  module Body = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('stmt, 'l) t = T of ('stmt, 'l) List.t
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Stmt.ground, Stmt.ground List.ground) t
    ]

    let make stmts = inj (T stmts)
  end

  module FunDecl = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('l, 'b) t = T of 'l * 'b
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Tag.ground List.ground, Body.ground) t
    ]

    let make args body = inj (T (args, body))
  end

  module Prog = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('l, 'f) t = T of 'l * 'f
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (FunDecl.ground List.ground, FunDecl.ground) t
    ]

    let make decls main_decl = inj (T (decls, main_decl))
  end

  module Arg = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec 'd t = RValue | LValue of 'd
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = Nat.ground t
    ]

    let rvalue = inj RValue
    let lvalue x = inj (LValue x) 
  end

  module Value = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec t = Unit | Bot
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]

    let unit = inj Unit
    let bot = inj Bot
  end

  (* module Envr = struct *)
    (* [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"] *)
    (* [%%distrib *)
      (* type nonrec ('d, 'l) t = T of ('d * 'd, 'l) List.t *)
      (* [@@deriving gt ~options:{ show; gmap }] *)
      (* type nonrec ground = (Nat.ground, Nat.ground List.ground) t *)
    (* ] *)

    (* let make elems = inj (T elems) *)
  (* end *)

  module State = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%distrib
      type nonrec ('env, 'mem, 'last_mem, 'assignments) t = T of 'env * 'mem * 'last_mem * 'assignments
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (((Nat.ground, Nat.ground) Pair.ground) List.ground,
                            Value.ground List.ground, Nat.ground, Nat.ground List.ground) t
    ]

    let make env mem last_mem assignments = inj (T (env, mem, last_mem, assignments))
  end

  let rec list_replaceo xs id value ys = ocanren {
    (* xs == [] & ys == [] | (* TODO: error *) *)
    { fresh x, xs' in
        xs == x :: xs' &
        id == Nat.o &
        ys == value :: xs } |
    { fresh x, xs', id', ys' in
        xs == x :: xs' &
        id == Nat.s id' &
        ys == x :: ys' &
        list_replaceo xs' id' value ys' }
    }

  let rec list_assoco a xs v' = ocanren {
    { fresh a', b', xs' in
      !(List.cons (a', b') xs' === xs) &
      a =/= a' &
      list_assoco a xs' v' } |
    { fresh a', b', xs' in
      !(List.cons (a', b') xs' === xs) &
      a == a' &
      v' == b' }
  }
  (* TODO: difference from List.assoco ?? *)

  let env_geto state id mem_id' = ocanren {
    fresh env, mem, mem_len, assignments in
      state == State.make env mem mem_len assignments &
      list_assoco id env mem_id'
  }

  let env_addo state id mem_id state' = ocanren {
    fresh env, env', mem, mem_len, assignments in
      state == State.make env mem mem_len assignments &
      state' == State.make env' mem mem_len assignments &
      !(List.cons (id, mem_id) env === env')
  }

  let inv_ido mem_len id id' = ocanren {
    fresh inv_id_inc in
      Nat.addo inv_id_inc id mem_len &
      Nat.addo id' 1 inv_id_inc
  }

  (* --- *)

  let rec list_ntho xs id x' = ocanren {
    (* xs == [] | (* TODO: error *) *)
    { fresh y', xs' in
      id == Nat.o &
      y' :: xs' == xs &
      x' == y' } |
    { fresh id', y', xs' in
      Nat.s id' == id &
      y' :: xs' == xs &
      list_ntho xs' id' x' }
  }

  (* TODO: use real holes *)
  let mem_geto state id value' = ocanren {
    fresh mem, mem_len, mem_id, mem_id_inv, _env, _assignments in
    state == State.make _env mem mem_len _assignments &
    env_geto state id mem_id &
    inv_ido mem_len mem_id mem_id_inv &
    list_ntho mem mem_id_inv value'
  }

  let mem_seto state id value state'= ocanren {
    fresh env, mem, mem_len, assignments, mem_id, inv_mem_id, mem', assignments' in
      state == State.make env mem mem_len assignments &
      env_geto state id mem_id &
      inv_ido mem_len mem_id inv_mem_id &
      list_replaceo mem mem_id value mem' &
      assignments' == id :: assignments &
      state' == State.make env mem' mem_len assignments'
  }

  let mem_addo state value state' = ocanren {
    fresh env, mem, mem_len, mem_len', assignments, mem' in
      state == State.make env mem mem_len assignments &
      mem' == value :: mem &
      mem_len' == Nat.s mem_len &
      state' == State.make env mem mem_len' assignments
  }

  let mem_checko state id state' = ocanren {
    mem_geto state id Value.bot & state' == state |
    mem_geto state id Value.unit & state' == state
  }

  (* --- *)

  let rec list_foldlo f acc xs acc' = ocanren {
    xs == [] & acc' == acc |
    { fresh x', xs', acc_upd in
      xs == x' :: xs' &
      list_foldlo f acc xs' acc_upd &
      f acc_upd x' acc' }
  }


  let rec list_foldr2o f acc xs ys acc' = ocanren {
    xs == [] & ys == [] & acc' == acc |
    { fresh x', xs', y', ys', acc_upd in
      xs == x' :: xs' &
      ys == y' :: ys' &
      f acc x' y' acc_upd &
      list_foldr2o f acc_upd xs' ys' acc' }
  }

  let rec list_foldl2o f acc xs ys acc' = ocanren {
    xs == [] & ys == [] & acc' == acc |
    { fresh x', xs', y', ys', acc_upd in
      xs == x' :: xs' &
      ys == y' :: ys' &
      list_foldl2o f acc xs' ys' acc_upd &
      f acc_upd x' y' acc' }
  }

  let arg_to_valueo state arg value' = ocanren {
    arg == Arg.rvalue & value' == Value.unit |
    { fresh id in
      arg == Arg.lvalue id &
      mem_geto state id value' }
  }

  let arg_to_rvalueo _arg value' = ocanren { value' == Arg.rvalue }

  let st_mem_leno state mem_len' = ocanren {
    fresh _env, _mem, _assignments in (* TODO: replace with real placeholder ? *)
      state == State.make _env _mem mem_len' _assignments
  }

  let st_add_argo state state_before id arg_tag arg state'' = ocanren {
    (* arg_tag == Tag.ref & arg == Arg.rvalue & state'' == state | *)
      (* TODO: error, TODO: allow later ?? *)
    { fresh arg', value' in
      arg_tag == Tag.ref &
      arg == Arg.lvalue arg' &
      env_geto state_before arg' value' &
      env_addo state id value' state'' } |
    { fresh value', state', mem_len_dec' in
      arg_tag == Tag.value &
      arg_to_valueo state_before arg value' &
      mem_addo state value' state' &
      st_mem_leno state (Nat.s mem_len_dec') &
      env_addo state' id mem_len_dec' state'' }
  }

  let st_spoil_foldero mem_len state mem id mem' = ocanren {
    fresh mem_id', mem_id_inv' in
      env_geto state id mem_id' &
      inv_ido mem_len mem_id' mem_id_inv' &
      list_replaceo mem mem_id_inv' Value.bot mem'
  }

  let st_spoil_assignmentso state state' = ocanren {
    fresh env, mem, mem', mem_len, assignments, nil' in
      state == State.make env mem mem_len assignments &
      list_foldlo (st_spoil_foldero mem_len state) mem assignments mem' &
      nil' == [] &
      state' == State.make env mem' mem_len nil'
  }

  (* --- *)

  let arg_to_lvalueo arg arg' = ocanren {
    arg' == Arg.lvalue arg
  }

  let rec list_dropo n xs xs' = ocanren {
    xs == [] & xs' == [] |
    n == Nat.o & xs == xs' |
    { fresh n', y, ys in
        Nat.s n' == n &
        xs == y :: ys &
        list_dropo n' ys xs' }
  }

  let rec eval_stmto state prog stmt state' = ocanren {
    { fresh f_id, args, f, args' in
      stmt == Stmt.call f_id args &
      list_ntho prog f_id f &
      List.mapo arg_to_lvalueo args args' &
      eval_funo state prog f args' state' } |
    { fresh id in stmt == Stmt.read id & mem_checko state id state' } |
    { fresh id in stmt === Stmt.write id & mem_seto state id Value.unit state' }
  }

  and eval_body_foldero prog state stmt state' =
    eval_stmto state prog stmt state'

  and eval_bodyo state prog body state' =
    list_foldlo (eval_body_foldero prog) state body state' 
    (* (List.fold_left (fun state stmt -> eval_stmt state prog stmt) state body) *)

  (* TODO: other types on translation to ocanren ? *)
  and add_arg_foldero state_before state_c arg_tag arg state_c' = ocanren {
    fresh state, id, state', id' in
      state_c == (state, id) &
      st_add_argo state state_before id arg_tag arg state' &
      id' == Nat.s id &
      state_c' == (state', id')
  }

  and eval_funo state prog decl args state' = ocanren {
    fresh arg_tags, body,
          env_before, mem_before, len_before, assignments_before,
          state_clean,
          state_with_vars, _counter,
          state_evaled,
          state_spoiled,
          _env, mem_spoiled, len, _assignments,
          mem_updated, len_to_drop,
          nil_env, nil_assignments in
      nil_env == [] &
      nil_assignments == [] &
      decl == FunDecl.make arg_tags body &
      state == State.make env_before mem_before len_before assignments_before &
      state_clean == State.make nil_env mem_before len_before nil_assignments &
      list_foldl2o (add_arg_foldero state) (state, Nat.o) arg_tags args (state_with_vars, _counter) & (* TODO: replace with real placeholder *)
      eval_bodyo state_with_vars prog body state_evaled &
      st_spoil_assignmentso state_evaled state_spoiled &
      state_spoiled == State.make _env mem_spoiled len _assignments &
      Nat.addo len_to_drop len_before len &
      list_dropo len_to_drop mem_spoiled mem_updated &
      state' == State.make env_before mem_updated len_before assignments_before
  }

  and eval_fun_empty_argso state prog decl state' = ocanren {
    fresh arg_tags, args, _hole in (* TODO: replace with real placeholder *)
      decl == FunDecl.make arg_tags _hole &
      List.mapo arg_to_rvalueo arg_tags args &
      eval_funo state prog decl args state'
  }

  (* --- *)

  let empty_stateo state = ocanren {
    fresh nil_env, nil_mem, nil_assignments in
      nil_env == [] &
      nil_assignments == [] &
      nil_mem == [] &
      state == State.make nil_env nil_mem Nat.o nil_assignments
  }

  let eval_progo all_prog state' = ocanren {
    fresh prog, main_decl, state in
      all_prog == Prog.make prog main_decl &
      empty_stateo state &
      eval_fun_empty_argso state prog main_decl state'
  }
end
