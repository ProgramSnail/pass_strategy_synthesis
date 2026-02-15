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
    [%%ocanren_inject
      type nonrec t = Ref | Val
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]

    module Test = struct
      @type answer = logic GT.list with show

      let test _ = show(answer) (Stream.take (run q (fun q -> ocanren {q == Ref})
                                                    (fun q -> q#reify reify)))
    end
  end

  module Stmt = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('d, 'dl) t = Call of 'd * 'dl | Read of 'd | Write of 'd
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Nat.ground, Nat.ground List.ground) t
    ]

    module Test = struct
      @type answer = Nat.ground List.ground GT.list with show
      @type answer'  = ground GT.list with show

      let test1 _ = show(answer) (Stream.take (run q (fun q -> ocanren {Call (1, [2]) == Call (1, q)})
                                                     (fun q -> q#reify (List.prj_exn Nat.prj_exn))))

      let test2 _ = show(answer') (Stream.take (run q (fun q -> ocanren {Call (1, [2]) == q})
                                                      (fun q -> q#reify (prj_exn))))
    end
  end

  module FunDecl = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('l, 'b) t = FunDecl of 'l * 'b
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Tag.ground List.ground, Stmt.ground List.ground) t
    ]

    module Test = struct
      @type answer  = ground GT.list with show
      let test _ = show(answer) (Stream.take (run q (fun q -> let open Tag in
                                                              let open Stmt in
                                                              ocanren {FunDecl ([Ref; Val], [Call (1, [0]); Write 1]) == q})
                                                    (fun q -> q#reify (prj_exn))))
    end
  end

  module Prog = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('l, 'f) t = Prog of 'l * 'f
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (FunDecl.ground List.ground, FunDecl.ground) t
    ]

    module Test = struct
      @type answer  = ground GT.list with show
      let test _ = show(answer) (Stream.take (run q (fun q -> let open FunDecl in
                                                              let open Tag in
                                                              let open Stmt in
                                                              ocanren {Prog ([], FunDecl ([Val], [Write 0; Read 0])) == q})
                                                    (fun q -> q#reify (prj_exn))))
    end
  end

  module Arg = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec 'd t = RValue | LValue of 'd
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = Nat.ground t
    ]

    module Test = struct
      @type answer = logic GT.list with show
      let test _ = show(answer) (Stream.take (run q (fun q -> ocanren {q == LValue 3})
                                                    (fun q -> q#reify reify)))
    end
  end

  module Value = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = Unit | Bot
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]

    module Test = struct
      @type answer = logic GT.list with show
      let test _ = show(answer) (Stream.take (run q (fun q -> ocanren {q == Bot | q == Unit})
                                                    (fun q -> q#reify reify)))
    end
  end

  module St = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('env, 'mem, 'last_mem, 'assignments) t = St of 'env * 'mem * 'last_mem * 'assignments
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (((Nat.ground, Nat.ground) Pair.ground) List.ground,
                            Value.ground List.ground, Nat.ground, Nat.ground List.ground) t
    ]

    module Test = struct
      @type answer  = ground GT.list with show
      let test _ = show(answer) (Stream.take (run q (fun q -> let open Value in
                                                              ocanren {St ([Std.pair 0 0], [Bot], 1, [0]) == q})
                                                    (fun q -> q#reify (prj_exn))))
    end
  end

  let rec list_replaceo xs id value ys = ocanren {
    (* xs == [] & ys == [] | (* NOTE: error *) *)
    { fresh x, xs' in
        xs == x :: xs' &
        id == Nat.o &
        ys == value :: xs' } |
    { fresh x, xs', id', ys' in
        xs == x :: xs' &
        id == Nat.s id' &
        ys == x :: ys' &
        list_replaceo xs' id' value ys' }
    }

  (* let rec list_assoco a xs v' = *)
    (* ocanren { *)
    (* fresh a', b', xs' in *)
      (* (Std.pair a' b') :: xs' == xs & *)
      (* { a =/= a' & list_assoco a xs' v' | *)
        (* a == a' & v' == b' } *)
  (* } *)
  (* TODO: difference from List.assoco ?? *)

  let env_geto state id mem_id' =
    let open St in
    ocanren {
    fresh env, mem, mem_len, assignments in
      state == St (env, mem, mem_len, assignments) &
      List.assoco id env mem_id'
  }

  let env_addo state id mem_id state' =
    let open St in
    ocanren {
    fresh env, env', mem, mem_len, assignments in
      state == St (env, mem, mem_len, assignments) &
      state' == St (env', mem, mem_len, assignments) &
      (Std.pair id mem_id) :: env == env'
  }

  let inv_ido mem_len id id' = ocanren {
    fresh inv_id_inc in
      Nat.addo inv_id_inc id mem_len &
      Nat.addo id' 1 inv_id_inc
  }

  (* --- *)

  let rec list_ntho xs id x' = ocanren {
    (* xs == [] | (* NOTE: error *) *)
    { fresh y', xs' in
      id == Nat.o &
      y' :: xs' == xs &
      x' == y' } |
    { fresh id', y', xs' in
      Nat.s id' == id &
      y' :: xs' == xs &
      list_ntho xs' id' x' }
  }

  let mem_geto state id value' =
    let open St in
    ocanren {
    fresh mem, mem_len, mem_id, mem_id_inv, _env, _assignments in
    state == St (_env, mem, mem_len, _assignments) &
    env_geto state id mem_id &
    inv_ido mem_len mem_id mem_id_inv &
    list_ntho mem mem_id_inv value'
  }

  let mem_seto state id value state'=
    let open St in
    ocanren {
    fresh env, mem, mem_len, assignments, mem_id, inv_mem_id, mem', assignments' in
      state == St (env, mem, mem_len, assignments) &
      env_geto state id mem_id &
      inv_ido mem_len mem_id inv_mem_id &
      list_replaceo mem inv_mem_id value mem' &
      assignments' == id :: assignments &
      state' == St (env, mem', mem_len, assignments')
  }

  let mem_addo state value state' =
    let open St in
    ocanren {
    fresh env, mem, mem_len, mem_len', assignments, mem' in
      state == St (env, mem, mem_len, assignments) &
      mem' == value :: mem &
      mem_len' == Nat.s mem_len &
      state' == St (env, mem', mem_len', assignments)
  }

  let mem_checko state id state' =
    let open Value in
    ocanren {
    mem_geto state id Unit & state' == state
  }

  (* --- *)

  let rec list_foldlo f acc xs acc' = ocanren {
    xs == [] & acc' == acc |
    { fresh x', xs', acc_upd in
      xs == x' :: xs' &
      list_foldlo f acc xs' acc_upd &
      f acc_upd x' acc' }
  }

  let rec list_foldro f acc xs acc' = ocanren {
    xs == [] & acc' == acc |
    { fresh x', xs', acc_upd in
      xs == x' :: xs' &
      f acc x' acc_upd &
      list_foldro f acc_upd xs' acc' }
    (* TODO: inf search on swap, investigate *)
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

  let arg_to_valueo state arg value' =
    let open Arg in
    let open Value in
    ocanren {
    arg == RValue & value' == Unit |
    { fresh id in
      arg == LValue id &
      mem_geto state id value' }
  }

  let arg_to_rvalueo _arg value' =
    let open Arg in
    ocanren { value' == RValue }

  let st_mem_leno state mem_len' =
    let open St in
    ocanren {
    fresh _env, _mem, _assignments in
      state == St (_env, _mem, mem_len', _assignments)
  }

  let st_add_argo state state_before id arg_tag arg state'' =
    (* let open Nat in *)
    let open Arg in
    let open Tag in
    ocanren {
    (* arg_tag == Tag.ref & arg == Arg.rvalue & state'' == state | *)
      (* NOTE: error, TODO: allow later ?? *)
    { fresh arg', value' in
      arg_tag == Ref &
      arg == LValue arg' &
      env_geto state_before arg' value' &
      env_addo state id value' state'' } |
    { fresh value', state', mem_len_prev' in
      arg_tag == Val &
      arg_to_valueo state_before arg value' &
      mem_addo state value' state' &
      st_mem_leno state mem_len_prev' &
      env_addo state' id mem_len_prev' state'' }
  }

  let st_spoil_foldero state id state' =
    let open Value in
    ocanren {
    mem_seto state id Bot state'
  }

  let st_spoil_assignmentso state state' =
    let open St in
    ocanren {
    fresh _env, _mem, _mem_len, assignments in
      state == St (_env, _mem, _mem_len, assignments) &
      list_foldlo st_spoil_foldero state assignments state'
  }

  (* --- *)

  let arg_to_lvalueo arg arg' =
    let open Arg in
    ocanren { arg' == LValue arg }

  let rec list_dropo n xs xs' = ocanren {
    xs == [] & xs' == [] |
    n == Nat.o & xs == xs' & xs =/= [] |
    { fresh n', _y, ys in
        Nat.s n' == n &
        xs == _y :: ys &
        list_dropo n' ys xs' }
  }

  let rec eval_stmto state prog stmt state' =
    let open Stmt in
    let open Value in
    ocanren {
    { fresh f_id, args, f, args' in
      stmt == Call (f_id, args) &
      list_ntho prog f_id f &
      List.mapo arg_to_lvalueo args args' &
      eval_funo state prog f args' state' } |
    { fresh id in stmt == Read id & mem_checko state id state' } |
    { fresh id in stmt === Write id & mem_seto state id Unit state' }
  }

  and eval_body_foldero prog state stmt state' =
    eval_stmto state prog stmt state'

  and eval_bodyo state prog body state' =
    list_foldro (eval_body_foldero prog) state body state' 

  and add_arg_foldero state_before state_c arg_tag arg state_c' =
    ocanren {
    fresh state, id, state', id' in
      state_c == Std.pair state id &
      st_add_argo state state_before id arg_tag arg state' &
      id' == Nat.s id &
      state_c' == Std.pair state' id'
  }

  and eval_funo state prog decl args state' =
    let open FunDecl in
    let open St in
    ocanren {
    fresh arg_tags, body,
          env_before, mem_before, len_before, assignments_before,
          state_clean,
          state_with_vars, _counter,
          state_evaled,
          state_spoiled,
          _env, mem_spoiled, len, _assignments,
          mem_updated,
          len_to_drop,
          nil_env, nil_assignments in
      nil_env == [] &
      nil_assignments == [] &
      decl == FunDecl (arg_tags, body) &
      state == St (env_before, mem_before, len_before, assignments_before) &
      state_clean == St (nil_env, mem_before, len_before, nil_assignments) &
      list_foldl2o (add_arg_foldero state) (Std.pair state Nat.o) arg_tags args (Std.pair state_with_vars _counter) & (* TODO: or foldr2o ?? *)
      eval_bodyo state_with_vars prog body state_evaled &
      st_spoil_assignmentso state_evaled state_spoiled &
      state_spoiled == St (_env, mem_spoiled, len, _assignments) &
      Nat.addo len_to_drop len_before len &
      list_dropo len_to_drop mem_spoiled mem_updated &
      state' == St (env_before, mem_updated, len_before, assignments_before)
  }

  and eval_fun_empty_argso state prog decl state' =
    let open FunDecl in
    ocanren {
    fresh arg_tags, args, _body in
      decl == FunDecl (arg_tags, _body) &
      List.mapo arg_to_rvalueo arg_tags args &
      eval_funo state prog decl args state'
  }

  (* --- *)

  let empty_stateo state =
    let open St in
    ocanren {
    fresh nil_env, nil_mem, nil_assignments in
      nil_env == [] &
      nil_assignments == [] &
      nil_mem == [] &
      state == St (nil_env, nil_mem, Nat.o, nil_assignments)
  }

  let eval_progo all_prog state' =
    let open Prog in
    ocanren {
    fresh prog, main_decl, state in
      all_prog == Prog (prog, main_decl) &
      empty_stateo state &
      eval_fun_empty_argso state prog main_decl state'
  }
end
