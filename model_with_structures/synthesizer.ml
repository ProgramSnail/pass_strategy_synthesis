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

  module ReadCap = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = Rd | NRd
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]
  end

  module WriteCap = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = AlwaysWr | MayWr | NeverWr
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]
  end

  (* NOTE: rename names ?? *)
  module CopyCap = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = Ref | Val
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]

  end

  module InCap = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = In | NIn
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]
  end

  module OutCap = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = Out | NOut
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = t
    ]
  end

  module Tag = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('r, 'w, 'c, 'i, 'o) t = Tag of 'r * 'w * 'c * 'i * 'o
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (ReadCap.ground, WriteCap.ground, CopyCap.ground, InCap.ground, OutCap.ground) t
    ]

    (* TODO: less repeats *)
    (* common constructors *)
    let rwi_val = let open ReadCap in
                  let open WriteCap in
                  let open CopyCap in
                  let open InCap in
                  let open OutCap in
                  ocanren { Tag (Rd, AlwaysWr, Val, In, NOut) }
    let ri_val = let open ReadCap in
                 let open WriteCap in
                 let open CopyCap in
                 let open InCap in
                 let open OutCap in
                 ocanren { Tag (Rd, NeverWr, Val, In, NOut) }
    let wi_val = let open ReadCap in
                 let open WriteCap in
                 let open CopyCap in
                 let open InCap in
                 let open OutCap in
                 ocanren { Tag (NRd, AlwaysWr, Val, In, NOut) }
    let i_val = let open ReadCap in
                let open WriteCap in
                let open CopyCap in
                let open InCap in
                let open OutCap in
                ocanren { Tag (NRd, NeverWr, Val, In, NOut) }
    let rwi_ref = let open ReadCap in
                  let open WriteCap in
                  let open CopyCap in
                  let open InCap in
                  let open OutCap in
                  ocanren { Tag (Rd, AlwaysWr, Ref, In, NOut) }
    let ri_ref = let open ReadCap in
                 let open WriteCap in
                 let open CopyCap in
                 let open InCap in
                 let open OutCap in
                 ocanren { Tag (Rd, NeverWr, Ref, In, NOut) }
    let wi_ref = let open ReadCap in
                 let open WriteCap in
                 let open CopyCap in
                 let open InCap in
                 let open OutCap in
                 ocanren { Tag (NRd, AlwaysWr, Ref, In, NOut) }
    let i_ref = let open ReadCap in
                let open WriteCap in
                let open CopyCap in
                let open InCap in
                let open OutCap in
                ocanren { Tag (NRd, NeverWr, Ref, In, NOut) }

    (* constraints *)
    let x_any tag = let open InCap in
                    let open OutCap in
                    ocanren { fresh r, w, c in
                              tag == Tag (r, w, c, NIn, NOut) }
    let i_any tag = let open InCap in
                    let open OutCap in
                    ocanren { fresh r, w, c in
                              tag == Tag (r, w, c, In, NOut) }
    let o_any tag = let open InCap in
                    let open OutCap in
                    ocanren { fresh r, w, c in
                              tag == Tag (r, w, c, NIn, Out) }
    let io_any tag = let open InCap in
                     let open OutCap in
                     ocanren { fresh r, w, c in
                               tag == Tag (r, w, c, In, Out) }

    (* accessors *)
    let is_reado tag = let open ReadCap in ocanren {
                         fresh w_, c_, i_, o_ in
                         tag == Tag (Rd, w_, c_, i_, o_) }
    let is_not_reado tag = let open ReadCap in ocanren {
                             fresh w_, c_, i_, o_ in
                             tag == Tag (NRd, w_, c_, i_, o_) }
    let is_always_writeo tag = let open WriteCap in ocanren {
                                 fresh r_, c_, i_, o_ in
                                 tag == Tag (r_, AlwaysWr, c_, i_, o_) }
    let is_may_writeo tag = let open WriteCap in ocanren {
                              fresh r_, c_, i_, o_ in
                              { tag == Tag (r_, AlwaysWr, c_, i_, o_) |
                                tag == Tag (r_, MayWr, c_, i_, o_) } }
    let is_never_writeo tag = let open WriteCap in ocanren {
                                fresh r_, c_, i_, o_ in
                                tag == Tag (r_, NeverWr, c_, i_, o_) }
    let is_refo tag = let open CopyCap in ocanren {
                        fresh r_, w_, i_, o_ in
                        tag == Tag (r_, w_, Ref, i_, o_) }
    let is_valueo tag = let open CopyCap in ocanren {
                          fresh r_, w_, i_, o_ in
                          tag == Tag (r_, w_, Val, i_, o_) }
    let is_ino tag = let open InCap in ocanren {
                       fresh r_, w_, c_, o_ in
                       tag == Tag (r_, w_, c_, In, o_) }
    let is_not_ino tag = let open InCap in ocanren {
                           fresh r_, w_, c_, o_ in
                           tag == Tag (r_, w_, c_, NIn, o_) }
    let is_outo tag = let open OutCap in ocanren {
                        fresh r_, w_, c_, i_ in
                        tag == Tag (r_, w_, c_, i_, Out) }
    let is_not_outo tag = let open OutCap in ocanren {
                            fresh r_, w_, c_, i_ in
                            tag == Tag (r_, w_, c_, i_, NOut) }

    let eq_copyo tag cp = let open CopyCap in ocanren {
                           fresh r_, w_, i_, o_ in
                           tag == Tag (r_, w_, cp, i_, o_) }

    module Test = struct
      @type answer = logic GT.list with show

      let test _ = show(answer) (Stream.take (run q (fun q -> let open ReadCap in
                                                              let open WriteCap in
                                                              let open CopyCap in
                                                              let open InCap in
                                                              let open OutCap in
                                                              ocanren {q == Tag (Rd, NeverWr, Ref, In, NOut)})
                                                    (fun q -> q#reify reify)))
    end
  end

  module Stmt = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('d, 'dl, 'sl) t = Call of 'd * 'dl | Read of 'd | Write of 'd | Choice of 'sl * 'sl
      [@@deriving gt ~options:{ show; gmap }]
      type ground = (Nat.ground, Nat.ground List.ground, ground List.ground) t
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
                                                              ocanren {FunDecl ([rwi_ref; rwi_val], [Call (1, [0]); Write 1]) == q})
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
                                                              ocanren {Prog ([], FunDecl ([ri_val], [Write 0; Read 0])) == q})
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
      type nonrec t = Unit | Undef | Bot
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
      type nonrec ('env, 'mem, 'last_mem, 'visited) t = St of 'env * 'mem * 'last_mem * 'visited
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (((Nat.ground, ((Tag.ground, Nat.ground) Pair.ground)) Pair.ground) List.ground,
                            Value.ground List.ground, Nat.ground, Nat.ground List.ground) t
    ]

    module Test = struct
      @type answer  = ground GT.list with show
      let test _ = show(answer) (Stream.take (run q (fun q -> let open Value in
                                                              let open Tag in
                                                              ocanren {St ([Std.pair 0 (Std.pair rwi_val 0)], [Bot], 1, [0]) == q})
                                                    (fun q -> q#reify (prj_exn))))
    end
  end

  (* --- *)

  let rec list_zip_witho f xs ys zs = ocanren {
    { fresh x, xs', y, ys', z, zs' in
      xs == x :: xs' &
      ys == y :: ys' &
      zs == z :: zs' &
      f x y z &
      list_zip_witho f xs' ys' zs' } |
    { fresh x, xs' in
      xs == x :: xs' &
      ys == [] &
      zs == [] } |
    { fresh y, ys' in
      xs == [] &
      ys == y :: ys' &
      zs == [] } |
    { xs == [] & ys == [] & zs == [] }
  }

  (* --- *)

  let value_combineo left right res = let open Value in ocanren {
    { left == Unit & right == Unit & res == Unit } |
    { left == Bot & right == Bot & res == Bot } |
    { left == Unit & right == Bot & res == Undef } |
    { left == Bot & right == Unit & res == Undef }
  }

  let memory_combineo left right res = ocanren {
    list_zip_witho value_combineo left right res
  }

  let state_combineo left right res = let open St in ocanren {
    fresh lenv, lmem, lmem_len, lvisited, renv, rmem, rmem_len, rvisited, res_mem in
    left == St (lenv, lmem, lmem_len, lvisited) &
    right == St (renv, rmem, rmem_len, rvisited) &
    lenv == renv & lmem_len == rmem_len &
    memory_combineo lmem rmem res_mem  &
    res == St (lenv, rmem, lmem_len, List.appendo lvisited rvisited)
    (* TODO: union visited lists instead ? *)
  }

  (* --- *)

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

  let env_geto state id tag' mem_id' =
    let open St in
    ocanren {
    fresh env, _mem, _mem_len, _visited, elem in
      state == St (env, _mem, _mem_len, _visited) &
      List.assoco id env elem &
      Std.pair tag' mem_id' == elem
  }

  let env_addo state id tg mem_id state' =
    let open St in
    ocanren {
    fresh env, env', mem, mem_len, visited, elem in
      state == St (env, mem, mem_len, visited) &
      Std.pair tg mem_id == elem & 
      (Std.pair id elem) :: env == env' &
      state' == St (env', mem, mem_len, visited)
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
    fresh mem, mem_len, mem_id, mem_id_inv, _env, _visited, _tag in
    state == St (_env, mem, mem_len, _visited) &
    env_geto state id _tag mem_id &
    inv_ido mem_len mem_id mem_id_inv &
    list_ntho mem mem_id_inv value'
  }

  let mem_seto state id value state'=
    let open St in
    ocanren {
    fresh env, mem, mem_len, visited, mem_id, inv_mem_id, mem', _tag in
      state == St (env, mem, mem_len, visited) &
      env_geto state id _tag mem_id &
      inv_ido mem_len mem_id inv_mem_id &
      list_replaceo mem inv_mem_id value mem' &
      state' == St (env, mem', mem_len, visited)
  }

  let mem_addo state value state' =
    let open St in
    ocanren {
      fresh env, mem, mem_len, mem_len', visited, mem' in
      state == St (env, mem, mem_len, visited) &
      mem' == value :: mem &
      mem_len' == Nat.s mem_len &
      state' == St (env, mem', mem_len', visited)
  }

  let mem_checko state id =
    let open Value in
    ocanren {
      mem_geto state id Unit
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

  let arg_to_rvalueo arg value' =
    let open Arg in
    let open Tag in
    ocanren { is_valueo arg & value' == RValue }

  let st_mem_leno state mem_len' =
    let open St in
    ocanren {
    fresh _env, _mem, _visited in
      state == St (_env, _mem, mem_len', _visited)
  }

  let tag_correcto tg =
    let open Tag in
    ocanren {
      {is_not_outo tg | { is_outo tg & is_always_writeo tg } } &
      {is_not_reado tg | { is_reado tg & is_ino tg } }
    }

  let st_add_argo state state_before id arg_tag arg state'' =
    (* let open Nat in *)
    let open Value in
    let open Arg in
    let open Tag in
    ocanren {
        tag_correcto arg_tag & {
        { fresh value', state', mem_len_prev' in
          is_valueo arg_tag &
          arg_to_valueo state_before arg value' &
          mem_addo state value' state' &
          st_mem_leno state mem_len_prev' &
          env_addo state' id arg_tag mem_len_prev' state'' } |
        { fresh arg', parent_tag, mem_id, state' in
          is_refo arg_tag &
            (* { arg == RValue } *) (* NOTE: not allowed for now *)
          arg == LValue arg' &
          env_geto state_before id parent_tag mem_id &
          env_addo state id arg_tag mem_id state' &
          { is_never_writeo arg_tag | { is_may_writeo arg_tag & is_may_writeo parent_tag } } &
          {
            { is_reado arg_tag & state' == state'' } |
            { is_not_reado arg_tag & mem_seto state' id Bot state'' }
          }
        }
      }
    }

  let st_spoil_foldero state_before state tg id state' =
    let open Value in
    let open Tag in
    let open St in
    ocanren {
      fresh env, mem, mem_len, _visited, parent_tg, _mem_id in
      state == St (env, mem, mem_len, _visited) &
      env_geto state id parent_tg _mem_id &
      { is_not_reado tg | { is_reado tg & mem_checko state_before id } } &
      { { is_never_writeo tg & state == state'} |
        { is_always_writeo tg & 
          is_outo tg & is_may_writeo parent_tg & mem_seto state id Unit state' } |
        { is_may_writeo tg & {
          { is_not_outo tg & is_valueo tg & state == state' } |
          { is_not_outo tg & is_refo tg & is_may_writeo parent_tg & mem_seto state id Bot state' }
        } }
      }
    }

  let st_spoil_by_argso state arg_tags args state' =
    ocanren {
      fresh state_before in
      state == state_before & (* TODO: required ? *)
      list_foldl2o (st_spoil_foldero state_before) state arg_tags args state'
    }

  (* let st_spoil_assignmentso state state' = *)
    (* let open St in *)
    (* ocanren { *)
    (* fresh _env, _mem, _mem_len, visited in *)
      (* state == St (_env, _mem, _mem_len, visited) & *)
      (* list_foldlo st_spoil_foldero state visited state' *)
  (* } *)

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

  let rec list_not_membero xs x = ocanren {
    xs == [] |
    { fresh x', xs' in
        xs == x' :: xs' &
        x' =/= x &
        list_not_membero xs' x }
  }

  let visited_checko state f_id =
    let open St in
    ocanren {
      fresh _env, _mem, _mem_len, visited in
      state == St (_env, _mem, _mem_len, visited) &
      List.membero visited f_id
    }

  let not_visited_checko state f_id =
    let open St in
    ocanren {
      fresh _env, _mem, _mem_len, visited in
      state == St (_env, _mem, _mem_len, visited) &
      list_not_membero visited f_id
    }

  let visited_addo state f_id state' =
    let open St in
    ocanren {
      fresh env, mem, mem_len, visited, visited' in
      state == St (env, mem, mem_len, visited) &
      visited' == f_id :: visited &
      state' == St (env,mem, mem_len, visited')
    }

  let rec eval_stmto state prog stmt state' =
    let open Stmt in
    let open Value in
    let open FunDecl in
    let open Tag in
    ocanren {
    { fresh f_id, args, f, args', state_after_call, arg_tags, _body in
      stmt == Call (f_id, args) &
      list_ntho prog f_id f &
      FunDecl (arg_tags, _body) == f &
      List.mapo arg_to_lvalueo args args' &
      (* TODO: FIXME: memoisation, do not do calls on check successfull *)
      
      (* NOTE: tmp simplification for less branching (TODO?) *)
      { { fresh state_with_visited in
          not_visited_checko state f_id &
          visited_addo state f_id state_with_visited &
          eval_funo state_with_visited prog f args' state_after_call } |
        { visited_checko state f_id &
          state_after_call == state } } &
      st_spoil_by_argso state_after_call arg_tags args state' } |
    { fresh id in stmt == Read id & mem_checko state id & state == state' } |
    { fresh id, tag, _mem_id in
      stmt == Write id &
      env_geto state id tag _mem_id &
      is_may_writeo tag &
      mem_seto state id Unit state' } |
    { fresh xs, ys in
      stmt == Choice (xs, ys) }
    (* TODO: FIXME: choice actions *)
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
          env_before, mem_before, len_before, visited_before,
          state_clean,
          state_with_vars, _counter,
          state_evaled,
          _env, _mem, _len, visited,
          nil_env, nil_visited in
      nil_env == [] &
      nil_visited == [] &
      decl == FunDecl (arg_tags, body) &
      state == St (env_before, mem_before, len_before, visited_before) &
      state_clean == St (nil_env, mem_before, len_before, nil_visited) &
      list_foldr2o (add_arg_foldero state)
                   (Std.pair state Nat.o) arg_tags args
                   (Std.pair state_with_vars _counter) & (* TODO: or foldr2o ?? *)
      eval_bodyo state_with_vars prog body state_evaled &
      state_evaled == St (_env,_mem, _len, visited) &
      state' == St (env_before, mem_before, len_before, visited)
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
    fresh nil_env, nil_mem, nil_visited in
      nil_env == [] &
      nil_visited == [] &
      nil_mem == [] &
      state == St (nil_env, nil_mem, Nat.o, nil_visited)
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
