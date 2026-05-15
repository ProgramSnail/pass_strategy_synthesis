(* NOTE: in previous models foldl & foldr are probably spapped
   <- TODO: fix ? *)

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

  module CopyCap = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = Rf | Cp
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

  module Mode = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('i, 'o) t = Mode of 'i * 'o
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (InCap.ground, OutCap.ground) t
    ]

    (* constructors *)
    let n_val = let open InCap in
                let open OutCap in
                ocanren { Mode (NIn, NOut) }
    let i_val = let open InCap in
                let open OutCap in
                ocanren { Mode (In, NOut) }
    let o_val = let open InCap in
                let open OutCap in
                ocanren { Mode (NIn, Out) }
    let io_val = let open InCap in
                 let open OutCap in
                 ocanren { Mode (In, Out) }

    (* accessors *)
    let is_ino m = let open InCap in ocanren {
                     fresh o_ in
                     m == Mode (In, o_) }
    let is_not_ino m = let open InCap in ocanren {
                         fresh o_ in
                         m == Mode (NIn, o_) }
    let is_outo m = let open OutCap in ocanren {
                      fresh i_ in
                      m == Mode (i_, Out) }
    let is_not_outo m = let open OutCap in ocanren {
                          fresh i_ in
                          m == Mode (i_, NOut) }

    (* module Test = struct *)
      (* @type answer = logic GT.list with show *)

      (* let test _ = show(answer) (Stream.take (run q (fun q -> let open InCap in *)
                                                              (* let open OutCap in *)
                                                              (* ocanren {q == Mode (In, NOut)}) *)
                                                    (* (fun q -> q#reify reify))) *)
    (* end *)
  end

  module Path = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('d, 'p) t = VarP of 'd | DerefP of 'p | AccessP of 'p * 'd
      [@@deriving gt ~options:{ show; gmap }]
      type ground = (Nat.ground, ground) t
    ]
  end

  module Type = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('r, 'w, 'c, 't, 'tl, 'mtl) t = UnitT of 'r * 'w | RefT of 'c * 't | TupleT of 'tl | FunT of 'mtl
      [@@deriving gt ~options:{ show; gmap }]
      type ground = (ReadCap.ground, WriteCap.ground, CopyCap.ground, ground, ground List.ground, (Mode.ground * ground) List.ground) t
    ]
  end

  (* moded type - no separated type ? *)

  module Expr = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('d, 'p, 'el) t = UnitE | PathE of 'p | RefE of 'd | TupleE of 'el
      [@@deriving gt ~options:{ show; gmap }]
      type ground = (Nat.ground, Path.ground, ground List.ground) t
    ]
  end

  module Stmt = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('p, 'el, 's) t = SkipS | CallS of 'p * 'el | WriteS of 'p | ReadS of 'p | SeqS of 's * 's | ChoiceS of 's * 's
      [@@deriving gt ~options:{ show; gmap }]
      type ground = (Path.ground, Expr.ground List.ground, ground) t
    ]
  end

  (* TODO: list of 3 is not impelmented ?, replaced with two lists for now *)
  module Decl = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ((* 'd, *) 't, 'e, (* 'dl, *) 'mtl, 's) t = VarD of (* 'd * *) 't * 'e | FunD of (* 'd * 'dl * *) 'mtl * 's
      [@@deriving gt ~options:{ show; gmap }]
      type ground = ((* Nat.ground, *) Type.ground, Expr.ground, (* Nat.ground List.ground, *) (Mode.ground * Type.ground) List.ground, Stmt.ground) t
    ]
  end

  module Prg = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('dl, 's) t = Prg of 'dl * 's
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Decl.ground List.ground, Stmt.ground) t
    ]
  end

  (* NOTE: deepvalue - not used (?) *)

  module MemVal = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = ZeroMV | SmthMV | BotMV
      [@@deriving gt ~options:{ show; gmap }]
      type ground = t
    ]
  end

  module ReadVal = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = ZeroRV | OneRV | TopRV
      [@@deriving gt ~options:{ show; gmap }]
      type ground = t
    ]
  end

  module WriteVal = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = ZeroWV | SmthWV | OneWV
      [@@deriving gt ~options:{ show; gmap }]
      type ground = t
    ]
  end

  module Value = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('vm, 'vr, 'vw, 'sl, 'd, 'vl) t = UnitV of 'vm * 'vr * 'vw
                                                  | FunV of 'sl
                                                  | RefV of 'd
                                                  | TupleV of 'vl
      [@@deriving gt ~options:{ show; gmap }]
      type ground = (MemVal.ground, ReadVal.ground, WriteVal.ground,
                     ((* Nat.ground List.ground * *) Stmt.ground) List.ground,
                     Nat.ground, ground List.ground) t
    ]
  end

  module RevPath = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('d, 'p) t = VarRP | DerefRP of 'p | AccessRP of 'p * 'd
      [@@deriving gt ~options:{ show; gmap }]
      type ground = (Nat.ground, ground) t
    ]
  end

  module Action = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec t = ReadA | AlwaysWriteA | MayWriteA
      [@@deriving gt ~options:{ show; gmap }]
      type ground = t
    ]
  end

  (* --- *)

  module MemEnv = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('vl, 'd) t = MemEnv of 'vl * 'd
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Value.ground List.ground, Nat.ground) t
    ]
  end

  module TypesEnv = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec 'dtl t = TypesEnv of 'dtl (* glob *) * 'dtl (* glob + loc *)
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = ((Nat.ground * Type.ground) List.ground) t
    ]
  end

  module ValsEnv = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec 'ddl t = ValsEnv of 'ddl (* glob *) * 'ddl (* glob + loc *)
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = ((Nat.ground * Nat.ground) List.ground) t
    ]
  end

  module VisitedEnv = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec 'sl t = VisitedEnv of 'sl
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (Stmt.ground List.ground) t
    ]
  end

  module StEnv = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('mem, 'types, 'vals, 'visited) t = StEnv of 'mem * 'types * 'vals * 'visited
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (MemEnv.ground, TypesEnv.ground, ValsEnv.ground, VisitedEnv.ground) t
    ]
  end

  (* --- *)

  (* - utils *)

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

  let rec list_not_membero xs x = ocanren {
    xs == [] |
    { fresh x', xs' in
      xs == x' :: xs' &
      x' =/= x &
      list_not_membero xs' x }
  }

  let rec list_foldro f acc xs acc' = ocanren {
    xs == [] & acc' == acc |
    { fresh x', xs', acc_upd in
      xs == x' :: xs' &
      list_foldro f acc xs' acc_upd &
      f acc_upd x' acc' }
  }

  let rec list_foldlo f acc xs acc' = ocanren {
    xs == [] & acc' == acc |
    { fresh x', xs', acc_upd in
      xs == x' :: xs' &
      f acc x' acc_upd &
      list_foldlo f acc_upd xs' acc' }
    (* TODO: inf search on swap, investigate *)
  }


  let rec list_foldl2o f acc xs ys acc' = ocanren {
    xs == [] & ys == [] & acc' == acc |
    { fresh x', xs', y', ys', acc_upd in
      xs == x' :: xs' &
      ys == y' :: ys' &
      f acc x' y' acc_upd &
      list_foldl2o f acc_upd xs' ys' acc' }
  }

  let rec list_foldr2o f acc xs ys acc' = ocanren {
    xs == [] & ys == [] & acc' == acc |
    { fresh x', xs', y', ys', acc_upd in
      xs == x' :: xs' &
      ys == y' :: ys' &
      list_foldr2o f acc xs' ys' acc_upd &
      f acc_upd x' y' acc' }
  }

  let rec list_foldl3o f acc xs ys zs acc' = ocanren {
    xs == [] & ys == [] & zs == [] & acc' == acc |
    { fresh x', xs', y', ys', z', zs', acc_upd in
      xs == x' :: xs' &
      ys == y' :: ys' &
      zs == z' :: zs' &
      f acc x' y' z' acc_upd &
      list_foldl3o f acc_upd xs' ys' zs' acc' }
  }

  let rec list_foldr3o f acc xs ys zs acc' = ocanren {
    xs == [] & ys == [] & zs == [] & acc' == acc |
    { fresh x', xs', y', ys', z', zs', acc_upd in
      xs == x' :: xs' &
      ys == y' :: ys' &
      zs == z' :: zs' &
      list_foldr3o f acc xs' ys' zs' acc_upd &
      f acc_upd x' y' z' acc' }
  }

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

  (* NOTE: unrequired ? *)
  (* let list_map2o f xs ys zs = ocanren { *)
    (* { xs == [] & ys == [] } | *)
    (* { fresh x', xs', y', ys', z', zs' in *)
      (* xs == x' :: xs' & *)
      (* ys == y' :: ys' & *)
      (* f x' y' z' *)
      (* mapo f xs' ys' zs' & *)
      (* zs == z' :: zs' } *)
  (* } *)

  (* - state utils *)

  let types_assoco id types tp =
    let open TypesEnv in
    ocanren {
      fresh _glob_tps, tps in
      types == TypesEnv (_glob_tps, tps) &
      List.assoco id tps tp
    }

  let vals_assoco id vals v =
    let open ValsEnv in
    ocanren {
      fresh _glob_vs, vs in
      vals == ValsEnv (_glob_vs, vs) &
      List.assoco id vs v
    }

  let types_glob_addo types x tp types' = 
    let open TypesEnv in
    ocanren {
      fresh glob_tps, tps in
      types == TypesEnv (glob_tps, tps) &
      types' == TypesEnv ((Std.pair x tp) :: glob_tps,
                          (Std.pair x tp) :: tps)
  }

  let types_addo types x tp types' = 
    let open TypesEnv in
    ocanren {
      fresh glob_tps, tps in
      types == TypesEnv (glob_tps, tps) &
      types' == TypesEnv (glob_tps, (Std.pair x tp) :: tps)
  }

  let vals_glob_addo vals x v vals' = 
    let open ValsEnv in
    ocanren {
      fresh glob_vs, vs in
      vals == ValsEnv (glob_vs, vs) &
      vals' == ValsEnv ((Std.pair x v) :: glob_vs,
                        (Std.pair x v) :: vs)
  }

  let vals_addo vals x v vals' = 
    let open ValsEnv in
    ocanren {
      fresh glob_vs, vs in
      vals == ValsEnv (glob_vs, vs) &
      vals' == ValsEnv (glob_vs, (Std.pair x v) :: vs)
  }

  let visited_appendo visitedl visitedr visited' = 
    let open VisitedEnv in
    ocanren {
      fresh vsl, vsr, vs' in
      visitedl == VisitedEnv vsl &
      visitedr == VisitedEnv vsr &
      List.appendo vsl vsr vs' &
      visited' == VisitedEnv vs'
  }

  let visited_checko visited stmt =
    let open VisitedEnv in
    ocanren {
      fresh vs in
      visited == VisitedEnv vs &
      List.membero vs stmt
    }

  let not_visited_checko visited stmt =
    let open VisitedEnv in
    ocanren {
      fresh vs in
      visited == VisitedEnv vs &
      list_not_membero vs stmt
    }

  let visited_addo visited stmt visited' =
    let open VisitedEnv in
    ocanren {
      fresh vs in
      visited == VisitedEnv vs &
      visited' == VisitedEnv (stmt :: vs)
    }

  (* --- *)

  let mem_geto mem id v =
    let open MemEnv in
    ocanren {
      fresh mem_data, mem_len, rev_id in
      MemEnv (mem_data, mem_len) == mem &
      Nat.addo (Nat.s rev_id) id mem_len &
      list_ntho mem_data rev_id v
  }

  let mem_addo mem v mem_with_id' =
    let open MemEnv in
    ocanren {
      fresh mem_data, mem_len, mem' in
      MemEnv (mem_data, mem_len) == mem &
      mem' == MemEnv (v :: mem_data, Nat.s mem_len) &
      Std.pair mem' mem_len == mem_with_id'
  }

  let mem_seto mem id v mem' =
    let open MemEnv in
    ocanren {
      fresh mem_data, mem_len, rev_id, mem_data' in
      MemEnv (mem_data, mem_len) == mem &
      Nat.addo (Nat.s rev_id) id mem_len &
      list_replaceo mem_data rev_id v mem_data' &
      MemEnv (mem_data', mem_len) == mem'
  }

  let is_trivial_vo v =
    let open Value in
    ocanren {
    fresh v_m, v_r, v_w in
    v == UnitV (v_m, v_r, v_w)
  }

  let rec pathvaro p x =
    let open Path in
    ocanren {
      p == VarP x |
      { fresh p' in p == DerefP p' & pathvaro p' x } |
      { fresh p', _id in p == AccessP (p', _id) & pathvaro p' x }
  }

  let rec pathrevo p rp rp' =
    let open Path in
    let open RevPath in
    ocanren {
      { fresh _x in
        p == VarP _x &
        rp == rp' } |
      { fresh p' in
        p == DerefP p' &
        pathrevo p' (DerefRP rp) rp' } |
      { fresh p', id in
        p == AccessP (p', id) &
        pathrevo p' (AccessRP (rp, id)) rp' }
  }

  let rec pathtypeo types p tp =
    let open Path in
    let open Type in
    ocanren {
      { fresh x in
        p == VarP x &
        types_assoco x types tp } |
      { fresh p', tp', _c in
        p == DerefP p' &
        pathtypeo types p' tp' &
        tp' == RefT (_c, tp) } |
      { fresh p', id', tp', tps in
        p == AccessP (p', id') &
        pathtypeo types p' tp' &
        tp' == TupleT tps &
        list_ntho tps id' tp }
  }

  let rec pathvalo mem vals p v =
    let open Path in
    let open Value in
    ocanren {
      { fresh x, id in
        p == VarP x &
        vals_assoco x vals id &
        mem_geto mem id v } |
      { fresh p', v', id in
        p == DerefP p' &
        pathvalo mem vals p' v' &
        v' == RefV id &
        mem_geto mem id v } |
      { fresh p', id, v', vs in
        p == AccessP (p', id) &
        pathvalo mem vals p' v' &
        v' == TupleV vs &
        list_ntho vs id v }
  }

  (* --- eval rules --- *)

  (* - value construction *)

  let rec valcopy_foldero mem_with_vs v tp mem_with_vs' =
    ocanren {
      fresh mem, vs, mem', v', vs' in
      Std.pair mem vs == mem_with_vs &
      valcopyo mem v tp (Std.pair mem' v') &
      vs' == v' :: vs &
      mem_with_vs' == Std.pair mem' vs'
  }
  and valcopyo mem v tp mem_with_id' = 
    let open Type in
    let open Value in
    let open ReadCap in
    (* let open CopyCap in *)
    let open MemVal in
    let open ReadVal in
    let open WriteVal in
    ocanren {
      { fresh r, w in
        is_trivial_vo v &
        tp == UnitT (r, w) &
        { { fresh v_m, _v_r, _v_w in
            r == Rd &
            v == UnitV (v_m, _v_r, _v_w) &
            mem_with_id' == Std.pair mem (UnitV (v_m, ZeroRV, ZeroWV)) } |
          { r == NRd &
            mem_with_id' == Std.pair mem (UnitV (BotMV, ZeroRV, ZeroWV)) } } } |
      { fresh stmts, ts in
        v == FunV stmts &
        tp == FunT ts &
        mem_with_id' == Std.pair mem v } |
      { fresh c, tp', id in
        v == RefV id &
        tp == RefT (c, tp') &
        (* { c == Rf & mem_with_id' == Std.pair mem v } | *)
        { fresh v', mem_cp, v_cp, mem_add, id_add in
          (* c == Cp & *)
          mem_geto mem id v' &
          valcopyo mem v' tp' (Std.pair mem_cp v_cp) &
          mem_addo mem_cp v_cp (Std.pair mem_add id_add) &
          mem_with_id' == (mem_add, RefV id_add) } } |
      { fresh vs, tps, mem', vs' in
        v == TupleV vs &
        tp == TupleT tps &
        list_foldr2o valcopy_foldero (Std.pair mem []) vs tps (Std.pair mem' vs') &
        mem_with_id' == Std.pair mem' (TupleV vs') }
  }

  (* - action rules *)

  let memvmodo a v_m v_m' =
    let open MemVal in
    let open Action in
    ocanren {
      { a == ReadA & v_m == ZeroMV & v_m' == ZeroMV } |
      { a == AlwaysWriteA & v_m' == ZeroMV } |
      { a == MayWriteA & v_m == ZeroMV & v_m' == ZeroMV } |
      { a == MayWriteA & v_m =/= ZeroMV & v_m' == SmthMV }
  }

  let readvmodo a v_r v_r' =
    let open ReadVal in
    let open Action in
    ocanren {
      { v_r == TopRV & v_r' == TopRV } |
      { v_r == OneRV & v_r' == OneRV } |
      { a == ReadA & v_r == ZeroRV & v_r' == OneRV } |
      { a == AlwaysWriteA & v_r == ZeroRV & v_r' == TopRV } |
      { a == MayWriteA & v_r == ZeroRV & v_r' == ZeroRV }
  }

  let writevmodo a v_w v_w' =
    let open WriteVal in
    let open Action in
    ocanren {
      { a == ReadA & v_w' == v_w } |
      { a == AlwaysWriteA & v_w' == OneWV } |
      { a == MayWriteA & v_w == OneWV & v_w' == OneWV } |
      { a == MayWriteA & v_w =/= OneWV & v_w' == v_w }
  }

  (* - value update *)

  (* NOTE: reversed path used *)
  let rec valchangeo mem v rp b mem_with_v' =
    let open RevPath in
    let open Value in
    ocanren {
      { rp == VarRP &
        mem_with_v' == Std.pair mem b } |
      { fresh rp', id, v', mem_upd, v_upd, mem_with_v_upd, mem_st in
        rp == DerefRP rp' &
        v == RefV id &
        mem_geto mem id v' &
        valchangeo mem v' rp' b mem_with_v_upd &
        Std.pair mem_upd v_upd == mem_with_v_upd &
        mem_seto mem_upd id v_upd mem_st &
        mem_with_v' == Std.pair mem_st (RefV id) } |
      { fresh rp', id, vs', v', mem_upd, v_upd, mem_with_v_upd, vs_upd in
        rp == AccessRP (rp', id) &
        v == TupleV vs' &
        list_ntho vs' id v' &
        valchangeo mem v' rp' b mem_with_v_upd &
        Std.pair mem_upd v_upd == mem_with_v_upd &
        list_replaceo vs' id v_upd vs_upd &
        mem_with_v' == Std.pair mem_upd (TupleV vs_upd) }
  }

  (* NOTE: reversed path used *)
  let rec valupdo mem v rp a mem_with_v' =
    let open RevPath in
    let open Value in
    ocanren {
      { fresh v_m, v_r, v_w,
              v_m', v_r', v_w',
              v' in
        rp == VarRP &
        v == UnitV (v_m, v_r, v_w) &
        memvmodo a v_m v_m' &
        readvmodo a v_r v_r' &
        writevmodo a v_w v_w' &
        v' == UnitV (v_m', v_r', v_w') &
        mem_with_v' == Std.pair mem v' } |
      { fresh rp', id, v', mem_upd, v_upd, mem_with_v_upd, mem_st in
        rp == DerefRP rp' &
        v == RefV id &
        mem_geto mem id v' &
        valupdo mem v' rp' a mem_with_v_upd &
        Std.pair mem_upd v_upd == mem_with_v_upd &
        mem_seto mem_upd id v_upd mem_st &
        mem_with_v' == Std.pair mem_st (RefV id) } |
      { fresh rp', id, vs', v', mem_upd, v_upd, mem_with_v_upd, vs_upd in
        rp == AccessRP (rp', id) &
        v == TupleV vs' &
        list_ntho vs' id v' &
        valupdo mem v' rp' a mem_with_v_upd &
        Std.pair mem_upd v_upd == mem_with_v_upd &
        list_replaceo vs' id v_upd vs_upd &
        mem_with_v' == Std.pair mem_upd (TupleV vs_upd) }
  }

  (* - value combination *)

  let memvalcombo u v u' =
    let open MemVal in
    ocanren {
      { u == ZeroMV & v == ZeroMV & u' == ZeroMV } |
      { u == BotMV & v == BotMV & u' == BotMV } |
      { { u =/= ZeroMV | { u == ZeroMV & v =/= ZeroMV } } &
        { u =/= BotMV | { u == BotMV & v =/= BotMV } } & 
        u' == SmthMV }
  }

  let readvalcombo u v u' =
    let open ReadVal in
    ocanren {
      { u == TopRV & v == TopRV & u' == TopRV } |
      { u == ZeroRV & v == ZeroRV & u' == ZeroRV } |
      { u == TopRV & v == ZeroRV & u' == ZeroRV } |
      { u == ZeroRV & v == TopRV & u' == ZeroRV } |
      { u =/= TopRV & v =/= TopRV &
        u =/= ZeroRV & v =/= ZeroRV & 
        u' == OneRV }
  }

  let writevalcombo u v u' =
    let open WriteVal in
    ocanren {
      { u == OneWV & v == OneWV & u' == OneWV } |
      { u == ZeroWV & v == ZeroWV & u' == ZeroWV } |
      { { u =/= ZeroWV | { u == ZeroWV & v =/= ZeroWV } } &
        { u =/= OneWV | { u == OneWV & v =/= OneWV } } & 
        u' == SmthWV }
  }

  let rec valcombo u v u' =
    let open Value in
    ocanren {
    { fresh u_m, u_r, u_w,
            v_m, v_r, v_w,
            u_m', u_r', u_w' in
      u == UnitV (u_m, u_r, u_w) &
      v == UnitV (v_m, v_r, v_w) &
      memvalcombo u_m v_m u_m' &
      readvalcombo u_r v_r u_r' &
      writevalcombo u_w v_w u_w' &
      u' == UnitV (u_m', u_r', u_w') } |
    { fresh ustmts, vstmts, ustmts' in
      u == FunV ustmts &
      v == FunV vstmts &
      (* TODO: swap stmts order o efficiency ? *)
      List.appendo ustmts vstmts ustmts' &
      u' == FunV ustmts' } |
    { fresh a, b in
      u == RefV a &
      v == RefV b &
      a == b &
      u' == RefV a } |
    { fresh us, vs, us' in
      u == TupleV us &
      v == TupleV vs &
      list_zip_witho valcombo us vs us' &
      u' == TupleV us' }
  }

  let memcombo m n m' =
    let open MemEnv in
    ocanren {
    fresh mm, ml, nm, nl, mm' in
    MemEnv (mm, ml) == m &
    MemEnv (nm, nl) == n &
    list_zip_witho valcombo mm nm mm' &
    m' == MemEnv (mm', ml)
  }

  (* - expression evaluation *)

  (* let rec exprval_foldero mem vals vs e vs' = ocanren { *)
    (* fresh v' in *)
    (* exprvalo mem vals e v' & *)
    (* vs' == v' :: vs *)
  (* } *)
  (* and *)
  let rec
  exprvalo mem vals e v' = 
    let open Expr in
    let open Value in
    let open MemVal in
    let open ReadVal in
    let open WriteVal in
    ocanren {
      { e == UnitE & v' == UnitV (ZeroMV, ZeroRV, ZeroWV) } |
      { fresh p in
        e == PathE p &
        pathvalo mem vals p v' } |
      { fresh x, v in
        e == RefE x &
        vals_assoco x vals v &
        v' == RefV v } |
      { fresh es, vs' in
        e == TupleE es &
        (* list_foldro (exprval_foldero mem vals) [] es vs' & *)
        List.mapo (exprvalo mem vals) es vs' &
        v' == TupleV vs' }
  }

  (* - expression typing *)

  let rec exprtypeo types e tp' = 
    let open Expr in
    let open Type in
    let open ReadCap in
    let open WriteCap in
    let open CopyCap in
    ocanren {
      { e == UnitE & tp' == UnitT (Rd, NeverWr) } |
      { fresh p in
        e == PathE p &
        pathtypeo types p tp' } |
      { fresh x, tp in
        e == RefE x &
        types_assoco x types tp &
        tp' == RefT (Rf, tp) } |
      { fresh es, tps' in
        e == TupleE es &
        List.mapo (exprtypeo types) es tps' &
        tp' == TupleT tps' }
  }

  (* - context initialization *)

  let add_declo st x d st' =
    let open StEnv in
    let open Decl in
    let open Value in
    let open Type in
    ocanren {
      fresh mem, types, vals, visited in
      st == StEnv (mem, types, vals, visited) &
      {
        { fresh tp, e, v,
                mem_cp, v_cp,
                mem_add, id_add,
                types', vals' in
          d == VarD (tp, e) &
          exprvalo mem vals e v &
          valcopyo mem v tp (Pair.pair mem_cp v_cp) &
          (* mem_cp == mem & v_cp == v & *)
          mem_addo mem_cp v_cp (Pair.pair mem_add id_add) &
          (* mem_add == mem_cp & *)
          types_glob_addo types x tp types' &
          (* types == types' & *)
          (* vals == vals' & *)
          vals_glob_addo vals x id_add vals' &
          st' == StEnv (mem_add, types', vals', visited) } |
        { fresh tps, s,
                mem_add, id_add,
                types', vals' in
          d == FunD (tps, s) &
          mem_addo mem (FunV [s]) (Pair.pair mem_add id_add) &
          types_glob_addo types x (FunT tps) types' &
          vals_glob_addo vals x id_add vals' &
          st' == StEnv (mem_add, types', vals', visited)
         }
      }
  }

  let empty_memo m =
    let open MemEnv in
    ocanren { m == MemEnv ([], 0) }

  let empty_stateo st =
    let open StEnv in
    let open TypesEnv in
    let open ValsEnv in
    let open VisitedEnv in
    ocanren {
      fresh m in
      empty_memo m &
      st == StEnv (m, TypesEnv ([], []), ValsEnv ([], []), VisitedEnv [])
  }

  (* TODO: better way ??? *)
  let globals_min_ido x = ocanren { x == 10 }

  let prog_init_foldero st_with_id d st_with_id' =
    ocanren {
      fresh st, x, st' in
      Std.pair st x == st_with_id &
      add_declo st x d st' &
      st_with_id' == Std.pair st' (Nat.s x)
  }

  let prog_inito prog st' =
    let open Prg in
    ocanren {
      fresh decls, s, st_init, min_id, st_with_id', _id' in
      prog == Prg (decls, s) &
      empty_stateo st_init &
      globals_min_ido min_id &
      list_foldlo prog_init_foldero (Std.pair st_init min_id) decls st_with_id' &
      Std.pair st' _id' == st_with_id'
  }

  (* - call values spoil *)

  (* TODO: check that negation is interpreted correctly *)
  let is_correct_tagso r w m c =
    let open ReadCap in
    let open WriteCap in
    let open Mode in
    let open CopyCap in
    ocanren {
      { r == NRd | r == Rd & is_ino m } &
      { is_not_outo m | is_outo m & w == AlwaysWr & c == Rf }
  }

  let tryreado r v_m v_r v_w v' =
    let open Action in
    let open Value in
    let open ReadCap in
    ocanren {
      { fresh v_m', v_r', v_w' in
        r == Rd &
        memvmodo ReadA v_m v_m' &
        readvmodo ReadA v_r v_r' &
        writevmodo ReadA v_w v_w' &
        v' == UnitV (v_m', v_r', v_w') } |
      { r == NRd &
        v' == UnitV (v_m, v_r, v_w)}
  }

  let tryspoilo m w v_m v_m' =
    let open Mode in
    let open WriteCap in
    let open MemVal in
    ocanren {
      { is_outo m & { w == AlwaysWr | w == MayWr } & v_m' == v_m } |
      { is_not_outo m & w == AlwaysWr & v_m' == BotMV } |
      { is_not_outo m & w == MayWr & v_m' == SmthMV }
  }

  let rec valspoil_foldero m c mem_with_vs tp v mem_with_vs' = ocanren {
    fresh mem, vs, mem', v' in
    Std.pair mem vs == mem_with_vs &
    valspoilo mem v tp m c (Std.pair mem' v') &
    mem_with_vs' == Std.pair mem' (v' :: vs)
  }
  and valspoilo mem v tp m c mem_with_v' =
    let open Type in
    let open Value in
    let open WriteCap in
    let open CopyCap in
    let open Action in
    ocanren {
      { fresh r, w,
              v_m, v_r, v_w,
              v', v'' in
        tp == UnitT (r, w) &
        v == UnitV (v_m, v_r, v_w) &
        is_correct_tagso r w m c &
        tryreado r v_m v_r v_w v' &
        {
          { { c == Cp | { c == Rf & w == NeverWr } } &
            mem_with_v' == Std.pair mem v' } |
          { fresh v_m', v_r', v_w',
                  v_m'', v_r'', v_w'',
                  v_m''' in
            c == Rf &
            { w == AlwaysWr | w == MayWr } &
            v' == UnitV (v_m', v_r', v_w') &
            {
              { w == AlwaysWr &
                memvmodo AlwaysWriteA v_m' v_m'' &
                readvmodo AlwaysWriteA v_r' v_r'' &
                writevmodo AlwaysWriteA v_w' v_w'' } |
              { w == MayWr &
                memvmodo MayWriteA v_m' v_m'' &
                readvmodo MayWriteA v_r' v_r'' &
                writevmodo MayWriteA v_w' v_w'' }
            } &
            tryspoilo m w v_m'' v_m''' &
            v'' == UnitV (v_m''', v_r'', v_w'') &
            mem_with_v' == Std.pair mem v'' }
        } } |
      { fresh ts, _stmts in
        tp == FunT ts &
        v == FunV _stmts &
        mem_with_v' == Std.pair mem v } |
      { fresh ctp', tp', id', v', mem_sp, v_sp, mem_set in
        tp == RefT (ctp', tp') &
        v == RefV id' &
        mem_geto mem id' v' &
        valspoilo mem v' tp' m ctp' (Std.pair mem_sp v_sp) &
        mem_seto mem_sp id' v_sp mem_set &
        mem_with_v' == Std.pair mem_set (RefV id') } |
      { fresh tps, vs, mem_sp, vs_sp in
        tp == TupleT tps &
        v == TupleV vs &
        list_foldr2o (valspoil_foldero m c)
                     (Std.pair mem []) tps vs
                     (Std.pair mem_sp vs_sp) &
        mem_with_v' == Std.pair mem_sp (TupleV vs_sp)
      }
  }

  (* full spoil *)

  let argsspoilpo st m tp p mem' =
    let open StEnv in
    let open CopyCap in
    let open RevPath in
    ocanren {
      fresh mem, types, vals, visited,
            x, id, b(* , tp' *), rp,
            mem_sp, b_sp, v_sp, mem_upd, v_upd in
      st == StEnv (mem, types, vals, visited) &
      pathvaro p x &
      vals_assoco x vals id &
      pathvalo mem vals p b &
      (* pathtypeo types p tp' & *)
      valspoilo mem b tp m Cp (Std.pair mem_sp b_sp) &
      pathrevo p VarRP rp &
      mem_geto mem_sp id v_sp &
      valchangeo mem_sp v_sp rp b_sp (Std.pair mem_upd v_upd) &
      mem_seto mem_upd id v_upd mem'
  }

  let rec argsspoile_foldero types vals visited m mem tp e mem' =
    let open StEnv in
    ocanren {
      fresh st in
      st == StEnv (mem, types, vals, visited) &
      argsspoileo st m tp e mem'
  }
  and argsspoileo st m tp e mem' =
    let open StEnv in
    let open Expr in
    let open Type in
    let open Path in
    ocanren {
      fresh _r, _w, mem, types, vals, visited in
      st == StEnv (mem, types, vals, visited) &
      {
        { e == UnitE &
          tp == UnitT (_r, _w) &
          mem' == mem } |
        { fresh p in
          e == PathE p &
          argsspoilpo st m tp p mem' } |
        { fresh x in
          e == RefE x &
          argsspoilpo st m tp (VarP x) mem' } |
        { fresh es, tps in
          e == TupleE es &
          tp == TupleT tps &
          list_foldl2o (argsspoile_foldero types vals visited m) mem tps es mem'}
      }
  }

  (* - funciton argument addition *)

  let addargo st oldvals x tp e st' =
    let open StEnv in
    ocanren {
      fresh mem, types, vals, visited, v,
            mem_cp, v_cp,
            mem_add, id_add,
            types', vals' in
      st == StEnv (mem, types, vals, visited) &
      exprvalo mem oldvals e v &
      valcopyo mem v tp (Std.pair mem_cp v_cp) &
      mem_addo mem_cp v_cp (Std.pair mem_add id_add) &
      types_addo types x tp types' &
      vals_addo vals x id_add vals' &
      st' == StEnv (mem_add, types', vals', visited)
  }

  (* - function evaluation *)
  (* NOTE: not needed due to performed optimization in stmt_eval ? *)

  let writeval_to_capo v_w w' =
    let open WriteVal in
    let open WriteCap in
    ocanren {
      { v_w == ZeroWV & w' == NeverWr } |
      { v_w == SmthWV & w' == MayWr } |
      { v_w == OneWV & w' == AlwaysWr }
  }

  let rec tags_checko mem v tp =
    let open ReadVal in
    let open ReadCap in
    let open Type in
    let open Value in
    ocanren {
      { fresh v_m, v_r, v_w,
              r, w in
        v == UnitV (v_m, v_r, v_w) &
        tp == UnitT (r, w) &
        {
          { r == Rd & v_r == OneRV } |
          { r == NRd & v_r == ZeroRV } |
          { r == NRd & v_r == TopRV }
        } &
        writeval_to_capo v_w w
         } |
      { fresh _stmts, _ts in
        v == FunV _stmts &
        tp == FunT _ts } |
      { fresh id, _c, tp', v' in
        v == RefV id &
        tp == RefT (_c, tp') &
        mem_geto mem id v' &
        tags_checko mem v' tp' } |
      { fresh vs, tps in
        v == TupleV vs &
        tp == TupleT tps &
        List.mapo (tags_checko mem) vs tps }
  }

  (* - statement evaluation *)

  let rec stmt_addarg_foldero vals st_with_id mtp e st_with_id' = ocanren {
    fresh st, x, m, tp, st' in
    Std.pair st x == st_with_id &
    Std.pair m tp == mtp &
    addargo st vals x tp e st' &
    st_with_id' == Std.pair st' (Nat.s x)
  }
  and f_tags_check_foldero mem vals x mtp x' = ocanren {
    fresh m, tp, id', v' in
    mtp == Std.pair m tp &
    vals_assoco x vals id' &
    mem_geto mem id' v' &
    tags_checko mem v' tp &
    x' == Nat.s x
  }
  and stmt_eval_func_foldero mem types vals tps visited stmt visited' =
    let open StEnv in
    ocanren {
      { fresh visited_add, st,
              st', mem', types', vals',
              _x', visited'' in
        not_visited_checko visited stmt &
        visited_addo visited stmt visited_add &
        st == StEnv (mem, types, vals, visited_add) &
        stmt_evalo st stmt st' &
        st' == StEnv (mem', types', vals', visited'') &
        list_foldlo (f_tags_check_foldero mem' vals') 0 tps _x' &
        visited' == visited''
         } |
      { visited_checko visited stmt &
        visited == visited' }
  }
  and stmt_eval_spoil_foldero types vals visited mem mtp e mem' =
    let open StEnv in
    ocanren {
      fresh m, tp, st in
      Std.pair m tp == mtp &
      st == StEnv (mem, types, vals, visited) &
      argsspoileo st m tp e mem'
  }
  and stmt_evalo st s st' =
    let open StEnv in
    let open Stmt in
    let open Value in
    let open Type in
    let open WriteCap in
    let open TypesEnv in
    let open ValsEnv in
    let open RevPath in
    let open Action in
    ocanren {
      fresh mem, types, vals, visited in
      st == StEnv (mem, types, vals, visited) &
      {
        { s == SkipS & st == st' } |
        { fresh f, es, v, tp,
                glob_tps, _tps,
                glob_vs, _vs,
                types_call, vals_call,
                fstmts, tps, st_call,
                state_with_args,
                mem_swa, types_swa,
                vals_swa, visited_swa,
                _arg_id, mem_spoiled,
                visited' in
          s == CallS (f, es) &
          pathvalo mem vals f v &
          pathtypeo types f tp &
          types == TypesEnv (glob_tps, _tps) &
          vals == ValsEnv (glob_vs, _vs) &
          types_call == TypesEnv (glob_tps, glob_tps) &
          vals_call == ValsEnv (glob_vs, glob_vs) &
          v == FunV fstmts &
          tp == FunT tps &
          st_call == StEnv (mem, types_call, vals_call, visited) &
          list_foldl2o (stmt_addarg_foldero vals)
                       (Std.pair st_call 0) tps es
                       (Std.pair state_with_args _arg_id) &
          state_with_args == StEnv (mem_swa, types_swa, vals_swa, visited_swa) &
          list_foldlo (stmt_eval_func_foldero mem_swa types_swa vals_swa tps) visited_swa fstmts visited' &
          (* TODO: FIXME check left or right order *)
          list_foldl2o (stmt_eval_spoil_foldero types vals (* NOTE: not important*) visited')
                       mem tps es mem_spoiled &
          st' == StEnv (mem_spoiled, types, vals, visited')
        } |
        { fresh p, tp, _r, w, x, id, v, rp,
                mem_upd, v_upd, mem_set in
          s == WriteS p &
          pathtypeo types p tp &
          tp == UnitT (_r, w) &
          { w == AlwaysWr | w == MayWr } &
          pathvaro p x &
          vals_assoco x vals id &
          mem_geto mem id v &
          pathrevo p VarRP rp &
          valupdo mem v rp AlwaysWriteA (Std.pair mem_upd v_upd) &
          mem_seto mem_upd id v_upd mem_set &
          st' == StEnv (mem_set, types, vals, visited) } |
        { fresh p, tp, _r, _w, x, id, v, rp,
                mem_upd, v_upd, mem_set in
          s == ReadS p &
          pathtypeo types p tp &
          tp == UnitT (_r, _w) &
          pathvaro p x &
          vals_assoco x vals id &
          mem_geto mem id v &
          pathrevo p VarRP rp &
          valupdo mem v rp ReadA (Std.pair mem_upd v_upd) &
          mem_seto mem_upd id v_upd mem_set &
          st' == StEnv (mem_set, types, vals, visited) } |
        (* { fresh p in *)
          (* s == ReadS p & *)
          (* pathvalo mem vals p ZeroV & *)
          (* st == st' } | *)
        { fresh sl, sr, stl in
          s == SeqS (sl, sr) &
          stmt_evalo st sl stl &
          stmt_evalo stl sr st' } |
        { fresh sl, sr, stl, str,
                meml, typesl, valsl, visitedl,
                memr, typesr, valsr, visitedr,
                visited', mem' in
          s == ChoiceS (sl, sr) &
          stmt_evalo st sl stl &
          stmt_evalo st sr str &
          stl == StEnv (meml, typesl, valsl, visitedl) &
          str == StEnv (memr, typesr, valsr, visitedr) &
          typesl == typesr &
          valsl == valsr &
          memcombo meml memr mem' &
          visited_appendo visitedr visitedl visited' &
          st' == StEnv (mem', typesl, valsl, visited') }
      }
  }

  (* --- program execution --- *)

  let prog_evalo prog st' =
    let open Prg in
    ocanren {
      fresh decls, s, init_st in
      prog == Prg (decls, s) &
      prog_inito prog init_st &
      stmt_evalo init_st s st'
  }
end
