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

  (* TODO: access: data or int ? *)
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
      type nonrec ((* 'd, *) 't, 'e, 'dl, 'mtl, 's) t = VarD of (* 'd * *) 't * 'e | FunD of (* 'd * *) 'dl * 'mtl * 's
      [@@deriving gt ~options:{ show; gmap }]
      type ground = ((* Nat.ground, *) Type.ground, Expr.ground, Nat.ground List.ground, (Mode.ground * Type.ground) List.ground, Stmt.ground) t
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

  module Value = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('sl, 'd, 'vl) t = ZeroV | SmthV | BotV | FunV of 'sl | RefV of 'd | TupleV of 'vl
      [@@deriving gt ~options:{ show; gmap }]
      type ground = (((* Nat.ground List.ground * *) Stmt.ground) List.ground, Nat.ground, ground List.ground) t
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

  module StEnv = struct
    [@@@warning "-26-27-32-33-34-35-36-37-38-39-60-66-67"]
    [%%ocanren_inject
      type nonrec ('mem, 'types, 'vals) t = StEnv of 'mem * 'types * 'vals
      [@@deriving gt ~options:{ show; gmap }]
      type nonrec ground = (MemEnv.ground, TypesEnv.ground, ValsEnv.ground) t
    ]
  end

  (* --- *)

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

  let rec list_foldr3o f acc xs ys zs acc' = ocanren {
    xs == [] & ys == [] & zs == [] & acc' == acc |
    { fresh x', xs', y', ys', z', zs', acc_upd in
      xs == x' :: xs' &
      ys == y' :: ys' &
      zs == z' :: zs' &
      f acc x' y' z' acc_upd &
      list_foldr3o f acc_upd xs' ys' zs' acc' }
  }

  let rec list_foldl3o f acc xs ys zs acc' = ocanren {
    xs == [] & ys == [] & zs == [] & acc' == acc |
    { fresh x', xs', y', ys', z', zs', acc_upd in
      xs == x' :: xs' &
      ys == y' :: ys' &
      zs == z' :: zs' &
      list_foldl3o f acc xs' ys' zs' acc_upd &
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
    v == ZeroV | v == SmthV | v == BotV
  }

  let rec pathvaro p x =
    let open Path in
    ocanren {
      p == VarP x |
      { fresh p' in p == DerefP p' & pathvaro p' x } |
      { fresh p', _id in p == AccessP (p', _id) & pathvaro p' x }
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
      fresh mem, vs, mem', v', mem_with_v', vs' in
      Std.pair mem vs == mem_with_vs &
      valcopyo mem v tp mem_with_v' &
      Std.pair mem' v' == mem_with_v' &
      vs' == v' :: vs &
      mem_with_vs' == Std.pair mem vs'
  }
  and valcopyo mem v tp mem_with_id' = 
    let open Type in
    let open Value in
    let open ReadCap in
    let open CopyCap in
    ocanren {
      { fresh r, w in
        is_trivial_vo v &
        tp == UnitT (r, w) &
        { { r == Rd & mem_with_id' == Std.pair mem v } |
          { r == NRd & mem_with_id' == Std.pair mem BotV } } } |
      { fresh stmts, ts in
        v == FunV stmts &
        tp == FunT ts &
        mem_with_id' == Std.pair mem v } |
      { fresh c, tp', id in
        v == RefV id &
        tp == RefT (c, tp') &
        { { c == Rf & mem_with_id' == Std.pair mem v } |
          { fresh v, mem_cp, v_cp, mem_with_v_cp,
                  mem_add, id_add, mem_with_id_add in
            c == Cp &
            mem_geto mem id v &
            valcopyo mem v tp mem_with_v_cp &
            Std.pair mem v_cp == mem_with_v_cp &
            mem_addo mem_cp v_cp mem_with_id_add &
            Std.pair mem_add id_add == mem_with_id_add &
            mem_with_id' == (mem_add, RefV id_add) } } } |
      { fresh vs, tps, init_mem_with_vs, mem_with_vs', mem', vs' in
        v == TupleV vs &
        tp == TupleT tps &
        init_mem_with_vs == Std.pair mem [] &
        list_foldl2o valcopy_foldero init_mem_with_vs vs tps mem_with_vs' &
        Std.pair mem' vs' == mem_with_vs' &
        mem_with_id' == Std.pair mem' (TupleV vs') }
  }

  (* - value update *)

  let rec valupdo mem v p b mem_with_v' =
    let open Path in
    let open Value in
    ocanren {
      { fresh x in
        p == VarP x &
        mem_with_v' == Std.pair mem b } |
      { fresh p', id, v', mem_upd, v_upd, mem_with_v_upd, mem_st in
        p == DerefP p' &
        v == RefV id &
        mem_geto mem id v' &
        valupdo mem v' p' b mem_with_v_upd &
        Std.pair mem_upd v_upd == mem_with_v_upd &
        mem_seto mem_upd id v_upd mem_st &
        mem_with_v' == Std.pair mem_st (RefV id) } |
      { fresh p', id, vs', v', mem_upd, v_upd, mem_with_v_upd, vs_upd in
        p == AccessP (p', id) &
        v == TupleV vs' &
        list_ntho vs' id v' &
        valupdo mem v' p' b mem_with_v_upd &
        Std.pair mem_upd v_upd == mem_with_v_upd &
        list_replaceo vs' id v_upd vs_upd &
        mem_with_v' == Std.pair mem_upd (TupleV vs_upd) }
  }

  (* - value combination *)

  let rec valcombo u v u' =
    let open Value in
    ocanren {
    { is_trivial_vo u &
      is_trivial_vo v &
      (* TODO: do not use disequality constraint ? *)
      { { u == v & u' == u } | { u =/= v & u' == BotV } } } |
    { fresh ustmts, vstmts, ustmts' in
      u == FunV ustmts &
      v == FunV vstmts &
      (* TODO: swap stmts order o efficiency ? *)
      List.appendo ustmts vstmts ustmts' &
      u' == FunV ustmts' } |
    { fresh a, b in
      u == RefV a &
      v == RefV b &
      a == b } |
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

  let rec exprvalo mem vals e v' = 
    let open Expr in
    let open Value in
    ocanren {
      { e == UnitE & v' == ZeroV } |
      { fresh p in
        e == PathE p &
        pathvalo mem vals p v' } |
      { fresh x, v in
        e == RefE x &
        vals_assoco x vals v &
        v' == RefV v } |
      { fresh es, vs' in
        e == TupleE es &
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
    ocanren {
      fresh mem, types, vals in
      st == StEnv (mem, types, vals) &
      {
        { fresh tp, e, v,
                mem_with_v_cp, mem_cp, v_cp,
                mem_with_id_add, mem_add, id_add,
                types', vals' in
          d == VarD (tp, e) &
          exprvalo mem vals e v &
          valcopyo mem v tp mem_with_v_cp &
          Pair.pair mem_cp v_cp == mem_with_v_cp &
          mem_addo mem_cp v_cp mem_with_id_add &
          Pair.pair mem_add id_add == mem_with_id_add &
          types_glob_addo types x tp types' &
          vals_glob_addo vals x id_add vals' &
          st' == StEnv (mem_add, types', vals')
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
    ocanren {
      fresh m in
      empty_memo m &
      st == StEnv (m, TypesEnv ([], []), ValsEnv ([], []))
  }

  (* TODO: better way ??? *)
  let globals_min_ido x = ocanren { x == 1000 }

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
  let is_correct_tagso v r w _r' w' m c =
    let open Value in
    let open ReadCap in
    let open WriteCap in
    let open Mode in
    let open CopyCap in
    ocanren {
      { r == NRd | v == ZeroV } &
      { r == NRd | is_ino m } &
      { is_not_outo m | w == AlwaysWr } &
      { w == NeverWr |
        { is_not_outo m & c == Cp } |
        w' == AlwaysWr } &
      is_trivial_vo v
  }

  let rec valspoil_foldero m c mem_with_vs tp u v mem_with_vs' = ocanren {
    fresh mem, vs, mem', v' in
    Std.pair mem vs == mem_with_vs &
    valspoilo mem v tp u m c (Std.pair mem' v') &
    mem_with_vs' == Std.pair mem' (v' :: vs)
  }
  and valspoilo mem v tp u m c mem_with_v' =
    let open Type in
    let open Value in
    let open Mode in
    let open WriteCap in
    let open CopyCap in
    ocanren {
      { fresh r, w, r', w' in
        tp == UnitT (r, w) &
        u == UnitT (r', w') &
        is_trivial_vo v &
        is_correct_tagso v r w r' w' m c &
        {
          { is_not_outo m &
            c == Rf &
            { w == AlwaysWr | w == MayWr } &
            mem_with_v' == Std.pair mem BotV } |
          { is_outo m &
            w == AlwaysWr &
            mem_with_v' == Std.pair mem ZeroV } |
          { { is_outo m | c == Cp | w == NeverWr } &
            { is_not_outo m | w == MayWr | w == NeverWr } &
            mem_with_v' == Std.pair mem v }
        } } |
      { fresh ts, us, _stmts in
        tp == FunT ts &
        u == FunT us &
        v == FunV _stmts &
        ts == us &
        mem_with_v' == Std.pair mem v } |
      { fresh ctp', tp', cu', u', id', v', mem_sp, v_sp, mem_set in
        tp == RefT (ctp', tp') &
        u == RefT (cu', u') &
        v == RefV id' &
        mem_geto mem id' v' &
        valspoilo mem v' tp' u' m ctp' (Std.pair mem_sp v_sp) &
        mem_seto mem_sp id' v_sp mem_set &
        mem_with_v' == Std.pair mem_set (RefV id') } |
      { fresh tps, us, vs, mem_sp,vs_sp in
        tp == TupleT tps &
        u == TupleT us &
        v == TupleV vs &
        list_foldl3o (valspoil_foldero m c)
                     (Std.pair mem []) tps us vs
                     (Std.pair mem_sp vs_sp) &
        mem_with_v' == Std.pair mem_sp (TupleV vs_sp)
      }
  }

  (* full spoil *)

  let argspoilpo st m tp p mem' =
    let open StEnv in
    let open CopyCap in
    ocanren {
      fresh mem, types, vals, x, id, b, tp',
            mem_sp, b_sp, v_sp, mem_upd, v_upd in
      st == StEnv (mem, types, vals) &
      pathvaro p x &
      vals_assoco x vals id &
      pathvalo mem vals p b &
      pathtypeo types p tp' &
      valspoilo mem b tp tp' m Cp (Std.pair mem_sp b_sp) &
      mem_geto mem_sp id v_sp &
      valupdo mem_sp v_sp p b_sp (Std.pair mem_upd v_upd) &
      mem_seto mem_upd id v_upd mem'
  }

  let rec argspoile_foldero types vals m mem tp e mem' =
    let open StEnv in
    ocanren {
      fresh st in
      st == StEnv (mem, types, vals) &
      argspoileo st m tp e mem'
  }
  and argspoileo st m tp e mem' =
    let open StEnv in
    let open Expr in
    let open Type in
    let open Path in
    ocanren {
      fresh _r, _w, mem, types, vals in
      st == StEnv (mem, types, vals) &
      {
        { e == UnitE &
          tp == UnitT (_r, _w) &
          mem' == mem } |
        { fresh p in
          e == PathE p &
          argspoilpo st m tp p mem' } |
        { fresh x in
          e == RefE x &
          argspoilpo st m tp (VarP x) mem' } |
        { fresh es, tps in
          e == TupleE es &
          tp == TupleT tps &
          list_foldl2o (argspoile_foldero types vals m) mem tps es mem'}
      }
  }

  (* - funciton argument addition *)

  let addargo st oldvals x tp e st' =
    let open StEnv in
    ocanren {
      fresh mem, types, vals, v,
            mem_cp, v_cp,
            mem_add, id_add,
            types', vals' in
      st == StEnv (mem, types, vals) &
      exprvalo mem oldvals e v &
      valcopyo mem v tp (Std.pair mem_cp v_cp) &
      mem_addo mem_cp v_cp (Std.pair mem_add id_add) &
      types_addo types x tp types' &
      vals_addo vals x id_add vals' &
      st' == StEnv (mem_add, types', vals')
  }

  (* - function evaluation *)
  (* NOTE: not needed due to performed optimization in stmt_eval ? *)

  (* - statement evaluation *)
  (* TODO *)

  let rec stmt_addarg_foldero vals st_with_id mtp e st_with_id' = ocanren {
    fresh st, x, m, tp, st' in
    Std.pair st x == st_with_id &
    Std.pair m tp == mtp &
    addargo st vals x tp e st' &
    st_with_id' == Std.pair st' (Nat.s x)
  }
  and stmt_eval_spoil_foldero types vals mem mtp e mem' =
    let open StEnv in
    ocanren {
      fresh m, tp, st in
      Std.pair m tp == mtp &
      st == StEnv (mem, types, vals) &
      argspoileo st m tp e mem'
  }
  and stmt_evalo st s st' =
    let open StEnv in
    let open Stmt in
    let open Value in
    let open Type in
    let open WriteCap in
    let open TypesEnv in
    let open ValsEnv in
    ocanren {
      fresh mem, types, vals in
      st == StEnv (mem, types, vals) &
      {
        { s == SkipS & st == st' } |
        { fresh f, es, v, tp,
                glob_tps, _tps,
                glob_vs, _vs,
                types', vals',
                fstmts, tps, st',
                state_with_args, _arg_id,
                _states_evaled, mem_spoiled in
          s == CallS (f, es) &
          pathvalo mem vals f v &
          pathtypeo types f tp &
          types == TypesEnv (glob_tps, _tps) &
          vals == ValsEnv (glob_vs, _vs) &
          types' == TypesEnv (glob_tps, glob_tps) &
          vals' == ValsEnv (glob_vs, glob_vs) &
          v == FunV fstmts &
          tp == FunT tps &
          st' == StEnv (mem, types', vals') &
          list_foldl2o (stmt_addarg_foldero vals)
                       (Std.pair st' 0) tps es
                       (Std.pair state_with_args _arg_id) &
          List.mapo (stmt_evalo state_with_args) fstmts _states_evaled &
          (* TODO: FIXME check left or right order *)
          list_foldl2o (stmt_eval_spoil_foldero types vals)
                      mem tps es mem_spoiled &
          st' == StEnv (mem_spoiled, types, vals) } |
        { fresh p, tp, _r, w, x, id, v,
                mem_upd, v_upd, mem_set in
          s == WriteS p &
          pathtypeo types p tp &
          tp == UnitT (_r, w) &
          { w == AlwaysWr | w == MayWr } &
          pathvaro p x &
          vals_assoco x vals id &
          mem_geto mem id v &
          valupdo mem v p ZeroV (Std.pair mem_upd v_upd) &
          mem_seto mem_upd id v_upd mem_set &
          st' == StEnv (mem_set, types, vals) } |
        { fresh p in
          s == ReadS p &
          pathvalo mem vals p ZeroV &
          st == st' } |
        { fresh sl, sr, stl in
          s == SeqS (sl, sr) &
          stmt_evalo st sl stl &
          stmt_evalo stl sr st' } |
        { fresh sl, sr, stl, str,
                meml, typesl, valsl,
                memr, typesr, valsr,
                mem' in
          s == ChoiceS (sl, sr) &
          stmt_evalo st sl stl &
          stmt_evalo st sr str &
          str == StEnv (memr, typesr, valsr) &
          stl == StEnv (meml, typesl, valsl) &
          typesl == typesr &
          valsl == valsr &
          memcombo meml memr mem' &
          st' == StEnv (mem', typesl, valsl) }
      }
  }

  (* --- program execution --- *)

  let prog_evalo prog st' =
    let open Prg in
    let open Stmt in
    ocanren {
      fresh decls, s, init_st in
      prog == Prg (decls, s) &
      decls == [] &
      s == SkipS &
      prog_inito prog init_st &
      stmt_evalo init_st s st'
  }

  (* --- tests --- *)
  (* TODO *)

  (* - shortcuts *)
  (* TODO *)

end
