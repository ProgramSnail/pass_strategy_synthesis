module Functional =
struct

  type data = int
  type memid = int

  (* --- syntax --- *)

  type read_cap = Rd | NRd

  type write_cap = AlwaysWr | MayWr | NeverWr
  type copy_cap = Cp | Rf

  type in_cap = In | NIn
  type out_cap = Out | NOut

  type mode = in_cap * out_cap

  type path = VarP of data | DerefP of path | AccessP of path * data

  type atype = UnitT of read_cap * write_cap
             | RefT of copy_cap * atype
             | TupleT of atype list
             | FunT of (mode * atype) list (* TODO: declaration id for ease of impl / performance instead (?) *)

  type mtype = mode * atype

  type expr = UnitE
            | PathE of path
            (* TODO: extend to include arbitrary path *)
            | RefE of data
            | TupleE of expr list

  type stmt = SkipS
            | CallS of path * expr list
            | WriteS of path
            | ReadS of path
            | SeqS of stmt * stmt
            | ChoiceS of stmt * stmt

  type decl = VarD of (* data * *) atype * expr
            | FunD of (* data * *) (* (data * *) mtype (* )  *) list * stmt

  type prog = decl list * stmt

  (* --- exceptions --- *)

  (* exception Incorrect_memory_access of int *)
  (* exception Ref_rvalue_argument of int *)
  (* exception Incorrect_const_cast of int *)
  (* exception Invalid_argument_tag of int *)
  (* exception Incompatible_states *)
  (* exception Incompatible_path_and_type *)
  (* exception Incompatible_path_and_mem *)
  (* exception Incompatible_path_and_type_for_tag *)
  exception Typing_error of string
  exception Eval_error of string
  exception Cant_fold3_error

  (* value model & memory model *)

  type deepvalue = ZeroDV
                 | SmthDV
                 | BotDV
                 | FunDV of ((* data list * *) stmt) list
                 | RefDV of deepvalue
                 | TupleDV of deepvalue list

  type value = ZeroV
             | SmthV
             | BotV
             | FunV of ((* data list * *) stmt) list
             | RefV of memid
             | TupleV of value list

  (* TODO: any additional difference between rvalue and lvalue now ?? *)

  (* --- *)

  type mem = value list * memid (* NOTE: memory and first free elem *)
  type types = (data * atype) list
  type vals = (data * memid) list
  type state = mem * types * vals

  (* --- *)

  (* - utils *)

  let rec list_replace (xs : 'a list) (id : int) (y : 'a) : 'a list = match xs, id with
   | _ :: xs, 0 -> y :: xs
   | x :: xs, _ -> x :: list_replace xs (id - 1) y
   | [], _ -> raise Not_found

  (* TODO: FIXME: check if this foldl or foldr *)
  let rec list_foldl3 f (acc : 'a) (xs : 'b list) (ys : 'c list) (zs : 'd list) : 'a = match xs, ys, zs with
    | x :: xs, y :: ys, z :: zs -> list_foldl3 f (f acc x y z) xs ys zs 
    | [], [], [] -> acc
    | _, _, _ -> raise Cant_fold3_error

  (* --- *)

  (* NOTE: old variant with assoc array *)
  (* let mem_get (mem : mem) (id : memid) : value = List.assoc id (fst mem) *)
  (* let mem_add (mem : mem) (v : value) : mem * memid = *)
    (* (((snd mem, v) :: fst mem, snd mem + 1), snd mem) *)
  (* let mem_set (mem : mem) (id : memid) (v : value) : mem = *)
    (* ((id, v) :: fst mem, snd mem) *)
  let mem_get (mem : mem) (id : memid) : value = (* FIXME TMP Printf.printf "l%i i%i %i: access\n" (snd mem) id (snd mem - id - 1); *)
                                                 List.nth (fst mem) (snd mem - id - 1)
  let mem_add (mem : mem) (v : value) : mem * memid =
    ((v :: fst mem, snd mem + 1), snd mem)
  let mem_set (mem : mem) (id : memid) (v : value) : mem =
    (list_replace (fst mem) (snd mem - id - 1) v, snd mem)

  let rec v_to_deepv (mem : mem) (v : value) : deepvalue = match v with
    | ZeroV -> ZeroDV
    | SmthV -> SmthDV
    | BotV -> BotDV
    | FunV s -> FunDV s
    | RefV id -> RefDV (v_to_deepv mem @@ mem_get mem id)
    | TupleV vs -> TupleDV (List.map (v_to_deepv mem) vs)

  let is_trivial_v (v : value) : bool = 
    v == ZeroV || v == SmthV || v == BotV

  (* --- path accessors --- *)

  let rec pathvar (p : path) : data = match p with
    | VarP x -> x
    | DerefP p -> pathvar p
    | AccessP (p, _) -> pathvar p

  let rec pathtype (types : types) (p : path) : atype = match p with
    | VarP x -> List.assoc x types
    | DerefP p -> (match pathtype types p with
                    | RefT (_, t) -> t
                    | _ -> raise @@ Typing_error "pathtype: deref")
    | AccessP (p, id) -> match pathtype types p with
                           | TupleT ts -> (List.nth ts id)
                           | _ -> raise @@ Typing_error "pathtype: access"

  let rec pathval (mem :  mem) (vals : vals) (p : path) : value = match p with
    | VarP x -> mem_get mem @@ ((* Printf.printf "%i: " x; (* FIXME TMP *)
                                ignore @@ List.map (fun (x, _) -> Printf.printf "%i " x) vals;
                                Printf.printf "mem size: %i, " (List.length (fst mem));
                                Printf.printf "mem size stored: %i " (snd mem);
                                Printf.printf "\n"; *)
                                List.assoc x vals)
    | DerefP p -> (match pathval mem vals p with
                    | RefV id -> mem_get mem id
                    | _ -> raise @@ Typing_error "pathval: deref")
    | AccessP (p, id) -> match pathval mem vals p with
                           | TupleV vs -> (List.nth vs id)
                           | _ -> raise @@ Typing_error "pathval: access"

  (* --- eval rules --- *)

  (* - value construction *)

  let rec valcopy (mem : mem) (v : value) (t : atype) : mem * value =
    if is_trivial_v v
    then match t with
    | UnitT (Rd, _) -> (mem, v)
    | UnitT (NRd, _) -> (mem, BotV)
    | _ -> raise @@ Typing_error "valcopy: trivial value, wrong type"
    else match t, v with
    (* NOTE: replaced with if | best choice ?? *)
    (* | UnitT (Rd, w), ZeroV -> (mem, v) *)
    (* | UnitT (Rd, w), SmthV -> (mem, v) *)
    (* | UnitT (Rd, w), BotV -> (mem, v) *)
    (* | UnitT (NRd, w), ZeroV -> (mem, BotV) *)
    (* | UnitT (NRd, w), SmthV -> (mem, BotV) *)
    (* | UnitT (NRd, w), BotV -> (mem, BotV) *)
    | FunT _, FunV _ -> (mem, v)
    | RefT (Rf, _), RefV _ -> (mem, v)
    | RefT (Cp, t), RefV id -> let (mem', v') = valcopy mem (mem_get mem id) t in
                               let (mem'', id'') = mem_add mem' v' in
                               (mem'', RefV id'') 
    | TupleT ts, TupleV vs -> let folder = fun (mem, vs') v t -> let (mem', v') = valcopy mem v t in
                                                                 (mem, v' :: vs') in 
                              let mem', vs' = List.fold_left2 folder (mem, []) vs ts in
                              (mem', TupleV vs')
    | _, _ -> raise @@ Typing_error "valcopy: not trivial value, wrong type"

  (* - value update *)

  let rec valupd (mem : mem) (v : value) (p : path) (b : value) : mem * value = match p, v with
    | VarP x, _ -> (mem, b)
    | DerefP p, RefV id -> let (mem', v') = valupd mem (mem_get mem id) p b in
                           (mem_set mem' id v', RefV id)
    | AccessP (p, id), TupleV vs -> let (mem', v') = valupd mem (List.nth vs id) p b in
                                    (mem', TupleV (list_replace vs id v'))
    | _, _ -> raise @@ Typing_error "valupd"

  (* - value combination *)

  let rec valcomb (u : value) (v : value) : value =
    if is_trivial_v u && is_trivial_v v
    then (if u == v then u else BotV)
    else match u, v with
      | FunV ustmts, FunV vstmts  -> FunV (ustmts @ vstmts)
      | RefV a, RefV b -> if a == b then u else raise @@ Typing_error "valcomb: ref"
      | TupleV us, TupleV vs -> TupleV (List.map2 valcomb us vs)
      | _, _ -> raise @@ Typing_error "valcomb"

  let rec memcomb (m : mem) (n : mem) : mem =
    if snd m != snd n
    then raise @@ Typing_error "memcomb"
    else (List.map2 valcomb (fst m) (fst n), snd m)

  (* - expression evaluation *)

  let rec exprval (mem : mem) (vals : vals) (e : expr) : value = match e with
    | UnitE -> ZeroV
    | PathE p -> pathval mem vals p
    | RefE x -> RefV (List.assoc x vals)
    | TupleE es -> TupleV (List.map (exprval mem vals) es)

  (* - expression typing *)

  let rec exprtype (types : types) (e : expr) : atype = match e with
    | UnitE -> UnitT (Rd, NeverWr)
    | PathE p -> pathtype types p
    | RefE x -> RefT (Rf, List.assoc x types)
    | TupleE es -> TupleT (List.map (exprtype types) es)

  (* - context initialization *)

  (* let rec valcopy (mem : mem) (v : value) (t : atype) : mem * value = match t, v with *)
  
  (* TODO: check new in vars *)
  let add_decl (state : state) (x : data) (d : decl) : state =
    match state with (mem, types, vals) -> match d with
    | VarD (t, e) -> let v = exprval mem vals e in
                     let (mem', v') = valcopy mem v t in
                     let (mem'', id) = mem_add mem' v' in
                     (mem'', (x, t) :: types, (x, id) :: vals)
    | FunD (ts, s)  -> let (mem', id) = mem_add mem (FunV [s]) in
                       (mem', (x, FunT ts) :: types, (x, id) :: vals)

  let empty_mem : mem = ([], 0)
  let empty_state : state = (empty_mem, [], [])

  (* TODO: better way ??? *)
  let globals_min_id : data = 1000

  let prog_init (prog : prog) : state =
    match prog with (decls, _) -> fst @@ List.fold_left (* TODO: FIXME: check x's order *)
                                    (fun (st, x) d -> (add_decl st x d, x + 1))
                                    (empty_state, globals_min_id)
                                    decls

  (* - call values spoil *)

  (* TODO: check all cases *)
  let is_correct_tags (v : value) (r : read_cap) (w : write_cap)
                      (r' : read_cap) (w' : write_cap) (m : mode)
                      (c : copy_cap) : bool =
    (* FIXME TMP *)
    (* Printf.printf "%b %b %b %b %b\n" *)
      (* (r != Rd || v == ZeroV) *)
      (* (r != Rd || fst m == In) *)
      (* (snd m != Out || w == AlwaysWr) *)
      (* (* TODO: FIXME: why always write ?? *) *)
      (* (((not ((w == AlwaysWr || w == MayWr) && (snd m == Out || c == Rf))) || w' == AlwaysWr)) *)
      (* (is_trivial_v v); *)
    (r != Rd || v == ZeroV) &&
    (r != Rd || fst m == In) &&
    (snd m != Out || w == AlwaysWr) &&
    (* TODO: check *)
    ((not ((w == AlwaysWr || w == MayWr) && (snd m == Out || c == Rf))) || w' == AlwaysWr) &&
    is_trivial_v v

  let rec valspoil (mem : mem) (v : value) (t : atype)
                   (u : atype) (m : mode) (c : copy_cap)
                   : mem * value = match t, u, v with
    | UnitT (r, w), UnitT (r', w'), _ ->
      if not @@ is_trivial_v v
        then raise @@ Typing_error "valspoil: unit, not trivial"
      else if not @@ is_correct_tags v r w r' w' m c
        then raise @@ Typing_error "valspoil: unit, not correct"
      else if snd m == NOut && c == Rf && (w == AlwaysWr || w == MayWr)
        then (mem, BotV)
      else if snd m == Out && w == AlwaysWr
        then (mem, ZeroV)
      else (mem, v)
    | FunT ts, FunT us, FunV _ -> if ts == us then (mem, v) else raise @@ Typing_error "valspoil: fun"
    | RefT (ct, t), RefT (cu, u), RefV id ->
      let (mem', v') = valspoil mem (mem_get mem id) t u m ct in
      (mem_set mem id v', RefV id)
    | TupleT ts, TupleT us, TupleV vs ->
        let folder = fun (mem, vs') t u v ->
          let (mem', v') = valspoil mem v t u m c in (mem', v' :: vs') in
        let (mem', vs') = list_foldl3 folder (mem, []) ts us vs in
        (mem', TupleV vs')
    | _, _, _ ->  raise @@ Typing_error "valspoil"

  (* full spoil *)

  let argsspoilp (state : state) (m : mode) (t : atype) (p : path) : mem =
    match state with (mem, types, vals) ->
    let x = pathvar p in
    let id = List.assoc x vals in
    let b = pathval mem vals p in
    let t' = pathtype types p in
    let (mem', b') = valspoil mem b t t' m Rf in
    let (mem'', v'') = valupd mem' (mem_get mem' id) p b' in
    mem_set mem'' id v''

  let rec argsspoile (state : state) (m : mode) (t : atype) (e : expr) : mem =
    match state with (mem, types, vals) -> match e, t with
      | UnitE, UnitT _ -> mem
      | PathE p, t -> argsspoilp state m t p
      | RefE x, t -> argsspoilp state m t (VarP x)
      (* TODO: FIXME: check RefE case ? *)
      | TupleE es, TupleT ts -> List.fold_left2
                                  (fun mem' t' e' -> argsspoile (mem', types, vals) m t' e')
                                  mem ts es
      | _, _ ->  raise @@ Typing_error "valspoile"

  (* - funciton argument addition *)

  let addarg (state : state) (oldvals : vals) (x : data) (t : atype) (e : expr) : state =
    match state with (mem, types, vals) ->
    let v = exprval mem oldvals e in
    (* let t' = pathtype types p in *)
    let (mem', v') = valcopy mem v t in
    let (mem'', id) = mem_add mem' v' in
    (mem'', (x, t) :: types, (x, id) :: vals)

  (* - function evaluation *)
  (* NOTE: not needed due to performed optimization in stmt_eval *)
  (* let func_eval (mem : mem) (vals : vals) (s : stmt) (ts : mtype list) (es : expr list) = *)

  (* - statement evaluation *)

  let rec stmt_eval (state : state) (s : stmt) : state =
    match state with (mem, types, vals) -> match s with
    (* TODO: FIXME: Add memoization *)
    | SkipS -> state
    | CallS (f, es) -> let v = (* FIXME TMP Printf.printf "call, before v\n"; *)
                               pathval mem vals f in
                       let t = (* FIXME TMP Printf.printf "call, before t\n"; *)
                               pathtype types f in
                       let types' : types = [] in
                       let vals' : vals = [] in
                       (match v, t with
                          | FunV (* xs, *) fstmts (* ) *), FunT ts ->
                            (* TODO: memoisation of the called functions *)
                            let (state_with_args, _) = (* FIXME TMP Printf.printf "call, before args\n"; *)
                                                       List.fold_left2 (* TODO: FIXME: check x's order *)
                              (fun (st, x) (m, t) e -> (addarg st vals x t e, x + 1))
                              ((mem, types', vals'), 0) ts es in
                            (* NOTE: same x's, so can use same args for all the statements *)
                            let _states_evaled = (* FIXME TMP Printf.printf "call, before eval\n"; *)
                                                 List.map (stmt_eval state_with_args) fstmts in
                            let mem_spoiled = (* FIXME TMP Printf.printf "call, before spoil\n"; *)
                                              List.fold_left2
                              (fun mem (m, t) e -> argsspoile (mem, types, vals) m t e)
                              mem ts es in
                            (mem_spoiled, types, vals)
                          | FunV _, _ -> raise @@ Eval_error "call: function type"
                          | _, FunT _ -> raise @@ Eval_error "call: function val"
                          | _, _ -> raise @@ Eval_error "call: function type & val")
    | WriteS p -> (match pathtype types p with
                     | UnitT (_, w) ->
                       if w == NeverWr
                       then raise @@ Eval_error "write: write tag"
                       else let x = pathvar p in
                            let id = List.assoc x vals in
                            let (mem', v') = valupd mem (mem_get mem id) p ZeroV in
                            (mem_set mem' id v', types, vals)
                     | _ -> raise @@ Eval_error "write: type")
    | ReadS p -> if pathval mem vals p != ZeroV
                 then raise @@ Eval_error "read"
                 else state
    | SeqS (sl, sr) -> let statel = stmt_eval state sl in
                       stmt_eval statel sr
    | ChoiceS (sl, sr) -> let statel = stmt_eval state sl in
                          let stater = stmt_eval state sr in
                          match statel with (meml, typesl, valsl) ->
                          match stater with (memr, typesr, valsr) ->
                          if typesl != typesr || valsl != valsr
                          then raise @@ Eval_error "choice"
                          else (memcomb meml memr, typesl, valsl)

  (* --- program execution --- *)

  let prog_eval (prog : prog) : state =
    match prog with (decls, s) ->
    let init_state = prog_init prog in
    stmt_eval init_state s

  let prog_eval_noret (prog : prog) : unit =
    ignore @@ prog_eval prog

  (* --- tests --- *)

  (* - shortcuts *)

  let ( #. ) x y = SeqS (x, y)

  let v0 = VarP 0
  let v1 = VarP 1
  let v2 = VarP 2
  let v3 = VarP 3
  let v4 = VarP 4
  let v5 = VarP 5
  let vg0 = VarP (globals_min_id)
  let vg1 = VarP (globals_min_id + 1)
  let vg2 = VarP (globals_min_id + 2)
  let vg3 = VarP (globals_min_id + 3)
  let vg4 = VarP (globals_min_id + 4)
  let vg5 = VarP (globals_min_id + 5)

  let rf0E = RefE 0
  let rf1E = RefE 1
  let rf2E = RefE 2
  let rf3E = RefE 3
  let rf4E = RefE 4
  let rf5E = RefE 5
  let rfg0E = RefE globals_min_id
  let rfg1E = RefE (globals_min_id + 1)
  let rfg2E = RefE (globals_min_id + 2)
  let rfg3E = RefE (globals_min_id + 3)
  let rfg4E = RefE (globals_min_id + 4)
  let rfg5E = RefE (globals_min_id + 5)
  let pE p = PathE p

  let drf p = DerefP p
  let access p i = AccessP (p, i)

  let wr x = ReadS x 
  let rd x = WriteS x
  let skp = SkipS

  let uT_r_aw = UnitT (Rd, AlwaysWr)
  let uT_r_mw = UnitT (Rd, MayWr)
  let uT_aw = UnitT (NRd, AlwaysWr)
  let uT_mw = UnitT (NRd, MayWr)
  let uT_r = UnitT (Rd, NeverWr)
  let uT = UnitT (NRd, NeverWr)

  let rfT t = RefT (Rf, t)
  let cpT t = RefT (Cp, t)

  let moded t = ((In, NOut), t)

  let defgu t = VarD (t, UnitE)
  let defg t e = VarD (t, e)

  let wrS p = WriteS p 
  let rdS p = ReadS p 
  let callS f args = CallS (f, args)

  (* - utils tests *)

  let%expect_test "mem add / get / set" =
    let mem = empty_mem in
    let (mem, id1) = mem_add mem ZeroV in 
    let (mem, id2) = mem_add mem SmthV in 
    let (mem, id3) = mem_add mem BotV in 
    Printf.printf "%i %i %i " id1 id2 id3;
    Printf.printf "%b %b %b " (mem_get mem id1 == ZeroV)
                              (mem_get mem id2 == SmthV)
                              (mem_get mem id3 == BotV);
    let mem = mem_set mem id1 BotV in 
    let mem = mem_set mem id2 ZeroV in 
    let mem = mem_set mem id3 SmthV in 
    Printf.printf "%b %b %b" (mem_get mem id1 == BotV)
                              (mem_get mem id2 == ZeroV)
                              (mem_get mem id3 == SmthV);
    [%expect {| 0 1 2 true true true true true true |}]

  (* - basic var tests *)

  let%expect_test "empty" =
    prog_eval_noret ([], SkipS);
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple var" =
    prog_eval_noret ([VarD (UnitT (Rd, MayWr), UnitE)], ReadS (VarP globals_min_id));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple var, no read" =
    try(prog_eval_noret ([VarD (UnitT (NRd, MayWr), UnitE)], ReadS (VarP globals_min_id));
         [%expect.unreachable]);
    with Eval_error msg -> Printf.printf "%s" msg;
    [%expect {| read |}]

  let%expect_test "simple vars, no read & read" =
    prog_eval_noret ([VarD (UnitT (NRd, MayWr), UnitE);
                      VarD (UnitT (Rd, MayWr), UnitE)],
                     ReadS (VarP (globals_min_id + 1)));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple var, write" =
    prog_eval_noret ([VarD (UnitT (NRd, MayWr), UnitE)], WriteS (VarP globals_min_id));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple var, no write" =
    try(prog_eval_noret ([VarD (UnitT (NRd, NeverWr), UnitE)], WriteS (VarP globals_min_id));
         [%expect.unreachable]);
    with Eval_error msg -> Printf.printf "%s" msg;
    [%expect {| write: write tag |}]

  let%expect_test "simple var, write & read" =
    prog_eval_noret ([VarD (UnitT (NRd, MayWr), UnitE)], SeqS (WriteS (VarP globals_min_id),
                                                               ReadS (VarP globals_min_id)));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* - basic call tests *)

  (* let%expect_test "simple call with read" = *)
    (* prog_eval_noret ([VarD (UnitT (Rd, NeverWr), UnitE); *)
                      (* FunD ([(In, NOut), UnitT (Rd, NeverWr)], ReadS (VarP 0))], *)
                     (* CallS (VarP (globals_min_id + 1), *)
                            (* [PathE (VarP globals_min_id)])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "simple call with write" = *)
    (* prog_eval_noret ([VarD ((UnitT (Rd, MayWr)), UnitE); *)
                      (* VarD (RefT (Rf, (UnitT (Rd, MayWr))), RefE globals_min_id); *)
                      (* FunD ([(In, NOut), RefT (Cp, UnitT (Rd, MayWr))], WriteS (DerefP (VarP 0)))], *)
                     (* CallS (VarP (globals_min_id + 2), *)
                            (* [PathE (VarP (globals_min_id + 1))])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  let%expect_test "simple call with read, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_mw;
        defg (rfT uT_r_mw) rfg0E;
        FunD (
          [moded @@ cpT @@ uT_r],
          rdS @@ drf @@ v0
        )
      ],
      callS vg2 [pE vg1]
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple call with write, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_mw;
        defg (rfT uT_r_mw) rfg0E;
        FunD (
          [moded @@ cpT @@ uT_r_mw],
          wrS @@ drf @@ v0
        )
      ],
      callS vg2 [pE vg1]
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple call with read after write, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_mw;
        defg (rfT uT_r_mw) rfg0E;
        FunD (
          [moded @@ cpT @@ uT_mw],
          (wrS @@ drf @@ v0) #.
          (rdS @@ drf @@ v0)
        )
      ],
      callS vg2 [pE vg1]
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple call with forbidden write, dsl" =
    try (prog_eval_noret (
      [
        defgu uT_r_mw;
        defg (rfT uT_r_mw) rfg0E;
        FunD (
          [moded @@ cpT @@ uT_r],
          wrS @@ drf @@ v0
        )
      ],
      callS vg2 [pE vg1]
    );
    [%expect.unreachable]);
    with Eval_error msg -> Printf.printf "%s" msg;
    [%expect {| write: write tag |}]

  (* TODO: FIXME: why is condition on always write in parent ?? *)
  let%expect_test "simple call with write to ref, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        FunD (
          [moded @@ rfT @@ uT_aw],
          wrS @@ drf @@ v0
        )
      ],
      callS vg2 [pE vg1]
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple call with forbidden write to ref, dsl" =
    try (prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        FunD (
          [moded @@ rfT @@ uT_aw],
          wrS @@ drf @@ v0
        )
      ],
      (callS vg2 [pE vg1]) #.
      (rdS @@ drf @@ vg1)
    );
    [%expect.unreachable]);
    with Eval_error msg -> Printf.printf "%s" msg;
    [%expect {| read |}]

  (* let%expect_test "call inside call, dsl" = *)
    (* prog_eval_noret ( *)
      (* [ *)
        (* defgu uT_r_aw; *)
        (* defg (rfT uT_r_aw) rfg0E; *)
        (* FunD ( *)
          (* [moded @@ rfT @@ uT_aw], *)
          (* wrS @@ drf @@ v0 *)
        (* ); *)
        (* FunD ( *)
          (* [moded @@ cpT @@ uT_aw], *)
          (* (callS vg2 [pE v0]) #. *)
          (* (wrS @@ drf @@ v0) *)
        (* ) *)
      (* ], *)
      (* (callS vg3 [pE vg1]) #. *)
      (* (rdS @@ drf @@ vg1) *)
    (* ); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  let%expect_test "simple call with global variable usage, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        FunD (
          [moded @@ cpT @@ uT_aw],
          (wrS @@ vg0) #.
          (rdS @@ drf @@ vg1)
        )
      ],
      (callS vg2 [pE vg1]) #.
      (rdS @@ drf @@ vg1)
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple call with read & write (2 args), dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        FunD (
          [
            moded @@ rfT @@ uT_r;
            moded @@ rfT @@ uT_aw;
          ],
          (rdS @@ drf @@ v0) #.
          (wrS @@ drf @@ v1)
        )
      ],
      callS vg4 [pE vg1; pE vg3]
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- FIXME --- CURRENT REWRITE POINT --- FIXME --- *)

  (* --- tests --- *)

  (* let rwi_value : tag = (Rd, AlwaysWr, Cp, In, NOut) *)
  (* let rmwi_value : tag = (Rd, MayWr, Cp, In, NOut) *)
  (* let ri_value : tag = (Rd, NeverWr, Cp, In, NOut) *)
  (* let wi_value : tag = (NRd, AlwaysWr, Cp, In, NOut) *)
  (* let mwi_value : tag = (NRd, MayWr, Cp, In, NOut) *)
  (* let i_value : tag = (NRd, NeverWr, Cp, In, NOut) *)
  (* let rwi_ref : tag = (Rd, AlwaysWr, Rf, In, NOut) *)
  (* let rmwi_ref : tag = (Rd, MayWr, Rf, In, NOut) *)
  (* let ri_ref : tag = (Rd, NeverWr, Rf, In, NOut) *)
  (* let wi_ref : tag = (NRd, AlwaysWr, Rf, In, NOut) *)
  (* let mwi_ref : tag = (NRd, MayWr, Rf, In, NOut) *)
  (* let i_ref : tag = (NRd, NeverWr, Rf, In, NOut) *)

  (* >> tests without functions *)

  (* let%expect_test "empty" = *)
    (* eval_prog ([], ([], [])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "ref param in main failure" = *)
    (* try (eval_prog ([], ([i_ref], [])); *)
         (* [%expect.unreachable]) *)
    (* with Ref_rvalue_argument id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* let%expect_test "read empty args" = *)
    (* try (eval_prog ([], ([], [Read 0])); *)
         (* [%expect.unreachable]) *)
    (* with Not_found -> Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "write empty args" = *)
    (* try (eval_prog ([], ([], [Write 0])); *)
         (* [%expect.unreachable]) *)
    (* with Not_found -> Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "simple write" = *)
    (* eval_prog ([], ([wi_value], [Write 0])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "simple read" = (* NOTE: should not work with read-before-write check*) *)
    (* eval_prog ([], ([ri_value], [Read 0])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "multiple read & write" = *)
    (* eval_prog ([], ([rwi_value], [Write 0; Read 0; Write 0; Write 0; Read 0; Read 0])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "multiple read & write, multiple args" = *)
    (* eval_prog ([], ([wi_value; wi_value; wi_value], [Write 0; Read 0; Write 1; Write 0; Write 2; Read 1; Write 2; Read 0; Read 2])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "main, access out of range" = *)
    (* try(eval_prog ([], ([wi_value], [Write 0; Read 5 ])); *)
         (* [%expect.unreachable]) *)
    (* with Not_found -> Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "main, access out of range" = *)
    (* try(eval_prog ([], ([wi_value], [Write 0; Write 5 ])); *)
         (* [%expect.unreachable]) *)
    (* with Not_found -> Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* >> tests with one function *)

  (* let%expect_test "simple function call with value arg" = *)
    (* eval_prog ([([wi_value], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "simple function call with ref arg" = *)
    (* eval_prog ([([wi_ref], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with value arg & read" = *)
    (* eval_prog ([([wi_value], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Read 0 ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* --- *)

  (* let%expect_test "function with ref arg & read" = *)
    (* try (eval_prog ([([rwi_ref], [Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Read 0 ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_memory_access id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* let%expect_test "function with ref arg & call twice" = *)
    (* try (eval_prog ([([rwi_ref], [Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Call (0, [0]) ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_memory_access id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* NOTE: behaviour is fixed with new capabilities *)
  (* let%expect_test "function with ref arg, write first & call twice" = *)
    (* eval_prog ([([wi_ref], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)


  (* let%expect_test "function with ref arg & read, write" = *)
    (* try (eval_prog ([([rwi_ref], [Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Read 0; Write 0 ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_memory_access id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* let%expect_test "function with ref arg & write, read" = *)
    (* eval_prog ([([rwi_ref], [Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Write 0; Read 0 ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with ref arg, no write inside & read" = *)
    (* eval_prog ([([ri_ref], [Read 0; Read 0])], ([wi_value], [Write 0; Call (0, [0]); Read 0 ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* --- *)

  (* let%expect_test "function with value arg, read out of range" = *)
    (* try(eval_prog ([([ri_ref], [Read 0; Read 1])], ([wi_value; i_value], [Write 0; Call (0, [0]); Read 0 ])); *)
         (* [%expect.unreachable]) *)
    (* with Not_found -> Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with ref arg, read out of range" = *)
    (* try(eval_prog ([([ri_ref], [Read 0; Read 1])], ([wi_value; i_value], [Write 0; Call (0, [0]); Read 0 ])); *)
         (* [%expect.unreachable]) *)
    (* with Not_found -> Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with value arg, write out of range" = *)
    (* try(eval_prog ([([rwi_value], [Read 0; Write 1])], ([wi_value; i_value], [Write 0; Call (0, [0]); Read 0 ])); *)
         (* [%expect.unreachable]) *)
    (* with Not_found -> Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with value arg, call out of range" = *)
    (* try(eval_prog ([([ri_value], [Read 0])], ([wi_value; i_value], [Write 0; Call (0, [2]); Read 0 ])); *)
         (* [%expect.unreachable]) *)
    (* with Not_found -> Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* --- *)

  (* let%expect_test "function with ref & value args, no write inside & read" = *)
    (* eval_prog ( *)
      (* [([ri_ref; ri_value], [Read 0; Read 1])], *)
      (* ([wi_value; wi_value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with ref & value args, write value inside & read" = *)
    (* eval_prog ( *)
      (* [([ri_ref; rwi_value], [Read 0; Read 1; Write 1; Read 1])], *)
      (* ([wi_value; wi_value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with ref & value args, write both inside & read" = *)
    (* try (eval_prog ( *)
      (* [([rwi_ref; rwi_value],[Read 0; Read 1; Write 0; Write 1; Read 1])], *)
      (* ([wi_value; wi_value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_memory_access id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* --- *)

  (* let%expect_test "function with ref two same ref args, read both & read" = *)
    (* eval_prog ( *)
      (* [([ri_ref; ri_ref],[Read 0; Read 1; Read 1])], *)
      (* ([wi_value], [Write 0; Call (0, [0; 0]); Read 0 ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with ref two same ref args, read both & nothing" = *)
    (* eval_prog ( *)
      (* [([ri_ref; ri_ref],[Read 0; Read 1; Read 1])], *)
      (* ([wi_value], [Write 0; Call (0, [0; 0]); ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with ref & copy of the same arg, read & write both & nothing" = *)
    (* eval_prog ( *)
      (* [([rwi_ref; rwi_value],[Read 0; Read 1; Write 0; Write 1; Read 1])], *)
      (* ([wi_value], [Write 0; Call (0, [0; 0]); ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "function with copy & ref of the same arg, read & write both & nothing" = *)
    (* eval_prog ( *)
      (* [([rwi_value; rwi_ref],[Read 0; Read 1; Write 0; Write 1; Read 1])], *)
      (* ([wi_value], [Write 0; Call (0, [0; 0]); ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* TODO: FIXME: now correct (use state before for mem check), is this good ?, proper way to fix ? *)
  (* let%expect_test "function with ref two same ref args, read & write both, error" = *)
    (* try ( *)
      (* eval_prog ( *)
      (* [([rwi_ref; rwi_ref],[Read 0; Read 1; Write 0; Write 1; Read 1])], *)
      (* ([wi_value], [Write 0; Call (0, [0; 0]); ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* >> tests with several functions *)

  (* let%expect_test "two functions with ref arg, read func -> write func" = *)
    (* eval_prog ( *)
      (* [([ri_ref], [Read 0]); ([wi_ref], [Write 0])], *)
      (* ([wi_value], [Write 0; Call (0, [0]); Read 0; Call (1, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "two functions with ref arg, write func -> read func" = *)
    (* try (eval_prog ( *)
      (* [([ri_ref], [Read 0]); ([wi_ref], [Write 0])], *)
      (* ([wi_value], [Write 0; Call (1, [0]); Call (0, [0]) ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_memory_access id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* let%expect_test "two functions: ref arg after value arg" = *)
    (* eval_prog ( *)
      (* [([rwi_ref], [Read 0; Write 0]); ([rwi_value], [Read 0; Write 0])], *)
      (* ([wi_value], [Write 0; Call (1, [0]); Read 0; Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "two functions: value arg after spoiled ref arg" = *)
    (* try (eval_prog ( *)
      (* [([rwi_ref], [Read 0; Write 0]); ([rwi_value], [Read 0; Write 0])], *)
      (* ([wi_value], [Write 0; Call (0, [0]); Call (1, [0]) ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_memory_access id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* --- *)

  (* let%expect_test "simple function call with value arg, const cast error" = *)
    (* try (eval_prog ([([ri_value], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_const_cast id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* let%expect_test "simple function call with ref arg, const cast error" = *)
    (* try (eval_prog ([([ri_ref], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_const_cast id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* let%expect_test "simple function call with value arg, const cast ok" = *)
    (* eval_prog ([([ri_value], [Read 0])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "simple function call with ref arg, const cast ok" = *)
    (* eval_prog ([([ri_ref], [Read 0])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* --- *)

  (* let%expect_test "simple function call with arg, recursive calls" = *)
    (* eval_prog ([([rwi_value], [Write 0; Read 0; Write 0; Call (0, [0])])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* --- *)

  (* TODO: out arguments test, etc. *)

  (* --- *)

  (* TODO: more Combine statement tests *)

  (* let%expect_test "simple function call with value arg and choice, rw" = *)
    (* eval_prog ([([wi_value], [Choice ([Write 0; Read 0], [Write 0]); Read 0])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "simple function call with ref arg and choice, rw" = *)
    (* try (eval_prog ([([ri_ref], [Choice ([Read 0], [Write 0])])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
         (* [%expect.unreachable]) *)
    (* with Incorrect_const_cast id -> Printf.printf "%i" id; *)
    (* [%expect {| 0 |}] *)

  (* let%expect_test "simple function call with ref arg and choice, rr" = *)
    (* eval_prog ([([ri_ref], [Choice ([Read 0], [Read 0; Read 0])])], ([wi_value], [Write 0; Call (0, [0]) ])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

end
