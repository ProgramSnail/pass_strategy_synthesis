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

  type decl = VarD of (* data * *) atype (* * expr *)
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

  (* type deepvalue = ZeroDV *)
                 (* | SmthDV *)
                 (* | BotDV *)
                 (* | FunDV of ((* data list * *) stmt) list *)
                 (* | RefDV of deepvalue *)
                 (* | TupleDV of deepvalue list *)

  type memval = ZeroMV | SmthMV | BotMV (* | TopMV ?? *)
  type readval = ZeroRV | OneRV | TopRV
  type writeval = ZeroWV | SmthWV | OneWV

  type value = UnitV of memval * readval * writeval
             | FunV (* of ((* data list * *) stmt) list *)
             | RefV of memid
             | TupleV of value list

  type revpath = VarRP | DerefRP of revpath | AccessRP of revpath * data

  type action = ReadA | AlwaysWriteA | MayWriteA

  (* TODO: any additional difference between rvalue and lvalue now ?? *)

  (* --- *)

  type mem = value list * memid (* NOTE: memory and first free elem *)
  type types = (data * atype) list
  type vals = (data * memid) list
  type state = mem * types * vals

  (* --- *)

  (* - state utils *)

  let types_assoc (x : data) (types : types) : atype =
    (* try ( List.assoc x (fst types) ) *)
    (* with Not_found -> *)
    List.assoc x types
  let vals_assoc (x : data) (vals : vals) : memid =
    (* try ( List.assoc x (fst vals) ) *)
    (* with Not_found -> *)
    List.assoc x vals

  let types_add (types : types) (x : data) (t : atype) =
    (x, t) :: types

  let vals_add (vals : vals) (x : data) (id : memid) =
    (x, id) :: vals

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

  (* let rec v_to_deepv (mem : mem) (v : value) : deepvalue = match v with *)
    (* | ZeroV -> ZeroDV *)
    (* | SmthV -> SmthDV *)
    (* | BotV -> BotDV *)
    (* | FunV s -> FunDV s *)
    (* | RefV id -> RefDV (v_to_deepv mem @@ mem_get mem id) *)
    (* | TupleV vs -> TupleDV (List.map (v_to_deepv mem) vs) *)

  let is_trivial_v (v : value) : bool =
    match v with | UnitV (_, _, _) -> true
                 | _ -> false

  (* --- path accessors --- *)

  let rec pathvar (p : path) : data = match p with
    | VarP x -> x
    | DerefP p -> pathvar p
    | AccessP (p, _) -> pathvar p

  let rec pathrev (p : path) (acc : revpath) : revpath = match p with
    | VarP x -> acc
    | DerefP p -> pathrev p @@ DerefRP acc
    | AccessP (p, i) -> pathrev p @@ AccessRP (acc, i)

  let rec pathtype (types : types) (p : path) : atype = match p with
    | VarP x -> types_assoc x types
    | DerefP p -> (match pathtype types p with
                    | RefT (_, t) -> t
                    | _ -> raise @@ Typing_error "pathtype: deref")
    | AccessP (p, id) -> match pathtype types p with
                           | TupleT ts -> (* FIXME TMP Printf.printf "pathtype access sz=%i id=%i\n" (List.length ts) id; *)
                                          (List.nth ts id)
                           | _ -> raise @@ Typing_error "pathtype: access"

  let rec pathval (mem :  mem) (vals : vals) (p : path) : value = match p with
    | VarP x -> mem_get mem @@ ((* Printf.printf "%i: " x; (* FIXME TMP *)
                                ignore @@ List.map (fun (x, _) -> Printf.printf "%i " x) vals;
                                Printf.printf "mem size: %i, " (List.length (fst mem));
                                Printf.printf "mem size stored: %i " (snd mem);
                                Printf.printf "\n"; *)
                                vals_assoc x vals)
    | DerefP p -> (match pathval mem vals p with
                    | RefV id -> mem_get mem id
                    | _ -> raise @@ Typing_error "pathval: deref")
    | AccessP (p, id) -> match pathval mem vals p with
                           | TupleV vs -> (* FIXME TMP Printf.printf "pathval access sz=%i id=%i\n" (List.length vs) id; *)
                                          (List.nth vs id)
                           | _ -> raise @@ Typing_error "pathval: access"

  (* --- eval rules --- *)

  (* - value construction *)

  let rec valbuild (mem : mem) (t : atype) : mem * value =
    match t with
    | UnitT (Rd, _) -> (mem, UnitV (ZeroMV, ZeroRV, ZeroWV))
    | UnitT (NRd, _) -> (mem, UnitV (BotMV, ZeroRV, ZeroWV))
    | FunT _ -> raise @@ Typing_error "valbuild: funciton value is not supported"
    | RefT (_, t) -> let (mem', v') = valbuild mem t in
                     let (mem'', id'') = mem_add mem' v' in
                     (mem'', RefV id'') 
    | TupleT ts -> let folder = fun t (mem, vs') -> let (mem', v') = valbuild mem t in
                                                        (mem', v' :: vs') in 
                   let mem', vs' = List.fold_right folder ts (mem, []) in
                   (mem', TupleV vs')

  (* NOTE: not needed now *)
  (* let rec valcopy (mem : mem) (v : value) (t : atype) : mem * value = *)
    (* match t, v with *)
    (* | UnitT (Rd, _), UnitV (v_m, _, _) -> (mem, UnitV (v_m, ZeroRV, ZeroWV)) *)
    (* | UnitT (NRd, _), UnitV _ -> (mem, UnitV (BotMV, ZeroRV, ZeroWV)) *)
    (* | FunT _, FunV -> (mem, v) *)
    (* | RefT (Rf, _), RefV _ -> (mem, v) *)
    (* | RefT (_, t), RefV id -> let (mem', v') = valcopy mem (mem_get mem id) t in *)
                               (* let (mem'', id'') = mem_add mem' v' in *)
                               (* (mem'', RefV id'') *) 
    (* | TupleT ts, TupleV vs -> let folder = fun v t (mem, vs') -> let (mem', v') = valcopy mem v t in *)
                                                                 (* (mem', v' :: vs') in *) 
                              (* let mem', vs' = List.fold_right2 folder vs ts (mem, []) in *)
                              (* (mem', TupleV vs') *)
    (* | _, _ -> raise @@ Typing_error "valcopy: not trivial value, wrong type" *)

  (* - action rules *)

  let memvmod (a : action) (v_m : memval) : memval =
    match a, v_m with
      | ReadA, ZeroMV -> ZeroMV
      | ReadA, _ -> raise @@ Eval_error "memvmod: forbidden read"
      | AlwaysWriteA, _ -> ZeroMV
      | MayWriteA, ZeroMV -> ZeroMV
      | MayWriteA, _ -> SmthMV

  let readvmod (a : action) (v_r : readval) : readval =
    match a, v_r with
      | _, TopRV -> TopRV
      | _, OneRV -> OneRV
      | ReadA, ZeroRV -> OneRV
      | AlwaysWriteA, ZeroRV -> TopRV
      | MayWriteA, ZeroRV -> ZeroRV

  let writevmod (a : action) (v_w : writeval) : writeval =
    match a, v_w with
      | ReadA, v -> v
      | AlwaysWriteA, _ -> OneWV
      | MayWriteA, OneWV -> OneWV
      | MayWriteA, v -> v

  (* - value update *)

  let rec valchange (mem : mem) (v : value) (p : revpath) (b : value) : mem * value = match p, v with
    | VarRP, _ -> (mem, b)
    | DerefRP p, RefV id -> let (mem', v') = valchange mem (mem_get mem id) p b in
                            (mem_set mem' id v', RefV id)
    | AccessRP (p, id), TupleV vs -> let (mem', v') = valchange mem (List.nth vs id) p b in
                                     (mem', TupleV (list_replace vs id v'))
    | _, _ -> raise @@ Typing_error "valupd"

  let rec valupd (mem : mem) (v : value) (p : revpath) (a : action) : mem * value = match p, v with
    | VarRP, UnitV (v_m, v_r, v_w) -> (mem, UnitV (memvmod a v_m, readvmod a v_r, writevmod a v_w))
    | VarRP, RefV id -> let (mem', v') = valupd mem (mem_get mem id) p a in
                            (mem_set mem' id v', RefV id)
    (* TODO: add test on foldl vs foldr in this situation *)
    | VarRP, TupleV vs -> let (mem', vs') = List.fold_right
                                              (fun v (mem, vs') -> let (mem', v') = valupd mem v p a in
                                              (mem', v' :: vs')) vs (mem, []) in
                              (mem', TupleV vs')
    | DerefRP p, RefV id -> let (mem', v') = valupd mem (mem_get mem id) p a in
                            (mem_set mem' id v', RefV id)
    | AccessRP (p, id), TupleV vs -> let (mem', v') = valupd mem (List.nth vs id) p a in
                                     (mem', TupleV (list_replace vs id v'))
    | _, _ -> raise @@ Typing_error "valupd"

  (* - value combination *)

  let memvalcomb (u : memval) (v : memval) : memval =
    match u, v with
      | ZeroMV, ZeroMV -> ZeroMV
      | BotMV, BotMV -> BotMV
      | _, _ -> SmthMV

  let readvalcomb (u : readval) (v : readval) : readval =
    match u, v with
      | TopRV, TopRV -> TopRV
      | ZeroRV, ZeroRV -> ZeroRV
      | TopRV, ZeroRV -> ZeroRV
      | ZeroRV, TopRV -> ZeroRV
      | _, _ -> OneRV

  let writevalcomb (u : writeval) (v : writeval) : writeval =
    match u, v with
      | OneWV, OneWV -> OneWV
      | ZeroWV, ZeroWV -> ZeroWV
      | _, _ -> SmthWV

  let rec valcomb (u : value) (v : value) : value =
    match u, v with
      | UnitV (u_m, u_r, u_w), UnitV (v_m, v_r, v_w) ->
        UnitV (memvalcomb u_m v_m, readvalcomb u_r v_r, writevalcomb u_w v_w)
      | FunV, FunV -> FunV
      | RefV a, RefV b -> if a == b then u else raise @@ Typing_error "valcomb: ref"
      | TupleV us, TupleV vs -> TupleV (List.map2 valcomb us vs)
      | _, _ -> raise @@ Typing_error "valcomb"

  let rec memcomb (m : mem) (n : mem) : mem =
    if snd m != snd n
    then raise @@ Typing_error "memcomb"
    else (List.map2 valcomb (fst m) (fst n), snd m)

  (* - expression evaluation *)

  let rec exprval (mem : mem) (vals : vals) (e : expr) : value = match e with
    | UnitE -> UnitV (ZeroMV, ZeroRV, ZeroWV)
    | PathE p -> pathval mem vals p
    | RefE x -> RefV (vals_assoc x vals)
    | TupleE es -> TupleV (List.map (exprval mem vals) es)

  (* - expression typing *)

  let rec exprtype (types : types) (e : expr) : atype = match e with
    | UnitE -> UnitT (Rd, NeverWr)
    | PathE p -> pathtype types p
    | RefE x -> RefT (Rf, types_assoc x types)
    | TupleE es -> TupleT (List.map (exprtype types) es)

  (* - context initialization *)

  (* let rec valcopy (mem : mem) (v : value) (t : atype) : mem * value = match t, v with *)
  
  (* TODO: check new in vars *)
  let add_decl (state : state) (x : data) (d : decl) : state =
    match state with (mem, types, vals) -> match d with
    | VarD t -> let (mem', v) = valbuild mem t in
                let (mem'', id) = mem_add mem' v in
                (mem'', types_add types x t, vals_add vals x id)
    | FunD (ts, s)  -> let (mem', id) = mem_add mem FunV in
                       (mem', types_add types x (FunT ts), vals_add vals x id)

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

  (* TODO: check assignment type matches types separately later ?? *)
  let is_correct_tags (r : read_cap) (w : write_cap)
                      (m : mode) (c : copy_cap) : bool =
    (snd m != Out || c == Rf) &&
    (snd m != Out || w == AlwaysWr) &&
    (r != Rd || fst m == In)

  let tryread (r : read_cap) (v_m : memval)
              (v_r : readval) (v_w : writeval) : value =
    match r with
      | Rd -> UnitV (memvmod ReadA v_m,
                     readvmod ReadA v_r,
                     writevmod ReadA v_w)
      | NRd -> UnitV (v_m, v_r, v_w) 
  
  let tryspoil (m : mode) (w : write_cap) (v_m : memval) : memval =
    match m, w with
      | (_, Out), AlwaysWr -> v_m
      | (_, Out), MayWr -> v_m
      | (_, NOut), AlwaysWr -> BotMV
      | (_, NOut), MayWr -> SmthMV
      | _ -> raise @@ Typing_error "tryspoil: unexpected pair mode + write cap"

  let rec valspoil (mem : mem) (v : value) (t : atype)
                   (m : mode) (c : copy_cap)
                   : mem * value = match t, v with
    | UnitT (r, w), UnitV (v_m, v_r, v_w) ->
      if not @@ is_correct_tags r w m c
        then raise @@ Typing_error "valspoil: trivial type tags combination is not correct"
      else
        let v' = tryread r v_m v_r v_w in
        if c == Cp || w == NeverWr
          then (mem, v')
        else (match v' with
          | UnitV (v_m', v_r', v_w') ->
            let (v_m'', v_r'', v_w'') =
              (if w == AlwaysWr
                then (memvmod AlwaysWriteA v_m',
                      readvmod AlwaysWriteA v_r',
                      writevmod AlwaysWriteA v_w')
                else (* MayWr *)
                     (memvmod MayWriteA v_m',
                      readvmod MayWriteA v_r',
                      writevmod MayWriteA v_w'))
            in
            let v_m''' = tryspoil m w v_m'' in
            (mem, UnitV (v_m''', v_r'', v_w''))
          | _ -> raise @@ Typing_error "valspoil: value after tryread is not unit")
    | FunT ts, FunV -> (mem, v)
    | RefT (ct, t), RefV id ->
      let (mem', v') = valspoil mem (mem_get mem id) t m ct in
      (mem_set mem id v', RefV id)
    | TupleT ts, TupleV vs ->
        let folder = fun (mem, vs') t v ->
          let (mem', v') = valspoil mem v t m c in (mem', v' :: vs') in
        let (mem', vs') = List.fold_left2 folder (mem, []) ts vs in
        (mem', TupleV (List.rev vs'))
    | _, _ ->  raise @@ Typing_error "valspoil"

  (* full spoil *)

  let argsspoilp (state : state) (m : mode) (t : atype) (p : path) : mem =
    match state with (mem, types, vals) ->
    let x = pathvar p in
    let id = vals_assoc x vals in (* base var address *)
    let b = pathval mem vals p in (* subvalue in var *)
    (* let t' = pathtype types p in (* type of subvalue *) *)
    let (mem', b') = valspoil mem b t m Cp in (* spoil subvalue *)
    (* TODO: FIXME: why copy (Cp)? maybe sometimes use top-level capability ? *)
    let pi = pathrev p VarRP in
    let (mem'', v'') = valchange mem' (mem_get mem' id) pi b' in (* set subvalue into var *)
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

  let addarg (state : state) (x : data) (t : atype) : state =
    match state with (mem, types, vals) ->
    let (mem', v) = valbuild mem t in
    let (mem'', id) = mem_add mem' v in
    (mem'', types_add types x t, vals_add vals x id)

  let writeval_to_cap (v_w : writeval) : write_cap =
    match v_w with
      | ZeroWV -> NeverWr
      | SmthWV -> MayWr
      | OneWV -> AlwaysWr

  let rec tags_check (mem : mem) (v : value) (t : atype) : unit =
    match v, t with
      | UnitV (v_m, v_r, v_w), UnitT (r, w) ->
        if (r == Rd) && (v_r != OneRV)
          then raise @@ Eval_error "tags_check: wrong read tag"
        else if (r == NRd) && (v_r == OneRV)
          then raise @@ Eval_error "tags_check: wrong not read tag"
        else if writeval_to_cap v_w != w
          then raise @@ Eval_error "tags_check: wrong write tag"
        else ()
      | FunV, FunT _ -> ()
      | RefV id, RefT (_, t) -> tags_check mem (mem_get mem id) t
      | TupleV vs, TupleT ts -> ignore @@ List.map2 (tags_check mem) vs ts
      | _, _ -> raise @@ Typing_error "tags_check"

  (* - writability check *)

  let rec is_all_type_writable (t : atype) : bool =
    match t with
      | UnitT (_, w) -> w == MayWr || w == AlwaysWr
      | FunT _ -> true
      | RefT (_, t) -> is_all_type_writable t
      | TupleT ts -> List.for_all is_all_type_writable ts


  (* - function evaluation *)

  let rec func_eval (state : state) (d : decl) : unit =
    match d with
    | FunD (ts, stmt) ->
      (match state with (mem, types, vals) ->
       let (state_with_args, _) = List.fold_left
         (fun (st, x) (m, t) -> (addarg st x t, x + 1))
         (state, 0) ts in
    (* NOTE: same x's, so can use same args for all the statements *)
       match stmt_eval state_with_args stmt with (mem_after_stmt, _, vals_after_stmt) ->
       ignore @@ List.fold_left
         (fun x (_, t) ->
            let id = vals_assoc x vals_after_stmt in
            let v = mem_get mem_after_stmt id in
            tags_check mem_after_stmt v t; x + 1)
         0 ts)
    | VarD _ -> ()

  (* - statement evaluation *)

  and stmt_eval (state : state) (s : stmt) : state =
    match state with (mem, types, vals) -> match s with
    | SkipS -> state
    | CallS (f, es) -> let v = pathval mem vals f in
                       let t = pathtype types f in
                       (match v, t with
                          | FunV, FunT ts ->
                             let mem_spoiled = List.fold_left2
                               (fun mem (m, t) e -> argsspoile (mem, types, vals) m t e)
                               mem ts es in
                             (mem_spoiled, types, vals)
                          | FunV, _ -> raise @@ Eval_error "call: function type"
                          | _, FunT _ -> raise @@ Eval_error "call: function val"
                          | _, _ -> raise @@ Eval_error "call: function type & val")
    | WriteS p -> if not @@ is_all_type_writable @@ pathtype types p
                  then raise @@ Eval_error "write: write tag"
                  else let x = pathvar p in
                       let id = vals_assoc x vals in
                       let pi = pathrev p VarRP in
                       let (mem', v') = valupd mem (mem_get mem id) pi AlwaysWriteA in
                       (mem_set mem' id v', types, vals)
    | ReadS p -> let x = pathvar p in
                 let id = vals_assoc x vals in
                 let pi = pathrev p VarRP in
                 let (mem', v') = valupd mem (mem_get mem id) pi ReadA in
                 (mem_set mem' id v', types, vals)
                 (* NOTE: handled inside through undefined in memvmod *)
                 (* if pathval mem vals p == SmthV || pathval mem vals p == BotV *) 
                 (* then raise @@ Eval_error "read: spoiled value" *)
    | SeqS (sl, sr) -> let statel = stmt_eval state sl in
                       stmt_eval statel sr
    | ChoiceS (sl, sr) -> let statel = stmt_eval state sl in
                          let stater = stmt_eval state sr in
                          match statel with (meml, typesl, valsl) ->
                          match stater with (memr, typesr, valsr) ->
                          if typesl != typesr || valsl != valsr
                          then raise @@ Eval_error "choice"
                          (* TODO: FIXME: better list union ??  *)
                          else (memcomb meml memr, typesl, valsl)

  (* --- program execution --- *)

  let prog_eval (prog : prog) : state =
    match prog with (decls, s) ->
    let init_state = prog_init prog in
    ignore @@ List.map (func_eval init_state) decls;
    stmt_eval init_state s

  let prog_eval_noret (prog : prog) : unit =
    ignore @@ prog_eval prog

  (* --- tests --- *)

  (* - shortcuts *)

  let ( #. ) x y = SeqS (x, y)
  let ( |. ) x y = ChoiceS (x, y)

  let v0 = VarP 0
  let v1 = VarP 1
  let v2 = VarP 2
  let v3 = VarP 3
  let v4 = VarP 4
  let v5 = VarP 5
  let v6 = VarP 6
  let v7 = VarP 7
  let v8 = VarP 8
  let vg0 = VarP globals_min_id
  let vg1 = VarP (globals_min_id + 1)
  let vg2 = VarP (globals_min_id + 2)
  let vg3 = VarP (globals_min_id + 3)
  let vg4 = VarP (globals_min_id + 4)
  let vg5 = VarP (globals_min_id + 5)
  let vg6 = VarP (globals_min_id + 6)
  let vg7 = VarP (globals_min_id + 7)
  let vg8 = VarP (globals_min_id + 8)
  let vg9 = VarP (globals_min_id + 9)
  let vg10 = VarP (globals_min_id + 10)
  let vg11 = VarP (globals_min_id + 11)

  let rf0E = RefE 0
  let rf1E = RefE 1
  let rf2E = RefE 2
  let rf3E = RefE 3
  let rf4E = RefE 4
  let rf5E = RefE 5
  let rf3E = RefE 3
  let rf4E = RefE 4
  let rf5E = RefE 5
  let rfg0E = RefE globals_min_id
  let rfg1E = RefE (globals_min_id + 1)
  let rfg2E = RefE (globals_min_id + 2)
  let rfg3E = RefE (globals_min_id + 3)
  let rfg4E = RefE (globals_min_id + 4)
  let rfg5E = RefE (globals_min_id + 5)
  let rfg6E = RefE (globals_min_id + 6)
  let rfg7E = RefE (globals_min_id + 7)
  let rfg8E = RefE (globals_min_id + 8)

  let pE p = PathE p

  let drf p = DerefP p
  let access i p = AccessP (p, i)

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

  let defgu t = VarD t
  let defg t e = VarD t

  let wrS p = WriteS p 
  let rdS p = ReadS p 
  let callS f args = CallS (f, args)

  let uV m = UnitV (m, ZeroRV, ZeroWV)

  (* - utils tests *)

  let v_memval_is v m =
    match v with
     | UnitV (v_m, _, _) -> v_m == m
     | _ -> false

  let%expect_test "mem add / get / set" =
    let mem = empty_mem in
    let (mem, id1) = mem_add mem @@ uV ZeroMV in 
    let (mem, id2) = mem_add mem @@ uV SmthMV in 
    let (mem, id3) = mem_add mem @@ uV BotMV in 
    Printf.printf "%i %i %i " id1 id2 id3;
    Printf.printf "%b %b %b " (v_memval_is (mem_get mem id1) ZeroMV)
                              (v_memval_is (mem_get mem id2) SmthMV)
                              (v_memval_is (mem_get mem id3) BotMV);
    let mem = mem_set mem id1 @@ uV BotMV in 
    let mem = mem_set mem id2 @@ uV ZeroMV in 
    let mem = mem_set mem id3 @@ uV SmthMV in 
    Printf.printf "%b %b %b" (v_memval_is (mem_get mem id1) BotMV)
                             (v_memval_is (mem_get mem id2) ZeroMV)
                             (v_memval_is (mem_get mem id3) SmthMV);
    [%expect {| 0 1 2 true true true true true true |}]

  (* - basic var tests *)

  let%expect_test "empty" =
    prog_eval_noret ([], SkipS);
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple var" =
    prog_eval_noret ([VarD (UnitT (Rd, MayWr))],
                      ReadS (VarP globals_min_id));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple var, forbidden read" =
    try(prog_eval_noret ([VarD (UnitT (NRd, MayWr))],
                         ReadS (VarP globals_min_id));
         [%expect.unreachable]);
    with Eval_error msg -> Printf.printf "%s" msg;
    [%expect {| memvmod: forbidden read |}]

  let%expect_test "simple vars, no read & read" =
    prog_eval_noret ([VarD (UnitT (NRd, MayWr));
                      VarD (UnitT (Rd, MayWr))],
                     ReadS (VarP (globals_min_id + 1)));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple var, write" =
    prog_eval_noret ([VarD (UnitT (NRd, MayWr))],
                     WriteS (VarP globals_min_id));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple var, forbidden write" =
    try(prog_eval_noret ([VarD (UnitT (NRd, NeverWr))],
                         WriteS (VarP globals_min_id));
         [%expect.unreachable]);
    with Eval_error msg -> Printf.printf "%s" msg;
    [%expect {| write: write tag |}]

  let%expect_test "simple var, write & read" =
    prog_eval_noret ([VarD (UnitT (NRd, MayWr))],
                     SeqS (WriteS (VarP globals_min_id),
                           ReadS (VarP globals_min_id)));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* - basic call tests *)

  (* let%expect_test "simple call with read" = *)
    (* prog_eval_noret ([VarD (UnitT (Rd, NeverWr)); *)
                      (* FunD ([((In, NOut), UnitT (Rd, NeverWr)], ReadS (VarP 0)))], *)
                     (* CallS (VarP (globals_min_id + 1), *)
                            (* [PathE (VarP globals_min_id)])); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* let%expect_test "simple call with write" = *)
    (* prog_eval_noret ([VarD ((UnitT (Rd, MayWr))); *)
                      (* VarD (RefT (Rf, UnitT (Rd, MayWr)), RefE globals_min_id); *)
                      (* FunD ([((In, NOut), RefT (Cp, UnitT (Rd, MayWr)))], WriteS (DerefP (VarP 0)))], *)
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
        defgu uT_aw;
        defg (rfT uT_aw) rfg0E;
        FunD (
          [moded @@ cpT @@ uT_aw],
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
        defgu uT_aw;
        defg (rfT uT_aw) rfg0E;
        FunD (
          [moded @@ cpT @@ uT_aw],
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
    [%expect {| memvmod: forbidden read |}]

  let%expect_test "simple call with write to ref with fix, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        FunD (
          [moded @@ rfT @@ uT_aw],
          wrS @@ drf @@ v0
        )
      ],
      (callS vg2 [pE vg1]) #.
      (wrS @@ drf @@ vg1) #.
      (rdS @@ drf @@ vg1)
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "call inside call, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        FunD (
          [moded @@ rfT @@ uT_aw],
          wrS @@ drf @@ v0
        );
        FunD (
          [moded @@ cpT @@ uT_aw],
          (callS vg2 [pE v0]) #.
          (wrS @@ drf @@ v0)
        )
      ],
      (callS vg3 [pE vg1]) #.
      (rdS @@ drf @@ vg1)
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  (* NOTE: memoization used *)
  let%expect_test "call inside call, recursive, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        FunD (
          [moded @@ cpT @@ uT_aw],
          (callS vg2 [pE v0]) #.
          (wrS @@ drf @@ v0)
        )
      ],
      (callS vg2 [pE vg1]) #.
      (rdS @@ drf @@ vg1)
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "call to fix after call, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        FunD (
          [moded @@ rfT @@ uT_aw],
          wrS @@ drf @@ v0
        );
        FunD (
          [((In, Out), rfT @@ uT_aw)],
          wrS @@ drf @@ v0
        )
      ],
      (callS vg2 [pE vg1]) #.
      (callS vg3 [pE vg1]) #.
      (rdS @@ drf @@ vg1)
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple call with global variable usage, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r) rfg0E;
        FunD (
          [moded @@ cpT @@ uT],
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
        defgu uT_r;
        defg (rfT uT_r) rfg0E;
        defgu uT_aw;
        defg (rfT uT_aw) rfg2E;
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

  let%expect_test "simple call with different arguments modifiers, copy, dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E;
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg2E;
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg4E;
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg6E;
        FunD (
          [
            ((NIn, NOut), cpT @@ uT);
            ((In, NOut), cpT @@ uT_r_aw);
            ((NIn, Out), rfT @@ uT_aw);
            ((In, Out), rfT @@ uT_r_aw);
          ],
          (rdS @@ drf @@ v1) #.
          (rdS @@ drf @@ v3) #.
          (wrS @@ drf @@ v1) #.
          (wrS @@ drf @@ v2) #.
          (wrS @@ drf @@ v3)
        )
      ],
      (callS vg8 [pE vg1; pE vg3; pE vg5; pE vg7]) #.
      (rdS @@ drf @@ vg1) #.
      (rdS @@ drf @@ vg3) #.
      (rdS @@ drf @@ vg5) #.
      (rdS @@ drf @@ vg7)
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple call with different arguments modifiers, ref, dsl" =
    prog_eval_noret (
      [
        defgu uT_r;
        defg (rfT uT_r) rfg0E;
        defgu uT_r;
        defg (rfT uT_r) rfg2E;
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg4E;
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg6E;
        FunD (
          [
            ((NIn, NOut), rfT @@ uT);
            ((In, NOut), rfT @@ uT_r);
            ((NIn, Out), rfT @@ uT_aw);
            ((In, Out), rfT @@ uT_r_aw);
          ],
          (rdS @@ drf @@ v1) #.
          (rdS @@ drf @@ v3) #.
          (wrS @@ drf @@ v2) #.
          (wrS @@ drf @@ v3)
        )
      ],
      (callS vg8 [pE vg1; pE vg3; pE vg5; pE vg7]) #.
      (rdS @@ drf @@ vg1) #.
      (rdS @@ drf @@ vg3) #.
      (rdS @@ drf @@ vg5) #.
      (rdS @@ drf @@ vg7)
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  (* - tests for presentation *)

  let%expect_test "presentation test 1 (simple types), dsl" =
    prog_eval_noret (
      [
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg0E; (* x *)
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg2E; (* y *)
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg4E; (* z *)
        defgu uT_r_aw;
        defg (rfT uT_r_aw) rfg6E; (* k *)
        FunD ( (* f *)
          [
            (moded @@ rfT @@ uT_r_aw);
            (moded @@ rfT @@ uT_r);
          ],
          (rdS @@ drf @@ v0) #.
          (wrS @@ drf @@ v0) #.
          (rdS @@ drf @@ v1)
        );
        FunD ( (* w *)
          [
            (moded @@ cpT @@ uT_mw);
          ],
          (wrS @@ drf @@ v0) |. skp
        );
        FunD ( (* g *)
          [
            (moded @@ rfT @@ uT_aw);
            (moded @@ cpT @@ uT_r_mw);
          ],
          (wrS @@ drf @@ v0) #.
          ((wrS @@ drf @@ v1) |. (wrS @@ drf @@ v0)) #.
          (rdS @@ drf @@ v0) #.
          (rdS @@ drf @@ v1)
        );
        FunD ( (* r *)
          [
            (moded @@ rfT @@ uT_r);
          ],
          (rdS @@ drf @@ v0)
        )
      ],
      let xV = vg1 in
      let yV = vg3 in
      let zV = vg5 in
      let kV = vg7 in
      let fF = vg8 in
      let wF = vg9 in
      let gF = vg10 in
      let rF = vg11 in
      (callS wF [pE xV]) #.
      (callS rF [pE xV]) #.
      (callS fF [pE xV; pE yV]) #.
      (callS rF [pE yV]) #.
      (callS gF [pE zV; pE kV]) #.
      (wrS @@ drf @@ zV) #.
      (callS wF [pE zV]) #.
      (callS fF [pE yV; pE zV]) #.
      (callS rF [pE kV])
    );
    Printf.printf "done!";
    [%expect {| done! |}]

  (* TODO tags, access *)
  (* let%expect_test "presentation test 2 (complex types), dsl" = *)
    (* prog_eval_noret ( *)
      (* let userT = TupleT [uT_r_aw; uT_r_aw; uT_r_aw] in *)
      (* let dataT =  TupleT [uT_r_aw; uT_r_aw] in *)
      (* let requestT = TupleT [cpT userT; *)
                             (* cpT dataT; *)
                             (* cpT dataT] in *)
      (* let requestArgsT = TupleT [cpT userT; (* TODO: tags *) *)
                                 (* cpT dataT; *)
                                 (* cpT dataT] in *)
      (* let userE = TupleE [UnitE; UnitE; UnitE] in *)
      (* let dataE =  TupleE [UnitE; UnitE] in *)
      (* let requestE = TupleE [rfg0E; rfg1E; rfg2E] in *)
      (* [ *)
        (* defg userT userE; *)
        (* defg dataT dataE; *)
        (* defgu uT_r_aw; (* time *) *)
        (* defg requestT requestE; *)
        (* FunD ( (* send *) *)
          (* [ *)
            (* (moded @@ requestArgsT) *)
          (* ], *)
          (* ( *)
          (* ( (* TODO access *) *)
            (* (rdS @@ drf @@ v0) #. *)
            (* (wrS @@ drf @@ v0) #. *)
            (* (rdS @@ drf @@ v0) #. *)
            (* (wrS @@ drf @@ v0) *)
          (* ) |. *)
          (* skp) #. *)
          (* TODO access *)
          (* (wrS @@ drf @@ v0) #. *)
          (* (rdS @@ drf @@ v1) *)
        (* ); *)
      (* ], *)
      (* (callS vg4 [pE vg3]) #. *)
      (* TODO access *)
      (* (wrS @@ drf @@ vg3) #. *)
      (* ((rdS @@ drf @@ vg3) |. (rdS @@ drf @@ vg3)) #. *)
      (* (rdS @@ drf @@ vg3) *)
    (* ); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* - complex tests *)

  (* TODO: FIXME: rw tags *)
  (* NOTE: path access isreversed to intuitive function application
           by definition *)
  (* let%expect_test "complex test: send, dsl" = *)
    (* prog_eval_noret ( *)
      (* TODO: set optimal ref mods later *)
      (* let user_utilsT = TupleT [uT_r_aw (* 0 id *); uT_r_aw] in *)
      (* let user_infoT =  TupleT [uT_r_aw (* 0 name *); uT_r_aw; uT_r_aw] in *)
      (* let userT = TupleT [cpT user_utilsT (* 0 utils *); cpT user_infoT (* 1 info *)] in *)
      (* let versionT = TupleT [uT_r_aw (* 0 id *); uT_r_aw; uT_r_aw] in *)
      (* let utilsT = TupleT [uT_r_aw (* 0 has_version *); uT_r_aw (* 1 id *)] in *)
      (* let requestT = TupleT [cpT userT (* 0 user *); *)
                             (* cpT versionT (* 1 version *); *)
                             (* cpT utilsT (* 2 utils *); *)
                             (* cpT uT_r_aw (* 3 data *); *)
                             (* uT_r_aw (* 4 operation_date *)] in *)
      (* let user_utilsE = TupleE [UnitE (* 0 id *); UnitE] in *)
      (* let user_infoE =  TupleE [UnitE (* 0 name *); UnitE; UnitE] in *)
      (* let userE = TupleE [rfg0E (* 0 utils *); rfg1E (* 1 info *)] in *)
      (* let versionE = TupleE [UnitE (* 0 id *); UnitE; UnitE] in *)
      (* let utilsE = TupleE [UnitE (* 0 has_version *); UnitE (* 1 id *)] in *)
      (* let requestE = TupleE [rfg2E (* 0 user *); *)
                             (* rfg3E (* 1 version *); *)
                             (* rfg4E (* 2 utils *); *)
                             (* rfg5E (* 3 data *); *)
                             (* UnitE (* 4 operation_date *)] in *)
      (* let get_version_idID = vg7 in *)
      (* let updated_versionID = vg8 in *)
      (* let sendID = vg9 in *)
      (* let send_allID = vg10 in *)
      (* let get_version_idF = FunD ([moded requestT], *)
        (* (rdS @@ access 0 @@ drf @@ access 1 v0) |. skp) in *)
      (* let updated_versionF = FunD ([moded requestT], *)
        (* (rdS @@ access 0 @@ drf @@ access 2 v0) #. *)
        (* TODO: read all the substructure ?? *)
        (* (rdS @@ access 0 @@ drf @@ access 1 v0) #. *)
        (* (rdS @@ access 1 @@ drf @@ access 1 v0)) in *)
      (* let sendF = FunD ([moded requestT], *)
        (* (( *)
           (* (wrS @@ access 0 @@ drf @@ access 2 v0) #. *)
           (* (rdS @@ drf @@ access 3 v0) #. *)
           (* (wrS @@ drf @@ access 3 v0) #. *)
           (* (rdS @@ access 0 @@ drf @@ access 1 @@ drf @@ access 0 v0) *)
         (* ) |. skp) #. *)
         (* (wrS @@ access 4 v0) #. *)
         (* TODO: read all the substructure ?? *)
         (* (rdS @@ access 4 v0) (*rdS v0*)) in (* FIXME: TMP, parial read, should be full *) *)
      (* let send_allF = FunD ([moded requestT], *)
        (* (wrS @@ access 4 v0) (*wrS v0*) #. (* FIXME: TMP, parial write, should be full *) *)
        (* (callS sendID [pE v0]) #. *)
        (* (callS get_version_idID [pE v0]) #. *)
        (* (callS updated_versionID [pE v0]) #. *)
        (* TODO: read all the substructure ?? *)
        (* (wrS @@ access 0 @@ drf @@ access 1 v0) #. *)
        (* (wrS @@ access 1 @@ drf @@ access 1 v0) #. *)
        (* --- *)
        (* ((rdS @@ access 0 @@ drf @@ access 0 @@ drf @@ access 0 v0) |. *)
         (* (rdS @@ access 0 @@ drf @@ access 1 v0))) in *)
      (* let varID = vg6 in *)
      (* [ *)
        (* defg user_utilsT user_utilsE; *)
        (* defg user_infoT user_infoE; *)
        (* defg userT userE; *)
        (* defg versionT versionE; *)
        (* defg utilsT utilsE; *)
        (* defgu uT_r_aw; *)
        (* defg requestT requestE; *)
        (* get_version_idF; *)
        (* updated_versionF; *)
        (* sendF; *)
        (* send_allF *)
      (* ], *)
      (* callS send_allID [pE varID] *)
    (* ); *)
    (* Printf.printf "done!"; *)
    (* [%expect {| done! |}] *)

  (* TODO: version with more optimal modifiers *)
end
