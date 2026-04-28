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
             | FunT of data (* declaration id for ease of impl (?) *)

  type mtype = mode * atype

  type expr = UnitE
            | PathE of path
            (* | RefE *)
            | TupleE of expr list

  type stmt = CallS of path * expr list
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

  (* value model & memory model *)

  type deepvalue = ZeroDV
                 | SmthDV
                 | BotDV
                 | FunDV of (* data list * *) stmt
                 | RefDV of deepvalue
                 | TupleDV of deepvalue list

  type value = ZeroV
             | SmthV
             | BotV
             | FunV of (* data list * *) stmt
             | RefV of memid
             | TupleV of value list

  (* TODO: any additional difference between rvalue and lvalue now ?? *)

  (* --- *)

  type mem = (memid * value) list * memid (* NOTE: memory and first free elem *)
  type types = (data * atype) list
  type vals = (data * memid) list
  type state = mem * types * vals

  (* --- *)

  (* TODO: FIXME: use list_replace for memory instead ?? *)
  let mem_get (mem : mem) (id : memid) : value = List.assoc id (fst mem)
  let mem_add (mem : mem) (v : value) : mem * memid =
    (((snd mem, v) :: fst mem, snd mem + 1), snd mem)
  let mem_set (mem : mem) (id : memid) (v : value) : mem =
    ((id, v) :: fst mem, snd mem)

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
    | VarP x -> mem_get mem @@ List.assoc x vals
    | DerefP p -> (match pathval mem vals p with
                    | RefV id -> mem_get mem id
                    | _ -> raise @@ Typing_error "pathval: deref")
    | AccessP (p, id) -> match pathval mem vals p with
                           | TupleV vs -> (List.nth vs id)
                           | _ -> raise @@ Typing_error "pathval: access"

  (* --- eval rules --- *)

  (* - utils *)

  let rec list_replace (xs : 'a list) (id : int) (y : 'a) : 'a list = match xs, id with
   | _ :: xs, 0 -> y :: xs
   | x :: xs, _ -> x :: list_replace xs (id - 1) y
   | [], _ -> raise Not_found

  (* - value construction *)

  let rec valcopy (mem : mem) (v : value) (t : atype) : mem * value = match t, v with
    | UnitT (Rd, w), ZeroV -> (mem, v)
    | UnitT (Rd, w), SmthV -> (mem, v)
    | UnitT (Rd, w), BotV -> (mem, v)
    | UnitT (NRd, w), ZeroV -> (mem, BotV)
    | UnitT (NRd, w), SmthV -> (mem, BotV)
    | UnitT (NRd, w), BotV -> (mem, BotV)
    | FunT _, FunV _ -> (mem, v)
    | RefT (Rf, _), RefV _ -> (mem, v)
    | RefT (Cp, t), RefV id -> let (mem', v') = valcopy mem (mem_get mem id) t in
                               let (mem'', id'') = mem_add mem' v' in
                               (mem'', RefV id'') 
    | TupleT ts, TupleV vs -> let folder = fun (mem, vs') v t -> let (mem', v') = valcopy mem v t in
                                                                 mem, v' :: vs' in 
                              let mem', vs' = List.fold_left2 folder (mem, []) vs ts in
                              (mem', TupleV vs')
    | _, _ -> raise @@ Typing_error "valcopy"

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
      (* TODO: FIXME: combining semanticsfor funcitons statements *)
      | FunV s, FunV t  -> if s == t then u else raise @@ Typing_error "valcomb: fun"
      | RefV a, RefV b -> if a == b then u else raise @@ Typing_error "valcomb: ref"
      | TupleV us, TupleV vs -> TupleV (List.map2 valcomb us vs)
      | _, _ ->  raise @@ Typing_error "valcomb"

  (* TODO: func for list memory, not assoc list *)
  (* let rec memcomb (m : mem) (n : mem) : mem = *)
    (* if snd m != snd n *)
    (* then raise @@ Typing_error "memcomb" *)
    (* else (List.map2 valcomb (fst m) (fst n), snd m) *)

  (* - call values spoil *)

  (* TODO: check all cases *)
  let is_correct_tags (v : value) (r : read_cap) (w : write_cap)
                      (r' : read_cap) (w' : write_cap) (m : mode)
                      (c : copy_cap) : bool =
    (r != Rd || v == ZeroV) &&
    (r != Rd || fst m == In) &&
    (o != Out || w == AlwaysWr) &&
    (* TODO: check *)
    ((not @@ (w == AlwaysWr || w == MayWr) && (snd m == Out || c == Rf)) || w' == AlwaysWr) &&
    is_trivial_v v

  let rec valspoil (mem : mem) (v : value) (t : atype)
                   (u : atype) (m : mode) (c : copy_cap)
                   : mem * value = match t, u, v with
    | UnitT (r, w), UnitT (r', w'), _ -> (* TODO FIXME *) raise Not_found
    | FunT ts, FunT us, FunV _ -> if ts == us then (mem, v) else raise @@ Typing_error "valspoil: fun"
    | RefT (ct, t), RefT (cu, u), RefV id ->
      let (mem', v') = valspoil mem (mem_get mem id) t u m ct in
      (mem_set mem id v', RefV id)
    | TupleT ts, TupleT us, TupleV vs -> (* TODO FIXME *) raise Not_found
    | _, _, _ ->  raise @@ Typing_error "valspoil"

(* --- FIXME --- CURRENT REWRITE POINT --- FIXME --- *)

  (* let rec argsspoil (* full spoil *) *)

  (* --- *)

  let rec list_zip_with f xs ys = match xs, ys with (* TODO: alternative from stdlib *)
    | x :: xs, y :: ys -> f x y :: list_zip_with f xs ys 
    | _, _ -> []

  (* --- combination --- *)

  let value_combine (left : value) (right : value) : value = match left, right with
    | UnitV, UnitV -> UnitV
    | BotV, BotV -> BotV
    | _, _ -> UndefV (* NOTE: should be expanded in relational interpreter to not use ineq (?) *)

  let memory_combine (left : value list) (right : value list) : value list =
    list_zip_with value_combine left right

  let state_combine (left : state) (right : state) : state = match left, right with
    (lenv, lmem, lmem_len, lvisited), (renv, rmem, rmem_len, rvisited) ->
    if lenv != renv || lmem_len != rmem_len then raise Incompatible_states
    else (lenv, memory_combine lmem rmem, lmem_len, List.append lvisited rvisited)
    (* TODO: union visited lists instead ? *)

  (* --- tag accessors --- *)

  let is_read (tag : tag) : bool = match tag with
    | (Rd, _, _, _, _) -> true
    | _ -> false

  let is_always_write (tag : tag) : bool = match tag with
    | (_, AlwaysWr, _, _, _) -> true
    | _ -> false

  let is_may_write (tag : tag) : bool = match tag with
    | (_, AlwaysWr, _, _, _) -> true
    | (_, MayWr, _, _, _) -> true
    | _ -> false

  let is_never_write (tag : tag) : bool = match tag with
    | (_, NeverWr, _, _, _) -> true
    | _ -> false

  let is_copy (tag : tag) : bool = match tag with
    | (_, _, Cp, _, _) -> true
    | _ -> false

  let is_in (tag : tag) : bool = match tag with
    | (_, _, _, In, _) -> true
    | _ -> false

  let is_out (tag : tag) : bool = match tag with
    | (_, _, _, _, Out) -> true
    | _ -> false

  (* --- *)

  let rec list_replace xs id value = match (xs, id) with
   | (_x :: xs, 0) -> value :: xs
   | (x :: xs, _n) -> x :: list_replace xs (id - 1) value 
   | ([], _) -> raise Not_found

  let inv_id (mem_len : int) (id : data) : data = mem_len - id - 1

  (* --- path accessors --- *)

  let rec pathtype (t : argtype) (p : path) : argtype = match t, p with
    | t, VarP x -> t
    | RefT (tag, t), DerefP p -> pathtype t p
    | TupleT ts, AccessP (p, n) -> pathtype (List.nth ts n) p
    | _, _ -> raise Incompatible_path_and_type

  let rec pathmem (m : argmem) (p : path) : data = match m, p with
    | VarM m, VarP x -> m
    | RefM m, DerefP p -> pathmem m p
    | TupleM ms, AccessP (p, n) -> pathmem (List.nth ms n) p
    | _, _ -> raise Incompatible_path_and_mem

  let rec pathtag (t : argtype) (p : path) : tag = match t, p with
    | RefT (tag, t), VarP x -> tag
    | RefT (tag, t), DerefP p -> pathtag t p
    | TupleT ts, AccessP (p, n) -> pathtag (List.nth ts n) p
    | _, _ -> raise Incompatible_path_and_type_for_tag

  let rec pathvar (p : path) : data = match p with
    | VarP x -> x
    | DerefP p -> pathvar p
    | AccessP (p, n) -> pathvar p

  let typeof (env : env) (p : path) : argtype = pathtype (snd (List.assoc (pathvar p) env)) p
  let accessmem (env : env) (p : path) : data = pathmem (fst (List.assoc (pathvar p) env)) p
  let argtag (env : env) (p : path) : tag = pathtag (snd (List.assoc (pathvar p) env)) p
  (* TODO: check indices *)
  let access_get (env : env) (mem : value list) (mem_len : data) (p : path) : value = List.nth mem @@ inv_id mem_len @@ accessmem env p
  let access_set (env : env) (mem : value list) (mem_len : data) (p : path) (value : value) : value list = list_replace mem (inv_id mem_len @@ accessmem env p) value

  (* --- *)

  let visited_add (state : state) (id : data) : state =
    match state with (env, mem, mem_len, visited) -> (env, mem, mem_len, id :: visited)

  let visited_check (state : state) (id : data) : bool =
    match state with (_, _, _, visited) -> List.exists (fun i -> i == id) visited

  (* --- *)

  (* TODO: replacewith more useful path versions *)
  let env_get (state : state) (id : data) : (argmem * argtype) =
    match state with (env, _mem, _mem_len, _visited) -> List.assoc id env

  let env_add (state : state) (id : data) (argmem : argmem) (argtype : argtype) : state = match state with
    (env, mem, mem_len, visited) -> let env = (id, (argmem, argtype)) :: env in
                           (env, mem, mem_len, visited)

  let mem_get (state : state) (p : path) : value = match state with
    (env, mem, mem_len, _visited) -> access_get env mem mem_len p

  let mem_set (state : state) (p : path) (value : value) : state = match state with
    (env, mem, mem_len, visited) -> (env, access_set env mem mem_len p value, mem_len, visited)

  let mem_add (state : state) (value : value) : state = match state with
    (env, mem, mem_len, visited) -> let mem = value :: mem in (env, mem, mem_len + 1, visited)

  let mem_check (state : state) (p : path) : unit =
    (* TODO: use path in error instead *)
    if mem_get state p == BotV then raise @@ Incorrect_memory_access (pathvar p) else ()

  (* --- *)

  let arg_to_value (state : state) (arg : arg) : value = match arg with
    | RValue -> UnitV
    | LValue p -> mem_get state p
  (* TODO: FIXME: args as argmem ?? *)

  let st_mem_len (state : state) : int =
    match state with (_, _, mem_len, _) -> mem_len

  let check_tag_correct (tag : tag) (id : data) : unit =
    if (* (is_in tag && not (is_read tag)) || *) (* TODO: required ?? *)
       is_out tag > is_always_write tag ||
       is_read tag > is_in tag
       (* || is_copy tag && is_out tag *) (* ?? *)
    then raise @@ Invalid_argument_tag id
    else ()

  let st_add_arg (state : state) (state_before : state)
      (id : data) (arg_tag : tag) (arg : arg) : state =
    check_tag_correct arg_tag id;
    if is_copy arg_tag
    then let state = mem_add state (arg_to_value state_before arg) in
         env_add state id arg_tag (st_mem_len state - 1)
    else match arg with
      | RValue -> raise @@ Ref_rvalue_argument id (* TODO: allow later ?? *)
      | LValue arg -> let (parent_tag, mem_id) = env_get state_before arg in
                      if is_may_write arg_tag > is_always_write parent_tag (* TODO: FIXME: not updated semantics ?? *)
                      then raise @@ Incorrect_const_cast id
                      else if is_read arg_tag
                      then env_add state id arg_tag mem_id
                      (* TODO: parent state is spoiled, check that this is correct *)
                      else let state_ext = env_add state id arg_tag mem_id in
                           mem_set state_ext id BotV

  (* TODO: FIXME: not enough tests on incorrect const cast (passed without ref or out check) *)
  (* TODO; FIXME: forbid duplicates,  collect lists of all spoils & checks ? *)
  let st_spoil_by_args (state : state) (arg_tags : tag list) (args : data list) : state =
    match state with (env, mem, mem_len, _visited) ->
    let state_before = state in
    let spoil_folder (state : state) (tag : tag) (id : data) : state =
      let parent_tag = fst (env_get state id) in
      (* NOTE: replaced with later condition *)
      (* if is_write tag > is_write parent_tag && (not (is_copy tag) || is_out tag) then raise @@ Incorrect_const_cast idi else *)
      let state = if is_read tag then (mem_check state_before id; state) else state (* NOTE: state override *)
      in if is_never_write tag then state (* TODO: FIXME: check *)
      else match is_out tag with
        | true -> if not @@ is_always_write parent_tag then raise @@ Incorrect_const_cast id
                  else mem_set state id UnitV
        | false -> if is_copy tag then state
                   else if not @@ is_may_write parent_tag then raise @@ Incorrect_const_cast id (* TODO: check that may modifier correct *)
                   else mem_set state id BotV
    in List.fold_left2 spoil_folder state arg_tags args

  let list_drop n xs = List.of_seq @@ Seq.drop n @@ List.to_seq xs

  let rec eval_stmt (state : state) (prog : fun_decl list) (stmt : stmt) : state =
    match stmt with
      | Call (f_id, args) -> let (arg_tags, _) as f_decl = List.nth prog f_id in
                             let state_with_visited = if visited_check state f_id
                                          then state
                                          else let new_state_with_visited = visited_add state f_id in
                                               let state_fun = eval_fun new_state_with_visited prog f_decl (List.map (fun arg -> LValue arg) args) in
                                               (* NOTE: now memory in function is not spoiled  *)
                                               state_fun
                             in st_spoil_by_args state_with_visited arg_tags args
      | Read id -> mem_check state id; state
      | Write id -> if is_may_write @@ fst @@ env_get state id
                    then mem_set state id UnitV
                    else raise @@ Incorrect_const_cast id
      | Choice (xs, ys) -> let state_x = eval_body state prog xs in
                           let state_y = eval_body state prog ys in
                           state_combine state_x state_y
                           (* TODO: FIXME: additional may write / always write checks ?? *)

  and eval_body (state : state) (prog : fun_decl list) (body : body) : state =
    List.fold_left (fun state stmt -> eval_stmt state prog stmt) state body

  and eval_fun (state : state) (prog : fun_decl list) (decl : fun_decl) (args : arg list) : state =
    match decl with (arg_tags, body) ->
    match state with (env_before, mem_before, len_before, visited_before) as state_before ->
    let state : state = ([], mem_before, len_before, visited_before) in
    let (state, _) = List.fold_left2 (fun (state, id) arg_tag arg -> (st_add_arg state state_before id arg_tag arg, id + 1))
                                     (state, 0) arg_tags args in
    let state = eval_body state prog body in
    match state with (_env, mem, len, visited) ->
    (env_before, mem_before, len_before, visited)
    (* (env_before, list_drop (len - len_before) mem, len_before, visited) (* TODO: save some assignments ?? *) *)

  and eval_fun_empty_args (state : state) (prog : fun_decl list) (decl : fun_decl) : state =
    match decl with (arg_tags, _) ->
    let args = List.map (fun _ -> RValue) arg_tags in
    eval_fun state prog decl args

  let empty_state : state = ([], [], 0, [])

  let eval_prog ((prog, main_decl) : prog) = ignore @@ eval_fun_empty_args empty_state prog main_decl

  (* tests *)

  let rwi_value : tag = (Rd, AlwaysWr, Cp, In, NOut)
  let rmwi_value : tag = (Rd, MayWr, Cp, In, NOut)
  let ri_value : tag = (Rd, NeverWr, Cp, In, NOut)
  let wi_value : tag = (NRd, AlwaysWr, Cp, In, NOut)
  let mwi_value : tag = (NRd, MayWr, Cp, In, NOut)
  let i_value : tag = (NRd, NeverWr, Cp, In, NOut)
  let rwi_ref : tag = (Rd, AlwaysWr, Rf, In, NOut)
  let rmwi_ref : tag = (Rd, MayWr, Rf, In, NOut)
  let ri_ref : tag = (Rd, NeverWr, Rf, In, NOut)
  let wi_ref : tag = (NRd, AlwaysWr, Rf, In, NOut)
  let mwi_ref : tag = (NRd, MayWr, Rf, In, NOut)
  let i_ref : tag = (NRd, NeverWr, Rf, In, NOut)

  (* >> tests without functions *)

  let%expect_test "empty" =
    eval_prog ([], ([], []));
    Printf.printf "done!";
    [%expect {| done! |}]

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
