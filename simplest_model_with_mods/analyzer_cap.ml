module Functional =
struct

  (* --- types --- *)

  type data = int

  type read_cap = Rd | NRd
  type write_cap = Wr | NWr
  type copy_cap = Cp | NCp

  type in_cap = In | NIn
  type out_cap = Out | NOut

  type tag = read_cap * write_cap * copy_cap * in_cap * out_cap

  type stmt = Call of data * data list | Read of data | Write of data

  type body = stmt list


  type fun_decl = tag list * body

  type prog = fun_decl list * fun_decl

  (* --- exceptions --- *)

  exception Incorrect_memory_access of int
  exception Ref_rvalue_argument of int
  exception Incorrect_const_cast of int
  exception Invalid_argument_tag of int

  (* --- static interpreter (no rec) --- *)

  (* TODO: allow data (rvalue) in calls ?? *)
  type arg = RValue | LValue of data
  type value = UnitV | BotV (* NOTE: RefV of data - not needed for now *)

  type env = (int * (tag * data)) list

  (* env * memory * last unused memory * visited functions *) 
  type state = env * value list * int * int list

  (* --- *)

  let is_read (tag : tag) : bool = match tag with
    | (Rd, _, _, _, _) -> true  
    | (NRd, _, _, _, _) -> false

  let is_write (tag : tag) : bool = match tag with
    | (_, Wr, _, _, _) -> true  
    | (_, NWr, _, _, _) -> false

  let is_copy (tag : tag) : bool = match tag with
    | (_, _, Cp, _, _) -> true  
    | (_, _, NCp, _, _) -> false

  let is_in (tag : tag) : bool = match tag with
    | (_, _, _, In, _) -> true  
    | (_, _, _, NIn, _) -> false

  let is_out (tag : tag) : bool = match tag with
    | (_, _, _, _, Out) -> true  
    | (_, _, _, _, NOut) -> false

  (* --- *)

  let rec list_replace xs id value = match (xs, id) with
   | (_x :: xs, 0) -> value :: xs
   | (x :: xs, _n) -> x :: list_replace xs (id - 1) value 
   | ([], _) -> raise Not_found

  let visited_add (state : state) (id : data) : state =
    match state with (env, mem, mem_len, visited) -> (env, mem, mem_len, id :: visited)

  let visited_check (state : state) (id : data) : bool =
    match state with (_, _, _, visited) -> List.exists (fun i -> i == id) visited

  let env_get (state : state) (id : data) : (tag * data) =
    match state with (env, _mem, _mem_len, _visited) -> List.assoc id env

  let env_add (state : state) (id : data) (mode : tag) (mem_id : data) : state = match state with
    (env, mem, mem_len, visited) -> let env = (id, (mode, mem_id)) :: env in
                           (env, mem, mem_len, visited)

  let inv_id (mem_len : int) (id : data) : data = mem_len - id - 1

  let mem_get (state : state) (id : data) : value = match state with
    (_env, mem, mem_len, _visited) -> List.nth mem @@ inv_id mem_len @@ snd @@ env_get state id

  let mem_set (state : state) (id : data) (value : value) : state = match state with
    (env, mem, mem_len, visited) -> let mem_id = inv_id mem_len @@ snd @@ env_get state id in
                                        let mem = list_replace mem mem_id value in (env, mem, mem_len, visited)

  let mem_add (state : state) (value : value) : state = match state with
    (env, mem, mem_len, visited) -> let mem = value :: mem in (env, mem, mem_len + 1, visited)

  let mem_check (state : state) (id : data) : state =
    if mem_get state id == BotV then raise @@ Incorrect_memory_access id else state


  let arg_to_value (state : state) (arg : arg) : value = match arg with
    | RValue -> UnitV
    | LValue id -> mem_get state id

  let st_mem_len (state : state) : int =
    match state with (_, _, mem_len, _) -> mem_len

  (* TODO *)
  let check_tag_correct (tag : tag) (id : data) : unit =
    if (* (is_in tag && not (is_read tag)) || *) (* TODO: required ?? *)
       (is_out tag && not (is_write tag))
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
                      if is_write arg_tag > is_write parent_tag
                      then raise @@ Incorrect_const_cast id
                      else if is_read arg_tag
                      then env_add state id arg_tag mem_id
                      (* TODO: parent state is spoiled, check that this is correct *)
                      else let state_ext = env_add state id arg_tag mem_id in
                           mem_set state_ext id BotV

  (* TODO: FIXME: do not spoil out arguments *)
  let st_spoil_by_args (state : state) (arg_tags : tag list) (args : data list) : state =
    match state with (env, mem, mem_len, _visited) ->
    let spoil_folder (state : state) (tag : tag) (id : data) : state =
      let parent_tag = fst (env_get state id) in
      if not (is_copy tag) && not (is_out tag)
      then (if is_write tag > is_write parent_tag
               (* || is_read tag > is_read parent_tag *) (* TODO FIXME: check that can read *)
            then raise @@ Incorrect_const_cast id
            else let state_checked = if is_read tag
                                     then mem_check state id
                                     else state
                 in
                 if is_write tag
                 then mem_set state_checked id BotV
                 else state_checked)
      else state
    in List.fold_left2 spoil_folder state arg_tags args

  let list_drop n xs = List.of_seq @@ Seq.drop n @@ List.to_seq xs

  (* TODO: FIXME: require at least one read / write for read / write args ?? *)
  let rec eval_stmt (state : state) (prog : fun_decl list) (stmt : stmt) : state =
    match stmt with
      | Call (f_id, args) -> let (arg_tags, _) as f_decl = List.nth prog f_id in
                             let state_with_visited = if visited_check state f_id
                                          then state
                                          else let new_state_with_visited = visited_add state f_id in
                                               let state_fun = eval_fun new_state_with_visited prog f_decl (List.map (fun arg -> LValue arg) args) in
                                               (* NOTE: now memory in function is not spoiled  *)
                                               state_fun
                             in
                             (* let state_checked = List.fold_left2 (fun s arg arg_tag -> *)
                                  (* if is_read arg_tag *)
                                  (* then mem_check s arg *)
                                  (* else s) *)
                                (* state_with_visited args arg_tags in *)
                             st_spoil_by_args state_with_visited arg_tags args
      | Read id -> mem_check state id
      | Write id -> if is_write @@ fst @@ env_get state id
                    then mem_set state id UnitV
                    else raise @@ Incorrect_const_cast id

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

  let rwi_value : tag = (Rd, Wr, Cp, In, NOut)
  let ri_value : tag = (Rd, NWr, Cp, In, NOut)
  let wi_value : tag = (NRd, Wr, Cp, In, NOut)
  let i_value : tag = (NRd, NWr, Cp, In, NOut)
  let rwi_ref : tag = (Rd, Wr, NCp, In, NOut)
  let ri_ref : tag = (Rd, NWr, NCp, In, NOut)
  let wi_ref : tag = (NRd, Wr, NCp, In, NOut)
  let i_ref : tag = (NRd, NWr, NCp, In, NOut)

  (* >> tests without functions *)

  let%expect_test "empty" =
    eval_prog ([], ([], []));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "ref param in main failure" =
    try (eval_prog ([], ([i_ref], []));
         [%expect.unreachable])
    with Ref_rvalue_argument id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "read empty args" =
    try (eval_prog ([], ([], [Read 0]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "write empty args" =
    try (eval_prog ([], ([], [Write 0]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple write" =
    eval_prog ([], ([wi_value], [Write 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple read" = (* NOTE: should not work with read-before-write check*)
    eval_prog ([], ([ri_value], [Read 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "multiple read & write" =
    eval_prog ([], ([rwi_value], [Write 0; Read 0; Write 0; Write 0; Read 0; Read 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "multiple read & write, multiple args" =
    eval_prog ([], ([wi_value; wi_value; wi_value], [Write 0; Read 0; Write 1; Write 0; Write 2; Read 1; Write 2; Read 0; Read 2]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "main, access out of range" =
    try(eval_prog ([], ([wi_value], [Write 0; Read 5 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "main, access out of range" =
    try(eval_prog ([], ([wi_value], [Write 0; Write 5 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  (* >> tests with one function *)

  let%expect_test "simple function call with value arg" =
    eval_prog ([([wi_value], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple function call with ref arg" =
    eval_prog ([([wi_ref], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg & read" =
    eval_prog ([([wi_value], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with ref arg & read" =
    try (eval_prog ([([rwi_ref], [Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "function with ref arg & call twice" =
    try (eval_prog ([([rwi_ref], [Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  (* NOTE: behaviour is fixed with new capabilities *)
  let%expect_test "function with ref arg, write first & call twice" =
    eval_prog ([([wi_ref], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]


  let%expect_test "function with ref arg & read, write" =
    try (eval_prog ([([rwi_ref], [Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Read 0; Write 0 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "function with ref arg & write, read" =
    eval_prog ([([rwi_ref], [Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]); Write 0; Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref arg, no write inside & read" =
    eval_prog ([([ri_ref], [Read 0; Read 0])], ([wi_value], [Write 0; Call (0, [0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with value arg, read out of range" =
    try(eval_prog ([([ri_ref], [Read 0; Read 1])], ([wi_value; i_value], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref arg, read out of range" =
    try(eval_prog ([([ri_ref], [Read 0; Read 1])], ([wi_value; i_value], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg, write out of range" =
    try(eval_prog ([([rwi_value], [Read 0; Write 1])], ([wi_value; i_value], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg, call out of range" =
    try(eval_prog ([([ri_value], [Read 0])], ([wi_value; i_value], [Write 0; Call (0, [2]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with ref & value args, no write inside & read" =
    eval_prog (
      [([ri_ref; ri_value], [Read 0; Read 1])],
      ([wi_value; wi_value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref & value args, write value inside & read" =
    eval_prog (
      [([ri_ref; rwi_value], [Read 0; Read 1; Write 1; Read 1])],
      ([wi_value; wi_value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref & value args, write both inside & read" =
    try (eval_prog (
      [([rwi_ref; rwi_value],[Read 0; Read 1; Write 0; Write 1; Read 1])],
      ([wi_value; wi_value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  (* --- *)

  (* NOTE: maybe important case in the future *)
  let%expect_test "function with ref two same ref args, read both & read" =
    eval_prog (
      [([ri_ref; ri_ref],[Read 0; Read 1; Read 1])],
      ([wi_value], [Write 0; Call (0, [0; 0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* NOTE: changed semantics by comporasion with prev analyzer, new test *)
  let%expect_test "function with ref two same ref args, read & write both & nothing" =
    eval_prog (
      [([ri_ref; ri_ref],[Read 0; Read 1; Read 1])],
      ([wi_value], [Write 0; Call (0, [0; 0]); ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* NOTE: changed semantics by comporasion with prev analyzer, new test *)
  let%expect_test "function with ref & copy of the same arg, read both & nothing" =
    eval_prog (
      [([rwi_ref; rwi_value],[Read 0; Read 1; Write 0; Write 1; Read 1])],
      ([wi_value], [Write 0; Call (0, [0; 0]); ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* NOTE: maybe important case in the future *)
  let%expect_test "function with ref two same ref args, read & write both, error" =
    try (eval_prog (
      [([rwi_ref; rwi_ref],[Read 0; Read 1; Write 0; Write 1; Read 1])],
      ([wi_value], [Write 0; Call (0, [0; 0]); ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  (* >> tests with several functions *)

  let%expect_test "two functions with ref arg, read func -> write func" =
    eval_prog (
      [([ri_ref], [Read 0]); ([wi_ref], [Write 0])],
      ([wi_value], [Write 0; Call (0, [0]); Read 0; Call (1, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "two functions with ref arg, write func -> read func" =
    try (eval_prog (
      [([ri_ref], [Read 0]); ([wi_ref], [Write 0])],
      ([wi_value], [Write 0; Call (1, [0]); Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "two functions: ref arg after value arg" =
    eval_prog (
      [([rwi_ref], [Read 0; Write 0]); ([rwi_value], [Read 0; Write 0])],
      ([wi_value], [Write 0; Call (1, [0]); Read 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "two functions: value arg after spoiled ref arg" =
    try (eval_prog (
      [([rwi_ref], [Read 0; Write 0]); ([rwi_value], [Read 0; Write 0])],
      ([wi_value], [Write 0; Call (0, [0]); Call (1, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  (* --- *)

  let%expect_test "simple function call with value arg, const cast error" =
    try (eval_prog ([([ri_value], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_const_cast id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "simple function call with ref arg, const cast error" =
    try (eval_prog ([([ri_ref], [Write 0; Read 0; Write 0])], ([wi_value], [Write 0; Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_const_cast id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "simple function call with value arg, const cast ok" =
    eval_prog ([([ri_value], [Read 0])], ([wi_value], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple function call with ref arg, const cast ok" =
    eval_prog ([([ri_ref], [Read 0])], ([wi_value], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "simple function call with arg, recursive calls" =
    eval_prog ([([rwi_value], [Write 0; Read 0; Write 0; Call (0, [0])])], ([wi_value], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]
end
