module Functional =
struct

  (* --- types --- *)

  type data = int

  type tag = Ref | Value
  type mode = Const | Mut
  type stmt = Call of data * data list | Read of data | Write of data

  type body = stmt list

  type fun_decl = (mode * tag) list * body

  type prog = fun_decl list * fun_decl

  (* --- exceptions --- *)

  exception Incorrect_memory_access of int
  exception Ref_rvalue_argument of int
  exception Incorrect_const_cast of int

  (* --- static interpreter (no rec) --- *)

  (* TODO: allow data (rvalue) in calls ?? *)
  type arg = RValue | LValue of data
  type value = UnitV | BotV (* NOTE: RefV of data - not needed for now *)

  type env = (int * (mode * data)) list

  (* env * memory * last unused memory * visited functions *) 
  type state = env * value list * int * int list

  let rec list_replace xs id value = match (xs, id) with
   | (_x :: xs, 0) -> value :: xs
   | (x :: xs, _n) -> x :: list_replace xs (id - 1) value 
   | ([], _) -> raise Not_found

  let visited_add (state : state) (id : data) : state =
    match state with (env, mem, mem_len, visited) -> (env, mem, mem_len, id :: visited)

  let visited_check (state : state) (id : data) : bool =
    match state with (_, _, _, visited) -> List.exists (fun i -> i == id) visited

  let env_get (state : state) (id : data) : (mode * data) =
    match state with (env, _mem, _mem_len, _visited) -> List.assoc id env

  let env_add (state : state) (id : data) (mode : mode) (mem_id : data) : state = match state with
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

  let st_add_arg (state : state) (state_before : state)
      (id : data) (arg_tag : mode * tag) (arg : arg) : state =
    match (arg_tag, arg) with
      | ((mode, Ref), RValue) -> raise @@ Ref_rvalue_argument id (* TODO: allow later ?? *) 
      | ((mode, Ref), LValue arg) -> let (parent_mode, mem_id) = env_get state_before arg in
                                     if mode == Mut && parent_mode == Const
                                     then raise @@ Incorrect_const_cast id
                                     else env_add state id mode mem_id
      | ((mode, Value), arg) -> let state = mem_add state (arg_to_value state_before arg) in
                                env_add state id mode (st_mem_len state - 1)

  let st_spoil_by_args (state : state) (arg_tags : (mode * tag) list) (args : data list) : state =
    match state with (env, mem, mem_len, _visited) ->
    let spoilFolder state tag id =
      match tag with
      | (Mut, Ref) -> if fst (env_get state id) == Const
                      then raise @@ Incorrect_const_cast id
                      else mem_set state id BotV
      | _ -> state
    in 
    List.fold_left2 spoilFolder state arg_tags args

  let list_drop n xs = List.of_seq @@ Seq.drop n @@ List.to_seq xs

  let rec eval_stmt (state : state) (prog : fun_decl list) (stmt : stmt) : state =
    match stmt with
      | Call (f_id, args) -> let (arg_tags, _) as f_decl = List.nth prog f_id in
                             let state_with_visited = if visited_check state f_id
                                          then state
                                          else let new_state_with_visited = visited_add state f_id in
                                               ignore @@ eval_fun new_state_with_visited prog f_decl (List.map (fun arg -> LValue arg) args);
                                               (* NOTE:  do not spoil args in function, etc. instead ??  *)
                                               new_state_with_visited in
                             let state_checked = List.fold_left  mem_check state_with_visited args in
                             st_spoil_by_args state_checked arg_tags args
      | Read id -> mem_check state id
      | Write id -> if fst (env_get state id) == Const
                    then raise @@ Incorrect_const_cast id
                    else mem_set state id UnitV

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
    (env_before, list_drop (len - len_before) mem, len_before, visited) (* TODO: save some assignments ?? *)

  and eval_fun_empty_args (state : state) (prog : fun_decl list) (decl : fun_decl) : state =
    match decl with (arg_tags, _) ->
    let args = List.map (fun _ -> RValue) arg_tags in
    eval_fun state prog decl args

  let empty_state : state = ([], [], 0, [])

  let eval_prog ((prog, main_decl) : prog) = ignore @@ eval_fun_empty_args empty_state prog main_decl

  (* tests *)

  (* >> tests without functions *)

  let%expect_test "empty" =
    eval_prog ([], ([], []));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "ref param in main failure" =
    try (eval_prog ([], ([(Const, Ref)], []));
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
    eval_prog ([], ([(Mut, Value)], [Write 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple read" = (* NOTE: should not work with read-before-write check*)
    eval_prog ([], ([(Const, Value)], [Read 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "multiple read & write" =
    eval_prog ([], ([(Mut, Value)], [Write 0; Read 0; Write 0; Write 0; Read 0; Read 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "multiple read & write, multiple args" =
    eval_prog ([], ([(Mut, Value); (Mut, Value); (Mut, Value)], [Write 0; Read 0; Write 1; Write 0; Write 2; Read 1; Write 2; Read 0; Read 2]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "main, access out of range" =
    try(eval_prog ([], ([(Mut, Value)], [Write 0; Read 5 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "main, access out of range" =
    try(eval_prog ([], ([(Mut, Value)], [Write 0; Write 5 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  (* >> tests with one function *)

  let%expect_test "simple function call with value arg" =
    eval_prog ([([(Mut, Value)], [Write 0; Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple function call with ref arg" =
    eval_prog ([([(Mut, Ref)], [Write 0; Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg & read" =
    eval_prog ([([(Mut, Value)], [Write 0; Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with ref arg & read" =
    try (eval_prog ([([(Mut, Ref)], [Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "function with ref arg & call twice" =
    try (eval_prog ([([(Mut, Ref)], [Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]); Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  (* TODO: FIXME:: test change, with current system function args assumed to be read inside function *)
  (* TODO: add one more modefier: Read / NotRead ? *)
  let%expect_test "function with ref arg, write first & call twice" =
    try (eval_prog ([([(Mut, Ref)], [Write 0; Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]); Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "function with ref arg & read, write" =
    try (eval_prog ([([(Mut, Ref)], [Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]); Read 0; Write 0 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "function with ref arg & write, read" =
    eval_prog ([([(Mut, Ref)], [Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]); Write 0; Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref arg, no write inside & read" =
    eval_prog ([([(Const, Ref)], [Read 0; Read 0])], ([(Mut, Value)], [Write 0; Call (0, [0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with value arg, read out of range" =
    try(eval_prog ([([(Const, Value)], [Read 0; Read 1])], ([(Mut, Value); (Const, Value)], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref arg, read out of range" =
    try(eval_prog ([([(Const, Ref)], [Read 0; Read 1])], ([(Mut, Value); (Const, Value)], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg, write out of range" =
    try(eval_prog ([([(Mut, Value)], [Read 0; Write 1])], ([(Mut, Value); (Const, Value)], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg, call out of range" =
    try(eval_prog ([([(Const, Value)], [Read 0])], ([(Mut, Value); (Mut, Value)], [Write 0; Call (0, [2]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with ref & value args, no write inside & read" =
    eval_prog (
      [([(Const, Ref); (Const, Value)], [Read 0; Read 1])],
      ([(Mut, Value); (Mut, Value)], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref & value args, write value inside & read" =
    eval_prog (
      [([(Const, Ref); (Mut, Value)], [Read 0; Read 1; Write 1; Read 1])],
      ([(Mut, Value); (Mut, Value)], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref & value args, write both inside & read" =
    try (eval_prog (
      [([(Mut, Ref); (Mut, Value)],[Read 0; Read 1; Write 0; Write 1; Read 1])],
      ([(Mut, Value); (Mut, Value)], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  (* --- *)

  (* NOTE: maybe important case in the future *)
  let%expect_test "function with ref two same ref args, read both & read" =
    eval_prog (
      [([(Const, Ref); (Const, Ref)],[Read 0; Read 1; Read 1])],
      ([(Mut, Value)], [Write 0; Call (0, [0; 0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* NOTE: maybe important case in the future *)
  let%expect_test "function with ref two same ref args, read both & nothing" =
    eval_prog (
      [([(Mut, Ref); (Mut, Ref)],[Read 0; Read 1; Write 0; Write 1; Read 1])],
      ([(Mut, Value)], [Write 0; Call (0, [0; 0]); ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* >> tests with several functions *)

  let%expect_test "two functions with ref arg, read func -> write func" =
    eval_prog (
      [([(Const, Ref)], [Read 0]); ([(Mut, Ref)], [Write 0])],
      ([(Mut, Value)], [Write 0; Call (0, [0]); Read 0; Call (1, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "two functions with ref arg, write func -> read func" =
    try (eval_prog (
      [([(Const, Ref)], [Read 0]); ([(Mut, Ref)], [Write 0])],
      ([(Mut, Value)], [Write 0; Call (1, [0]); Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "two functions: ref arg after value arg" =
    eval_prog (
      [([(Mut, Ref)], [Read 0; Write 0]); ([(Mut, Value)], [Read 0; Write 0])],
      ([(Mut, Value)], [Write 0; Call (1, [0]); Read 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "two functions: value arg after spoiled ref arg" =
    try (eval_prog (
      [([(Mut, Ref)], [Read 0; Write 0]); ([(Mut, Value)], [Read 0; Write 0])],
      ([(Mut, Value)], [Write 0; Call (0, [0]); Call (1, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  (* --- *)

  let%expect_test "simple function call with value arg" =
    try (eval_prog ([([(Const, Value)], [Write 0; Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_const_cast id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "simple function call with ref arg" =
    try (eval_prog ([([(Const, Ref)], [Write 0; Read 0; Write 0])], ([(Mut, Value)], [Write 0; Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_const_cast id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "simple function call with value arg" =
    eval_prog ([([(Const, Value)], [Read 0])], ([(Mut, Value)], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple function call with ref arg" =
    eval_prog ([([(Const, Ref)], [Read 0])], ([(Mut, Value)], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "simple function call with arg, recursive calls" =
    eval_prog ([([(Mut, Value)], [Write 0; Read 0; Write 0; Call (0, [0])])], ([(Mut, Value)], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* TODO: tests for Mut / Const mods *)
end
