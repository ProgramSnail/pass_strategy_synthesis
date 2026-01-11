(* (,,) -< Pair.inj _ (Pair.inj _ _) *)

module Functional =
struct

  (* --- types --- *)

  type data = int

  type tag = Ref | Value
  type stmt = Call of data * data list | Read of data | Write of data

  type body = stmt list

  type fun_decl = tag list * body

  type prog = fun_decl list * fun_decl

  (* --- exceptions --- *)

  exception Incorrect_memory_access of int
  exception Ref_rvalue_argument of int

  (* --- static interpreter (no rec) --- *)

  (* TODO: allow data (rvalue) in calls ?? *)
  type arg = RValue | LValue of data
  type value = UnitV | BotV (* NOTE: RefV of data - not needed for now *)

  type env = (int * data) list

  (* env * memory * last unused memory * assignments *) 
  type state = env * value list * int * data list

  (* TODO: replace with pairs *)
  let rec list_replace xs id value = match (xs, id) with
   | (_x :: xs, 0) -> value :: xs
   | (x :: xs, _n) -> x :: list_replace xs (id - 1) value 
   | ([], _) -> raise Not_found


  let env_get state id = match state with
    (env, _mem, _mem_len, _assignments) -> List.assoc id env

  let env_add state id mem_id = match state with
    (env, mem, mem_len, assignments) -> let env = (id, mem_id) :: env in
                                        (env, mem, mem_len, assignments)

  let inv_id mem_len id = mem_len - id - 1

  let mem_get state id = match state with
    (_env, mem, mem_len, _assignments) -> List.nth mem @@ inv_id mem_len @@ env_get state id

  let mem_set state id value= match state with
    (env, mem, mem_len, assignments) -> let mem_id = inv_id mem_len @@ env_get state id in
                                        let mem = list_replace mem mem_id value in (env, mem, mem_len, id :: assignments)

  let mem_add state value = match state with
    (env, mem, mem_len, assignments) -> let mem = value :: mem in (env, mem, mem_len + 1, assignments)

  let mem_check state id = if mem_get state id == BotV then raise @@ Incorrect_memory_access id else state


  let arg_to_value state arg = match arg with
    | RValue -> UnitV
    | LValue id -> mem_get state id

  let st_mem_len state =
    match state with (_, _, mem_len, _) -> mem_len

  let st_add_arg state state_before id arg_tag arg =
    match (arg_tag, arg) with
      | (Ref, RValue) -> raise @@ Ref_rvalue_argument id (* TODO: allow later ?? *) 
      | (Ref, LValue arg) -> env_add state id (env_get state_before arg)
      | (Value, arg) -> let state = mem_add state (arg_to_value state_before arg) in
                        env_add state id (st_mem_len state - 1)

  let st_spoil_assignments state =
    match state with (env, mem, mem_len, assignments) ->
    (* TODO: use env var ids instead of mem_ids ?? *)
    (env, List.fold_left (fun mem id -> list_replace mem (inv_id mem_len @@ env_get state id) BotV) mem assignments, mem_len, [])

  let rec eval_stmt state prog stmt =
    match stmt with
      | Call (f_id, args) -> eval_fun state prog (List.nth prog f_id) (List.map (fun arg -> LValue arg) args)
      | Read id -> mem_check state id
      | Write id -> mem_set state id UnitV

  and eval_body state prog body =
    List.fold_left (fun state stmt -> eval_stmt state prog stmt) state body

  and eval_fun state prog decl args =
    match decl with (arg_tags, body) ->
    match state with (env_before, mem_before, len_before, assignments_before) as state_before ->
    let state = ([], mem_before, len_before, []) in
    let (state, _) = List.fold_left2 (fun (state, id) arg_tag arg -> (st_add_arg state state_before id arg_tag arg, id + 1)) (state, 0) arg_tags args in
    let state = eval_body state prog body in
    let state = st_spoil_assignments state in
    match state with (_env, mem, len, _assignments) ->
    (env_before, List.drop (len - len_before) mem, len_before, assignments_before) (* TODO: save some assignments ?? *)

  and eval_fun_empty_args state prog decl =
    match decl with (arg_tags, _) ->
    let args = List.map (fun _ -> RValue) arg_tags in
    eval_fun state prog decl args

  let empty_state = ([], [], 0, [])

  let eval_prog (prog, main_decl) = ignore @@ eval_fun_empty_args empty_state prog main_decl

  (* tests *)

  (* >> tests without functions *)

  let%expect_test "empty" =
    eval_prog ([], ([], []));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "ref param in main failure" =
    try (eval_prog ([], ([Ref], []));
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
    eval_prog ([], ([Value], [Write 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple read" = (* NOTE: should not work with read-before-write check*)
    eval_prog ([], ([Value], [Read 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "multiple read & write" =
    eval_prog ([], ([Value], [Write 0; Read 0; Write 0; Write 0; Read 0; Read 0]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "multiple read & write, multiple args" =
    eval_prog ([], ([Value; Value; Value], [Write 0; Read 0; Write 1; Write 0; Write 2; Read 1; Write 2; Read 0; Read 2]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "main, access out of range" =
    try(eval_prog ([], ([Value], [Write 0; Read 5 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "main, access out of range" =
    try(eval_prog ([], ([Value], [Write 0; Write 5 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  (* >> tests with one function *)

  let%expect_test "simple function call with value arg" =
    eval_prog ([([Value], [Write 0; Read 0; Write 0])], ([Value], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "simple function call with ref arg" =
    eval_prog ([([Ref], [Write 0; Read 0; Write 0])], ([Value], [Write 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg & read" =
    eval_prog ([([Value], [Write 0; Read 0; Write 0])], ([Value], [Write 0; Call (0, [0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with ref arg & read" =
    try (eval_prog ([([Ref], [Read 0; Write 0])], ([Value], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "function with ref arg & call twice" =
    try (eval_prog ([([Ref], [Read 0; Write 0])], ([Value], [Write 0; Call (0, [0]); Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "function with ref arg, write first & call twice" =
    eval_prog ([([Ref], [Write 0; Read 0; Write 0])], ([Value], [Write 0; Call (0, [0]); Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref arg & read, write" =
    try (eval_prog ([([Ref], [Read 0; Write 0])], ([Value], [Write 0; Call (0, [0]); Read 0; Write 0 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "function with ref arg & write, read" =
    eval_prog ([([Ref], [Read 0; Write 0])], ([Value], [Write 0; Call (0, [0]); Write 0; Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref arg, no write inside & read" =
    eval_prog ([([Ref], [Read 0; Read 0])], ([Value], [Write 0; Call (0, [0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with value arg, read out of range" =
    try(eval_prog ([([Value], [Read 0; Read 1])], ([Value; Value], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref arg, read out of range" =
    try(eval_prog ([([Ref], [Read 0; Read 1])], ([Value; Value], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg, write out of range" =
    try(eval_prog ([([Value], [Read 0; Write 1])], ([Value; Value], [Write 0; Call (0, [0]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with value arg, call out of range" =
    try(eval_prog ([([Value], [Read 0])], ([Value; Value], [Write 0; Call (0, [2]); Read 0 ]));
         [%expect.unreachable])
    with Not_found -> Printf.printf "done!";
    [%expect {| done! |}]

  (* --- *)

  let%expect_test "function with ref & value args, no write inside & read" =
    eval_prog (
      [([Ref; Value], [Read 0; Read 1])],
      ([Value; Value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref & value args, write value inside & read" =
    eval_prog (
      [([Ref; Value], [Read 0; Read 1; Write 1; Read 1])],
      ([Value; Value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "function with ref & value args, write both inside & read" =
    try (eval_prog (
      [([Ref; Value],[Read 0; Read 1; Write 0; Write 1; Read 1])],
      ([Value; Value], [Write 0; Write 1; Call (0, [0; 1]); Read 0; Read 1 ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  (* --- *)

  (* NOTE: maybe important case in the future *)
  let%expect_test "function with ref two same ref args, read both & read" =
    eval_prog (
      [([Ref; Ref],[Read 0; Read 1; Read 1])],
      ([Value], [Write 0; Call (0, [0; 0]); Read 0 ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* NOTE: maybe important case in the future *)
  let%expect_test "function with ref two same ref args, read both & nothing" =
    eval_prog (
      [([Ref; Ref],[Read 0; Read 1; Write 0; Write 1; Read 1])],
      ([Value], [Write 0; Call (0, [0; 0]); ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  (* >> tests with several functions *)

  let%expect_test "two functions with ref arg, read func -> write func" =
    eval_prog (
      [([Ref], [Read 0]); ([Ref], [Write 0])],
      ([Value], [Write 0; Call (0, [0]); Read 0; Call (1, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "two functions with ref arg, write func -> read func" =
    try (eval_prog (
      [([Ref], [Read 0]); ([Ref], [Write 0])],
      ([Value], [Write 0; Call (1, [0]); Call (0, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

  let%expect_test "two functions: ref arg after value arg" =
    eval_prog (
      [([Ref], [Read 0; Write 0]); ([Value], [Read 0; Write 0])],
      ([Value], [Write 0; Call (1, [0]); Read 0; Call (0, [0]) ]));
    Printf.printf "done!";
    [%expect {| done! |}]

  let%expect_test "two functions: value arg after spoiled ref arg" =
    try (eval_prog (
      [([Ref], [Read 0; Write 0]); ([Value], [Read 0; Write 0])],
      ([Value], [Write 0; Call (0, [0]); Call (1, [0]) ]));
         [%expect.unreachable])
    with Incorrect_memory_access id -> Printf.printf "%i" id;
    [%expect {| 0 |}]

end
