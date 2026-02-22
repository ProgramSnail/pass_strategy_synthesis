open Tests_f
open Synthesizer
open Relational

let%expect_test "inv id: test 1" = print_endline (inv_id_t ()); [%expect {| [O] |}]
let%expect_test "some test" = print_endline (inv_id_t2 ()); [%expect {| [S (O)] |}]
let%expect_test "some test" = print_endline (inv_id_t3 ()); [%expect {| [S (O)] |}]
let%expect_test "some test" = print_endline (list_drop_t ()); [%expect {| [[S (S (S (O)))]] |}]
let%expect_test "some test" = print_endline (list_replace_t ()); [%expect {| [[S (O); O; S (S (S (O))); S (S (S (S (O))))]] |}]
let%expect_test "some test" = print_endline (arg_to_value_t ()); [%expect {| [Unit] |}]
let%expect_test "some test" = print_endline (st_add_arg_t ()); [%expect {| [St ([(O, O)], [Unit], S (O), [])] |}]
let%expect_test "some test" = print_endline (write_eval_t1 ()); [%expect {| [St ([(S (O), S (O)); (O, O)], [Bot; Unit], S (S (O)), [O])] |}]
let%expect_test "some test" = print_endline (write_eval_t2 ()); [%expect {| [St ([(S (O), S (O)); (O, O)], [Unit; Bot], S (S (O)), [S (O)])] |}]
let%expect_test "some test" = print_endline (writes_eval_t ()); [%expect {| [St ([(S (O), S (O)); (O, O)], [Unit; Unit], S (S (O)), [S (O); O])] |}]
let%expect_test "some test" = print_endline (call_eval_t1 ()); [%expect {| [St ([(O, O)], [Bot], S (O), [])] |}]
let%expect_test "some test" = print_endline (call_eval_t2 ()); [%expect {| [St ([(S (O), S (O)); (O, O)], [Unit; Bot], S (S (O)), [])] |}]
let%expect_test "some test" = print_endline (call_eval_t3 ()); [%expect {| [St ([(S (O), S (O)); (O, O)], [Bot; Unit], S (S (O)), [])] |}]
let%expect_test "some test" = print_endline (call_eval_t4 ()); [%expect {| [St ([(S (O), S (O)); (O, O)], [Bot; Bot], S (S (O)), [])] |}]
let%expect_test "some test" = print_endline (call_eval_t5 ()); [%expect {| [St ([(S (O), S (O)); (O, O)], [Bot; Bot], S (S (O)), [])] |}]
let%expect_test "some test" = print_endline (mem_set_t1 ()); [%expect {| [St ([(O, O)], [Unit], S (O), [O])] |}]
let%expect_test "some test" = print_endline (mem_set_t2 ()); [%expect {| [St ([(O, O)], [Bot], S (O), [O])] |}]
let%expect_test "some test" = print_endline (meem_set_t3 ()); [%expect {| [St ([(O, S (O))], [Bot; Unit], S (S (O)), [O])] |}]
let%expect_test "some test" = print_endline (add_arg_folder_t ()); [%expect {| [St ([(O, O)], [Unit], S (O), [])] |}]
let%expect_test "some test" = print_endline (foldl2_t ()); [%expect {| [St ([(O, O)], [Unit], S (O), [])] |}]
let%expect_test "some test" = print_endline (rvalue_t ()); [%expect {| [[]; [RValue]; [RValue; RValue]] |}]
let%expect_test "some test" = print_endline (empty_state_t ()); [%expect {| [St ([], [], O, [])] |}]
let%expect_test "some test" = print_endline (fun_eval_t1 ()); [%expect {| [St ([], [], O, [])] |}]
let%expect_test "some test" = print_endline (fun_eval_t2 ()); [%expect {| [St ([], [], O, [])] |}]
let%expect_test "some test" = print_endline (fun_eval_t3 ()); [%expect {| [] |}]
let%expect_test "some test" = print_endline (fun_eval_t4 ()); [%expect {| [] |}]
let%expect_test "some test" = print_endline (fun_eval_t5 ()); [%expect {| [] |}]
let%expect_test "some test" = print_endline (prog_eval_t1 ()); [%expect {| [St ([], [], O, [])] |}]
let%expect_test "some test" = print_endline (prog_eeal_t2 ()); [%expect {| [St ([], [], O, [])] |}]
let%expect_test "some test" = print_endline (prog_eval_t3 ()); [%expect {| [St ([], [], O, [])] |}]
let%expect_test "some test" = print_endline (prog_eval_t4 ()); [%expect {| [] |}]
let%expect_test "some test" = print_endline (synt_t1 ()); [%expect {| [Val] |}]
let%expect_test "some test" = print_endline (synt_t2 ()); [%expect {| [Ref; Val] |}]
let%expect_test "some test" = print_endline (synt_t3 ()); [%expect {| [[Ref; Val]; [Val; Val]] |}]
let%expect_test "some test" = print_endline (synt_t4 ()); [%expect {| [[Val]] |}]
let%expect_test "some test" = print_endline (synt_t5 ()); [%expect {| [[Ref; Ref]; [Ref; Val]; [Val; Ref]; [Val; Val]] |}]
let%expect_test "some test" = print_endline (synt_t6 ()); [%expect {| [[Ref; Ref]; [Val; Ref]; [Ref; Val]; [Val; Val]] |}]
let%expect_test "some test" = print_endline (synt_t7 ()); [%expect {| [[Ref; Val]; [Val; Val]] |}]
let%expect_test "some test" = print_endline (synt_t8 ()); [%expect {| [[Val; Ref]; [Val; Val]] |}]
(* TODO: test with assymetric args order *)
(* TODO: tests names *)

let%expect_test "Tag type test" = print_endline (Tag.Test.test ()); [%expect {| [Ref] |}]
let%expect_test "Stmt type test (1)" = print_endline (Stmt.Test.test1 ()); [%expect {| [[S (S (O))]] |}]
let%expect_test "Stmt type test (2)" = print_endline (Stmt.Test.test2 ()); [%expect {| [Call (S (O), [S (S (O))])] |}]
let%expect_test "FunDecl type test" = print_endline (FunDecl.Test.test ()); [%expect {| [FunDecl ([Ref; Val], [Call (S (O), [O]); Write (S (O))])] |}]
let%expect_test "Prog type test" = print_endline (Prog.Test.test ()); [%expect {| [Prog ([], FunDecl ([Val], [Write (O); Read (O)]))] |}]
let%expect_test "Arg type test" = print_endline (Arg.Test.test ()); [%expect {| [LValue (S (S (S (O))))] |}]
let%expect_test "Value type test" = print_endline (Value.Test.test ()); [%expect {| [Bot; Unit] |}]
let%expect_test "St type test" = print_endline (St.Test.test ()); [%expect {| [St ([(O, O)], [Bot], S (O), [O])] |}]







