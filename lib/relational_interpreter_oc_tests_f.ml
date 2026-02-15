open Relational_semantic_interpreter_oc
open Relational
open GT
open OCanren
open OCanren.Std

@type answer  = St.ground GT.list with show
@type answerArgs = (Arg.ground List.ground) GT.list with show
@type answerValue = Value.ground GT.list with show
@type answerNat = Nat.ground GT.list with show
@type answerNats = (Nat.ground List.ground) GT.list with show
@type answerTag = Tag.ground GT.list with show
@type answerTags = (Tag.ground List.ground) GT.list with show

let inv_id_t _ = show(answerNat) (Stream.take (run q
  (fun q -> ocanren { inv_ido 2 1 q })
  (fun q -> q#reify Nat.prj_exn)))

let inv_id_t2 _ = show(answerNat) (Stream.take (run q
  (fun q -> ocanren { inv_ido 2 0 q })
  (fun q -> q#reify Nat.prj_exn)))

let inv_id_t3 _ = show(answerNat) (Stream.take (run q
  (fun q -> ocanren { inv_ido 2 q 0 })
  (fun q -> q#reify Nat.prj_exn)))

let list_drop_t _ = show(answerNats) (Stream.take (run q
  (fun q -> ocanren { list_dropo 2 [1; 2; 3] q })
  (fun q -> q#reify (List.prj_exn Nat.prj_exn))))

let list_replace_t  _ = show(answerNats) (Stream.take (run q
  (fun q -> ocanren { list_replaceo [1; 2; 3; 4] 1 0 q })
  (fun q -> q#reify (List.prj_exn Nat.prj_exn))))

let arg_to_value_t _ = show(answerValue) (Stream.take (run q
  (fun q -> let open Arg in
            ocanren {
    fresh s in
      empty_stateo s &
      arg_to_valueo s RValue q })
  (fun q -> q#reify (Value.prj_exn))))

let st_add_arg_t _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            ocanren {
    fresh s, s', cnt in
      empty_stateo s &
      empty_stateo s' &
      st_add_argo s  s' Nat.o Val RValue q })
  (fun q -> q#reify (St.prj_exn))))

let write_eval_t1 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            let open Stmt in
            let open FunDecl in
            ocanren {
    fresh s, p, stmt in
      s == St ([Std.pair 1 1; Std.pair 0 0], [Bot; Bot], 2, []) &
      p == [FunDecl ([Ref; Ref], [Write 0; Write 1])] &
      stmt == Write 0 &
      eval_stmto s p stmt q})
  (fun q -> q#reify (St.prj_exn))))

let write_eval_t2 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            let open Stmt in
            let open FunDecl in
            ocanren {
    fresh s, p, stmt in
      s == St ([Std.pair 1 1; Std.pair 0 0], [Bot; Bot], 2, []) &
      p == [FunDecl ([Ref; Ref], [Write 0; Write 1])] &
      stmt == Write 1 &
      eval_stmto s p stmt q})
  (fun q -> q#reify (St.prj_exn))))

let writes_eval_t _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            let open Stmt in
            let open FunDecl in
            ocanren {
    fresh s, p, stmts in
      s == St ([Std.pair 1 1; Std.pair 0 0], [Bot; Bot], 2, []) &
      p == [FunDecl ([Ref; Ref], [Write 0; Write 1])] &
      stmts == [Write 0; Write 1] &
      eval_bodyo s p stmts q})
  (fun q -> q#reify (St.prj_exn))))

let call_eval_t1 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            let open Stmt in
            let open FunDecl in
            ocanren {
    fresh s, p, stmt in
      s == St ([Std.pair 0 0], [Unit], 1, []) &
      p == [FunDecl ([Ref], [Write 0])] &
      stmt == Call (0, [0]) &
      eval_stmto s p stmt q})
  (fun q -> q#reify (St.prj_exn))))

let call_eval_t2 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            let open Stmt in
            let open FunDecl in
            ocanren {
    fresh s, p, stmt in
      s == St ([Std.pair 1 1; Std.pair 0 0], [Unit; Unit], 2, []) &
      p == [FunDecl ([Ref], [Write 0])] &
      stmt == Call (0, [0]) &
      eval_stmto s p stmt q})
  (fun q -> q#reify (St.prj_exn))))

let call_eval_t3 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            let open Stmt in
            let open FunDecl in
            ocanren {
    fresh s, p, stmt in
      s == St ([Std.pair 1 1; Std.pair 0 0], [Unit; Unit], 2, []) &
      p == [FunDecl ([Ref], [Write 0])] &
      stmt == Call (0, [1]) &
      eval_stmto s p stmt q})
  (fun q -> q#reify (St.prj_exn))))

let call_eval_t4 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            let open Stmt in
            let open FunDecl in
            ocanren {
    fresh s, p, stmt in
      s == St ([Std.pair 1 1; Std.pair 0 0], [Unit; Unit], 2, []) &
      p == [FunDecl ([Ref; Ref], [Write 0; Write 1])] &
      stmt == Call (0, [0; 1]) &
      eval_stmto s p stmt q})
  (fun q -> q#reify (St.prj_exn))))

let call_eval_t5 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            let open Stmt in
            let open FunDecl in
            ocanren {
    fresh s, p, stmt in
      s == St ([Std.pair 1 1; Std.pair 0 0], [Unit; Unit], 2, []) &
      p == [FunDecl ([Ref; Ref], [Write 0; Write 1])] &
      stmt == Call (0, [1; 0]) &
      eval_stmto s p stmt q})
  (fun q -> q#reify (St.prj_exn))))

let mem_set_t1 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            ocanren {
    fresh s in
      s == St ([Std.pair 0 0], [Bot], 1, []) &
      mem_seto s 0 Unit q})
  (fun q -> q#reify (St.prj_exn))))

let mem_set_t2 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            ocanren {
    fresh s in
      s == St ([Std.pair 0 0], [Unit], 1, []) &
      mem_seto s 0 Bot q})
  (fun q -> q#reify (St.prj_exn))))

let meem_set_t3 _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            let open Value in
            let open St in
            ocanren {
    fresh s in
      s == St ([Std.pair 0 1], [Unit; Unit], 2, []) &
      mem_seto s 0 Bot q})
  (fun q -> q#reify (St.prj_exn))))

let add_arg_folder_t _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            ocanren {
    fresh s, s', cnt in
      empty_stateo s &
      empty_stateo s' &
      add_arg_foldero s (Std.pair s' Nat.o) Val RValue (Std.pair q cnt) })
  (fun q -> q#reify (St.prj_exn))))

let foldl2_t _ = show(answer) (Stream.take (run q
  (fun q -> let open Arg in
            let open Tag in
            ocanren {
    fresh s, s', cnt, arg_tags, args in
      arg_tags == [Val] &
      args == [RValue] &
      empty_stateo s &
      empty_stateo s' &
      list_foldl2o (add_arg_foldero s) (Std.pair s' Nat.o) arg_tags args (Std.pair q cnt) })
  (fun q -> q#reify (St.prj_exn))))


let rvalue_t _ = show(answerArgs) (Stream.take ~n:3 (run q
  (fun q -> let open Arg in
            ocanren {fresh v in List.mapo arg_to_rvalueo v q})
  (fun q -> q#reify (List.prj_exn Arg.prj_exn))))

(* empty state test *)
let empty_state_t _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {empty_stateo q})
  (fun q -> q#reify (St.prj_exn))))

(* fun eval test *)
let fun_eval_t1 _ = show(answer) (Stream.take (run q
  (fun q -> (* let open Prog in *)
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren { fresh s, p, d in
                        empty_stateo s &
                        p == [] &
                        d == FunDecl ([], []) &
                        eval_fun_empty_argso s p d q })
  (fun q -> q#reify (St.prj_exn))))

(* fun eval test *)
let fun_eval_t2 _ = show(answer) (Stream.take (run q
  (fun q -> (* let open Prog in *)
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren { fresh s, p, d in
                        empty_stateo s &
                        p == [] &
                        d == FunDecl ([Val], [Write 0; Read 0]) &
                        eval_fun_empty_argso s p d q })
  (fun q -> q#reify (St.prj_exn))))

(* fun eval test *)
let fun_eval_t3 _ = show(answer) (Stream.take (run q
  (fun q -> (* let open Prog in *)
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren { fresh s, p, d in
                        empty_stateo s &
                        p == [FunDecl ([Ref], [Write 0])] &
                        d == FunDecl ([Val], [Call (0, [0]); Read 0]) &
                        eval_fun_empty_argso s p d q })
  (fun q -> q#reify (St.prj_exn))))

(* fun eval test *)
let fun_eval_t4 _ = show(answer) (Stream.take (run q
  (fun q -> (* let open Prog in *)
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren { fresh s, p, d in
                        empty_stateo s &
                        p == [FunDecl ([Ref], [Write 0])] &
                        d == FunDecl ([Val; Val], [Call (0, [1]); Write 0; Read 1]) &
                        eval_fun_empty_argso s p d q })
  (fun q -> q#reify (St.prj_exn))))

(* fun eval test *)
let fun_eval_t5 _ = show(answer) (Stream.take (run q
  (fun q -> (* let open Prog in *)
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren { fresh s, p, d in
                        empty_stateo s &
                        p == [FunDecl ([Ref; Ref], [Write 0; Write 1])] &
                        d == FunDecl ([Val; Val], [Call (0, [1; 0]); Write 0; Read 0; Read 1]) &
                        eval_fun_empty_argso s p d q })
  (fun q -> q#reify (St.prj_exn))))

(* prog eval test *)
let prog_eval_t1 _ = show(answer) (Stream.take (run q
  (fun q -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren {eval_progo (Prog ([], FunDecl ([Val], [Write 0; Read 0]))) q})
  (fun q -> q#reify (St.prj_exn))))

(* prog with func eval test *)
let prog_eeal_t2 _ = show(answer) (Stream.take (run q
  (fun q -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren {eval_progo (Prog ([FunDecl ([Val], [Write 0; Read 0])], FunDecl ([Val], [Write 0; Read 0; Call (0, [0])]))) q})
  (fun q -> q#reify (St.prj_exn))))

(* prog with func eval test *)
let prog_eval_t3 _ = show(answer) (Stream.take (run q
  (fun q -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren {eval_progo (Prog ([FunDecl ([Ref], [Write 0; Read 0])], FunDecl ([Val], [Write 0; Read 0; Call (0, [0])]))) q})
  (fun q -> q#reify (St.prj_exn))))

(* prog with func eval test *)
let prog_eval_t4 _ = show(answer) (Stream.take (run q
  (fun q -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            ocanren {eval_progo (Prog ([FunDecl ([Ref], [Write 0])], FunDecl ([Val], [Call (0, [0]); Read 0]))) q})
  (fun q -> q#reify (St.prj_exn))))

(* annotation gen prog test *)
let synt_t1 _ = show(answerTag) (Stream.take (run q
  (fun q -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            let open St in
            ocanren {eval_progo (Prog ([FunDecl ([q], [Write 0])], FunDecl ([Val], [Call (0, [0]); Read 0]))) (St ([], [], 0, []))})
  (fun q -> q#reify (Tag.prj_exn))))

(* annotation gen prog test *)
let synt_t2 _ = show(answerTag) (Stream.take (run q
  (fun q -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            let open St in
            ocanren {eval_progo (Prog ([FunDecl ([q], [Write 0])], FunDecl ([Val], [Call (0, [0]); Write 0; Read 0]))) (St ([], [], 0, []))})
  (fun q -> q#reify (Tag.prj_exn))))

(* annotation gen prog test *)
let synt_t3 _ = show(answerTags) (Stream.take (run qr
  (fun q r -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            let open St in
            ocanren {eval_progo (Prog ([FunDecl ([q], [Write 0])], FunDecl ([r], [Call (0, [0]); Write 0; Read 0]))) (St ([], [], 0, []))})
  (fun q r -> [q#reify (Tag.prj_exn); r#reify (Tag.prj_exn)])))

(* annotation gen prog test *)
let synt_t4 _ = show(answerTags) (Stream.take (run q
  (fun q -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            let open St in
            ocanren {eval_progo (Prog ([FunDecl ([q], [Write 0])], FunDecl ([Val; Val], [Call (0, [1]); Write 0; Read 1]))) (St ([], [], 0, []))})
  (fun q -> [q#reify (Tag.prj_exn)]))) (* -> [Val] *)

(* annotation gen prog test *)
let synt_t5 _ = show(answerTags) (Stream.take (run qr
  (fun q r -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            let open St in
            ocanren {eval_progo (Prog ([FunDecl ([q; r], [Write 0])], FunDecl ([Val; Val], [Call (0, [0; 1]); Write 0; Read 0]))) (St ([], [], 0, []))})
  (fun q r -> [q#reify (Tag.prj_exn); r#reify (Tag.prj_exn)]))) (* all variants *)

(* annotation gen prog test *)
let synt_t6 _ = show(answerTags) (Stream.take (run qr
  (fun q r -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            let open St in
            ocanren {eval_progo (Prog ([FunDecl ([q; r], [Write 0])], FunDecl ([Val; Val], [Call (0, [1; 0]); Write 0; Read 0]))) (St ([], [], 0, []))})
  (fun q r -> [q#reify (Tag.prj_exn); r#reify (Tag.prj_exn)]))) (* all variants *)

(* annotation gen prog test *)
let synt_t7 _ = show(answerTags) (Stream.take (run qr
  (fun q r -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            let open St in
            ocanren {eval_progo (Prog ([FunDecl ([q; r], [Write 0; Write 1])], FunDecl ([Val; Val], [Call (0, [0; 1]); Write 0; Read 0; Read 1]))) (St ([], [], 0, []))})
  (fun q r -> [q#reify (Tag.prj_exn); r#reify (Tag.prj_exn)])))

(* annotation gen prog test *)
let synt_t8 _ = show(answerTags) (Stream.take (run qr
  (fun q r -> let open Prog in
            let open FunDecl in
            let open Tag in
            let open Stmt in
            let open St in
            ocanren {eval_progo (Prog ([FunDecl ([q; r], [Write 0; Write 1])], FunDecl ([Val; Val], [Call (0, [1; 0]); Write 0; Read 0; Read 1]))) (St ([], [], 0, []))})
  (fun q r -> [q#reify (Tag.prj_exn); r#reify (Tag.prj_exn)])))
