open Synthesizer
open Relational
open GT
open OCanren
open OCanren.Std

open Prg
open Stmt
open Decl
open Type
open Expr
open Path
open CopyCap
open ReadCap
open WriteCap
open InCap
open OutCap
open Mode

@type answer  = StEnv.ground GT.list with show

  (* - shortcuts *)

(* TODO *)

(* NOTE: redo with fold ?? *)
let rec seqo stmts stmt' = ocanren {
    { stmts == [] & stmt' == SkipS } |
    { fresh s in
      stmts == [s] &
      stmt' == s } |
    { fresh s, s', ss, stmt_rest' in
      stmts == s :: s' :: ss &
      seqo (s' :: ss) stmt_rest' &
      stmt' == SeqS(s, stmt_rest')
    }
  }

  (* - basic var tests *)

let prog_eval_t_empty _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog in
              prog == Prg ([], SkipS) &
              prog_evalo prog q})
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_var _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg in
              globals_min_ido xg &
              prog == Prg ([VarD (UnitT (Rd, MayWr), UnitE)],
                           ReadS (VarP xg)) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

(* NOTE: does not work well for tests :( *)
(* let prog_eval_t2_simple_var_ans _ = show(answer) (Stream.take (run q *)
  (* (fun q -> ocanren { *)
              (* fresh xg in *)
              (* globals_min_ido xg & *)
              (* q == StEnv (MemEnv ([ZeroV], 1), *)
                          (* TypesEnv ([(xg, UnitT (Rd, MayWr))], *)
                                    (* [(xg, UnitT (Rd, MayWr))]), *)
                          (* ValsEnv ([(xg, 0)], [(xg, 0)])) }) *)
  (* (fun q -> q#reify (StEnv.prj_exn)))) *)

let prog_eval_t_simple_var_fbd_rd _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg in
              globals_min_ido xg &
              prog == Prg ([VarD (UnitT (NRd, MayWr), UnitE)],
                           ReadS (VarP xg)) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_vars_fbd_rd_rd _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg in
              globals_min_ido xg &
              yg == Nat.s xg &
              prog == Prg ([VarD (UnitT (NRd, MayWr), UnitE);
                            VarD (UnitT (Rd, MayWr), UnitE)],
                           ReadS (VarP yg)) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_var_wr _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg in
              globals_min_ido xg &
              prog == Prg ([VarD (UnitT (NRd, MayWr), UnitE)],
                           WriteS (VarP xg)) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_var_fbd_wr _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg in
              globals_min_ido xg &
              prog == Prg ([VarD (UnitT (NRd, NeverWr), UnitE)],
                           WriteS (VarP xg)) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_var_wr_rd _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg in
              globals_min_ido xg &
              prog == Prg ([VarD (UnitT (NRd, MayWr), UnitE)],
                           SeqS (WriteS (VarP xg),
                                 ReadS (VarP xg))) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

  (* - basic call tests *)

let prog_eval_t_simple_call_rd _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, fg, xd, fd in
              globals_min_ido xg &
              fg == Nat.s xg &
              xd == VarD (UnitT (Rd, NeverWr), UnitE) &
              fd == FunD ([(Mode (In, NOut), UnitT (Rd, NeverWr))], ReadS (VarP 0)) &
              prog == Prg ([xd; fd], CallS (VarP fg, [PathE (VarP xg)])) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_call_rd_ref _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, MayWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, MayWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (Rd, MayWr)))],
                          ReadS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], CallS (VarP fg, [PathE (VarP yg)])) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_call_wr _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, MayWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, MayWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (Rd, MayWr)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], CallS (VarP fg, [PathE (VarP yg)])) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_call_wr_rd _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (NRd, MayWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (NRd, MayWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (NRd, AlwaysWr)))],
                          SeqS (WriteS (DerefP (VarP 0)),
                                ReadS (DerefP (VarP 0)))) &
              prog == Prg ([xd; yd; fd], CallS (VarP fg, [PathE (VarP yg)])) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_call_fbd_wr _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, MayWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, MayWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (Rd, NeverWr)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], CallS (VarP fg, [PathE (VarP yg)])) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_call_ref_wr _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (Rd, AlwaysWr)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], CallS (VarP fg, [PathE (VarP yg)])) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_call_ref_fbd_wr _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (Rd, AlwaysWr)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], SeqS (CallS (VarP fg, [PathE (VarP yg)]),
                                               ReadS (DerefP (VarP yg)))) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_simple_call_ref_wr_with_fix _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (Rd, AlwaysWr)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], SeqS (CallS (VarP fg, [PathE (VarP yg)]),
                                         SeqS (WriteS (DerefP (VarP yg)),
                                               ReadS (DerefP (VarP yg))))) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_call_in_call _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, f2g, xd, yd, fd, f2d in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              f2g == Nat.s fg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (Rd, AlwaysWr)))],
                          WriteS (DerefP (VarP 0))) &
              f2d == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (Rd, AlwaysWr)))],
                           SeqS (CallS (VarP fg, [PathE (VarP 0)]),
                                 WriteS (DerefP (VarP 0)))) &
              prog == Prg ([xd; yd; fd; f2d], SeqS (CallS (VarP f2g, [PathE (VarP yg)]),
                                               ReadS (DerefP (VarP yg)))) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_fix_call_after_call _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, f2g, xd, yd, fd, f2d in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              f2g == Nat.s fg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (NRd, AlwaysWr)))],
                          WriteS (DerefP (VarP 0))) &
              f2d == FunD ([(Mode (In, Out), RefT (Rf, UnitT (NRd, AlwaysWr)))],
                           WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd; f2d], SeqS (CallS (VarP fg, [PathE (VarP yg)]),
                                              SeqS (CallS (VarP f2g, [PathE (VarP yg)]),
                                                    ReadS (DerefP (VarP yg))))) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_call_with_glob_usage _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (Rd, AlwaysWr)))],
                          SeqS (WriteS (VarP xg),
                                ReadS (DerefP (VarP 0)))) &
              prog == Prg ([xd; yd; fd], SeqS (CallS (VarP fg, [PathE (VarP yg)]),
                                               ReadS (DerefP (VarP yg)))) &
              prog_evalo prog q
              })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_call_with_rd_wr_2_args _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, x2g, y2g, fg, xd, yd, x2d, y2d, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              x2g == Nat.s yg &
              y2g == Nat.s x2g &
              fg == Nat.s y2g &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              x2d == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              y2d == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE x2g) &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (Rd, NeverWr)));
                           (Mode (In, NOut), RefT (Rf, UnitT (NRd, AlwaysWr)))],
                          SeqS (ReadS (DerefP (VarP 0)),
                                WriteS (DerefP (VarP 1)))) &
              prog == Prg ([xd; yd; x2d; y2d; fd],
                           CallS (VarP fg, [PathE (VarP yg);
                                            PathE (VarP y2g)])) &
              prog_evalo prog q
              })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_call_with_dif_mods_cp _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg,
                          x2g, y2g,
                          x3g, y3g,
                          x4g, y4g,
                          fg,
                          xd, yd,
                          x2d, y2d,
                          x3d, y3d,
                          x4d, y4d,
                          fd,
                          fstmts,
                          stmts in
              globals_min_ido xg &
              yg == Nat.s xg &
              x2g == Nat.s yg &
              y2g == Nat.s x2g &
              x3g == Nat.s y2g &
              y3g == Nat.s x3g &
              x4g == Nat.s y3g &
              y4g == Nat.s x4g &
              fg == Nat.s y4g &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              x2d == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              y2d == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE x2g) &
              x3d == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              y3d == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE x3g) &
              x4d == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              y4d == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE x4g) &
              seqo [ReadS (DerefP (VarP 1));
                    ReadS (DerefP (VarP 3));
                    WriteS (DerefP (VarP 1));
                    WriteS (DerefP (VarP 2));
                    WriteS (DerefP (VarP 3))] fstmts &
              fd == FunD ([(Mode (NIn, NOut), RefT (Cp, UnitT (NRd, AlwaysWr)));
                           (Mode (In, NOut), RefT (Cp, UnitT (Rd, AlwaysWr)));
                           (Mode (NIn, Out), RefT (Cp, UnitT (NRd, AlwaysWr)));
                           (Mode (In, Out), RefT (Cp, UnitT (Rd, AlwaysWr)))],
                          fstmts) &
              seqo [CallS (VarP fg, [PathE (VarP yg);
                                     PathE (VarP y2g);
                                     PathE (VarP y3g);
                                     PathE (VarP y4g)]);
                    ReadS (DerefP (VarP yg));
                    ReadS (DerefP (VarP y2g));
                    ReadS (DerefP (VarP y3g));
                    ReadS (DerefP (VarP y4g))] stmts &
              prog == Prg ([xd; yd;
                            x2d; y2d;
                            x3d; y3d;
                            x4d; y4d;
                            fd],
                           stmts) &
              prog_evalo prog q
              })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_eval_t_call_with_dif_mods_rf _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg,
                          x2g, y2g,
                          x3g, y3g,
                          x4g, y4g,
                          fg,
                          xd, yd,
                          x2d, y2d,
                          x3d, y3d,
                          x4d, y4d,
                          fd,
                          fstmts,
                          stmts in
              globals_min_ido xg &
              yg == Nat.s xg &
              x2g == Nat.s yg &
              y2g == Nat.s x2g &
              x3g == Nat.s y2g &
              y3g == Nat.s x3g &
              x4g == Nat.s y3g &
              y4g == Nat.s x4g &
              fg == Nat.s y4g &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              x2d == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              y2d == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE x2g) &
              x3d == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              y3d == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE x3g) &
              x4d == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              y4d == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE x4g) &
              seqo [ReadS (DerefP (VarP 1));
                    ReadS (DerefP (VarP 3));
                    WriteS (DerefP (VarP 2));
                    WriteS (DerefP (VarP 3))] fstmts &
              fd == FunD ([(Mode (NIn, NOut), RefT (Rf, UnitT (NRd, NeverWr)));
                           (Mode (In, NOut), RefT (Rf, UnitT (Rd, NeverWr)));
                           (Mode (NIn, Out), RefT (Rf, UnitT (NRd, AlwaysWr)));
                           (Mode (In, Out), RefT (Rf, UnitT (Rd, AlwaysWr)))],
                          fstmts) &
              seqo [CallS (VarP fg, [PathE (VarP yg);
                                     PathE (VarP y2g);
                                     PathE (VarP y3g);
                                     PathE (VarP y4g)]);
                    ReadS (DerefP (VarP yg));
                    ReadS (DerefP (VarP y2g));
                    ReadS (DerefP (VarP y3g));
                    ReadS (DerefP (VarP y4g))] stmts &
              prog == Prg ([xd; yd;
                            x2d; y2d;
                            x3d; y3d;
                            x4d; y4d;
                            fd],
                           stmts) &
              prog_evalo prog q
              })
  (fun q -> q#reify (StEnv.prj_exn))))

(* @type answerArgs = (Arg.ground List.ground) GT.list with show *)
(* @type answerValue = Value.ground GT.list with show *)
(* @type answerNat = Nat.ground GT.list with show *)
(* @type answerNats = (Nat.ground List.ground) GT.list with show *)
(* @type answerTag = Tag.ground GT.list with show *)
(* @type answerTags = (Tag.ground List.ground) GT.list with show *)
(* @type answerCopyCap = CopyCap.ground GT.list with show *)
(* @type answerCopyCaps = (CopyCap.ground List.ground) GT.list with show *)

(* let inv_id_t _ = show(answerNat) (Stream.take (run q *)
  (* (fun q -> ocanren { inv_ido 2 1 q }) *)
  (* (fun q -> q#reify Nat.prj_exn))) *)

(* let inv_id_t2 _ = show(answerNat) (Stream.take (run q *)
  (* (fun q -> ocanren { inv_ido 2 0 q }) *)
  (* (fun q -> q#reify Nat.prj_exn))) *)

(* let inv_id_t3 _ = show(answerNat) (Stream.take (run q *)
  (* (fun q -> ocanren { inv_ido 2 q 0 }) *)
  (* (fun q -> q#reify Nat.prj_exn))) *)

(* let list_drop_t _ = show(answerNats) (Stream.take (run q *)
  (* (fun q -> ocanren { list_dropo 2 [1; 2; 3] q }) *)
  (* (fun q -> q#reify (List.prj_exn Nat.prj_exn)))) *)

(* let list_replace_t  _ = show(answerNats) (Stream.take (run q *)
  (* (fun q -> ocanren { list_replaceo [1; 2; 3; 4] 1 0 q }) *)
  (* (fun q -> q#reify (List.prj_exn Nat.prj_exn)))) *)

(* let arg_to_value_t _ = show(answerValue) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* ocanren { *)
    (* fresh s in *)
      (* empty_stateo s & *)
      (* arg_to_valueo s RValue q }) *)
  (* (fun q -> q#reify (Value.prj_exn)))) *)

(* let st_add_arg_t _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* ocanren { *)
    (* fresh s, s', cnt in *)
      (* empty_stateo s & *)
      (* empty_stateo s' & *)
      (* st_add_argo s  s' Nat.o rwi_val RValue q }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let write_eval_t1 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* let open Stmt in *)
            (* let open FunDecl in *)
            (* ocanren { *)
    (* fresh s, p, stmt in *)
      (* s == St ([Std.pair 1 (Std.pair wi_ref 1); Std.pair 0 (Std.pair wi_ref 0)], [Bot; Bot], 2, []) & *)
      (* p == [FunDecl ([wi_ref; wi_ref], [Write 0; Write 1])] & *)
      (* stmt == Write 0 & *)
      (* eval_stmto s p stmt q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let write_eval_t2 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* let open Stmt in *)
            (* let open FunDecl in *)
            (* ocanren { *)
    (* fresh s, p, stmt in *)
      (* s == St ([Std.pair 1 (Std.pair wi_ref 1); Std.pair 0 (Std.pair wi_ref 0)], [Bot; Bot], 2, []) & *)
      (* p == [FunDecl ([wi_ref; wi_ref], [Write 0; Write 1])] & *)
      (* stmt == Write 1 & *)
      (* eval_stmto s p stmt q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let writes_eval_t _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* let open Stmt in *)
            (* let open FunDecl in *)
            (* ocanren { *)
    (* fresh s, p, stmts in *)
      (* s == St ([Std.pair 1 (Std.pair wi_ref 1); Std.pair 0 (Std.pair wi_ref 0)], [Bot; Bot], 2, []) & *)
      (* p == [FunDecl ([wi_ref; wi_ref], [Write 0; Write 1])] & *)
      (* stmts == [Write 0; Write 1] & *)
      (* eval_bodyo s p stmts q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let call_eval_t1 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* let open Stmt in *)
            (* let open FunDecl in *)
            (* ocanren { *)
    (* fresh s, p, stmt in *)
      (* s == St ([Std.pair 0 (Std.pair wi_ref 0)], [Unit], 1, []) & *)
      (* p == [FunDecl ([wi_ref], [Write 0])] & *)
      (* stmt == Call (0, [0]) & *)
      (* eval_stmto s p stmt q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let call_eval_t2 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* let open Stmt in *)
            (* let open FunDecl in *)
            (* ocanren { *)
    (* fresh s, p, stmt in *)
      (* s == St ([Std.pair 1 (Std.pair wi_ref 1); Std.pair 0 (Std.pair wi_ref 0)], [Unit; Unit], 2, []) & *)
      (* p == [FunDecl ([wi_ref], [Write 0])] & *)
      (* stmt == Call (0, [0]) & *)
      (* eval_stmto s p stmt q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let call_eval_t3 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* let open Stmt in *)
            (* let open FunDecl in *)
            (* ocanren { *)
    (* fresh s, p, stmt in *)
      (* s == St ([Std.pair 1 (Std.pair wi_ref 1); Std.pair 0 (Std.pair wi_ref 0)], [Unit; Unit], 2, []) & *)
      (* p == [FunDecl ([wi_ref], [Write 0])] & *)
      (* stmt == Call (0, [1]) & *)
      (* eval_stmto s p stmt q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let call_eval_t4 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* let open Stmt in *)
            (* let open FunDecl in *)
            (* ocanren { *)
    (* fresh s, p, stmt in *)
      (* s == St ([Std.pair 1 (Std.pair wi_ref 1); Std.pair 0 (Std.pair wi_ref 0)], [Unit; Unit], 2, []) & *)
      (* p == [FunDecl ([wi_ref; wi_ref], [Write 0; Write 1])] & *)
      (* stmt == Call (0, [0; 1]) & *)
      (* eval_stmto s p stmt q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let call_eval_t5 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* let open Stmt in *)
            (* let open FunDecl in *)
            (* ocanren { *)
    (* fresh s, p, stmt in *)
      (* s == St ([Std.pair 1 (Std.pair wi_ref 1); Std.pair 0 (Std.pair wi_ref 0)], [Unit; Unit], 2, []) & *)
      (* p == [FunDecl ([wi_ref; wi_ref], [Write 0; Write 1])] & *)
      (* stmt == Call (0, [1; 0]) & *)
      (* eval_stmto s p stmt q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let mem_set_t1 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* ocanren { *)
    (* fresh s in *)
      (* s == St ([Std.pair 0 (Std.pair wi_ref 0)], [Bot], 1, []) & *)
      (* mem_seto s 0 Unit q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let mem_set_t2 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* ocanren { *)
    (* fresh s in *)
      (* s == St ([Std.pair 0 (Std.pair wi_ref 0)], [Unit], 1, []) & *)
      (* mem_seto s 0 Bot q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let meem_set_t3 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* let open Value in *)
            (* let open St in *)
            (* ocanren { *)
    (* fresh s in *)
      (* s == St ([Std.pair 0 (Std.pair wi_ref 1)], [Unit; Unit], 2, []) & *)
      (* mem_seto s 0 Bot q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let add_arg_folder_t _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* ocanren { *)
    (* fresh s, s', cnt in *)
      (* empty_stateo s & *)
      (* empty_stateo s' & *)
      (* add_arg_foldero s (Std.pair s' Nat.o) rwi_val RValue (Std.pair q cnt) }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* let foldl2_t _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Arg in *)
            (* let open Tag in *)
            (* ocanren { *)
    (* fresh s, s', cnt, arg_tags, args in *)
      (* arg_tags == [rwi_val] & *)
      (* args == [RValue] & *)
      (* empty_stateo s & *)
      (* empty_stateo s' & *)
      (* list_foldl2o (add_arg_foldero s) (Std.pair s' Nat.o) arg_tags args (Std.pair q cnt) }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)


(* let rvalue_t _ = show(answerArgs) (Stream.take ~n:3 (run q *)
  (* (fun q -> let open Arg in *)
            (* ocanren {fresh v in List.mapo arg_to_rvalueo v q}) *)
  (* (fun q -> q#reify (List.prj_exn Arg.prj_exn)))) *)

(* empty state test *)
(* let empty_state_t _ = show(answer) (Stream.take (run q *)
  (* (fun q -> ocanren {empty_stateo q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* fun eval test *)
(* let fun_eval_t1 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> (* let open Prog in *) *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren { fresh s, p, d in *)
                        (* empty_stateo s & *)
                        (* p == [] & *)
                        (* d == FunDecl ([], []) & *)
                        (* eval_fun_empty_argso s p d q }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* fun eval test *)
(* let fun_eval_t2 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> (* let open Prog in *) *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren { fresh s, p, d in *)
                        (* empty_stateo s & *)
                        (* p == [] & *)
                        (* d == FunDecl ([wi_val], [Write 0; Read 0]) & *)
                        (* eval_fun_empty_argso s p d q }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* fun eval test *)
(* let fun_eval_t3 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> (* let open Prog in *) *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren { fresh s, p, d in *)
                        (* empty_stateo s & *)
                        (* p == [FunDecl ([wi_ref], [Write 0])] & *)
                        (* d == FunDecl ([wi_val], [Call (0, [0]); Read 0]) & *)
                        (* eval_fun_empty_argso s p d q }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* fun eval test *)
(* let fun_eval_t4 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> (* let open Prog in *) *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren { fresh s, p, d in *)
                        (* empty_stateo s & *)
                        (* p == [FunDecl ([wi_ref], [Write 0])] & *)
                        (* d == FunDecl ([wi_val; wi_val], [Call (0, [1]); Write 0; Read 1]) & *)
                        (* eval_fun_empty_argso s p d q }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* fun eval test *)
(* let fun_eval_t5 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> (* let open Prog in *) *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren { fresh s, p, d in *)
                        (* empty_stateo s & *)
                        (* p == [FunDecl ([wi_ref; wi_ref], [Write 0; Write 1])] & *)
                        (* d == FunDecl ([wi_val; wi_val], [Call (0, [1; 0]); Write 0; Read 0; Read 1]) & *)
                        (* eval_fun_empty_argso s p d q }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* fun eval test *)
(* let fun_eval_t6 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> (* let open Prog in *) *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren { fresh s, p, d in *)
                        (* empty_stateo s & *)
                        (* p == [FunDecl ([wi_val], [Write 0])] & *)
                        (* d == FunDecl ([wi_val], [Call (0, [0])]) & *)
                        (* eval_fun_empty_argso s p d q }) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* prog eval test *)
(* let prog_eval_t1 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren {eval_progo (Prog ([], FunDecl ([wi_val], [Write 0; Read 0]))) q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* prog with func eval test *)
(* let prog_eval_t2 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren {eval_progo (Prog ([FunDecl ([wi_val], [Write 0; Read 0])], *)
                                       (* FunDecl ([wi_val], [Write 0; Read 0; Call (0, [0])]))) q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* prog with func eval test *)
(* let prog_eval_t3 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren {eval_progo (Prog ([FunDecl ([wi_ref], [Write 0; Read 0])], *)
                                       (* FunDecl ([wi_val], [Write 0; Read 0; Call (0, [0])]))) q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* prog with func eval test *)
(* let prog_eval_t4 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren {eval_progo (Prog ([FunDecl ([wi_ref], [Write 0])], *)
                                       (* FunDecl ([wi_val], [Call (0, [0]); Read 0]))) q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* prog with func eval test *)
(* let prog_eval_t5 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren {eval_progo (Prog ([FunDecl ([wi_val], [Write 0])], *)
                                       (* FunDecl ([wi_val], [Call (0, [0]); Read 0]))) q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* prog with func eval test *)
(* let prog_eval_t6 _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren {eval_progo (Prog ([FunDecl ([ri_val], [Write 0])], *)
                                       (* FunDecl ([wi_val], [Call (0, [0]); Read 0]))) q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

(* annotation gen prog test *)
(* let synt_t1 _ = show(answerTag) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {i_any q & *)
                     (* eval_progo (Prog ([FunDecl ([q], [Write 0])], *)
                                       (* FunDecl ([wi_val], [Call (0, [0]); Read 0]))) (St ([], [], 0, [0]))}) *)
  (* (fun q -> q#reify (Tag.prj_exn)))) *)

(* annotation gen prog test *)
(* let synt_t2 _ = show(answerTag) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {i_any q & is_not_reado q & *)
                     (* eval_progo (Prog ([FunDecl ([q], [Write 0])], *)
                                       (* FunDecl ([wi_val], [Call (0, [0]); Write 0; Read 0]))) (St ([], [], 0, [0]))}) *)
  (* (fun q -> q#reify (Tag.prj_exn)))) *)

(* annotation gen prog test *)
(* let synt_t3 _ = show(answerTags) (Stream.take (run qr *)
  (* (fun q r -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {i_any q & is_not_reado q & i_any r & is_not_reado r & *)
                     (* eval_progo (Prog ([FunDecl ([q], [Write 0])], *)
                                       (* FunDecl ([r], [Call (0, [0]); Write 0; Read 0]))) (St ([], [], 0, [0]))}) *)
  (* (fun q r -> [q#reify (Tag.prj_exn); r#reify (Tag.prj_exn)]))) *)

(* annotation gen prog test *)
(* let synt_t4 _ = show(answerTags) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {i_any q & is_not_reado q & *)
                     (* eval_progo (Prog ([FunDecl ([q], [Write 0])], *)
                                       (* FunDecl ([wi_val; wi_val], [Call (0, [1]); Write 0; Read 1]))) (St ([], [], 0, [0]))}) *)
  (* (fun q -> [q#reify (Tag.prj_exn)]))) (* -> [Val] *) *)

(* annotation gen prog test *)
(* let synt_t5 _ = show(answerCopyCaps) (Stream.take (run qr *)
  (* (fun q r -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {fresh q', r' in *)
                     (* i_any q' & is_not_reado q' & *)
                     (* i_any r' & is_not_reado r' & is_never_writeo r' & *)
                     (* eq_copyo q' q & eq_copyo r' r & *)
                     (* eval_progo (Prog ([FunDecl ([q'; r'], [Write 0])], *)
                                       (* FunDecl ([wi_val; wi_val], [Call (0, [0; 1]); Write 0; Read 0]))) (St ([], [], 0, [0]))}) *)
  (* (fun q r -> [q#reify (CopyCap.prj_exn); r#reify (CopyCap.prj_exn)]))) (* all variants *) *)

(* annotation gen prog test *)
(* let synt_t6 _ = show(answerCopyCaps) (Stream.take (run qr *)
  (* (fun q r -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {fresh q', r' in *)
                     (* i_any q' & is_not_reado q' & *)
                     (* i_any r' & is_not_reado r' & is_never_writeo r' & *)
                     (* eq_copyo q' q & eq_copyo r' r & *)
                     (* eval_progo (Prog ([FunDecl ([q'; r'], [Write 0])], *)
                                       (* FunDecl ([wi_val; wi_val], [Call (0, [1; 0]); Write 0; Read 0]))) (St ([], [], 0, [0]))}) *)
  (* (fun q r -> [q#reify (CopyCap.prj_exn); r#reify (CopyCap.prj_exn)]))) (* all variants *) *)

(* annotation gen prog test *)
(* let synt_t7 _ = show(answerCopyCaps) (Stream.take (run qr *)
  (* (fun q r -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {fresh q', r' in *)
                     (* i_any q' & is_not_reado q' & i_any r' & is_not_reado r' & *)
                     (* eq_copyo q' q & eq_copyo r' r & *)
                     (* eval_progo (Prog ([FunDecl ([q'; r'], [Write 0; Write 1])], *)
                                       (* FunDecl ([wi_val; wi_val], [Call (0, [0; 1]); Write 0; Read 0; Read 1]))) (St ([], [], 0, [0]))}) *)
  (* (fun q r -> [q#reify (CopyCap.prj_exn); r#reify (CopyCap.prj_exn)]))) *)

(* annotation gen prog test *)
(* let synt_t8 _ = show(answerCopyCaps) (Stream.take (run qr *)
  (* (fun q r -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {fresh q', r' in *)
                     (* i_any q' & is_not_reado q' & i_any r' & is_not_reado r' & *)
                     (* eq_copyo q' q & eq_copyo r' r & *)
                     (* eval_progo (Prog ([FunDecl ([q'; r'], [Write 0; Write 1])], *)
                                       (* FunDecl ([wi_val; wi_val], [Call (0, [1; 0]); Write 0; Read 0; Read 1]))) (St ([], [], 0, [0]))}) *)
  (* (fun q r -> [q#reify (CopyCap.prj_exn); r#reify (CopyCap.prj_exn)]))) *)

(* annotation gen prog test *)
(* let synt_t9 _ = show(answerCopyCaps) (Stream.take (run qr *)
  (* (fun q r -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* let open St in *)
            (* ocanren {fresh q', r' in *)
                     (* i_any q' & is_not_reado q' & *)
                     (* i_any r' & is_reado r' & is_never_writeo r' & *)
                     (* eq_copyo q' q & eq_copyo r' r & *)
                     (* eval_progo (Prog ([FunDecl ([q'; r'], [Write 0; Read 1])], *)
                                       (* FunDecl ([wi_val; wi_val], [Call (0, [0; 1]); Read 0; Read 1]))) (St ([], [], 0, [0]))}) *)
  (* (fun q r -> [q#reify (CopyCap.prj_exn); r#reify (CopyCap.prj_exn)]))) *)

(* TODO: FIXME: implement memoization cuts *)
(* prog with recursive function call *)
(* let rec_eval_t _ = show(answer) (Stream.take (run q *)
  (* (fun q -> let open Prog in *)
            (* let open FunDecl in *)
            (* let open Tag in *)
            (* let open Stmt in *)
            (* ocanren {eval_progo (Prog ([FunDecl ([wi_ref], [Write 0; Call (0, [0])])], *)
                                       (* FunDecl ([wi_val], [Call (0, [0]); Write 0; Read 0]))) q}) *)
  (* (fun q -> q#reify (St.prj_exn)))) *)

