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

@type answer =
  StEnv.ground GT.list with show
@type answerCpCap =
  CopyCap.ground GT.list with show

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

let prog_eval_t_call_in_call_rec _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (Rd, AlwaysWr)))],
                          SeqS (CallS (VarP fg, [PathE (VarP 0)]),
                                WriteS (DerefP (VarP 0)))) &
              prog == Prg ([xd; yd; fd], SeqS (CallS (VarP fg, [PathE (VarP yg)]),
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

(* - basic synthesis tests *)

let prog_cp_cap_synt_t_simple_call_ref_wr _ = show(answerCpCap) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd, st in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (q, UnitT (Rd, AlwaysWr)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], CallS (VarP fg, [PathE (VarP yg)])) &
              prog_evalo prog st })
  (fun q -> q#reify (CopyCap.prj_exn))))

let prog_cp_cap_synt_t_simple_call_ref_wr' _ = show(answerCpCap) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd,
                    st, rd_cap, wr_cap in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (q, UnitT (rd_cap, wr_cap)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], CallS (VarP fg, [PathE (VarP yg)])) &
              prog_evalo prog st })
  (fun q -> q#reify (CopyCap.prj_exn))))

let prog_cp_cap_synt_t_simple_call_ref_fbd_wr _ = show(answerCpCap) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd, st in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (q, UnitT (Rd, AlwaysWr)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], SeqS (CallS (VarP fg, [PathE (VarP yg)]),
                                               ReadS (DerefP (VarP yg)))) &
              prog_evalo prog st })
  (fun q -> q#reify (CopyCap.prj_exn))))

let prog_cp_cap_synt_t_simple_call_ref_fbd_wr' _ = show(answerCpCap) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xg, yg, fg, xd, yd, fd,
                    st, rd_cap, wr_cap in
              globals_min_ido xg &
              yg == Nat.s xg &
              fg == Nat.s yg &
              xd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (q, UnitT (rd_cap, wr_cap)))],
                          WriteS (DerefP (VarP 0))) &
              prog == Prg ([xd; yd; fd], SeqS (CallS (VarP fg, [PathE (VarP yg)]),
                                               ReadS (DerefP (VarP yg)))) &
              prog_evalo prog st })
  (fun q -> q#reify (CopyCap.prj_exn))))

(* - complex tests *)

let deref_accesso id v p' = ocanren {
    p' == DerefP (AccessP (VarP v, id))
  }

let access_deref_accesso id_ext id_int v p' = ocanren {
    p' == AccessP (DerefP (AccessP (VarP v, id_int)), id_ext)
  }

let access_deref_access_deref_accesso id_ext id_mid id_int v p' = ocanren {
    p' == AccessP (DerefP (AccessP (DerefP (AccessP (VarP v, id_int)), id_mid)), id_ext)
  }

(* TODO *)
let prog_eval_compl_test_send _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh (* types *)
                    uT_r_aw,
                    user_utilsT, user_infoT,
                    userT, versionT, utilsT,
                    requestT,
                    moded_requestT,
                    (* global vars init exprs *)
                    user_utilsE, user_infoE,
                    userE, versionE, utilsE,
                    requestE,
                    (* global vars ids *)
                    user_utilsID, user_infoID,
                    userID, versionID, utilsID,
                    dataID, requestID,
                    (* function ids *)
                    get_version_idID,
                    updated_versionID,
                    sendID,
                    send_allID,
                    (* function definitions *)
                    get_version_idF,
                    updated_versionF,
                    sendFBranch,
                    sendF,
                    send_allF,
                    (* other *)
                    prog in
              (* types *)
              uT_r_aw == UnitT (Rd, AlwaysWr) &
              user_utilsT == TupleT [uT_r_aw (* 0 id *); uT_r_aw] &
              user_infoT ==  TupleT [uT_r_aw (* 0 name *); uT_r_aw; uT_r_aw] &
              userT == TupleT [RefT (Cp, user_utilsT) (* 0 utils *);
                               RefT (Cp, user_infoT) (* 1 info *)] &
              versionT == TupleT [uT_r_aw (* 0 id *); uT_r_aw; uT_r_aw] &
              utilsT == TupleT [uT_r_aw (* 0 has_version *); uT_r_aw (* 1 id *)] &
              requestT == TupleT [RefT (Cp, userT) (* 0 user *);
                                  RefT (Cp, versionT) (* 1 version *);
                                  RefT (Cp, utilsT) (* 2 utils *);
                                  RefT (Cp, uT_r_aw) (* 3 data *);
                                  uT_r_aw (* 4 operation_date *)] &
              moded_requestT == (Mode (In, NOut), requestT) &
              (* global vars init exprs *)
              user_utilsE == TupleE [UnitE (* 0 id *); UnitE] &
              user_infoE ==  TupleE [UnitE (* 0 name *); UnitE; UnitE] &
              userE == TupleE [RefE user_utilsID (* 0 utils *);
                               RefE user_infoID (* 1 info *)] &
              versionE == TupleE [UnitE (* 0 id *); UnitE; UnitE] &
              utilsE == TupleE [UnitE (* 0 has_version *); UnitE (* 1 id *)] &
              requestE == TupleE [RefE userID (* 0 user *);
                                  RefE versionID (* 1 version *);
                                  RefE utilsID (* 2 utils *);
                                  RefE dataID (* 3 data *);
                                  UnitE (* 4 operation_date *)] &
              (* global vars ids *)
              globals_min_ido user_utilsID &
              user_infoID == Nat.s user_utilsID &
              userID == Nat.s user_infoID &
              versionID == Nat.s userID &
              utilsID == Nat.s versionID &
              dataID == Nat.s utilsID &
              requestID == Nat.s dataID &
              (* function ids *)
              get_version_idID == Nat.s requestID &
              updated_versionID == Nat.s get_version_idID &
              sendID == Nat.s updated_versionID &
              send_allID == Nat.s sendID &
              (* function definitions *)
              fresh gvi_access0 in
              access_deref_accesso 0 1 0 gvi_access0 &
              get_version_idF == ChoiceS (ReadS gvi_access0, SkipS) &

              fresh uv_access0, uv_access1, uv_access2 in
              access_deref_accesso 0 2 0 uv_access0 &
              access_deref_accesso 0 1 0 uv_access1 &
              access_deref_accesso 1 1 0 uv_access2 &
              seqo [ReadS uv_access0;
                    ReadS uv_access1;
                    ReadS uv_access2]
                   updated_versionF &

              fresh sb_access0, sb_access1, sb_access2, sb_access3 in
              access_deref_accesso 0 2 0 sb_access0 &
              deref_accesso 3 0 sb_access1 &
              deref_accesso 3 0 sb_access2 &
              access_deref_access_deref_accesso 0 1 0 0 sb_access3 &
              seqo [WriteS sb_access0;
                    ReadS sb_access1;
                    WriteS sb_access2;
                    ReadS sb_access3]
                   sendFBranch &
              seqo [ChoiceS (sendFBranch, SkipS);
                    WriteS (AccessP (VarP 0, 4));
                    (* TODO: read all the substructure ?? *)
                    ReadS (AccessP (VarP 0, 4)) (*rdS v0*)] (* FIXME: TMP, parial read, should be full *)
                   sendF &

              fresh sa_access0, sa_access1, sa_access2, sa_access3 in
              access_deref_accesso 0 1 0 sa_access0 &
              access_deref_accesso 1 1 0 sa_access1 &
              access_deref_access_deref_accesso 0 0 0 0 sa_access2 &
              access_deref_accesso 0 1 0 sa_access3 &
              seqo [WriteS (AccessP (VarP 0, 4)) (*wrS v0*); (* FIXME: TMP, parial write, should be full *)
                    CallS (VarP sendID, [PathE (VarP 0)]);
                    CallS (VarP get_version_idID, [PathE (VarP 0)]);
                    CallS (VarP updated_versionID, [PathE (VarP 0)]);
                    (* TODO: read all the substructure ?? *)
                    WriteS sa_access0;
                    WriteS sa_access1;
                    ChoiceS (
                      ReadS sa_access2,
                      ReadS sa_access3
                    )]
                   send_allF &

              prog == Prg ([
                VarD (user_utilsT, user_utilsE);
                VarD (user_infoT, user_infoE);
                VarD (userT, userE);
                VarD (versionT, versionE);
                VarD (utilsT, utilsE);
                VarD (uT_r_aw, UnitE); (* data *)
                VarD (requestT, requestE);
                FunD ([moded_requestT], get_version_idF);
                FunD ([moded_requestT], updated_versionF);
                FunD ([moded_requestT], sendF);
                FunD ([moded_requestT], send_allF)
              ],
              (* SkipS *)
              CallS (VarP send_allID, [PathE (VarP requestID)])
              ) &
              prog_evalo prog q })
  (fun q -> q#reify (StEnv.prj_exn))))

(* TODO: + synth. test *)
