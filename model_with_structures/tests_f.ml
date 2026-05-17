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
open StEnv

@type answer =
  StEnv.ground GT.list with show
@type answerCpCap =
  CopyCap.ground GT.list with show
@type answerCpCapList =
  (CopyCap.ground GT.list) GT.list with show

(* - shortcuts *)

(* NOTE: redo with fold ?? *)
let seq_foldero stmt_acc stmt stmt_acc' = ocanren {
    stmt_acc' == SeqS(stmt, stmt_acc)
  }
let seqo stmts stmt' = ocanren {
    list_foldro seq_foldero SkipS stmts stmt'
  }
(* ocanren { *)
    (* { stmts == [] & stmt' == SkipS } | *)
    (* { fresh s in *)
      (* stmts == [s] & *)
      (* stmt' == s } | *)
    (* { fresh s, s', ss, stmt_rest' in *)
      (* stmts == s :: s' :: ss & *)
      (* seqo (s' :: ss) stmt_rest' & *)
      (* stmt' == SeqS(s, stmt_rest') *)
    (* } *)
  (* } *)

let deref_accesso id v p' = ocanren {
    p' == DerefP (AccessP (VarP v, id))
  }

let access_deref_accesso id_ext id_int v p' = ocanren {
    p' == AccessP (DerefP (AccessP (VarP v, id_int)), id_ext)
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

(* NOTE: should add ? *)
(* let prog_eval_t_simple_call_noarg _ = show(answer) (Stream.take (run q *)
  (* (fun q -> ocanren { *)
              (* fresh prog, xg, fg, xd, fd in *)
              (* globals_min_ido xg & *)
              (* fg == Nat.s xg & *)
              (* xd == VarD (UnitT (Rd, NeverWr), UnitE) & *)
              (* fd == FunD ([], SkipS) & *)
              (* prog == Prg ([xd; fd], CallS (VarP fg, [])) & *)
              (* prog_evalo prog q }) *)
  (* (fun q -> q#reify (StEnv.prj_exn)))) *)

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
              xd == VarD (UnitT (Rd, NeverWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, NeverWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (Rd, NeverWr)))],
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
              xd == VarD (UnitT (NRd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (NRd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (NRd, AlwaysWr)))],
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
              xd == VarD (UnitT (NRd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (NRd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (NRd, AlwaysWr)))],
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
              xd == VarD (UnitT (NRd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (NRd, AlwaysWr)), RefE xg) &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (NRd, AlwaysWr)))],
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
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (NRd, AlwaysWr)))],
                          WriteS (DerefP (VarP 0))) &
              f2d == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (NRd, AlwaysWr)))],
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
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (NRd, AlwaysWr)))],
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
              fd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (Rd, NeverWr)))],
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
              fd == FunD ([(Mode (NIn, NOut), RefT (Cp, UnitT (NRd, NeverWr)));
                           (Mode (In, NOut), RefT (Cp, UnitT (Rd, AlwaysWr)));
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
              fd == FunD ([(Mode (In, NOut), RefT (q, UnitT (NRd, AlwaysWr)))],
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
              fd == FunD ([(Mode (In, NOut), RefT (q, UnitT (NRd, AlwaysWr)))],
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

(* - presentation tests *)

(* simple types *)

let prog_eval_t_presentation_simple_tp _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xbg, xg,
                          ybg, yg,
                          zbg, zg,
                          kbg, kg,
                          fg, wg, gg, rg,
                          xbd, xd,
                          ybd, yd,
                          zbd, zd,
                          kbd, kd,
                          fd, wd, gd, rd,
                          fstmts, gstmts,
                          stmts in
              globals_min_ido xbg &
              xg == Nat.s xbg &
              ybg == Nat.s xg &
              yg == Nat.s ybg &
              zbg == Nat.s yg &
              zg == Nat.s zbg &
              kbg == Nat.s zg &
              kg == Nat.s kbg &
              fg == Nat.s kg &
              wg == Nat.s fg &
              gg == Nat.s wg &
              rg == Nat.s gg &
              xbd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              xd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xbg) &
              ybd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE ybg) &
              zbd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              zd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE zbg) &
              kbd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              kd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE kbg) &
              seqo [ReadS (DerefP (VarP 0));
                    WriteS (DerefP (VarP 0));
                    ReadS (DerefP (VarP 1))] fstmts &
              fd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (Rd, AlwaysWr)));
                           (Mode (In, NOut), RefT (Rf, UnitT (Rd, NeverWr)))],
                          fstmts) &
              wd == FunD ([(Mode (In, NOut), RefT (Cp, UnitT (NRd, MayWr)))],
                          ChoiceS (WriteS (DerefP (VarP 0)), SkipS)) &
              seqo [WriteS (DerefP (VarP 0));
                    ChoiceS (WriteS (DerefP (VarP 1)), WriteS (DerefP (VarP 0)));
                    ReadS (DerefP (VarP 0));
                    ReadS (DerefP (VarP 1))] gstmts &
              gd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (NRd, AlwaysWr)));
                           (Mode (In, NOut), RefT (Cp, UnitT (Rd, MayWr)))],
                          gstmts) &
              rd == FunD ([(Mode (In, NOut), RefT (Rf, UnitT (Rd, NeverWr)))],
                          ReadS (DerefP (VarP 0))) &
              seqo [
                    CallS (VarP wg, [PathE (VarP xg)]);
                    CallS (VarP rg, [PathE (VarP xg)]);
                    CallS (VarP fg, [PathE (VarP xg); PathE (VarP yg)]);
                    CallS (VarP rg, [PathE (VarP yg)]);
                    CallS (VarP gg, [PathE (VarP zg); PathE (VarP kg)]);
                    CallS (VarP wg, [PathE (VarP zg)]);
                    WriteS (DerefP (VarP zg));
                    CallS (VarP fg, [PathE (VarP yg); PathE (VarP zg)]);
                    CallS (VarP rg, [PathE (VarP kg)])
                  ] stmts &
              prog == Prg ([xbd; xd;
                            ybd; yd;
                            zbd; zd;
                            kbd; kd;
                            fd; wd; gd; rd],
                           stmts) &
              prog_evalo prog q
              })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_synt_t_presentation_simple_tp _ = show(answerCpCapList) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog, xbg, xg,
                          ybg, yg,
                          zbg, zg,
                          kbg, kg,
                          fg, wg, gg, rg,
                          xbd, xd,
                          ybd, yd,
                          zbd, zd,
                          kbd, kd,
                          fd, wd, gd, rd,
                          fstmts, gstmts,
                          stmts,
                          c_fx, c_fy, c_wx, c_gx, c_gy, c_rx,
                          st in
              globals_min_ido xbg &
              xg == Nat.s xbg &
              ybg == Nat.s xg &
              yg == Nat.s ybg &
              zbg == Nat.s yg &
              zg == Nat.s zbg &
              kbg == Nat.s zg &
              kg == Nat.s kbg &
              fg == Nat.s kg &
              wg == Nat.s fg &
              gg == Nat.s wg &
              rg == Nat.s gg &
              xbd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              xd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE xbg) &
              ybd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              yd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE ybg) &
              zbd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              zd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE zbg) &
              kbd == VarD (UnitT (Rd, AlwaysWr), UnitE) &
              kd == VarD (RefT (Rf, UnitT (Rd, AlwaysWr)), RefE kbg) &
              seqo [ReadS (DerefP (VarP 0));
                    WriteS (DerefP (VarP 0));
                    ReadS (DerefP (VarP 1))] fstmts &
              fd == FunD ([(Mode (In, NOut), RefT (c_fx, UnitT (Rd, AlwaysWr)));
                           (Mode (In, NOut), RefT (c_fy, UnitT (Rd, NeverWr)))],
                          fstmts) &
              wd == FunD ([(Mode (In, NOut), RefT (c_wx, UnitT (NRd, MayWr)))],
                          ChoiceS (WriteS (DerefP (VarP 0)), SkipS)) &
              seqo [WriteS (DerefP (VarP 0));
                    ChoiceS (WriteS (DerefP (VarP 1)), WriteS (DerefP (VarP 0)));
                    ReadS (DerefP (VarP 0));
                    ReadS (DerefP (VarP 1))] gstmts &
              gd == FunD ([(Mode (In, NOut), RefT (c_gx, UnitT (NRd, AlwaysWr)));
                           (Mode (In, NOut), RefT (c_gy, UnitT (Rd, MayWr)))],
                          gstmts) &
              rd == FunD ([(Mode (In, NOut), RefT (c_rx, UnitT (Rd, NeverWr)))],
                          ReadS (DerefP (VarP 0))) &
              seqo [
                    CallS (VarP wg, [PathE (VarP xg)]);
                    CallS (VarP rg, [PathE (VarP xg)]);
                    CallS (VarP fg, [PathE (VarP xg); PathE (VarP yg)]);
                    CallS (VarP rg, [PathE (VarP yg)]);
                    CallS (VarP gg, [PathE (VarP zg); PathE (VarP kg)]);
                    CallS (VarP wg, [PathE (VarP zg)]);
                    WriteS (DerefP (VarP zg));
                    CallS (VarP fg, [PathE (VarP yg); PathE (VarP zg)]);
                    CallS (VarP rg, [PathE (VarP kg)])
                  ] stmts &
              prog == Prg ([xbd; xd;
                            ybd; yd;
                            zbd; zd;
                            kbd; kd;
                            fd; wd; gd; rd],
                           stmts) &
              prog_evalo prog st &
              q ==  [c_fx; c_fy; c_wx; c_gx; c_gy; c_rx]
              })
  (fun q -> q#reify (List.prj_exn CopyCap.prj_exn))))

(* complex type *)

let deref_accesso id v p' = ocanren {
    p' == DerefP (AccessP (VarP v, id))
  }

let access_deref_accesso id_ext id_int v p' = ocanren {
    p' == AccessP (DerefP (AccessP (VarP v, id_int)), id_ext)
  }

(* --- *)

let p_rw_unitTo tp = ocanren {
    (* fresh r, w in *)
    tp == UnitT (Rd, AlwaysWr)
  }

let p_rw_userTo tp = ocanren {
    fresh x, y, z in
    p_rw_unitTo x &
    p_rw_unitTo y &
    p_rw_unitTo z &
    tp == TupleT [x; y; z]
  }

let p_rw_dataTo tp = ocanren {
    fresh x, y in
    p_rw_unitTo x &
    p_rw_unitTo y &
    tp == TupleT [x; y]
  }

let p_rw_timeTo tp = ocanren {
    p_rw_unitTo tp
  }

let p_rw_requestTo cu cd ct tp = ocanren {
    fresh userT, dataT, timeT in
    p_rw_userTo userT &
    p_rw_dataTo dataT &
    p_rw_timeTo timeT &
    tp == TupleT [RefT (cu, userT);
                  RefT (cd, dataT);
                  RefT (ct, timeT)]
  }

(* --- *)

let p_any_unitTo tp = ocanren {
    fresh r, w in
    tp == UnitT (r, w)
  }

let p_any_userTo tp = ocanren {
    fresh x, y, z in
    p_any_unitTo x &
    p_any_unitTo y &
    p_any_unitTo z &
    tp == TupleT [x; y; z]
  }

let p_any_dataTo tp = ocanren {
    fresh x, y in
    p_any_unitTo x &
    p_any_unitTo y &
    tp == TupleT [x; y]
  }

let p_any_timeTo tp = ocanren {
    p_any_unitTo tp
  }

let p_any_requestTo cu cd ct tp = ocanren {
    fresh userT, dataT, timeT in
    p_any_userTo userT &
    p_any_dataTo dataT &
    p_any_timeTo timeT &
    tp == TupleT [RefT (cu, userT);
                  RefT (cd, dataT);
                  RefT (ct, timeT)]
  }

(* --- *)

let prog_eval_t_presentation_complex_tp _ = show(answer) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog,
                    userT, dataT, timeT, requestT,
                    requestArgsT,
                    userE, dataE, timeE, requestE,
                    userVID, dataVID, timeVID, requestVID,
                    sendFID, sendD, sendBranchStmts, sendStmts,
                    stmts in
              globals_min_ido userVID &
              dataVID == Nat.s userVID &
              timeVID == Nat.s dataVID &
              requestVID == Nat.s timeVID &
              sendFID == Nat.s requestVID &

              p_rw_userTo userT &
              p_rw_dataTo dataT &
              p_rw_timeTo timeT &
              p_rw_requestTo Cp Cp Cp requestT &
              p_any_requestTo Cp Cp Cp requestArgsT & (* NOTE: for now *)

              userE == TupleE [UnitE; UnitE; UnitE] &
              dataE == TupleE [UnitE; UnitE] &
              timeE == UnitE &
              requestE == TupleE [RefE userVID; RefE dataVID; RefE timeVID] &

              fresh data_p, time_p,
                    user_id_p, user_name_p in
              deref_accesso 1 0 data_p &
              deref_accesso 2 0 time_p &
              access_deref_accesso 0 0 0 user_id_p &
              access_deref_accesso 1 0 0 user_name_p &
              seqo [ReadS data_p;
                    WriteS data_p;
                    ReadS user_name_p;
                    WriteS user_name_p] sendBranchStmts &
              seqo [ChoiceS (sendBranchStmts, SkipS);
                    WriteS time_p;

                    ReadS (VarP 0)
                    (* ReadS data_p0; *)
                    (* ReadS data_p1; *)
                    (* ReadS time_p; *)
                    (* ReadS user_id_p; *)
                    (* ReadS user_name_p; *)
                    (* ReadS user_surname_p *)
              ] sendStmts &
              (* sendStmts == SkipS & *)
              sendD == FunD ([(Mode (In, NOut), requestArgsT)], sendStmts) &

              fresh time_gp, user_name_gp, user_surname_gp in
              deref_accesso 2 requestVID time_gp &
              access_deref_accesso 1 0 requestVID user_name_gp &
              access_deref_accesso 2 0 requestVID user_surname_gp &
              seqo [
                    CallS (VarP sendFID, [PathE (VarP requestVID)]);
                    WriteS time_gp;
                    ChoiceS (ReadS user_name_gp,
                             ReadS user_surname_gp);
                    ReadS time_gp
                  ] stmts &
              prog == Prg ([
                            VarD (userT, userE);
                            VarD (dataT, dataE);
                            VarD (timeT, timeE);
                            VarD (requestT, requestE);
                            sendD
                            ],
                           stmts
                           ) &
              prog_evalo prog q
              })
  (fun q -> q#reify (StEnv.prj_exn))))

let prog_synt_t_presentation_complex_tp _ = show(answerCpCapList) (Stream.take (run q
  (fun q -> ocanren {
              fresh prog,
                    userT, dataT, timeT, requestT,
                    requestArgsT,
                    userE, dataE, timeE, requestE,
                    userVID, dataVID, timeVID, requestVID,
                    sendFID, sendD, sendBranchStmts, sendStmts,
                    stmts,
                    st, c_u, c_d, c_t in
              globals_min_ido userVID &
              dataVID == Nat.s userVID &
              timeVID == Nat.s dataVID &
              requestVID == Nat.s timeVID &
              sendFID == Nat.s requestVID &

              p_rw_userTo userT &
              p_rw_dataTo dataT &
              p_rw_timeTo timeT &
              p_rw_requestTo Cp Cp Cp requestT &
              p_any_requestTo c_u c_d c_t requestArgsT & (* NOTE: for now *)

              userE == TupleE [UnitE; UnitE; UnitE] &
              dataE == TupleE [UnitE; UnitE] &
              timeE == UnitE &
              requestE == TupleE [RefE userVID; RefE dataVID; RefE timeVID] &

              fresh data_p, time_p,
                    user_id_p, user_name_p, user_surname_p in
              deref_accesso 1 0 data_p &
              deref_accesso 2 0 time_p &
              access_deref_accesso 0 0 0 user_id_p &
              access_deref_accesso 1 0 0 user_name_p &
              access_deref_accesso 2 0 0 user_surname_p &
              seqo [ReadS data_p;
                    WriteS data_p;
                    ReadS user_name_p;
                    WriteS user_name_p] sendBranchStmts &
              seqo [ChoiceS (sendBranchStmts, SkipS);
                    WriteS time_p;
                    ReadS (VarP 0)
              ] sendStmts &
              (* sendStmts == SkipS & *)
              sendD == FunD ([(Mode (In, NOut), requestArgsT)], sendStmts) &

              fresh time_gp, user_name_gp, user_surname_gp in
              deref_accesso 2 requestVID time_gp &
              access_deref_accesso 1 0 requestVID user_name_gp &
              access_deref_accesso 2 0 requestVID user_surname_gp &
              seqo [
                    CallS (VarP sendFID, [PathE (VarP requestVID)]);
                    WriteS time_gp;
                    ChoiceS (ReadS user_name_gp,
                             ReadS user_surname_gp);
                    ReadS user_surname_gp; (* TMP *)
                    ReadS time_gp
                  ] stmts &
              prog == Prg ([
                            VarD (userT, userE);
                            VarD (dataT, dataE);
                            VarD (timeT, timeE);
                            VarD (requestT, requestE);
                            sendD
                            ],
                           stmts
                           ) &
              prog_evalo prog st &
              q == [c_u; c_d; c_t]
              })
  (fun q -> q#reify (List.prj_exn CopyCap.prj_exn))))

(* - complex tests *)

(* let deref_accesso id v p' = ocanren { *)
    (* p' == DerefP (AccessP (VarP v, id)) *)
  (* } *)

(* let access_deref_accesso id_ext id_int v p' = ocanren { *)
    (* p' == AccessP (DerefP (AccessP (VarP v, id_int)), id_ext) *)
  (* } *)

let access_deref_access_deref_accesso id_ext id_mid id_int v p' = ocanren {
    p' == AccessP (DerefP (AccessP (DerefP (AccessP (VarP v, id_int)), id_mid)), id_ext)
  }

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
                    WriteS (VarP 0));
                    ReadS (VarP 0))]
                   sendF &

              fresh sa_access0, sa_access1, sa_access2, sa_access3 in
              access_deref_accesso 0 1 0 sa_access0 &
              access_deref_accesso 1 1 0 sa_access1 &
              access_deref_access_deref_accesso 0 0 0 0 sa_access2 &
              access_deref_accesso 0 1 0 sa_access3 &
              seqo [WriteS (VarP 0));
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

(* rw versions *)

let rw_unitTo tp = ocanren {
    (* fresh r, w in *)
    tp == UnitT (Rd, AlwaysWr)
  }

let rw_user_utilsTo tp = ocanren {
    fresh x, y in
    rw_unitTo x &
    rw_unitTo y &
    tp == TupleT [x; y]
  }

let rw_user_infoTo tp = ocanren {
    fresh x, y, z in
    rw_unitTo x &
    rw_unitTo y &
    rw_unitTo z &
    tp == TupleT [x; y; z]
  }

let rw_versionTo tp = ocanren {
    fresh x, y, z in
    rw_unitTo x &
    rw_unitTo y &
    rw_unitTo z &
    tp == TupleT [x; y; z]
  }

let rw_utilsTo tp = ocanren {
    fresh x, y in
    rw_unitTo x &
    rw_unitTo y &
    tp == TupleT [x; y]
  }

let rw_dataTo tp = ocanren {
    rw_unitTo tp
  }

let rw_op_dateTo tp = ocanren {
    rw_unitTo tp
  }

let rw_userTo cu ci tp = ocanren {
    fresh utilsT, infoT in
    rw_user_infoTo infoT &
    rw_user_utilsTo utilsT &
    tp == TupleT [RefT (cu, utilsT) (* 0 utils *);
                  RefT (ci, infoT) (* 1 info *)]
  }

let rw_requestTo cus cv cut cd cus_u cus_i tp = ocanren {
    fresh userT, versionT, utilsT, dataT, op_dateT in
    rw_userTo cus_u cus_i userT &
    rw_versionTo versionT &
    rw_utilsTo utilsT &
    rw_dataTo dataT &
    rw_op_dateTo op_dateT &
    tp == TupleT [RefT (cus, userT) (* 0 user *);
                  RefT (cv, versionT) (* 1 version *);
                  RefT (cut, utilsT) (* 2 utils *);
                  RefT (cd, dataT) (* 3 data *);
                  op_dateT (* 4 operation_date *)]
  }
let rw_moded_requestTo cus cv cut cd cus_u cus_i tp = ocanren {
    fresh requestT in
    rw_requestTo cus cv cut cd cus_u cus_i requestT &
    tp == (Mode (In, NOut), requestT)
  }
let rw_boxed_moded_requestTo tp = ocanren {
    fresh cus, cv, cut, cd, cus_u, cus_i in
    rw_moded_requestTo cus cv cut cd cus_u cus_i tp
  }

(* any versions *)

let any_unitTo tp = ocanren {
    fresh r, w in
    tp == UnitT (r, w)
  }

let any_user_utilsTo tp = ocanren {
    fresh x, y in
    any_unitTo x &
    any_unitTo y &
    tp == TupleT [x; y]
  }

let any_user_infoTo tp = ocanren {
    fresh x, y, z in
    any_unitTo x &
    any_unitTo y &
    any_unitTo z &
    tp == TupleT [x; y; z]
  }

let any_versionTo tp = ocanren {
    fresh x, y, z in
    any_unitTo x &
    any_unitTo y &
    any_unitTo z &
    tp == TupleT [x; y; z]
  }

let any_utilsTo tp = ocanren {
    fresh x, y in
    any_unitTo x &
    any_unitTo y &
    tp == TupleT [x; y]
  }

let any_dataTo tp = ocanren {
    any_unitTo tp
  }

let any_op_dateTo tp = ocanren {
    any_unitTo tp
  }

let any_userTo cu ci tp = ocanren {
    fresh utilsT, infoT in
    any_user_infoTo infoT &
    any_user_utilsTo utilsT &
    tp == TupleT [RefT (cu, utilsT) (* 0 utils *);
                  RefT (ci, infoT) (* 1 info *)]
  }

let any_requestTo cus cv cut cd cus_u cus_i tp = ocanren {
    fresh userT, versionT, utilsT, dataT, op_dateT in
    any_userTo cus_u cus_i userT &
    any_versionTo versionT &
    any_utilsTo utilsT &
    any_dataTo dataT &
    any_op_dateTo op_dateT &
    tp == TupleT [RefT (cus, userT) (* 0 user *);
                  RefT (cv, versionT) (* 1 version *);
                  RefT (cut, utilsT) (* 2 utils *);
                  RefT (cd, dataT) (* 3 data *);
                  op_dateT (* 4 operation_date *)]
  }
let any_moded_requestTo cus cv cut cd cus_u cus_i tp = ocanren {
    fresh requestT in
    any_requestTo cus cv cut cd cus_u cus_i requestT &
    tp == (Mode (In, NOut), requestT)
  }
let any_boxed_moded_requestTo tp = ocanren {
    fresh cus, cv, cut, cd, cus_u, cus_i in
    any_moded_requestTo cus cv cut cd cus_u cus_i tp
  }

(* TODO: synt all modifiers, etc *)
let prog_synt_compl_test_send _ = show(answerCpCapList) (Stream.take (run q
  (fun q -> ocanren {
              fresh (* types *)
                    uT_r_aw,
                    user_utilsT, user_infoT,
                    userT, versionT, utilsT,
                    requestT,
                    (* moded_requestT, *)
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
                    prog,
                    (* synt *)
                    st in
              (* types *)
              rw_unitTo uT_r_aw &
              rw_user_utilsTo user_utilsT &
              rw_user_infoTo user_infoT &
              rw_userTo Cp Cp userT &
              rw_versionTo versionT &
              rw_utilsTo utilsT &
              rw_requestTo Cp Cp Cp Cp Cp Cp requestT &
              (* moded_requestTo moded_requestT & *)
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
                    ReadS (VarP 0)]
                   sendF &

              fresh sa_access0, sa_access1, sa_access2, sa_access3 in
              access_deref_accesso 0 1 0 sa_access0 &
              access_deref_accesso 1 1 0 sa_access1 &
              access_deref_access_deref_accesso 0 0 0 0 sa_access2 &
              access_deref_accesso 0 1 0 sa_access3 &
              seqo [WriteS (AccessP (VarP 0, 4));
                    CallS (VarP sendID, [PathE (VarP 0)]);
                    CallS (VarP get_version_idID, [PathE (VarP 0)]);
                    CallS (VarP updated_versionID, [PathE (VarP 0)]);
                    WriteS sa_access0;
                    WriteS sa_access1;
                    ChoiceS (
                      ReadS sa_access2,
                      ReadS sa_access3
                    )]
                   send_allF &

              fresh mrT_gvi, mrT_uv, mrT_s, mrT_sa in
              (* fresh gvi_c0, gvi_c1, gvi_c2, gvi_c3, gvi_c4, gvi_c5, mrT' in *)
              (* any_moded_requestTo gvi_c0 gvi_c1 gvi_c2 gvi_c3 gvi_c4 gvi_c5 mrT' & *)
              (* TODO *)
              any_moded_requestTo Cp Cp Cp Cp Cp Cp mrT_gvi &
              any_moded_requestTo Cp Cp Cp Cp Cp Cp mrT_uv &
              any_moded_requestTo Cp Cp Cp Cp Cp Cp mrT_s &
              any_moded_requestTo Cp Cp Cp Cp Cp Cp mrT_sa &

              q == [Cp] &
              (* [gvi_c0; gvi_c1; gvi_c2; gvi_c3; gvi_c4; gvi_c5] & *)

              prog == Prg ([
                VarD (user_utilsT, user_utilsE);
                VarD (user_infoT, user_infoE);
                VarD (userT, userE);
                VarD (versionT, versionE);
                VarD (utilsT, utilsE);
                VarD (uT_r_aw, UnitE); (* data *)
                VarD (requestT, requestE);
                (* FunD ([mrT'], get_version_idF); *)
                (* FunD ([mrT'], updated_versionF); *)
                (* FunD ([mrT'], sendF); *)
                (* FunD ([mrT'], send_allF) *)
                FunD ([mrT_gvi], get_version_idF);
                FunD ([mrT_uv], updated_versionF);
                FunD ([mrT_s], sendF);
                FunD ([mrT_sa], send_allF)
              ],
              (* SkipS *)
              CallS (VarP send_allID, [PathE (VarP requestID)])
              ) &
              prog_evalo prog st })
  (fun q -> q#reify (List.prj_exn CopyCap.prj_exn))))
