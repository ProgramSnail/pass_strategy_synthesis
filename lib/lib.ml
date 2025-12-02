open OCanren

(* TODO: lift to logic domain *)
type tag = Ref | ConstRef | ShallowCopy | ConstShallowCopy | DeepCopy | NoneRef;;
(* MoveShallowCopy ? *)

type typ = UnitT | IntT | BoolT | RefT of typ | PairT of typ * typ;;
type mode = InM | OutM | InOutM;;
type arg = Arg of tag * mode * typ;;

type op = AddOp | SubOp | NotOp | LessOp | MoreOp | LessEqOp | MoreEqOp | EqOp | NotEqOp;;

type expr = IntE of int
          | BoolE of bool
          | VarE of string
          (* pair *)
          | PairE of expr * expr
          | FstE of expr
          | SndE of expr
          (* pointers *)
          | DerefE of expr
          | RefE of expr;;

type stmt = DeclS of string * typ
          | AssignS of string * expr (* TODO: rvalue exprs *)
          | SeqS of stmt * stmt
          | ExprS of expr
          | CallS of string * string list (* TODO: exprs?? *)
          | IfS of expr * stmt * stmt;;

type func_def = {
  f_args: arg list;
  f_body: stmt;
};;

type prog = {
  p_func: (string * func_def) list;
  p_code: stmt;
};;

(* ------ *)

type value = IntV of int
           | BoolV of bool
           | BoxV of string (* ref to box, lvalue *)
           | RefV of value
           | PairV of value * value
           | UnitV;;

module M = Map.Make (String);;

type func_env = func_def M.t;;
type 'a frame = {
  f_vars: 'a M.t;
};;
type 'a state = {
  s_func: func_env;
  s_frames: 'a frame list;
  (* s_value: 'a; *)
};;

let init_state prog = { s_func = prog.p_func |> List.to_seq |> M.of_seq;
                        s_frames = [];
                        (* s_value = UnitV; *)
                      };;

let find_func name state = M.find_opt name state.s_func

let find_frame_var name frame = M.find_opt name frame.f_vars;;
let rec find_frames_var name frames =
  match frames with
  | [] -> None
  | fr :: frs -> (match find_frame_var name fr with
                  | Some x -> Some x
                  | None -> find_frames_var name frs);;
let find_var name state = find_frames_var name state.s_frames;;

let add_var name value state =
  match state.s_frames with
  | [] -> failwith "No frames found"
  | fr :: frs -> { state with s_frames = {f_vars = M.add name value fr.f_vars} :: frs};;

let update_frame_var name value frame =
  if M.find_opt name frame.f_vars != None then Some {f_vars = M.add name value frame.f_vars} else None;;
let rec update_frames_var name value frames =
  match frames with
  | [] -> None
  | fr :: frs -> (match update_frame_var name value fr with
                  | Some fr -> Some (fr :: frs)
                  | None -> Option.map (fun frs -> fr :: frs) @@ update_frames_var name value frs);;
let update_var name value state =
  Option.map (fun frs -> {state with s_frames = frs}) @@
             update_frames_var name value state.s_frames ;;

let check_op_types expr state = ();;

(* TODO *)
(* let ( let* ) = Option.bind;; *)

(* TODO *)
(* TODO: handle refs in proper way *)
(* NOTE: exprs are pure and do not change state *)
let rec check_expr_types expr state =
  match expr with
  | IntE _ -> IntT
  | BoolE b -> BoolT
  | VarE name -> RefT (Option.get @@ find_var name state)
  (* pair *)
  | PairE (fst_e, snd_e) -> PairT (check_expr_types fst_e state, check_expr_types snd_e state)
  | FstE e ->
    (match check_expr_types e state with
     | PairT (t, _) -> t
     | _ -> failwith "Fst type error")
  | SndE e ->
    (match check_expr_types e state with
     | PairT (_, t) -> t
     | _ -> failwith "Snd type error")
  (* pointers *)
  | DerefE e ->
    (match check_expr_types e state with
     | RefT t -> t
     | _ -> failwith "Deref type eror")
  | RefE e -> RefT (check_expr_types e state);;

let expect_eq fst_val snd_val msg =
 if fst_val == snd_val then fst_val else failwith msg;;

let expect_neq fst_val snd_val msg =
 if fst_val != snd_val then fst_val else failwith msg;;

(* TODO *)
let rec check_stmt_types stmt (state : typ state) =
  match stmt with
  | DeclS (name, typ) -> add_var name typ state
  | AssignS (name, val_e) ->
    let val_t = check_expr_types val_e state in
    (match find_var name state with
     | Some t -> ignore @@ expect_eq t val_t "Can't assign value of the different type"
     | None -> failwith "Varible to assign is not found");
    state
  | SeqS (fst_e, snd_e) ->
    let state = check_stmt_types fst_e state in
    check_stmt_types snd_e state
  | ExprS e -> ignore @@ check_expr_types e state; state
  | CallS (name, args) ->
    let func = find_func name state in
    (* (match *) 
    (* ) *)
    failwith "Unimplemened"
  | IfS (cond_e, then_e, else_e) ->
    ignore @@ expect_eq (check_expr_types cond_e state) BoolT "If condition is not bool";
    failwith "Unimplemened"
    ;;

(* TODO *)
let parse str = ();;
(* TODO *)
let eval stmt state = ();;
