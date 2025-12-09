open OCanren

type data = int

type tag = Ref | ConstRef | Value
type stmt = Call of data * data list | Read of data | Write of data

type body = stmt list

type fun_decl = tag list * body

type prog = fun_decl list * body

(* --- interpreter --- *)

(*
init vals values: 0
write: ++value
read: print value with name
*)

module M = Map.Make (Int);;

let read_var env id = env.(id);;
let inc_var env id = env.(id) <- env.(id) + 1; env;;
let replace_var env id value = env.(id) <- value; env;;

let apply_env f_env args env =
  List.fold_left2 replace_var env args (Array.to_list f_env);;

let rec eval_stmt env prog stmt =
  match stmt with
    | Call (f_id, args) -> eval_fun env prog (List.nth prog f_id) args
    | Read id -> Printf.printf "var.%i = %i\n" id @@ read_var env id; env
    | Write id -> inc_var env id

and eval_body env prog body = List.fold_left (fun env stmt -> eval_stmt env prog stmt) env body

and eval_fun env prog decl args =
  match decl with (arg_tags, body) ->
  let f_env = Array.map (fun x -> read_var env x) @@ Array.of_list args in
  let f_env_result = eval_body f_env prog body in
  apply_env f_env_result args env;;

(* --- abstracted types --- *)

type 'a a_stmt = ACall of 'a * 'a list | ARead of 'a | AWrite of 'a
type 'stmt a_body = 'stmt list
type ('id, 'stmt) a_fun_decl = 'id list * 'stmt a_body
type ('fun_decl, 'body) a_prog = 'fun_decl list * 'body

(* --- logic types --- *)

type l_data = Std.Nat.logic
type l_tag = tag ilogic
type l_stmt  = l_data a_stmt ilogic
type l_body  = l_data a_stmt ilogic
type l_fun_decl = (l_data, l_stmt) a_fun_decl ilogic
type l_prog  = (l_fun_decl, l_body) a_prog ilogic

(* --- relational verifier --- *)

(* TODO *)

(* --- comments --- *)

(*
>> ref | const ref | copy:

-> write into the arg => != const ref

-> call function with ref => != const ref

-> read var right after function call (no write between) => != ref

-> call function on var right after function call (no write between) => != ref

// TODO: check that vvar used to read before write inside? <- probably could be assumed correct
// TODO: intruduce Unused tag ?

------

>> :ref | copy:
write argument in function & write after any function call => !ref
call function with arg ref that modifies & write after any function call => !ref

*)

(* TODO: example *)
(* module Tree = struct *)
  (* ocanren type 'a tree = Leaf | Node of 'a * 'a tree * 'a tree *)

  (* type inttree = GT.int tree [@@deriving gt ~options:{show}] *)
  (* A shortcut for "ground" tree we're going to work with in "functional" code *)
  (* type rtree = Std.Nat.ground tree [@@deriving gt ~options:{show}] *)

  (* Logic counterpart *)
  (* type ltree = Std.Nat.logic tree_logic [@@deriving gt ~options:{show}] *)

  (* let leaf    () : Std.Nat.injected tree_injected = inj Leaf *)
  (* let node a b c : Std.Nat.injected tree_injected = inj @@ Node (a,b,c) *)

  (* Injection *)
  (* let rec inj_tree : inttree -> Std.Nat.injected tree_injected = fun tree -> *)
     (* inj @@ GT.(gmap tree_fuly Std.nat inj_tree tree) *)

  (* Projection *)
  (* let rec prj_tree : rtree -> inttree = *)
    (* fun eta -> GT.(gmap tree_fuly) Std.Nat.to_int prj_tree eta *)

  (* let reify_tree : (Std.Nat.injected tree_injected, ltree) Reifier.t = *)
    (* tree_reify Std.Nat.reify *)

  (* let prj_exn_tree : (Std.Nat.injected tree_injected, inttree) Reifier.t = *)
    (* let rec tree_to_int x = GT.gmap tree_fuly Std.Nat.to_int (tree_to_int) x in *)
    (* Reifier.fmap tree_to_int (tree_prj_exn Std.Nat.prj_exn) *)
(* end *)
