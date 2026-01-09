(* (,,) -< Pair.inj _ (Pair.inj _ _) *)

module Relational =
struct
  open GT
  open OCanren
  open OCanren.Std

  @type data_ground = Nat.ground with show, gmap
  @type data_logic = Nat.logic with show, gmap
  type data_injected = Nat.injected

  @type tag_ground = Ref | Value with show, gmap
  @type tag_logic = tag_ground logic with show, gmap
  type tag_injected = tag_ground ilogic

  @type ('d, 'dl) stmt_abs = Call of 'd * 'dl | Read of 'd | Write of 'd with show, gmap
  @type stmt_ground = (data_ground, data_ground List.ground) stmt_abs with show, gmap
  @type stmt_logic = (data_logic, data_logic List.logic) stmt_abs logic with show, gmap
  type stmt_injected = (data_injected, data_injected List.injected) stmt_abs ilogic

  @type body_ground = stmt_ground List.ground with show, gmap
  @type body_logic = stmt_logic List.logic with show, gmap
  type body_injected = stmt_injected List.injected

  @type fun_decl_ground = tag_ground List.ground * body_ground with show, gmap
  @type fun_decl_logic = (tag_logic List.logic * body_logic) logic with show, gmap
  type fun_decl_injected = (tag_injected List.injected * body_injected) ilogic

  @type prog_ground = fun_decl_ground List.ground * fun_decl_ground with show, gmap
  @type prog_logic = (fun_decl_logic List.logic * fun_decl_logic) logic with show, gmap
  type prog_injected = (fun_decl_injected List.injected * fun_decl_injected) ilogic

  @type 'd arg_abs = RValue | LValue of 'd with show, gmap
  @type arg_ground = data_ground arg_abs with show, gmap
  @type arg_logic = data_logic arg_abs logic with show, gmap
  type arg_injected = data_injected arg_abs ilogic

  @type value_ground = UnitV | BotV with show, gmap
  @type value_logic = value_ground logic with show, gmap
  type value_injected = value_ground ilogic

  (* ocanren type 'a lst = Nil | Cons of 'a * 'a lst *)
end
