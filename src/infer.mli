open Ast
open TypeAst

(** the constraint collected by collect function *)
type equation = Eq of typ * typ

(** function for printing lists of equations *)
(* val format_eqns     : Format.formatter -> equation list -> unit *)
(* val print_eqns      : equation list -> unit *)
(* val string_of_eqns  : equation list -> string *)

(** traverses the annotated expression and returns a list of equations(the constraints) that must be satisfied for e to typecheck *)
val collect : variant_spec list -> annotated_expr -> equation list

(** given an expression, return the type for that expression,
    failing if it can not be typed *)
val infer : variant_spec list -> expr -> string

