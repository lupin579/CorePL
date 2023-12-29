open Ast

(** a type variable like "a" ('a) *)
type talpha = string
(* a type name like "list" or "option" *)
type tname = string

(** the type of types *)
type typ =
  | TInt | TBool
    (** unit, int, bool, and string respectively *)
  | TAlpha of  talpha
    (** 'a would be represented as TAlpha "a" *)
  | TArrow of  typ * typ
    (** t1 -> t2 would be represented as TAlpha "a" *)
  | TStar  of  typ * typ
    (** t1 * t2 would be represented as TStar (t1, t2) *)
  | TVariant of typ list * tname
    (** 'a list would be represented as TVariant ([TAlpha "a"], "list") *)

(** we can see that constructor from Ast module is used *)
type variant_spec = {
  vars : talpha list;
  name : tname;
  constructors : (constructor * typ) list;
}


type annotated_expr =
  | AVar of typ * var
  | AApp of typ * annotated_expr * annotated_expr
  | AFun of typ * (var * typ) * annotated_expr
  | ALet of typ * (var * typ) * annotated_expr * annotated_expr
  | ALetRec of typ * (var * typ) * annotated_expr * annotated_expr
  | AInt of typ * int
  | ABool of typ * bool
  | APair of typ * annotated_expr * annotated_expr
  | ABinop of typ * bop * annotated_expr * annotated_expr
  | AIf of typ * annotated_expr * annotated_expr * annotated_expr
  | AVariant of typ * constructor * annotated_expr
  | AMatch of typ * annotated_expr * (annotated_pattern * annotated_expr) list
and annotated_pattern =
  | APInt of typ * int
  | APBool of typ * bool
  | APVar of typ * var
  | APPair of typ * annotated_pattern * annotated_pattern
  | APVariant of typ * constructor * annotated_pattern

val typeof : annotated_expr -> typ
val typeof_pat : annotated_pattern -> typ

val annotate : Ast.expr -> annotated_expr

val strip : annotated_expr -> Ast.expr
