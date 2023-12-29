type var = string
type constructor = string

type bop =
  | Add
  | Mult
  | Leq


(* [Var]   denotes the variable
   [Int]   denotes the inteager
   [Binop] denotes the binary operation expression
   [Let]   denotes the bind assciated with [Var]
   [If]    denotes the If expression*)
type expr =
  | Var of var
  | Int of int
  | Bool of bool
  | Binop of bop * expr * expr
  | Let of var * expr * expr
  | Rec of var * expr * expr
  | If of expr * expr * expr
  | Pair of expr * expr
  | Fst of expr
  | Snd of expr
  | Func of var * expr
  | Application of expr * expr
  | Variant of constructor * expr
  | Match of expr * (pattern * expr) list
and pattern = 
  | PInt of int
  | PBool of bool
  | PVar of var
  | PVariant of constructor * pattern (* | cons e *)
  | PPair of pattern * pattern (* | pair e1 * e2 *)
