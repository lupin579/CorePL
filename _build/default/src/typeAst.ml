open Ast

(** ast 
     | (annotation)
     V
    annotated_ast 
     | (collect)
     V
    equations
     | (unification)
     V
    substitution(solution)
     | (apply solution on annotated_ast)
     V
    newtyped_annotated_ast
     | (simplification)
     V
    simplified *)

type talpha = string
type tname = string
type typ =
  | TInt | TBool
  | TAlpha of talpha
  | TArrow of typ * typ
  | TStar of typ * typ
  | TVariant of typ list * tname(** e.g. type 'a 'b either = | Left of 'a | Right of 'b *)

(** a record for variant type *)
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

(* the first problem is how(use which name) to annotate nodes of ast *)
(* TODO for [v] in [Let] : why don't we use ann_expr v (cuz the var here is just a [type:string], doesn't have constructor [Var](to be the [type:expr]), so ann_expr can't reconognize it) *)
(* TODO the other half of the former problem : why we use the reversed anonotation of [v] compared with [AVar] in ALet *)
let annotate e =
  let nextval = ref 0 in
  let newval () = nextval := !nextval + 1; 
  TAlpha (Format.sprintf "i%02i" !nextval) in
  
  let rec ann_expr = function
    | Var v                    -> AVar     (newval(), v)
    | Int i                    -> AInt     (newval(), i)
    | Bool b                   -> ABool    (newval(), b)
    | Binop (op, e1, e2)       -> ABinop   (newval(), op, (ann_expr e1), (ann_expr e2))
    | Let (v, e1, e2)          -> ALet     (newval(), (v, newval()), (ann_expr e1), (ann_expr e2))  
    | Rec (v, e1, e2)          -> ALetRec  (newval(), (v, newval()), (ann_expr e1), (ann_expr e2))
    | If (e1, e2, e3)          -> AIf      (newval(), (ann_expr e1), (ann_expr e2), (ann_expr e3))
    | Pair (e1, e2)            -> APair    (newval(), (ann_expr e1), (ann_expr e2))
    | Func (v, e)              -> AFun     (newval(), (v, newval()), (ann_expr e))
    | Application (e1, e2)     -> AApp     (newval(), (ann_expr e1), (ann_expr e2))
    | Variant (cons, e)        -> AVariant (newval(), cons, ann_expr e) 
    | Match (e, ls)            -> AMatch   (newval(), (ann_expr e), List.map (fun (p, e) -> (ann_pattern p, ann_expr e)) ls) 
    | Fst _ | Snd _ -> failwith "todo"
  and ann_pattern = function
    | PInt i                  -> APInt    (newval(), i)
    | PBool b                 -> APBool   (newval(), b)
    | PVar v                  -> APVar    (newval(), v) 
    | PVariant (tn, p)        -> APVariant(newval(), tn, (ann_pattern p)) 
    | PPair (p1, p2)          -> APPair   (newval(), (ann_pattern p1), (ann_pattern p2))
  in ann_expr e 

let rec strip = function
  | AVar     (_,x)        -> Var x
  | AApp     (_,e1,e2)    -> Application (strip e1, strip e2)
  | AFun     (_,x,e)      -> Func (fst x, strip e)
  | ALet     (_,x,e1,e2)  -> Let (fst x, strip e1, strip e2)
  | ALetRec  (_,x,e1,e2)  -> Rec (fst x, strip e1, strip e2)
  | AInt     (_,n)        -> Int n
  | ABool    (_,b)        -> Bool b
  | AVariant (_,c,e)      -> Variant (c,strip e)
  | APair    (_,e1,e2)    -> Pair (strip e1, strip e2)
  | ABinop   (_,op,e1,e2) -> Binop (op, strip e1, strip e2)
  | AIf      (_,e1,e2,e3) -> If (strip e1, strip e2, strip e3)
  | AMatch   (_,e,ps)     -> let strip_case (p,e) = (strip_pattern p, strip e) in
                             Match (strip e, List.map strip_case ps)
and strip_pattern = function
  | APInt  (_,n)      -> PInt n
  | APBool (_,b)      -> PBool b
  | APVar (_,x)       -> PVar x
  | APVariant (_,c,p) -> PVariant (c,strip_pattern p)
  | APPair (_,p1,p2)  -> PPair (strip_pattern p1, strip_pattern p2)

let typeof = function
  | AVar (t,_) | AApp (t,_,_) | AFun (t,_,_) | ALet (t,_,_,_)
  | ALetRec (t,_,_,_) | AInt (t,_) | ABool (t,_)
  | AVariant (t,_,_) | APair (t,_,_) | ABinop (t,_,_,_) | AIf (t,_,_,_)
  | AMatch (t,_,_)

  -> t

let typeof_pat = function
  | APInt (t,_) | APBool (t,_) | APVar (t,_)
  | APVariant (t,_,_) | APPair (t,_,_)
  -> t
