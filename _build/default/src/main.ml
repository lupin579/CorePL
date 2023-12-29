open Ast(* module name must be capitalized *)

module Env = Map.Make(String)

let empty_env = Env.empty

type var = string

type env = value Env.t

and value =
  | VInt of int
  | VBool of bool
  | VClosure of var * expr * env
  | VPair of value * value
  | VVariant of constructor * value
  | VDummy of value ref
  | VError of string

(* [parse s] parses [s] into an AST. *)
let parse (s : string) : expr =
  let lexbuf = Lexing.from_string s in
  let ast = Parser.prog Lexer.read lexbuf in
  ast

let unbound_var_err = "variable is unbound"
let bop_err = "binary operation error"
let if_err = "wrong type for the if evaluation"
let func_err = "not a function"
let val_err = "not a value"
let fst_err = "not a pair"
let snd_err = "not a pair"
let match_err = "match error"
let pmatch_err = "uncompatible cons or type"
let app_rec_err = "error occured in dereference of VDummy"

let rec pmatch pat v = 
  match pat, v with
  | (PInt n1, VInt n2) -> if n1 = n2 then Some [] else None
  | (PBool b1, VBool b2) -> if b1 = b2 then Some [] else None
  | (PVar name, _) -> Some [(name, v)]
  | (PVariant (p_cons, pat'), VVariant (v_cons, v')) -> if p_cons = v_cons then pmatch pat' v' else None
  | (PPair (p1, p2), VPair (v1, v2)) ->
      begin
      match pmatch p1 v1, pmatch p2 v2 with
      | Some env1, Some env2 -> Some (env1 @ env2)
      | _ -> None
      end
  | _ -> failwith pmatch_err

let rec eval (env: env) (e : expr) : value = 
  match e with
  | Int i -> VInt i
  | Bool b -> VBool b
  | Var x -> eval_var env x
  | Binop (bop, e1, e2) -> eval_bop env bop e1 e2
  | Let (x, e1, e2) -> eval_let env x e1 e2
  | Rec (x, e1, e2) -> eval_letrec env x e1 e2
  | If (be, e1, e2) -> eval_if env be e1 e2
  | Func (x, e1) -> VClosure (x, e1, env)
  | Application (e1, e2) -> eval_app env e1 e2 
  | Pair (e1, e2) -> VPair (eval env e1, eval env e2)
  | Fst e -> eval_fst env e
  | Snd e -> eval_snd env e 
  | Variant (cons, e) -> eval_variant env cons e
  | Match (e, lis) -> eval_match env e lis
 
and eval_var env x =
  try Env.find x env
  with Not_found -> failwith unbound_var_err

(* match e with
   | PInt x -> e'  *)
and eval_match env e lis = 
  match lis with
  | (pat, e') :: t ->
      begin
      match pmatch pat (eval env e) with
      | Some extra_env -> 
          let nenv = Env.merge choose (Env.of_list extra_env) env
          in eval nenv e'
      | None -> eval_match env e t
      end
  | _ -> failwith match_err

and choose _ _ v2 = v2

and eval_variant env cons e = 
  let e' = eval env e
  in VVariant (cons, e')

(* output value with type value instead of type expr like before(in the simPL) *)
and eval_bop env bop e1 e2 = match bop, (eval env e1), (eval env e2) with
  | Add, VInt v1, VInt v2 -> VInt (v1 + v2)
  | Mult, VInt v1, VInt v2 -> VInt (v1 + v2)
  | Leq, VInt v1, VInt v2 -> VBool (v1 <= v2)
  | _ -> failwith "assd"

(* and eval_let env x e1 e2 = eval (env.add x (eval env e1)) e2 *)
and eval_let env x e1 e2 =
  let v = eval env e1 in 
  let env' = Env.add x v env in 
  eval env' e2

(* implement the backpatching with ref(mutable variables) to complete this recursive let *)
and eval_letrec env f e1 e2 = 
  let mut = ref (VError "cannot use that on the right-hand side of let rec") in
  let v = eval (Env.add f (VDummy mut) env) e1 in(* eval function to VClosure *)
  let env' = Env.add f v env in(* bind name to closure and add it to environment *)
  mut := v;eval env' e2
(* letrec f = 
   fun x -> if x == 1 then 1 else x + (f x-1) 
   in f 10 
   v = VClosure x e (env, (f:VDummy ref (VError)))
   env' = (env, VClosure x e (env, (f:VDummy ref (VError))))
   env' = (env, VClosure x e (env, (f:VDummy ref v)))

   *)

and  eval_if env be e1 e2 = match (eval env be) with
  | VBool true -> eval env e1
  | VBool false -> eval env e2
  | _ -> failwith if_err

and eval_app env e1 e2 =
  match eval env e1 with
  | VClosure (x, e, env') ->
      begin
      let env'' = Env.add x (eval env e2) env' in
      eval env'' e
      end
  | VDummy v -> 
      begin
      match !v with
      | VClosure (x, e, env') ->
        begin
        let env'' = Env.add x (eval env e2) env' in
        eval env'' e
        end
      | VError s -> VError s
      | _ -> failwith app_rec_err
      end
  | _ -> failwith func_err

and eval_fst env e =
      match eval env e with
      | VPair (v1, _) -> v1
      | _ -> failwith fst_err

and eval_snd env e =
      match eval env e with
      | VPair (_, v2) -> v2
      | _ -> failwith snd_err 

let string_of_val = function
  | VInt i -> string_of_int i
  | VBool b -> string_of_bool b 
  | _ -> failwith val_err

let rec fact x = if x = 1 then 1 else x * (fact x)
(* [interp s] interprets [s] by lexing and parsing it,
   evaluating it, and converting the result to a string. *)
let interp (s : string) : string =
  s |> parse |> eval empty_env |> string_of_val(* take a sequence of characters, parse it to AST, evaluate it to a value, finally convert it back to a string  *)









