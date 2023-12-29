open Ast
open TypeAst

type equation = Eq of typ * typ

(* let format_eqns _ _ = *)
(*   failwith "TODO" *)

(* let print_eqns _ = *)
(*   failwith "TODO" *)

(* let string_of_eqns = *)
(*   failwith "TODO" *)

let rec print_typs t =
  match t with
  | TInt -> Format.sprintf "TInt"
  | TBool -> Format.sprintf "TBool"
  | TAlpha ta -> Format.sprintf "TAlpha %s" ta
  | TArrow (t1, t2) -> Format.sprintf "%s -> %s" (print_typs t1) (print_typs t2)
  | TVariant _ -> Format.sprintf "TVariant"
  | TStar (t1, t2) -> Format.sprintf "(%s , %s)" (print_typs t1) (print_typs t2)

let find vars v =
  List.assoc v vars

let newval = 
  let i = ref 0 in
  fun () -> i := !i + 1;Format.sprintf "i%02i" !i

let rec get_spec (specs : variant_spec list) cons =
  match specs with
  | [] -> failwith "the variant has this cons doesn't exist"
  | spec :: tl -> 
      try
        let _ = List.assoc cons spec.constructors in
        spec
      with
      | Not_found -> get_spec tl cons

let rec collect_pat_var p =
  match p with
  | APInt _ | APBool _    -> []
  | APVar (t', tn)        -> [(tn, t')]
  | APPair (_, p1, p2)    -> (collect_pat_var p1) @ (collect_pat_var p2)
  | APVariant (_, _, p') -> collect_pat_var p'

let rec collect_expr (specs : variant_spec list) vars (e : annotated_expr)
                 : equation list =
  match e with
  | AVar (t, v) -> [Eq (t, find vars v)]
  | AApp (t, e1, e2) -> collect_app specs vars t e1 e2
  | AFun (t, (v, t'), e) -> collect_fun specs vars t (v, t') e
  | ALet (t, (v, t'), e1, e2) -> collect_let specs vars t (v, t') e1 e2 
  | ALetRec (t, (v, t'), e1, e2) -> collect_rec specs vars t (v, t') e1 e2
  | AInt (t, _) -> [Eq (t, TInt)]
  | ABool (t, _) -> [Eq (t, TBool)]
  | APair (t, e1, e2) -> collect_pair specs vars t e1 e2
  | ABinop (t, op, e1, e2) -> collect_binop specs vars t op e1 e2
  | AIf (t, e1, e2, e3) -> collect_if specs vars t e1 e2 e3
  | AVariant (t, cons, e) -> collect_variant specs vars t cons e 
  | AMatch (t, e, pat_list) -> collect_match specs vars t e pat_list

and collect_app specs vars t e1 e2 =
  let ft = typeof e1 in
  let at = typeof e2 in
  Eq (ft, TArrow (at, t)) :: collect_expr specs vars e2 @ collect_expr specs vars e1

(* TODO omit the [Eq (t', newval ())] *)
and collect_fun specs vars t (v, t') e =
  Eq (t, TArrow (t', typeof e)) :: (collect_expr specs ((v, t')::vars) e)

(* TODO add a new collection for e1 which is not exist in github *)
and collect_let specs vars t (v, t') e1 e2 =
  Eq (t, typeof e2) :: Eq (t', typeof e1) ::
    collect_expr specs vars e1 @ collect_expr specs ((v, t')::vars) e2

and collect_rec specs vars t (v, t') e1 e2 =
  let eqn1 = collect_expr specs ((v, t')::vars) e1 in
  let eqn2 = collect_expr specs ((v, t')::vars) e2 in
  Eq (t, typeof e2) :: Eq (t', typeof e1) :: eqn1 @ eqn2

and collect_pair specs vars t e1 e2 =
  Eq (t, TStar (typeof e1, typeof e2)) :: collect_expr specs vars e1 @ collect_expr specs vars e2

and collect_binop specs vars t op e1 e2 = 
  match op with
  | Add | Mult -> Eq (t, TInt) :: Eq (typeof e1, TInt) :: Eq (typeof e2, TInt) ::
    collect_expr specs vars e1 @ collect_expr specs vars e2
  | Leq -> Eq (t, TBool) :: Eq (typeof e1, typeof e2) :: collect_expr specs vars e1 @ collect_expr specs vars e2 

and collect_if specs vars t e1 e2 e3 =
  Eq (typeof e1, TBool) :: Eq (t, typeof e2) :: Eq (t, typeof e3) ::
    collect_expr specs vars e1 @ collect_expr specs vars e2 @ collect_expr specs vars e3

and collect_variant specs vars t cons e =
  match specs with
  | [] -> failwith "not found that variant type"
  | spec :: tl -> 
      try
        let vt = List.assoc cons spec.constructors in
        let se = collect_expr specs vars e in
        let typ_list = List.map (fun _ -> TAlpha (newval ())) spec.vars in 
        Eq (t, TVariant (typ_list, spec.name)) :: Eq (typeof e, vt) :: se
      with
      | Not_found -> collect_variant tl vars t cons e

and collect_match specs vars t e pat_lst =
  match pat_lst with
  | [] -> []
  | (p, e') :: tl -> Eq(typeof e', t) :: Eq(typeof e, typeof_pat p) ::
                     (collect_case specs vars (p, e')) @ 
                     collect_match specs vars t e tl

and collect_case specs vars (p, e') =
  match p with
  | APInt (t', _)         -> Eq(t', TInt) :: collect_expr specs vars e'
  | APBool (t', _)        -> Eq(t', TBool) :: collect_expr specs vars e'
  | APVar (t', tn)        -> collect_expr specs ((tn, t') :: vars) e'
  | APPair (t', p1, p2)   -> Eq(t', TStar (typeof_pat p1, typeof_pat p2)) ::
                             collect_pat specs p1 @
                             collect_pat specs p2 @
                             collect_expr specs ((collect_pat_var p)@vars) e'
  | APVariant (t', cons, p')->let spec = get_spec specs cons in
                              let typ_list = List.map (fun _ -> TAlpha (newval ())) spec.vars in
                              let tn = spec.name in
                              Eq(typeof_pat p', List.assoc cons spec.constructors) ::
                              Eq(t', TVariant (typ_list, tn)) ::
                              collect_pat specs p' @  
                              collect_expr specs ((collect_pat_var p)@vars) e'

and collect_pat specs p =
  match p with
  | APInt (t, _) -> [Eq(TInt, t)]
  | APBool (t, _) -> [Eq(TBool, t)]
  | APVar _ -> []
  | APPair (t, p1, p2) -> Eq(t, TStar (typeof_pat p1, typeof_pat p2)) :: collect_pat specs p1 @ collect_pat specs p2
  | APVariant (t, cons, p') -> let spec = get_spec specs cons in
                               let lis = List.map (fun _ -> TAlpha (newval ())) spec.vars in
                               let tn = spec.name in
                               let cons_typ = List.assoc cons spec.constructors in
                               Eq(t, TVariant (lis, tn)) :: 
                               Eq(typeof_pat p', cons_typ) ::
                               collect_pat specs p'

let collect specs e =
  collect_expr specs [] e

let rec subst_typ (x, t) old_t =
  match old_t with
  | TInt | TBool         -> old_t
  | TAlpha n when n = x  -> t
  | TAlpha _             -> old_t
  | TStar (l, r)         -> TStar (subst_typ (x, t) l,subst_typ (x, t) r)
  | TArrow (a, r)        -> TArrow (subst_typ (x, t) a, subst_typ (x, t) r)
  | TVariant (l, tn)     -> TVariant (List.map (subst_typ (x, t)) l, tn)
  (* | _ -> failwith "subst_typ error" *)

let rec subst_eqns (x, t) eqns =
  match eqns with
  | [] -> []
  | Eq(l, r) :: tl -> Eq(subst_typ (x, t) l, subst_typ (x, t) r) :: subst_eqns (x, t) tl

let rec occurs_in x t =
  match t with
  | TInt | TBool -> false
  | TAlpha n when x = n -> true
  | TAlpha _ -> false
  | TStar (l, r) -> occurs_in x l || occurs_in x r
  | TArrow (a, r) -> occurs_in x a || occurs_in x r
  | TVariant (l, _) -> List.fold_left (fun b t -> b || occurs_in x t) false l
  (* | t' -> failwith (print_typs t') *)

let rec unify eqns =
  match eqns with
  | [] -> []
  | Eq (t1, t2) :: tl when t1 = t2 -> unify tl
  | Eq (TAlpha x, t) :: tl
  | Eq (t, TAlpha x) :: tl 
    -> if occurs_in x t
       then failwith "circular type constraint is forbidden"
       else (x, t) :: unify (subst_eqns (x, t) tl)
  | Eq (TArrow (l, r), TArrow (l', r')) :: tl 
  | Eq (TStar (l, r), TStar (l', r')) :: tl
    -> unify (Eq (l, l') :: Eq (r, r') :: tl)
  | Eq (TVariant (lis, cons), TVariant (lis', cons')) :: tl
    when cons = cons' -> 
      unify ((List.map2 (fun t t' -> Eq (t, t')) lis lis') @ tl)
  | _ -> failwith "unify catch-all section error"

let rec subst_expr subt ae =
  match ae with
  | AInt (t, int) -> AInt (subst_typ subt t, int)
  | ABool (t, bool) -> ABool (subst_typ subt t, bool)
  | AIf (t, e1, e2, e3) -> AIf (subst_typ subt t, subst_expr subt e1, subst_expr subt e2, subst_expr subt e3)
  | AFun (t, (x, tx), e) -> AFun (subst_typ subt t, (x, subst_typ subt tx), subst_expr subt e)
  | AApp (t, e1, e2) -> AApp (subst_typ subt t, subst_expr subt e1, subst_expr subt e2)
  | ALet (t, (x, tx), e1, e2) -> ALet (subst_typ subt t, (x, subst_typ subt tx), subst_expr subt e1, subst_expr subt e2)
  | ALetRec (t, (x, tx), e1, e2) -> ALetRec (subst_typ subt t, (x, subst_typ subt tx), subst_expr subt e1, subst_expr subt e2)
  | AVar (t, v) -> AVar (subst_typ subt t, v)
  | APair (t, e1, e2) -> APair (subst_typ subt t, subst_expr subt e1, subst_expr subt e2)
  | ABinop (t, op, e1, e2) -> ABinop (subst_typ subt t, op, subst_expr subt e1, subst_expr subt e2)
  | AVariant (t, cons, e) -> AVariant (subst_typ subt t, cons, subst_expr subt e)
  | AMatch (t, e, l) -> AMatch (subst_typ subt t, subst_expr subt e, subst_pat_list subt l)

and subst_pat_list subt l =
  match l with
  | [] -> []
  | (p, e) :: tl -> (subst_pat subt p, subst_expr subt e) :: subst_pat_list subt tl

and subst_pat subt p =
  match p with
  | APInt (t, i) -> APInt (subst_typ subt t, i)
  | APBool (t, b) -> APBool (subst_typ subt t, b)
  | APVar (t, v) -> APVar (subst_typ subt t, v)
  | APPair (t, p1, p2) -> APPair (subst_typ subt t, subst_pat subt p1, subst_pat subt p2)
  | APVariant (t, cons, p') -> APVariant (subst_typ subt t, cons, subst_pat subt p')

let infer defs e =
  let annotated_expr = annotate e in
  let eqns = collect defs annotated_expr in
  let substitutions = unify eqns in
  let new_ae = List.fold_left (fun ae s -> subst_expr s ae) annotated_expr substitutions in
  print_typs (typeof new_ae)
