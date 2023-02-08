(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

(*
        --------------------------------------
                    FREE VARIABLES
        --------------------------------------
*)

let rec freevars_ty t =
    match t with
    | TyName s -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

(*
        -------------------------------------
                    SUBSTITUTIONS
        -------------------------------------
*)

let rec apply_substitution_ty (t : ty) (s : subst) : ty =
    match t with
    | TyName _ -> t
    | TyVar tv ->

        let finder = List.tryFind(fun (tvs, _) -> tv = tvs) s

        match finder with
        | None -> t
        | Some(_, t) ->
            let ftv = freevars_ty t
            if not (Set.contains tv ftv) then t else type_error "Cannot apply substitution from %O to %O. Circularity not allowed" tv t

    | TyArrow(t1, t2) -> TyArrow(apply_substitution_ty t1 s, apply_substitution_ty t2 s)
    | TyTuple tl -> TyTuple(List.map (fun t -> apply_substitution_ty t s) tl)

let apply_substitution_scheme (Forall (tvs, ts)) (s: subst): scheme =
    let new_substitution = List.filter(fun (tv, _) -> not (Set.contains tv tvs)) s
    Forall(tvs, apply_substitution_ty ts new_substitution)

let apply_substitution_scheme_env (env: scheme env) (s: subst): scheme env =
    List.map (fun (e, sch) -> e, apply_substitution_scheme sch s) env

// function that compose two substitutions by construction (constrained_s2 @ s1)
let compose_subst (s2 : subst) (s1 : subst) : subst =

    // function that applies the constraint of domains' disjunction and apply substitution
    let apply_subs_constrained (tv2, t2) =

        let finder = List.tryFind(fun (tv1, _) -> tv1 = tv2) s1

        match finder with
        | None -> tv2, t2
        | Some (tv1, t1) -> 
            if t1 = t2 then tv2, apply_substitution_ty t2 s1 
            else type_error "Cannot compose substitution with the same TyVar mapping for different ty. (s2 has [%d -> %O] while s1 has [%d -> %O])" tv2 t2 tv1 t1
     
    (List.map apply_subs_constrained s2) @ s1

(*
        -----------------------------------
                    UNIFICATION
        -----------------------------------
*)

// unify: function taking two types and calculating a substitution that makes two types to be the same (Martelli - Montanari algorithm)
let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1, t2 with
    | TyName tc1, TyName tc2 -> if tc1 = tc2 then [] else type_error "Cannot unify type constructors %s and %s." tc1 tc2
    | TyVar tv, t -> List.singleton(tv,t) 
    | t, TyVar tv -> List.singleton(tv,t) // question for professor: can I do it in a single way with (TyVar tv, t)?
    | TyArrow (t1, t2), TyArrow (t3, t4) -> compose_subst (unify t1 t3) (unify t2 t4)
    | TyTuple tt1, TyTuple tt2 ->

        let isMinLen = List.length tt1 > 1 && List.length tt2 > 1
        let isEqLen = List.length tt1 = List.length tt2

        if isMinLen && isEqLen then List.fold (fun acc (t1,t2) -> compose_subst (unify t1 t2) acc) List.Empty (List.zip tt1 tt2)
        else
            if isMinLen = false then type_error "Cannot unify tuples. Tuples needs at least two ty." else type_error "Cannot unify tuples with different lengths."
            // question for professor Is isMinLen needed and how much do I have to describe errors' details?
    | _ -> type_error "Cannot unify types %O and %O" t1 t2

// basic environment: add builtin operators at will
//

let ty_env_gamma_0 = [
    // binary int operators
    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("*", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
    ("/", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
    ("%", TyArrow(TyInt, TyArrow(TyInt, TyInt)))
    (">", TyArrow(TyInt, TyArrow(TyInt, TyBool)))
    (">=", TyArrow(TyInt, TyArrow(TyInt, TyBool)))
    ("<", TyArrow(TyInt, TyArrow(TyInt, TyBool)))
    ("<=", TyArrow(TyInt, TyArrow(TyInt, TyBool)))
    ("=", TyArrow(TyInt, TyArrow(TyInt, TyBool))) // = or ==
    ("<>", TyArrow(TyInt, TyArrow(TyInt, TyBool)))

    // binary float operators
    ("+.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("-.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("*.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("/.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("<.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    (">.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    (">=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<>.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))

    // binary bool operators
    ("and", TyArrow (TyBool, TyArrow(TyBool, TyBool)))
    ("or", TyArrow (TyBool, TyArrow(TyBool, TyBool)))

    // unary operators
    ("not", TyArrow (TyBool, TyBool))
    ("neg", TyArrow (TyInt, TyInt))
    ("neg.", TyArrow (TyFloat, TyFloat))

]


let scheme_env_gamma_0 = List.map (fun (op, t) -> op, Forall (Set.empty, t)) ty_env_gamma_0


(*
        ----------------------------------------
                TYPE INFERENCE ALGORITHM
        ----------------------------------------
*)

let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Let (x, tyo, e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let tvs = freevars_ty t1 - freevars_scheme_env env
        let sch = Forall (tvs, t1)
        let t2, s2 = typeinfer_expr ((x, sch) :: env) e2
        t2, compose_subst s2 s1

    | _ -> failwithf "not implemented"


// type checker
//
    
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
