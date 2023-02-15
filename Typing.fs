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
           FREE VARIABLES (TY, SCHEME, ENV)
        --------------------------------------
*)

// freevers_ty:
// it calculates the free type variables occurring on a type t
let rec freevars_ty t =
    match t with
    | TyName _ -> Set.empty
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyVar tv -> Set.singleton tv
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

// freevers_scheme:
// it calculates the free type variables occurring on a type scheme sch
let freevars_scheme (Forall (tvs, t)) = Set.difference (freevars_ty t) tvs 

// freevers_scheme_env:
// it calculates the free type variables occurring on an environment env
let freevars_scheme_env env =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

(*
        -------------------------------------
                    PRETTY PRINT
        -------------------------------------
*)

let rec pretty_ty_tvs mappings t =
    match t with
    | TyName s -> s
    | TyArrow (TyArrow(t1, t2), t3) -> sprintf "(%s -> %s) -> %s" (pretty_ty_tvs mappings t1) (pretty_ty_tvs mappings t2) (pretty_ty_tvs mappings t3)
    | TyArrow (t1, t2) -> sprintf "%s -> %s" (pretty_ty_tvs mappings t1) (pretty_ty_tvs mappings t2)
    | TyVar n -> 
        let _, pretty_tv = List.find (fun (ftv, _) -> ftv = n) mappings
        sprintf "'%c" pretty_tv
    | TyTuple ts -> sprintf "(%s)" (pretty_tupled (pretty_ty_tvs mappings) ts)

let pretty_ty_infer t =

    let ftvs = freevars_ty t

    if Set.count ftvs > 0 
        then
            let alphabet = List.truncate (Set.count ftvs) ['a' .. 'z']
            pretty_ty_tvs (List.zip (Set.toList ftvs) alphabet) t
        else
            Ast.pretty_ty t

(*
        --------------------------------------
                    GENERALIZATION
        --------------------------------------
*)

// generalize_to_scheme:
// it converts a type to a type scheme -> it calculates which type variables are polymorphic
let generalize_to_scheme (t: ty) (env: scheme env) : scheme =
    let alpha_vec = Set.difference (freevars_ty t) (freevars_scheme_env env)
    Forall(alpha_vec, t)

(*
        ------------------------------------
                  REFRESH OF TYVAR
        ------------------------------------
*) 

let mutable tyVarCounter = 0

// make_fresh_tyvar:
// it allows to get a fresh type variable
let make_fresh_tyvar () : ty =
    tyVarCounter <- tyVarCounter + 1
    TyVar tyVarCounter
    

(*
        -------------------------------------
                    SUBSTITUTIONS
        -------------------------------------
*)

// apply_substitution_ty:
// it applies a substitution to a type
let rec apply_substitution_ty (t : ty) (s : subst) : ty =
    match t with
    | TyName _ -> t
    | TyVar tv ->

        let finder = List.tryFind(fun (tvs, _) -> tv = tvs) s

        match finder with
        | None -> t
        | Some(_, t) ->

            // circularity check:
            // it calculates alpha occurring on t and checks if the matching type variable is in the set alpha
            let alpha_vec = freevars_ty t

            if not (Set.contains tv alpha_vec) then t
            else type_error "Cannot apply substitution from %O to %O. Circularity not allowed" tv t

    | TyArrow(t1, t2) -> TyArrow(apply_substitution_ty t1 s, apply_substitution_ty t2 s)
    | TyTuple tl -> TyTuple(List.map (fun t -> apply_substitution_ty t s) tl)

// apply_substitution_scheme:
// it applies a substitution to a type scheme
let apply_substitution_scheme (Forall (alpha_vec, t)) (s: subst): scheme =
    let new_subst = List.filter(fun (tv, _) -> not (Set.contains tv alpha_vec)) s
    Forall(alpha_vec, apply_substitution_ty t new_subst)

// apply_substitution_scheme_env:
// it applies a substitution to an environment
let apply_substitution_scheme_env (env: scheme env) (s: subst): scheme env =
    List.map (fun (e, sch) -> e, apply_substitution_scheme sch s) env

// compose_subst:
// it composes two substitutions by construction (constrained_s2 @ s1)
let compose_subst (s2 : subst) (s1 : subst) : subst =

    // it applies the constraint of domains' disjunction for a single element of substitution
    let apply_subs_constrained (tv2, t2) =

        // looking for a substitution with the same domain in s1
        let finder = List.tryFind(fun (tv1, _) -> tv1 = tv2) s1

        match finder with
        | None -> tv2, t2 // -> domains disjoint
        | Some (tv1, t1) -> // -> domains not disjoint -> t1 must be t2 in order to have same substitution
            if t1 = t2 then tv2, apply_substitution_ty t2 s1 
            else type_error "Cannot compose substitution with the same TyVar mapping for different ty. (s2 has [%d -> %O] while s1 has [%d -> %O])" tv2 t2 tv1 t1
     
     // need a map in order to apply constraints in all elements of substitution
    (List.map apply_subs_constrained s2) @ s1

(*
        -------------------------------------
                    INSTANTIATION
        -------------------------------------
*)

// instantiate:
// it converts a type scheme to a type -> it refreshes its polymorphic type variables
let instantiate_to_ty (Forall(tvs, ts)): ty =
    let update = Set.fold (fun acc tv -> (tv, make_fresh_tyvar ()) :: acc) List.empty tvs
    apply_substitution_ty ts update

(*
        -----------------------------------
                    UNIFICATION
        -----------------------------------
*)

let rec unify (t1 : ty) (t2 : ty) : subst =
    match t1, t2 with
    | TyName tn1, TyName tn2 -> if tn1 = tn2 then List.empty else type_error "Cannot unify type constructors %s and %s." tn1 tn2
    | (TyVar tv, t | t, TyVar tv) -> List.singleton(tv,t) 
    | TyArrow (t1, t2), TyArrow (t3, t4) -> compose_subst (unify t1 t3) (unify t2 t4)
    | TyTuple tt1, TyTuple tt2 ->

        assert (List.length tt1 > 1 && List.length tt2 > 1) // if false -> interromption runtime with unexpected_error message (it should't happen in the program)
        let isEqLen = List.length tt1 = List.length tt2

        if isEqLen then List.fold (fun acc (t1,t2) -> compose_subst (unify t1 t2) acc) List.empty (List.zip tt1 tt2)
        else
           type_error "Cannot unify tuples with different lengths."
    | _ -> type_error "Cannot unify types %O and %O" t1 t2

// basic environment: add builtin operators at will
//

let ty_env_gamma_0 = [

    // binary artimetic operators

    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
    ("*", TyArrow (TyInt, TyArrow(TyInt, TyInt)))
    ("/", TyArrow (TyInt, TyArrow(TyInt, TyInt)))
    ("%", TyArrow (TyInt, TyArrow(TyInt, TyInt)))

    ("+.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("-.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("*.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("/.", TyArrow (TyFloat, TyArrow (TyFloat, TyFloat)))
    ("%.", TyArrow (TyFloat, TyArrow(TyFloat, TyFloat)))

    // binary float operators

    (">", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    (">=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("<", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("<=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("=", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("<>", TyArrow (TyInt, TyArrow(TyInt, TyBool)))
    ("%", TyArrow (TyInt, TyArrow(TyInt, TyBool)))

    (">.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    (">=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("=.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("<>.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))
    ("%.", TyArrow (TyFloat, TyArrow(TyFloat, TyBool)))

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
    | Lit (LInt _) -> TyInt, List.empty
    | Lit (LBool _) -> TyBool, List.empty
    | Lit (LFloat _) -> TyFloat, List.empty 
    | Lit (LString _) -> TyString, List.empty
    | Lit (LChar _) -> TyChar, List.empty 
    | Lit LUnit -> TyUnit, List.empty

    | Var x ->

        let finder = List.tryFind (fun (y,_) -> y = x) env

        match finder with
        | None -> type_error "Identifier %s not definined in the environment" x
        | Some (_,sch) -> instantiate_to_ty sch, List.empty

    | Lambda (x, tyo, e) ->

        let alpha = make_fresh_tyvar ()
        let sch = Forall(Set.empty, alpha)

        let t2, s1 = typeinfer_expr ((x, sch) :: env) e

        let t1 = apply_substitution_ty alpha s1

        let s2 = match tyo with
                 | None -> List.empty
                 | Some t -> unify t1 t
       

        TyArrow(apply_substitution_ty t1 s2, t2), compose_subst s2 s1

    | App (e1, e2) ->
        let t1, s1 = typeinfer_expr env e1
        let t2, s2 = typeinfer_expr (apply_substitution_scheme_env env s1) e2

        let s3 = compose_subst s2 s1

        let alpha_freshed = make_fresh_tyvar ()

        let s4 = unify (TyArrow(apply_substitution_ty t2 s3, alpha_freshed)) (apply_substitution_ty t1 s3)

        apply_substitution_ty alpha_freshed s4, compose_subst s4 s3

    | Tuple tl -> 
        let add_tuple (ts, s) exp = 
            let t_i, s_i = typeinfer_expr (apply_substitution_scheme_env env s) exp
            ts @ List.singleton (apply_substitution_ty t_i s_i), compose_subst s_i s

        let ts, s = List.fold add_tuple (List.empty, List.empty) tl

        TyTuple ts, s

    | Let (x, tyo, e1, e2) ->

        let t1, s1 = typeinfer_expr env e1

        let s2 = match tyo with
                 | None -> List.empty
                 | Some t -> unify t1 t

        let s3 = compose_subst s2 s1

        let sch = generalize_to_scheme t1 (apply_substitution_scheme_env env s3)

        let t2, s4 = typeinfer_expr ((x, sch) :: apply_substitution_scheme_env env s3) e2

        let s5 = compose_subst s4 s3

        apply_substitution_ty t2 s5, s5


    | LetRec (f, tyo, e1, e2) ->
        
        let alpha = make_fresh_tyvar ()
        let f_sch = Forall(Set.empty, alpha)

        let t1, s1 = typeinfer_expr ((f, f_sch) :: env) e1

        let sch_1 = generalize_to_scheme t1 (apply_substitution_scheme_env env s1)

        let s2 = match tyo with
                 | None -> List.empty
                 | Some t -> unify t1 t

        let s3 = compose_subst s2 s1

        let t2, s4 = typeinfer_expr ((f, sch_1) :: (apply_substitution_scheme_env env s3)) e2

        let s5 = compose_subst s4 s3

        apply_substitution_ty t2 s5, s5
        
    
    | IfThenElse (e1, e2, e3o) -> 

        let t1, s1 = typeinfer_expr env e1

        let s2 = unify t1 TyBool

        let s3 = compose_subst s2 s1

        let t2, s4 = typeinfer_expr (apply_substitution_scheme_env env s3) e2
        
        let s5 = compose_subst s4 s3

        match e3o with 
        | None ->
            let s6 = unify t2 TyUnit

            t2, compose_subst s6 s5

        | Some e3 ->
            let t3, s6 = typeinfer_expr (apply_substitution_scheme_env env s5) e3

            let s7 = compose_subst s6 s5

            let s8 = unify (apply_substitution_ty t2 s7) (apply_substitution_ty t3 s7)

            let s9 = compose_subst s8 s7

            apply_substitution_ty t2 s8, s9

    | BinOp (e1, op, e2) ->
        if List.contains op (List.map (fun (str, _) -> str) scheme_env_gamma_0)
            then  
                typeinfer_expr env (App (App (Var op, e1), e2))
            else 
                unexpected_error "typeinfer_expr: unsupported binary operator (%s)" op

    | UnOp (op, e) ->
        if List.contains op (List.map (fun (str, _) -> str) scheme_env_gamma_0)
            then  
                typeinfer_expr env (App (Var op, e))
            else 
                unexpected_error "typeinfer_expr: unsupported unary operator (%s)" op

    | _ -> type_error "Expresssion inserted not implemented"


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

    | Tuple es -> TyTuple (List.map (typecheck_expr env) es)

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
