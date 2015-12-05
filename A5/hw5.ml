(*********************************************)
(* HW5: A Sound Static Type Checker for PROC *)
(*********************************************)

type exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | ISZERO of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

(* raise this exception when the program is determined to be ill-typed *)
exception TypeError

(* type *)
type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string

(* type equations are represented by a list of "equalities" (ty1 = ty2)  *)
type typ_eqn = (typ * typ) list

(* generate a fresh type variable *)
let tyvar_num = ref 0
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)
end

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> match e with
    | CONST n ->
        [(ty,TyInt)]
    | VAR x ->
        [(ty,TEnv.find tenv x)]
    | ADD (e1,e2) ->
        (ty,TyInt)::(gen_equations tenv e1 TyInt)
                    @(gen_equations tenv e2 TyInt)
    | SUB (e1,e2) ->
        (ty,TyInt)::(gen_equations tenv e1 TyInt)
                    @(gen_equations tenv e2 TyInt)
    | ISZERO e ->
        (ty, TyBool)::(gen_equations tenv e TyInt)
    | IF (e1,e2,e3) ->
        (gen_equations tenv e1 TyBool)
        @(gen_equations tenv e2 ty)
        @(gen_equations tenv e3 ty)
    | LET (x,e1,e2) ->
        let a = fresh_tyvar() in
        let new_tenv = TEnv.extend (x,a) tenv in
            (gen_equations tenv e1 a)@(gen_equations new_tenv e2 ty)
    | PROC (x,e) ->
        let a1 = fresh_tyvar() in
        let a2 = fresh_tyvar() in
        let a = TyFun(a1,a2) in
        let new_tenv = TEnv.extend (x,a1) tenv in
        (ty,a)::(gen_equations new_tenv e a2)
    | CALL (e1,e2) ->
        let a = fresh_tyvar() in
        let a_t = TyFun(a,ty) in
        (gen_equations tenv e1 a_t)@(gen_equations tenv e2 a)

let rec unify : typ -> typ -> Subst.t -> Subst.t
=fun t1 t2 s -> match (t1,t2) with
    | (TyInt,TyInt) -> s
    | (TyBool,TyBool) -> s
    | (t,TyVar a) -> unify (TyVar a) t s
    | (TyVar a,t) ->
        if t1 = t2
            then raise TypeError
            else Subst.extend a t s
    | (TyFun (t1,t2),TyFun (t'1,t'2)) ->
        let s' = unify t1 t'1 s in
        let t''1 = Subst.apply t2 s' in
        let t''2 = Subst.apply t'2 s' in
        unify t''1 t''2 s'
    | _ -> raise TypeError

let rec unifyall : typ_eqn -> Subst.t -> Subst.t
=fun eqn s -> match eqn with
    | [] -> s
    | (t1,t2)::u ->
        let s' = unify (Subst.apply t1 s) (Subst.apply t2 s) s in
            unifyall u s'

let solve : typ_eqn -> Subst.t
=fun eqn ->
    unifyall eqn Subst.empty 

let typeof : exp -> typ 
=fun exp -> 
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let subst = solve eqns in
  let ty = Subst.apply new_tv subst in
    ty

(* TESTS *)

(*
;;
let p0 = SUB (CONST 1, CONST 2) in
let result = try typeof p0 with _ ->
    (print_string("Failed test 0: found TypeError where none existed\n"); TyBool) in
match result with
 | TyInt -> print_string("Pass 0\n")
 | _ -> print_string("Failed test 0: incorrect answer\n")
;;

let p1 = PROC ("f", PROC ("x", SUB (CALL (VAR "f", CONST 3), CALL (VAR "f", VAR "x")))) in
let result = try typeof p1 with _ ->
    (print_string("Failed test 1: found TypeError where none existed\n"); TyBool) in
match result with
 | TyFun (TyFun (TyInt, TyInt), TyFun (TyInt, TyInt)) -> print_string("Pass 1\n")
 | _ -> print_string("Failed test 1: incorrect answer\n")
;;

let p2 = PROC ("f", CALL (VAR "f", CONST 11)) in
let result = try typeof p2 with _ ->
    (print_string("Failed test 2: found TypeError where none existed\n"); TyBool) in
match result with
 | TyFun (TyFun (TyInt, TyVar a), TyVar b) when a = b -> print_string("Pass 2\n")
 | _ -> print_string("Failed test 2: incorrect answer\n")
;;

let p3 = LET ("x", CONST 1, IF (VAR "x", SUB (VAR "x", CONST 1), CONST 0)) in
let result = try typeof p3 with _ ->
    (print_string("Pass 3\n"); TyBool) in
match result with
 | TyBool -> ()
 | _ -> print_string("Failed test 3: did not find TypeError\n")
;;
*)
