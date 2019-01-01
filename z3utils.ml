open Ast

open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver 
open Z3.Arithmetic
open Z3.Arithmetic.Integer


let rec z3fm_of_ae ctx ae = 
  let int_st = Integer.mk_sort ctx in
  match ae with
  | AeVal i -> 
     Expr.mk_numeral_int ctx i int_st
  | AeVar vr -> (
    match vr with
    | Var x -> 
       let var_str = mk_string ctx x in
       Expr.mk_const ctx var_str int_st
  )
  | AePlus (ae1, ae2) -> 
     Arithmetic.mk_add ctx [ z3fm_of_ae ctx ae1; z3fm_of_ae ctx ae2 ]
  | AeMinus (ae1, ae2) -> 
     Arithmetic.mk_sub ctx [ z3fm_of_ae ctx ae1; z3fm_of_ae ctx ae2 ]
  | AeMod (ae1, ae2) ->
     let mod_fname = (mk_string ctx "mod") in
     let mod_f = FuncDecl.mk_func_decl ctx mod_fname [int_st; int_st] int_st in
     mk_app ctx mod_f [ (z3fm_of_ae ctx ae1); (z3fm_of_ae ctx ae2) ]
  | AeFun (fn, aelst) -> 
     let fname = (mk_string ctx fn) in
     let dom_args = List.map (fun _ -> int_st) aelst in 
     let args = List.map (z3fm_of_ae ctx) aelst in 
     let f = FuncDecl.mk_func_decl ctx fname dom_args int_st in 
     mk_app ctx f args

let rec z3fm_of_be ctx be = 
  match be with
  | BeTrue -> mk_true ctx
  | BeFalse -> mk_false ctx
  | BeEq (ae1, ae2) -> mk_eq ctx (z3fm_of_ae ctx ae1) (z3fm_of_ae ctx ae2)
  | BeNEq (ae1, ae2) -> 
     mk_not ctx (mk_eq ctx (z3fm_of_ae ctx ae1) (z3fm_of_ae ctx ae2))
  | BeNot be' -> mk_not ctx (z3fm_of_be ctx be')
  | BeAnd (be1, be2) -> mk_and ctx [ z3fm_of_be ctx be1; z3fm_of_be ctx be2 ]
  | BeOr (be1, be2) -> mk_or ctx [ z3fm_of_be ctx be1; z3fm_of_be ctx be2 ]
  | BeImpl (be1, be2) -> 
     mk_implies ctx (z3fm_of_be ctx be1) (z3fm_of_be ctx be2)
  | BeEx (x, be') -> 
     let name = Symbol.mk_string ctx (string_of_var x) in 
     let var = Integer.mk_const ctx name in 
     let body = z3fm_of_be ctx be' in 
     let quan = 
       (Quantifier.mk_exists_const ctx [var] body 
				   (Some 1) [] [] 
				   (Some (Symbol.mk_string ctx "Q2")) (Some (Symbol.mk_string ctx "skid2")))
     in
     Quantifier.expr_of_quantifier quan 

(* return true in case fm is satisfiable *)
let check_formula ctx fm = 
  let g = (mk_goal ctx true false false) in
  Goal.add g [ fm ]; 
  (*  Printf.printf "%s\n" ("Goal: " ^ (Goal.to_string g)); *)
  (
    let solver = mk_solver ctx None in 
    List.iter (fun a -> (Solver.add solver [ a ])) (get_formulas g);
    if (check solver [] = SATISFIABLE) then true else false
  )
    
    (*
let () = 
	let cfg = [("model", "true"); ("proof", "false")] in
	let ctx = (mk_context cfg) in
	let x = Var "x" in 
	let be = BeNot (BeEx (x, BeEq (AeVar x, AeVal 1))) in 
	if check_formula ctx (z3fm_of_be ctx be) != SATISFIABLE 
	then print_endline "unsat"
	else print_endline "sat"
     *)
