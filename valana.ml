open Utils
open Ast 
open Eqana
open Brana
open Asst

let pt_br_in_range mu pt_brs =
	PtsMap.for_all
		(fun pt br ->
		 let br_set = PtsMap.find pt pt_brs in
		 BrFmSet.mem br br_set 
		)
		mu 

let op_iter lst op default_val =
	match lst with
	| [] -> default_val
	| hd :: lst' -> 
		 List.fold_left (fun acc ele -> op (acc, ele)) hd lst' 
		
let get_val_fm_map
			(pt_eqs : EqFmSet.t PtsMap.t)
			(pt_pt_brs : (BrFmSet.t PtsMap.t) PtsMap.t)
			(pt_cond : (PtBrAsstPairSet.t PtsMap.t)) 
	=
	PtsMap.mapi
		(fun pt eqs ->
		 let pt_brs = PtsMap.find pt pt_pt_brs in
		 let cond = PtBrAsstPairSet.elements (PtsMap.find pt pt_cond) in 
		 let lst =
			 List.filter (fun (mu, be) -> pt_br_in_range mu pt_brs) cond
		 in
		 let phi_lst = List.map (fun (mu, be) -> be) lst in
		 let eq_be_lst =
			 List.map 
				 (fun (x, ae) -> BeEq (AeVar x, ae))
				 (EqFmSet.elements eqs)
		 in
		 let eq_part =
			 op_iter eq_be_lst (fun (be1, be2) -> BeAnd (be1, be2)) BeTrue 
		 in
		 let lcl_part =
			 op_iter phi_lst (fun (be1, be2) -> BeOr (be1, be2)) BeFalse
		 in
		 BeAnd (eq_part, lcl_part)  
		)
		pt_eqs

let string_of_pt_val_be pt_val_be = 
	string_of_ptsmap
		pt_val_be string_of_pt string_of_be_paren "->" "\n" 
