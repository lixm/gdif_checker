open Utils
open Ast
open Parser
open Ggraph
open Eqana
open Brana
open Z3utils 

let compare_pair comp_func1 comp_func2 pair1 pair2 =
	match pair1 with
	|	(e11, e12) -> 
		 match pair2 with
		 | (e21, e22) ->
				let fst_comp = comp_func1 e11 e21 in
				if fst_comp <> 0 then
					fst_comp
				else
					comp_func2 e12 e22 

let rec compare_bexp be1 be2 =
	match be1 with
	| BeTrue -> (match be2 with | BeTrue -> 0 | _ -> 1)  
	| BeFalse -> (match be2 with | BeTrue -> -1 | BeFalse -> 0	| _ -> 1) 
	| BeEq (ae11, ae12) -> ( 
			 match be2 with
			 | BeEq (ae21, ae22) -> 
					let f = EqFormulas.compare_aexp in
					compare_pair f f (ae11, ae12) (ae21, ae22)
			 | BeTrue | BeFalse -> -1 
			 | _ -> 1
		 )
	| BeNEq (ae11, ae12) -> (
			 match be2 with
			 | BeNEq (ae21, ae22) -> 
					let f = EqFormulas.compare_aexp in
					compare_pair f f (ae11, ae12) (ae21, ae22)
			 | BeTrue | BeFalse | BeEq (_, _) -> -1 
			 | _ -> 1
		 )
	| BeNot be1' -> (
			 match be2 with
			 | BeNot be2' -> compare_bexp be1' be2'
			 | BeTrue | BeFalse | BeEq (_, _) | BeNEq (_, _) -> -1
			 | _ -> 1
		 )
	| BeAnd (be11, be12) -> (		 
			 match be2 with
			 | BeAnd (be21, be22) ->
					let f = compare_bexp in compare_pair f f (be11, be12) (be21, be22) 
			 | BeOr (_, _) | BeImpl (_, _) | BeEx (_, _) -> 1 
			 | _ -> -1 
		 )
	| BeOr (be11, be12) -> (
			 match be2 with
			 | BeOr (be21, be22) ->
					let f = compare_bexp in compare_pair f f (be11, be12) (be21, be22) 
			 | BeImpl (_, _) | BeEx (_, _) -> 1
			 | _ -> -1
		 )
	| BeImpl (be11, be12) -> (
			 match be2 with
			 | BeImpl (be21, be22) ->
					let f = compare_bexp in compare_pair f f (be11, be12) (be21, be22) 
			 | BeEx (_, _) -> 1
			 | _ -> -1 
		 )
	| BeEx (x, be1) -> (
			 match be2 with
			 | BeEx (x', be1') ->
					let f1 = EqFormulas.compare_var in 
					let f2 = compare_bexp in
					compare_pair f1 f2 (x, be1) (x', be1')  
			 | _ -> -1 
		 )
						
module PtBrAsstPairs =
	struct
		type t = ((BrFormulas.t PtsMap.t) * bexp)
		let compare (mu1, phi1) (mu2, phi2) =
			let f1 = PtsMap.compare (BrFormulas.compare) in
			let f2 = compare_bexp in
			compare_pair f1 f2 (mu1, phi1) (mu2, phi2)			
	end

module PtBrAsstPairSet = Set.Make(PtBrAsstPairs)

(* ae[a/x] *)
let rec subst_a ae x a = 
  match ae with 
  | AeVal _ -> ae 
  | AeVar x' -> if x' = x then a else ae
  | AePlus (ae1, ae2) -> AePlus (subst_a ae1 x a, subst_a ae2 x a)
  | AeMinus (ae1, ae2) -> AeMinus (subst_a ae1 x a, subst_a ae2 x a)
  | AeMod (ae1, ae2) -> AeMod (subst_a ae1 x a, subst_a ae2 x a)
  | AeFun (fname, aelst) -> 
     AeFun (fname, List.map (fun ae -> subst_a ae x a) aelst)

(* be[a/x] *)
let rec subst_b be x a = 
  match be with 
  | BeTrue | BeFalse -> be
  | BeEq (ae1, ae2) -> BeEq (subst_a ae1 x a, subst_a ae2 x a)
  | BeNEq (ae1, ae2) -> BeNEq (subst_a ae1 x a, subst_a ae2 x a)
  | BeNot be' -> BeNot (subst_b be' x a)
  | BeAnd (be1, be2) -> BeAnd (subst_b be1 x a, subst_b be2 x a)
  | BeOr (be1, be2) -> BeOr (subst_b be1 x a, subst_b be2 x a)
  | BeImpl (be1, be2) -> BeImpl (subst_b be1 x a, subst_b be2 x a) 
  | BeEx (x', be') -> 
     if x' = x then
       be
     else if VarSet.mem x' (fvs_a a) then
       raise (Failure "variable capture in substitution")
     else 
       BeEx (x', subst_b be' x a)

let dec_impl ctx be1 be2 =
(*
  let _ = print_endline (
	      "checking implication FROM " ^ 
		string_of_be_paren be1  ^ " TO " ^ string_of_be_paren be2 ^ "\n") 
  in 
*)
  let be_impl = BeImpl (be1, be2) in 
  let negated = BeNot be_impl in
  let z3fm_neg = z3fm_of_be ctx negated in 
  let res = not (check_formula ctx z3fm_neg) in 
  (*  let _ = print_endline ("implication " ^ if res then "holds" else "does not hold") in *)
  res

let raise_inv_err1 pt = 
  raise (Failure ("loop invariant at " ^ string_of_pt pt ^ 
		    " is not implied when entering the loop"))

let raise_inv_err2 pt = 
  raise (Failure ("loop invariant at " ^ string_of_pt pt ^ 
		    " is not implied when exiting the loop"))

let exists_asst pt pt_assts = 
  try let _ = List.assoc pt pt_assts in true
  with Not_found -> false

let use_snd pt_cond1 pt_cond2 pt_lst = 
  List.fold_left 
    (fun pt_cond pt -> 
     PtsMap.add pt (PtsMap.find pt pt_cond2) pt_cond) 
    pt_cond1
    pt_lst
    
let string_of_pt_cond pt_cond = 
	let str_of_val v = string_of_assertion_body (PtBrAsstPairSet.elements v) in
	string_of_ptsmap pt_cond string_of_pt str_of_val "->" "\n" 
									 
let raise_impl_err pt pt_cond pt_asst =
	let cond = PtsMap.find pt pt_cond in
	let asst = List.assoc pt pt_asst in 
  raise (Failure 
	   ("at " ^ string_of_pt pt ^ ": post-condition " ^ 
	      (string_of_assertion_body (PtBrAsstPairSet.elements cond)) ^ 
		" does not imply assertion " ^ 
		  (string_of_assertion_body asst) ^ 
		    " at program point " ^ 
		      (string_of_pt pt))) 																 

let ordr_ptbr_asst_pair_set z3ctx set1 set2 = 
	PtBrAsstPairSet.for_all
		(fun (mu, phi) -> 
		 let be2 = 
			 PtBrAsstPairSet.fold
				 (fun (mu', phi') be ->
					if (PtsMap.compare (BrFormulas.compare) mu mu' = 0) then 
						BeOr (be, phi')
					else
						be
				 )
				 set2 BeFalse 
		 in 
		 dec_impl z3ctx phi be2 
		)
		set1 

(* update a map from program points to conditions -- 
   a set of pairs (mu, phi) -- using a potentially 
   existing user assertion -- a list of pairs (mu, phi) 
   -- at program point pt *) 
let upd_pt_cond_with_asst z3ctx pt pt_cond pt_asst = 
	if (exists_asst pt pt_asst) then 
		let asst = List.assoc pt pt_asst in 
		let asst_set = PtBrAsstPairSet.of_list asst in 
		let cond = PtsMap.find pt pt_cond in 
		if not (ordr_ptbr_asst_pair_set z3ctx cond asst_set) then 
			let _ = raise_impl_err pt pt_cond pt_asst in 		
			pt_cond 
		else
			PtsMap.add pt asst_set pt_cond 
	else
		pt_cond

let transfer_cond cond_set f1 f2 =
	PtBrAsstPairSet.fold
		(fun (mu, phi) cond -> PtBrAsstPairSet.add (f1 mu, f2 phi) cond) 
		cond_set PtBrAsstPairSet.empty 

let transfer_cond_1 cond_set f =
	transfer_cond cond_set f (fun a -> a)
							 
let transfer_cond_2 cond_set f = 
	transfer_cond cond_set (fun a -> a) f	

(* pt_cond is supposed to contain a valid precondition at 
   the first program point of stmt *)	
let rec get_post_cond
					z3ctx
					stmt
					(pt_cond : (PtBrAsstPairSet.t PtsMap.t))
					pt_inv
					pt_asst
	=
	try
		let fst_pt = fst stmt in
		let pt_cond_new =
			upd_pt_cond_with_asst z3ctx fst_pt pt_cond pt_asst
		in
		let pre_cond = PtsMap.find fst_pt pt_cond_new in
		match stmt with
		| SSkip pt -> (pre_cond, pt_cond_new)
		| SAssg (pt, x, ae) ->
			 let nvar = Var (string_of_var x ^ "#" ^ string_of_pt pt) in
			 let post_of phi =
				 BeEx (nvar,
							 (BeAnd
									(BeEq ((AeVar x), (subst_a ae x (AeVar nvar))),
									 subst_b phi x (AeVar nvar))))
			 in
			 let post_cond = transfer_cond_2 pre_cond post_of in 
			 (post_cond, pt_cond_new)
		| SOt (pt, c, alst) -> (pre_cond, pt_cond_new)
		| SIn (pt, c, xlst) ->  
			 let post_of phi = List.fold_right (fun x fm -> BeEx (x, fm)) xlst phi in
			 let post_cond = transfer_cond_2 pre_cond post_of in 
			 (post_cond, pt_cond_new)
		| SSeq (stmt1, stmt2) -> 
			 let (post_cond1, pt_cond_1) =
				 get_post_cond z3ctx stmt1 pt_cond pt_inv pt_asst 
			 in
			 let pt_cond_1' = PtsMap.add (fst stmt2) post_cond1 pt_cond_1 in
			 get_post_cond z3ctx stmt2 pt_cond_1' pt_inv pt_asst
		| SIf (pt, be, stmt1, stmt2) ->
			 let (post_cond1, pt_cond_new1) = 
				 let upd_mu = PtsMap.add pt BrFormulas.Et in
				 let upd_phi phi = BeAnd (phi, be) in 
				 let pre_cond1 = transfer_cond pre_cond upd_mu upd_phi in
				 let pt_cond1 = PtsMap.add (fst stmt1) pre_cond1 pt_cond in 
				 get_post_cond z3ctx stmt1 pt_cond1 pt_inv pt_asst
			 in
			 let (post_cond2, pt_cond_new2) =
				 let upd_mu = PtsMap.add pt BrFormulas.Ef in
				 let upd_phi phi = BeAnd (phi, (BeNot be)) in
				 let pre_cond2 = transfer_cond pre_cond upd_mu upd_phi in
				 let pt_cond2 = PtsMap.add (fst stmt2) pre_cond2 pt_cond in
				 get_post_cond z3ctx stmt2 pt_cond2 pt_inv pt_asst
			 in
			 (
				 PtBrAsstPairSet.union post_cond1 post_cond2,
				 use_snd pt_cond_new1 pt_cond_new2 (pts_of_stmt stmt2)
			 )
		| SWhile (pt, be, stmt1) ->
			 if not (exists_asst pt pt_inv) then 
				 raise (Failure ("missing loop invariant at " ^ string_of_pt pt)) 
			 else
				 let inv = List.assoc pt pt_inv in 
				 let cond = PtsMap.find pt pt_cond in
				 let inv_set = PtBrAsstPairSet.of_list inv in 
				 if not (ordr_ptbr_asst_pair_set z3ctx cond inv_set) then 
					 raise_inv_err1 pt 
				 else
					 let (post_cond1, pt_cond1) = 
						 let upd_mu = PtsMap.add pt BrFormulas.Et in
						 let upd_phi phi = BeAnd (phi, be) in
						 let pre_cond1 = transfer_cond pre_cond upd_mu upd_phi in
						 let pt_cond1 = PtsMap.add (fst stmt1) pre_cond1 pt_cond in
						 get_post_cond z3ctx stmt1 pt_cond1 pt_inv pt_asst
					 in
					 if not (ordr_ptbr_asst_pair_set z3ctx post_cond1 inv_set) then
						 raise_inv_err2 pt
					 else
						 let post_cond =
							 let upd_mu = PtsMap.add pt BrFormulas.Ef in
							 let upd_phi phi = BeAnd (phi, (BeNot be)) in
							 transfer_cond inv_set upd_mu upd_phi
						 in
						 (post_cond, pt_cond1) 
	with Not_found ->
		raise (Failure "precondition not found")

let post_cond_proc z3ctx (pr, stmt) pt_inv pt_asst = 
  let zterm x = BeEq (AeVar x, AeVal 0) in 
  let vars_of_stmt = fvs_stmt stmt in  
  let phi_init =
    let min = VarSet.min_elt vars_of_stmt in 
    VarSet.fold
      (fun x conj -> BeAnd (conj, zterm x))
      (VarSet.remove min vars_of_stmt)
      (zterm min)
  in
	let mu_init =
		let brpts = brpts_of_stmt stmt in
		List.fold_left
			(fun mu pt -> PtsMap.add pt BrFormulas.Ebot mu)
			PtsMap.empty brpts 
	in
	let init_pt_cond =
		PtsMap.add
			(fst stmt)
			(PtBrAsstPairSet.singleton (mu_init, phi_init))
			(PtsMap.empty) 
	in 
  let (post_cond, pt_cond') = 
    get_post_cond z3ctx stmt init_pt_cond pt_inv pt_asst 
  in
  PtsMap.add (Pt ("f_" ^ (string_of_prin pr))) post_cond pt_cond'

let post_cond_sys z3ctx (Sys (prstmts, _)) pt_inv pt_asst =
	let post_cond_map = 
		List.fold_left
			(fun acc prstmt ->
			 use_snd
				 acc
				 (post_cond_proc z3ctx prstmt pt_inv pt_asst) 
				 (pts_of_stmt (Pervasives.snd prstmt) @
						[Pt ("f_" ^ (string_of_prin (Pervasives.fst prstmt)))]))
			PtsMap.empty
			prstmts
	in
	PtsMap.map
		(fun cond -> transfer_cond_2 cond simplify_be)
		post_cond_map
					
