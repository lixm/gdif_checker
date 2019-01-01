open Utils
open Lexer
open Ast
open Parser
open Ggraph

module EqFormulas = 
  struct 
    type t = var * aexp

    let compare_var var1 var2 = 
      match var1 with 
      | Var vrstr1 -> (
				match var2 with 
				| Var vrstr2 -> compare vrstr1 vrstr2
      )

    let rec compare_aexp ae1 ae2 = 
      match ae1 with 
      | AeVal n1 -> (
				match ae2 with 
				| AeVal n2 -> compare n1 n2
				| _ -> -1
      )
      | AeVar var1 -> (
				match ae2 with 
				| AeVal _ -> 1
				| AeVar var2 -> compare_var var1 var2
				| _ -> -1
      )
      | AePlus (ae11, ae12) -> (
				match ae2 with 
				| AeVal _ | AeVar _ -> 1
				| AePlus (ae21, ae22) -> compare_ops ae11 ae12 ae21 ae22
				| _ -> -1
      )
      | AeMinus (ae11, ae12) -> (
				match ae2 with 
				| AeVal _ | AeVar _ | AePlus (_, _) -> 1
				| AeMinus (ae21, ae22) -> compare_ops ae11 ae12 ae21 ae22
				| _ -> -1
      )
      | AeMod (ae11, ae12) -> (
				match ae2 with 
				| AeVal _ | AeVar _ | AePlus (_, _) | AeMinus (_, _) -> 1
				| AeMod (ae21, ae22) -> compare_ops ae11 ae12 ae21 ae22
				| _ -> -1
      )
      | AeFun (fname1, _) -> (
				match ae2 with 
				| AeFun (fname2, _) -> compare fname1 fname2
				| _ -> 1
      )
    and compare_ops ae11 ae12 ae21 ae22 = 
      let c1 = compare_aexp ae11 ae21 in 
      if c1 <> 0 then c1 else compare_aexp ae12 ae22

    let compare (x1, ae1) (x2, ae2) = 
      let cvar = compare_var x1 x2 in 
      if cvar <> 0 then cvar else compare_aexp ae1 ae2

    let is_fv_of_eqfm x' (x, ae) = 
      let rec is_fv_of_aexp x' ae = (
				match ae with 
				| AeVal _ -> false 
				| AeVar x'' -> (x' = x'')
				| AePlus (ae1, ae2) 
				| AeMinus (ae1, ae2) 
				| AeMod (ae1, ae2) ->
						(is_fv_of_aexp x' ae1 || is_fv_of_aexp x' ae2)
				| AeFun (fname, aelst) -> 
					 List.exists (fun ae' -> is_fv_of_aexp x' ae') aelst
      )
      in if x' = x then true else (is_fv_of_aexp x' ae)

  end
    
module EqFmSet = Set.Make(EqFormulas)
			 
let string_of_eqfm (x, ae) = string_of_var x  ^ " = " ^ string_of_aexp ae
								       
let string_of_eqfms eqfms = 
  let min = EqFmSet.min_elt eqfms in
  EqFmSet.fold 
    (fun eqfm acc -> acc ^ ", " ^ (string_of_eqfm eqfm))
    (EqFmSet.remove min eqfms)
    (string_of_eqfm min)

let same_eqfms s1 s2 = EqFmSet.subset s1 s2 && EqFmSet.subset s2 s1

type constraint_t = {ptsl: PtLists.t; ptsr: PtLists.t; 
										 kill: var list; gen: EqFmSet.t}

let string_of_pt_eqfms local_anamp = 
  PtsMap.fold  
    (fun pt eqfms acc -> 
     let set_str = string_of_eqfms eqfms in
     acc ^ "\n" ^ (string_of_pt pt) ^ "->" ^ "{" ^ set_str ^ "}"
    )
    local_anamp 
    ""
		
let string_of_pts_eqfms anamp =
	GLocsMap.fold
		(fun pts eqfms acc ->
		 let set_str = string_of_eqfms eqfms in
		 acc ^ "\n" ^ (string_of_pts pts) ^ "->" ^ "{" ^ set_str ^ "}" 
		)
		anamp
		""

let eqfms_sync aelst xlst = 
  List.fold_left 
    (fun acc (x, ae) -> EqFmSet.add (x, ae) acc)
    (EqFmSet.empty) (zip_exn xlst aelst)

(* collect constraints from a ggraph *)
let get_constraints glocs_gnode pts = 
  GLocsMap.fold 
    (fun k gn cnsmp -> 
     List.fold_left
       (fun cnsmp suc ->
				let pts' = suc.gsucc.glocs in
				match suc.acts with 
				| [FASkip] | [FABrt] | [FABrf] | [(FAOt _)] -> ( 
					let new_cns = {ptsl=pts'; ptsr=k; kill=[]; gen=EqFmSet.empty} in
					GLocsMap.add k (GLocsMap.find k cnsmp @ [new_cns]) cnsmp 
				)
				| [FAAssg (x, ae)] -> 
					 let new_cns = {ptsl=pts'; ptsr=k; kill=[x]; gen=EqFmSet.empty} in 
					 GLocsMap.add k ((GLocsMap.find k cnsmp) @ [new_cns]) cnsmp
				| [(FAIn (c, xlst))] -> 
					 let new_cns = {ptsl=pts'; ptsr=k; kill=xlst; gen=EqFmSet.empty} in 
					 GLocsMap.add k ((GLocsMap.find k cnsmp) @ [new_cns]) cnsmp
				| [(FAOt (c1, alst)); (FAIn (c2, xlst))] 
				| [(FAIn (c1, xlst)); (FAOt (c2, alst))] ->
					 let new_cns = {ptsl=pts'; ptsr=k;
													kill=xlst; gen=eqfms_sync alst xlst}
					 in
					 GLocsMap.add k ((GLocsMap.find k cnsmp) @ [new_cns]) cnsmp
				| _ -> raise (Failure "unexpected combination of actions") 
       )
       cnsmp
       gn.gsuccs
    )
    glocs_gnode
    (GLocsMap.mapi (fun pts _ -> []) glocs_gnode) 		

(* evaluate the rhs for the constraint cns *)
let eval_rhs cns loc_eqfms =
  let orig = GLocsMap.find cns.ptsr loc_eqfms in 
  let after_kill =
    EqFmSet.filter
      (fun eqfm ->
       not (List.exists
	      (fun x -> EqFormulas.is_fv_of_eqfm x eqfm) cns.kill))
      orig
  in
  EqFmSet.union after_kill cns.gen

let rec iterate cnsmp resmp wl =
  match wl with
  | [] -> resmp
  | cns :: wl' ->
		 let orig = GLocsMap.find cns.ptsl resmp in 
     let new_res = eval_rhs cns resmp in		 
     if not (EqFmSet.subset orig new_res) 
     then
       let resmp' = GLocsMap.add cns.ptsl (EqFmSet.inter orig new_res) resmp in
       let wl'' = wl' @ (GLocsMap.find cns.ptsl cnsmp) in 
       iterate cnsmp resmp' wl''
     else
       iterate cnsmp resmp wl'

let eval_zz ae =
  let rec eval_zro ae =
    match ae with
    | AeVal i -> i
    | AeVar x -> 0
    | AePlus (a1, a2) -> eval_zro a1 + eval_zro a2
    | AeMinus (a1, a2) -> eval_zro a1 - eval_zro a2
    | AeMod (a1, a2) -> eval_zro a1 mod eval_zro a2
    | AeFun (fn, ae) -> raise (Failure "function application result unknown")
  in
  try if (eval_zro ae) = 0 then true else false
  with e -> false

let all_eqfms glocs_gnode =
	GLocsMap.fold
		(fun k gl eqfms ->
		 List.fold_left
			 (fun eqfms suc ->
				match suc.acts with
				| [FAOt (c1, al); FAIn (c2, xl)]
				| [FAIn (c1, xl); FAOt (c2, al)] ->
					 EqFmSet.union eqfms (eqfms_sync al xl)
				| _ -> eqfms
			 )
			 eqfms
			 gl.gsuccs
		)
		glocs_gnode
		EqFmSet.empty
	
let init glocs_gnode sys cnsmap =
	match sys with
	| Sys (prstmt_lst, _) ->
		 let wl =
			 GLocsMap.fold (fun k cnslst wl -> wl @ cnslst) cnsmap [] 
		 in
		 let fst_pts = (List.map (fun (pr, stmt) -> (fst stmt)) prstmt_lst) in
		 let all_efs = all_eqfms glocs_gnode in 
		 let all_init_efs = EqFmSet.filter (fun (x, ae) -> eval_zz ae) all_efs in
		 let anamp =
			 GLocsMap.mapi
				 (fun pts _ -> if pts = fst_pts then all_init_efs else all_efs) 
				 glocs_gnode
		 in 
		 (anamp, wl)

let localize_eqana_res glocs_gnode anamp sys =
	let pts = pts_of_sys sys in
	GLocsMap.fold
		(fun pts eqfms pt_eqfms ->
		 let gn = GLocsMap.find pts glocs_gnode in
		 let succ_proc_ids =
			 List.flatten
				 (List.map (fun suc -> suc.procs) gn.gsuccs)
		 in
		 List.fold_left
			 (fun pt_eqfms k ->
				let pt = List.nth pts k in
				let current_eqfms = PtsMap.find pt pt_eqfms in
				PtsMap.add pt (EqFmSet.inter eqfms current_eqfms) pt_eqfms 
			 )
			 pt_eqfms
			 succ_proc_ids
		)		
		anamp		
	(
		List.fold_left
			(fun pt_eqfms pt ->
			 PtsMap.add pt (all_eqfms glocs_gnode) pt_eqfms 
			)
			PtsMap.empty
			pts 
	)
			 
let eqana sys =
  let pts = pts_of_sys sys in
  let (gnode0, gmap) = g_graph_of_sys sys in
  let cnsmp = get_constraints gmap pts in
  let (anamp0, wl0) = init gmap sys cnsmp in
  let res = iterate cnsmp anamp0 wl0 in
	localize_eqana_res gmap res sys

