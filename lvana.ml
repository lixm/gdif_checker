open Utils
open Lexer
open Ast
open Parser
open Ggraph

type constraint_t = {ptl: pt; ptr: pt; kill: VarSet.t; gen: VarSet.t}

let rec bevars_pt statement pt = 
  match statement with 
   | SSkip _ | SAssg _ | SOt _ | SIn _ ->  VarSet.empty
   | SSeq (statement1, statement2) -> 
      VarSet.union (bevars_pt statement1 pt) (bevars_pt statement2 pt)
   | SIf (pt', be, statement1, statement2) -> 
      let inc = (if pt' = pt then fvs_b be  else VarSet.empty) in 
      VarSet.union 
	inc
	(VarSet.union (bevars_pt statement1 pt) (bevars_pt statement2 pt))
   | SWhile (pt', be, statement)  -> 
      let inc = (if pt' = pt then fvs_b be else VarSet.empty) in 
      VarSet.union inc (bevars_pt statement pt)

let bevars_pt_sys (Sys (procs, _)) pt = 
  List.fold_left 
    VarSet.union VarSet.empty
    (List.map (fun (_, statement) -> bevars_pt statement pt) procs)

let get_constraints lsuccs pts sys = 
  List.fold_left 
    (fun cnsmp (pt, act, pt') -> 
     match act with 
     | FASkip -> 
	let new_cns = {ptl=pt; ptr=pt'; kill=VarSet.empty; gen=VarSet.empty}	in																		
	PtsMap.add pt' (PtsMap.find pt' cnsmp @ [new_cns]) cnsmp										
     | FABrt | FABrf ->  
	let gen = bevars_pt_sys sys pt in 
	let new_cns = {ptl=pt; ptr=pt'; kill=VarSet.empty; gen=gen} in 
	PtsMap.add pt' (PtsMap.find pt' cnsmp @ [new_cns]) cnsmp
     | FAAssg (x, ae) -> 
	let kill = VarSet.singleton x in 
	let new_cns = {ptl=pt; ptr=pt'; kill=kill; gen=fvs_a ae} in 
	PtsMap.add pt' (PtsMap.find pt' cnsmp @ [new_cns]) cnsmp
     | FAOt (c, al) -> 
	let gen = 
	  List.fold_left (fun acc ae -> VarSet.union acc (fvs_a ae)) 
			 VarSet.empty al 
	in 
	let new_cns = {ptl=pt; ptr=pt'; kill=VarSet.empty; gen=gen} in
	PtsMap.add pt' (PtsMap.find pt' cnsmp @ [new_cns]) cnsmp
     | FAIn (c, xl) -> 
	let kill = List.fold_right (VarSet.add) xl (VarSet.empty) in 
	let new_cns = {ptl=pt; ptr=pt'; kill=kill; gen=VarSet.empty} in
	PtsMap.add pt' (PtsMap.find pt' cnsmp @ [new_cns]) cnsmp
    )
    (List.fold_left
       (fun cnsmp pt -> PtsMap.add pt [] cnsmp)
       (PtsMap.empty)
       pts
    )
    lsuccs
    
(* evaluate the rhs for the constraint cns *)
let eval_rhs cns pt_lvs = 
  let orig = PtsMap.find cns.ptr pt_lvs in 
  let after_kill = 
    VarSet.filter (fun x -> not (VarSet.mem x cns.kill)) orig in
  VarSet.union after_kill cns.gen

let rec iterate cnsmp resmp wl = 
  match wl with 
  | [] -> resmp 
  | cns :: wl' -> 
     let new_res = eval_rhs cns resmp in 
     if not (VarSet.subset new_res (PtsMap.find cns.ptl resmp)) 
     then
       let resmp' = PtsMap.add cns.ptl new_res resmp in
       let wl'' = wl' @ (PtsMap.find cns.ptl cnsmp) in
       iterate cnsmp resmp' wl''
     else 
       iterate cnsmp resmp wl'

let init pts cnsmap = 
  let wl = PtsMap.fold (fun k cnslst wl -> wl @ cnslst) cnsmap [] in
  let anamp = 
    List.fold_left 
      (fun mp pt -> PtsMap.add pt (VarSet.empty) mp)
      (PtsMap.empty)
      pts
  in (anamp, wl)

let lvana sys = 
  let l_succ_of_sys =  
    match sys with 
    | Sys (l, _) -> 
       List.concat (
	   List.map 
	     (fun (pr, statement) -> 
	      l_succ statement (Pt ("f_" ^ (string_of_prin pr)))) 
	     l
	 )
  in 
  let pts = pts_of_sys sys in
  let cnsmp = get_constraints l_succ_of_sys pts sys in
  let (anamp0, wl0) = init pts cnsmp in
  iterate cnsmp anamp0 wl0
	
let string_of_lvs lvs =   
  if (VarSet.is_empty lvs) 
  then ""
  else 
    let min = VarSet.min_elt lvs in
    VarSet.fold 
      (fun x acc -> acc ^ ", " ^ (string_of_var x))
      (VarSet.remove min lvs)
      (string_of_var min)
      
let string_of_ptlvs pt_lvs = 
  PtsMap.fold 
    (fun k lvs acc -> 
     acc ^ "\n" ^ (string_of_pt k) ^ " -> {" ^ (string_of_lvs lvs) ^ "}")
    pt_lvs
    ""
