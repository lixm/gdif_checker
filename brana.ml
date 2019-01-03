open Utils 
open Lexer
open Ast
open Parser
open Ggraph

type constraint_t = {
		ptsl: PtLists.t; 
		ptsr: PtLists.t; 
		(* optionally, a program point is re-mapped to a new set *)
		upd: (pt * BrFmSet.t) option 
	} 

let glocs_of_sys glocs_gnode =
  GLocsMap.fold (fun k gn glocs_lst -> glocs_lst @ [k]) glocs_gnode []
								
let mk_upd pt act = 
	match act with
	| FABrt -> Some (pt, (BrFmSet.singleton BrFormulas.Et))
	| FABrf -> Some (pt, (BrFmSet.singleton BrFormulas.Ef)) 
	| _ -> None

let mk_constraint pts pts' k act = 
	let pt = (List.nth pts k) in 
	{ptsl=pts'; ptsr=pts; upd=(mk_upd pt act)}

(* glocs_gnode is a map from lists of program points to gnode's, 
   all_pts is the list containing all the program points of the system
   as well as the final program points *) 
let get_constraints glocs_gnode all_pts = 
	GLocsMap.fold 
		(
			fun pts gn cnsmp -> 
			List.fold_left
				(
					fun cnsmp suc -> 
					(
						match suc with 
						| {acts=[act]; procs=[k]; gsucc=gn} -> 
							 (
								 let new_cns = (mk_constraint pts suc.gsucc.glocs k act) in 
								 GLocsMap.add pts (GLocsMap.find pts cnsmp @ [new_cns]) cnsmp		
							 )
						| {acts=[act1;act2]; procs=[i;j]; gsucc=gn} ->	
							 let lst = [(i, act1); (j, act2)] in 
							 List.fold_left 
								 (
									 fun cnsmp (k, act) -> 
									 let new_cns = mk_constraint pts suc.gsucc.glocs k act in
									 GLocsMap.add pts (GLocsMap.find pts cnsmp @ [new_cns]) cnsmp 
								 )
								 cnsmp
								 lst 
						| _ -> cnsmp
					)
				)
				cnsmp
				gn.gsuccs 
		)
		glocs_gnode
    (GLocsMap.mapi (fun pts _ -> []) glocs_gnode) 

(* evaluate the rhs of the constraint cns
   the evaluation result is a map from program points to subsets of
   {Et,Ef,Ebot} *)
let eval_rhs cns pts_ptbrfms =
	let orig = GLocsMap.find cns.ptsr pts_ptbrfms in 
		match cns.upd with 
		| Some (pt, brfmset) -> PtsMap.add pt brfmset orig
		| None -> orig

let le_locbrfms mp1 mp2 =
	PtsMap.fold 
		(
			fun pt1 brfms1 le ->
			if le = false then
				false
			else
				try 
					let brfms2 = PtsMap.find pt1 mp2 in
					BrFmSet.subset brfms1 brfms2
				with Not_found ->
					(
						print_endline ("Program point not found: " ^
														 (string_of_pt pt1));
						false 
					)						
		)
		mp1
		true

let lub_locbrfms mp1 mp2 =
	PtsMap.merge
		(
			fun pt brfms_opt1 brfms_opt2 ->
			(
				match brfms_opt1 with
				| Some brfms1 ->
					 (
						 match brfms_opt2 with
						 | Some brfms2 -> Some (BrFmSet.union brfms1 brfms2)
						 | None -> None
					 )
				| None -> None
			)
		)
		mp1
		mp2

let rec iterate cnsmp resmp wl =
	match wl with
	| [] -> resmp
	| cns :: wl' -> 
		 let new_res = eval_rhs cns resmp in
		 let lhs_orig = GLocsMap.find cns.ptsl resmp in 
		 if (not (le_locbrfms new_res lhs_orig)) then
			 let resmp' =
				 GLocsMap.add cns.ptsl (lub_locbrfms new_res lhs_orig) resmp 
			 in
			 let wl'' = wl' @ (GLocsMap.find cns.ptsl cnsmp) in 
			 iterate cnsmp resmp' wl''
		 else
			 iterate cnsmp resmp wl'

let mk_locbrfms_mp pts brfms =
		List.fold_left
			(fun accmp pt -> PtsMap.add pt brfms accmp)
			PtsMap.empty
			pts

let rec brpts_of_stmt stmt = (
  match stmt with
  | SSkip _ | SAssg _ | SOt _ | SIn _ -> []
  | SSeq (stmt1, stmt2) -> 
     brpts_of_stmt stmt1 @ brpts_of_stmt stmt2 
  | SIf (pt, be, stmt1, stmt2) -> 
     pt :: (brpts_of_stmt stmt1 @ brpts_of_stmt stmt2) 
  | SWhile (pt, be, stmt) -> pt :: (brpts_of_stmt stmt) 
)

let brpts_of_sys sys = 
	match sys with
	| Sys (prstmt_lst, _) ->
		 List.flatten
			 (
				 List.map (fun (pr, stmt) -> brpts_of_stmt stmt) prstmt_lst  
			 )
	
let init glocs_gnode sys cnsmap =  
	match sys with
	| Sys (prstmt_lst, _) ->
		 (
			 let fst_pts = (List.map (fun (pr, stmt) -> (fst stmt)) prstmt_lst) in
			 let wl = GLocsMap.fold (fun pts cnslst wl -> wl @ cnslst) cnsmap [] in
			 let anamp =
				 GLocsMap.mapi
					 (fun pts _ -> 
						let brpts = brpts_of_sys sys in 
						(
							if pts = fst_pts then
								(mk_locbrfms_mp brpts (BrFmSet.singleton BrFormulas.Ebot)) 
							else
								(mk_locbrfms_mp brpts (BrFmSet.empty)) 
						)
					 )
					 glocs_gnode
			 in  
			 (anamp, wl)
		 )
					
let string_of_brs brs =
    BrFmSet.fold
      (fun br acc -> acc ^ (if (acc="") then "" else ", ") ^
											 (string_of_br br)
			)
      brs
      ""
			
let string_of_ptbrs brsmp =
	PtsMap.fold
		(fun pt brs acc ->
		 acc ^ "\n" ^ (string_of_pt pt) ^ " -> {" ^ (string_of_brs brs) ^ "}"
		)
		brsmp
		""

let string_of_pt_ptbrs local_anamp = 
	PtsMap.fold
		(fun pt ptbrs acc ->
		 acc ^ (if acc="" then "" else "\n") ^
			 "@" ^ (string_of_pt pt) ^ "\n" ^
				 (string_of_ptbrs ptbrs) ^ "\n"
		)
		local_anamp 
		""
	
let string_of_pts_ptbrs anamp = 
	GLocsMap.fold 
		(fun pts ptbrs acc -> 
		 acc ^ (if acc="" then "" else "\n") ^
			 "@" ^ (string_of_pts pts) ^ "\n" ^ 
				 (string_of_ptbrs ptbrs) ^ "\n"
		)
		anamp
		""					

let has_succ_at gnode k = 
  let succs = gnode.gsuccs in
	List.exists (fun suc -> (List.mem k suc.procs)) succs

let localize_brana_res glocs_gnode anamp sys =
	let pts = pts_of_sys sys in
	let brpts = brpts_of_sys sys in 
	GLocsMap.fold
		(fun pts ptbrs pt_ptbrs -> 
		 let gn = GLocsMap.find pts glocs_gnode in 
		 let succ_proc_ids =
			 List.flatten
				 (List.map (fun suc -> suc.procs) gn.gsuccs) 
		 in
		 List.fold_left
			 (fun pt_ptbrs k ->
				let pt = List.nth pts k in
				let current_ptbrs = PtsMap.find pt pt_ptbrs in
				PtsMap.add pt (lub_locbrfms ptbrs current_ptbrs) pt_ptbrs 
			 )
			 pt_ptbrs 
			 succ_proc_ids
		)
		anamp 
		(List.fold_left
		   (fun pt_ptbrs pt ->
				PtsMap.add pt (mk_locbrfms_mp brpts (BrFmSet.empty)) pt_ptbrs 
			 )
		   PtsMap.empty
		   pts
		)

let brana sys =
	let (gnode0, gmap) = g_graph_of_sys sys in	
	let cnsmp = get_constraints gmap (pts_of_sys sys) in
	let (anamp0, wl0) = init gmap sys cnsmp in 
	let res = iterate cnsmp anamp0 wl0 in
	localize_brana_res gmap res sys
