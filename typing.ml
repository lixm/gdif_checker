open Utils
open Lexer
open Ast
open Parser
open Ggraph
open Eqana
open Brana
open Lvana
open Z3utils
open Asst
open Valana 

let (--) i j =
  let rec aux n acc =
    if n < i then acc else aux (n-1) (n :: acc)
  in aux j []

(* the analysis/inference of security contexts *)
type constraint_t = {ptl: pt; ptr: pt; gen: VarSet.t * VarSet.t}

let get_sc_constraints sys = 
  let rec do_get_sccnstr statement pt' cnsmp =
    match statement with 
    | SSkip pt 
		| SAssg (pt, _, _) -> 
			 let new_cns = { ptl=pt'; ptr=pt; gen=(VarSet.empty, VarSet.empty) } in
			 PtsMap.add pt (PtsMap.find pt cnsmp @ [new_cns]) cnsmp
    | SOt (pt, c, _)
		| SIn (pt, c, _) -> 
			 let new_cns = 
				 { ptl=pt'; ptr=pt; 
					 gen=(VarSet.singleton (Var (string_of_pch c)), VarSet.empty) } in 
			 PtsMap.add pt (PtsMap.find pt cnsmp @ [new_cns]) cnsmp
    | SSeq (statement1, statement2) -> 
       let cnsmp1 = do_get_sccnstr statement1 (Ast.fst statement2) cnsmp in 
       do_get_sccnstr statement2 pt' cnsmp1 
    | SIf (pt, be, statement1, statement2) ->
       let cns1 = { ptl=Ast.fst statement1; ptr=pt; gen=(VarSet.empty, fvs_b be) } in
       let cns2 = { ptl=Ast.fst statement2; ptr=pt; gen=(VarSet.empty, fvs_b be) } in 
       let cnsmp' = PtsMap.add pt (PtsMap.find pt cnsmp @ [cns1; cns2]) cnsmp in 
       let cnsmp1' = do_get_sccnstr statement1 pt' cnsmp' in 
       let cnsmp2' = do_get_sccnstr statement2 pt' cnsmp1' in
       cnsmp2'
    | SWhile (pt, be, statement) -> 
       let fstpt = Ast.fst statement in 
       let cns1 = { ptl=fstpt; ptr=pt; gen=(VarSet.empty, fvs_b be)} in 
       let cns2 = 
				 { ptl=pt'; ptr=fstpt; gen=(VarSet.empty, VarSet.empty)} in 
       let cnsmp' = PtsMap.add pt (PtsMap.find pt cnsmp @ [cns1]) cnsmp in 
       let cnsmp'' = PtsMap.add fstpt (PtsMap.find fstpt cnsmp' @ [cns2]) cnsmp' in 
       do_get_sccnstr statement fstpt cnsmp''
  in
  let empty_stmt pr statement cnsmp = 
    let pts = pts_of_stmt statement @ [Pt ("f_" ^ (string_of_prin pr))] in 
    List.fold_left 
      (fun mp pt -> PtsMap.add pt [] mp) cnsmp pts 
  in
  match sys with 
  | Sys (pr_stmts, _) -> 
     List.fold_left 
       (fun cnsmp (pr, statement) -> 
				let initialized = empty_stmt pr statement cnsmp in 
				do_get_sccnstr statement (Pt ("f_" ^ (string_of_prin pr))) initialized
       )
       PtsMap.empty
       pr_stmts
       
let eval_rhs cns pt_cs_xs = 
  let (pchs, xs) = PtsMap.find cns.ptr pt_cs_xs in 
  (VarSet.union pchs (Pervasives.fst cns.gen), 
   VarSet.union xs (Pervasives.snd cns.gen))
    
let rec iterate cnsmp resmp wl = 
  match wl with 
  | [] -> resmp 
  | cns :: wl' -> 
     let (pchs', xs') = eval_rhs cns resmp in 
     let (pchs0, xs0) = PtsMap.find cns.ptl resmp in
     if not (VarSet.subset pchs' pchs0 && VarSet.subset xs' xs0) then
       let pchs_new = VarSet.union pchs0 pchs' in 
       let xs_new = VarSet.union xs0 xs' in 
       let resmp' = PtsMap.add cns.ptl (pchs_new, xs_new) resmp in
       let wl'' = wl' @ (PtsMap.find cns.ptl cnsmp) in
       iterate cnsmp resmp' wl''
     else 
       iterate cnsmp resmp wl'

let init pts cnsmap = 
  let wl = PtsMap.fold (fun k cnslst wl -> wl @ cnslst) cnsmap [] in
  let anamp = 
    List.fold_left 
      (fun mp pt -> PtsMap.add pt (VarSet.empty, VarSet.empty) mp)
      (PtsMap.empty)
      pts
  in (anamp, wl)

let sctx_inf sys = 
  let all_pts = pts_of_sys sys in
  let cnsmp = get_sc_constraints sys in 
  let (pt_cs_xs0, wl0) = init all_pts cnsmp in 
  iterate cnsmp pt_cs_xs0 wl0

let string_of_ptcsxs pt_cs_xs = 
  PtsMap.fold 
    (fun pt (pchs, xs) acc -> 
     acc ^ "\n" ^ string_of_pt pt ^ " -> ( { " ^ 
       string_of_vars pchs ^ " }, { " ^ string_of_vars xs ^ " } )"
    )
    pt_cs_xs 
    ""	  

(* take variables not assigned policies to be bottom *)
let slub_vars polmp xs allpr = 
  let bot_plc = [{cond=BeTrue; readers=allpr}] in 
  if VarSet.is_empty xs then
		bot_plc
  else
    let plc_var x = 
      try VarMap.find x polmp with Not_found -> bot_plc in
    let min = VarSet.min_elt xs in 
    VarSet.fold 
      (fun x plc -> plc @ (plc_var x)) (VarSet.remove min xs) (plc_var min) 
      
(* whether plc1 is syntactically less than or equal to plc2 *)
let syn_ord ctx allprs plc1 plc2 = 
  let plc2' = (* apply structrual eq rule *)
    { cond=BeTrue; readers=allprs } :: { cond=BeFalse; readers=[] } :: plc2 in 
  List.for_all 
    (fun conj1 -> 
     let nrdrs = List.filter (fun pr -> not (List.mem pr conj1.readers)) allprs in
     List.for_all 
       (fun pr -> 
				List.exists 
					(fun conj2 -> 
					 (dec_impl ctx conj1.cond conj2.cond && 
							not (List.mem pr conj2.readers)))
					plc2'
       )
       nrdrs
    )
    plc1

let full_polmp vars polmp0 = 
  VarSet.fold 
    (fun x full -> 
     let plc_opt = 
       try Some (VarMap.find x polmp0) with Not_found -> None
     in VarMap.add x plc_opt full 
    )
    vars
    VarMap.empty

type subst_t = { from_vr: var; to_ae: aexp }

let subst_lst substs plc = 
  List.fold_left 
    (fun acc_plc conj -> 
     let new_cond = 
       List.fold_left 
	 (fun acc_cond subst -> subst_b acc_cond subst.from_vr subst.to_ae)
	 conj.cond
	 substs
     in acc_plc @ [{ cond=new_cond; readers=conj.readers }]
    )
    []
    plc

let subst_polmp_lst substs polmp = VarMap.map (subst_lst substs) polmp

(* ctx is a context for Z3 *)
let ord_polmp ctx vars allprs polmp1 polmp2 = 
  let dom_polmp polmp = List.map Pervasives.fst (VarMap.bindings polmp) in 
  let rel_vars = 
    List.filter 
      (fun x -> List.mem x (dom_polmp polmp1) && List.mem x (dom_polmp polmp2)) 
      vars 
  in
  let rec ord_plc ctx rel_vars allprs polmp1 polmp2 = 
    match rel_vars with 
    | [] -> true
    | x :: rel_vars' -> 
       let plc1 = VarMap.find x polmp1 in 
       let plc2 = VarMap.find x polmp2 in 
       let le_res = syn_ord ctx allprs plc1 plc2 in 
       if le_res then
         ord_plc ctx rel_vars' allprs polmp1 polmp2 
       else
				 false
  in
  ord_plc ctx rel_vars allprs polmp1 polmp2 

let fm_impl fm plc = 
  List.map 
    (fun conj -> { cond=BeAnd (fm, conj.cond); readers=conj.readers }) 
    plc

let fm_impl_polmp fm polmp = VarMap.map (fm_impl fm) polmp

(* in policy comparisons, remote variables are treated as normal variables *)
let del_rem plc = 
  let rec del_rem_a ae = 
    match ae with 
    | AeVal _ -> ae 
    | AeVar (Var vrstr) -> (
      try let k = String.index vrstr '@' in AeVar (Var (String.sub vrstr 0 k))
      with Not_found -> ae
    )
    | AePlus (ae1, ae2) -> AePlus (del_rem_a ae1, del_rem_a ae2)
    | AeMinus (ae1, ae2) -> AeMinus (del_rem_a ae1, del_rem_a ae2)
    | AeMod (ae1, ae2) -> AeMod (del_rem_a ae1, del_rem_a ae2)
    | AeFun (fn, aelst) -> AeFun (fn, List.map (fun ae -> del_rem_a ae) aelst)
  in
  let rec del_rem_b be = 
    match be with 
    | BeTrue | BeFalse -> be
    | BeEq (ae1, ae2) -> BeEq (del_rem_a ae1, del_rem_a ae2)
    | BeNEq (ae1, ae2) -> BeNEq (del_rem_a ae1, del_rem_a ae2)
    | BeNot be1 -> BeNot (del_rem_b be1)
    | BeAnd (be1, be2) -> BeAnd (del_rem_b be1, del_rem_b be2)
    | BeOr (be1, be2) -> BeOr (del_rem_b be1, del_rem_b be2)
    | BeImpl (be1, be2) -> BeImpl (del_rem_b be1, del_rem_b be2)
    | BeEx (x, be1) -> BeEx (x, del_rem_b be1)
  in
  List.map (fun conj -> { cond=del_rem_b conj.cond; readers=conj.readers }) plc

let del_rem_polmp polmp = VarMap.map (del_rem) polmp

let cvar c j = (Var (string_of_pch c ^ "." ^ string_of_int j)) 
		 
let plc_comp_chan pol_mp c aelst xs allprs = 
  List.fold_left 
    (fun mp j -> 
     let xs' = VarSet.union xs (fvs_a (List.nth aelst (j - 1))) in 
     let pol' = slub_vars pol_mp xs' allprs in 
     VarMap.add (cvar c j) pol' mp
    )
    pol_mp
    (1--(List.length aelst))

let plc_comp_var pol_mp polch_mp c xlst xs allprs = 
  List.fold_left 
    (fun mp j -> 
     let pol' = 
       (VarMap.find (cvar c j) polch_mp) @ (slub_vars pol_mp xs allprs) 
     in
     VarMap.add (List.nth xlst (j - 1)) pol' mp
    )
    pol_mp
    (1--(List.length xlst))

let uplus_polmp polmp1 polmp2 = 
  VarMap.merge 
    (fun k plc_opt1 plc_opt2 -> 
     match plc_opt1, plc_opt2 with 
     | Some plc1, Some plc2 -> 
				raise (Failure ("the domains of policy maps\n" ^ 
													string_of_polmp polmp1 ^ "\nand\n" ^ 
														string_of_polmp polmp2 ^ "\nare not disjoint"))
     | plco1, None -> plco1 
     | None, plco2 -> plco2
    )
    polmp1 polmp2

let be_sat ctx be = check_formula ctx (z3fm_of_be ctx be) 

let plc_specialize ctx plc be = 
  List.map 
    (fun conj -> 
     if (dec_impl ctx be conj.cond) then 
       { cond=BeTrue; readers=conj.readers }
     else if (not (be_sat ctx (BeAnd (be, conj.cond)))) then 
       { cond=BeFalse; readers=conj.readers }
     else
       conj
    )
    plc

let dom_polmp polmp = List.map (Pervasives.fst) (VarMap.bindings polmp)

let fvs_plc0 plc = 
  List.fold_left 
    (fun fvs conj -> VarSet.union fvs (fvs_b conj.cond))
    VarSet.empty plc

let fvs_plc plc = fvs_plc0 (del_rem plc)
			   
let polmp_specialize ctx polmp be l xs pt pt_lvs allprs = 
  let xs' = VarSet.union (PtsMap.find pt pt_lvs) xs in 
  let ex_high x = (* there exists a local high variable in the policy of x*)
    let local_plc_vars = 
      VarSet.filter 
	(fun x' -> List.mem x' (dom_polmp polmp)) 
	(fvs_plc (VarMap.find x polmp)) 
    in
    VarSet.exists 
      (fun x' -> 
       syn_ord
				 ctx allprs (l @ (slub_vars polmp xs allprs)) ((VarMap.find x' polmp)) 
      ) 
      local_plc_vars
  in
  VarMap.mapi 
    (fun x plc ->     
     if (not (VarSet.mem x xs') && ex_high x) then
       plc_specialize ctx plc be
     else
			 plc
    )
    polmp

(* pol_mp is the local variable policy environment  
    ref_vars is the set of local variables referenced in policies *)
let rec well_typed 
					ctx val_mp pt_lvs pol_mp polch_mp 
					pt_sctx statement pt' ref_vars allprs = 
  (*  let _ = print_endline ("\ntyping statement: \n" ^ string_of_stmt statement 0) in *)
  match statement with 
  | SSkip pt -> true  
  | SAssg (pt, x, ae) -> 
     let valfm = PtsMap.find pt val_mp in 
     let (pchs, xs) = PtsMap.find pt pt_sctx in 
     let l = slub_vars polch_mp pchs allprs in 
     let polmp0 = VarMap.add x (l @ slub_vars pol_mp xs allprs) pol_mp in 
     let polmp1 = fm_impl_polmp valfm polmp0 in 
     let lvs_refs = VarSet.union (PtsMap.find pt' pt_lvs) ref_vars in 
     let polmp2 = subst_polmp_lst [ {from_vr=x; to_ae=ae} ] pol_mp in 
     ord_polmp ctx (VarSet.elements lvs_refs) allprs polmp1 polmp2 
  | SOt (pt, c, aelst) -> 
     let valfm = PtsMap.find pt val_mp in 
     let (pchs, xs) = PtsMap.find pt pt_sctx in 
     let l = slub_vars polch_mp pchs allprs in 
     let polmp_xs = fm_impl valfm (slub_vars pol_mp xs allprs) in
     let prc_c = VarMap.find (Var (string_of_pch c)) polch_mp in 
     let prc_ord = syn_ord ctx allprs (l @ polmp_xs) prc_c in 
     if not prc_ord then
       false 
     else
       let ar = List.length aelst in 
       let polmp0 = plc_comp_chan pol_mp c aelst xs allprs in 
       let polmp1 = fm_impl_polmp valfm polmp0 in 
       let polmp_uplus = uplus_polmp pol_mp polch_mp in 
       let asubst j = { from_vr=cvar c j; to_ae=List.nth aelst (j-1) } in
       let polmp2 = subst_polmp_lst (List.map asubst (1--ar)) polmp_uplus in 
       let lvs_refs = VarSet.union (PtsMap.find pt' pt_lvs) ref_vars in 
       let lvs_refs_chs = 
				 List.fold_left (fun acc j -> VarSet.add (cvar c j) acc) lvs_refs (1--ar) 
       in
       (*       if pt = Pt "l10" then 
	 print_endline ("polmp1:\n" ^ string_of_polmp polmp1 ^ "\npolmp2:\n" ^ string_of_polmp polmp2 ^ 
		       "\n\nvariables concerned:\n" ^ string_of_vars lvs_refs_chs ^ "\nlemmas:\n" ^ 
		       string_of_belst lems); *)
       ord_polmp ctx (VarSet.elements lvs_refs_chs) allprs polmp1 polmp2 
  | SIn (pt, c, xlst) -> 
     let valfm = PtsMap.find pt val_mp in 
     let (pchs, xs) = PtsMap.find pt pt_sctx in 
     let l = slub_vars polch_mp pchs allprs in 
     (*     if pt = Pt "l7" then print_endline (string_of_policy (del_rem (fm_impl valfm (slub_vars pol_mp xs allprs))));  *)
     let polmp_xs = fm_impl valfm (slub_vars pol_mp xs allprs) in
     let prc_c = VarMap.find (Var (string_of_pch c)) polch_mp in 
     let prc_ord = syn_ord ctx allprs (l @ polmp_xs) prc_c in 
     if not prc_ord then
       false 
     else 
       let ar = List.length xlst in 
       let polmp0 = plc_comp_var pol_mp polch_mp c xlst xs allprs in 
       let polmp1 = fm_impl_polmp valfm polmp0 in 
       let asubst j = { from_vr=List.nth xlst (j-1); to_ae=(AeVar (cvar c j)) } in
       let polmp2 = subst_polmp_lst (List.map asubst (1--ar)) pol_mp in
       let lvs_refs = VarSet.union (PtsMap.find pt' pt_lvs) ref_vars in 
       ord_polmp ctx (VarSet.elements lvs_refs) allprs polmp1 polmp2  
  | SSeq (statement1, statement2) -> 
     let wt1 = 
       well_typed ctx val_mp pt_lvs pol_mp polch_mp 
									pt_sctx statement1 (Ast.fst statement2) ref_vars allprs in 
     if not wt1 then
       false 
     else 
       well_typed ctx val_mp pt_lvs pol_mp polch_mp 
									pt_sctx statement2 pt' ref_vars allprs 
  | SIf (pt, be, statement1, statement2) -> 
     let (pchs', xs') = PtsMap.find pt' pt_sctx in 
     let l' = slub_vars polch_mp pchs' allprs in 
     let polmp1 = polmp_specialize ctx pol_mp be l' xs' pt' pt_lvs allprs in 
     (*     let _ = print_endline ("refined policy mapping \n" ^ string_of_polmp polmp1) in  *)
     let wt1 = 
       well_typed ctx val_mp pt_lvs polmp1 polch_mp 
									pt_sctx statement1 pt' ref_vars allprs 
		 in 
     if not wt1 then
       false
     else 
       let polmp2 =
				 polmp_specialize ctx pol_mp (BeNot be) l' xs' pt' pt_lvs allprs 
       in 
       well_typed ctx val_mp pt_lvs polmp2 polch_mp 
									pt_sctx statement2 pt' ref_vars allprs 
  | SWhile (pt, be, statement) -> 
     let (pchs', xs') = PtsMap.find (Ast.fst statement) pt_sctx in 
     let l = slub_vars polch_mp pchs' allprs in 
     let polmp' = polmp_specialize ctx pol_mp be l xs' pt' pt_lvs allprs in
     well_typed ctx val_mp pt_lvs polmp' polch_mp 
								pt_sctx statement pt ref_vars allprs 

let all_vars (Sys (prstmts, _)) = 
  List.fold_left 
    (fun acc sym_tb -> VarSet.union acc sym_tb.vars)
    VarSet.empty
    (List.map (fun (pr, statement) -> symtb_of_stmt statement) prstmts)

let all_cvars sys = 
  match sys with 
  | (Sys (prstmts, _)) ->
     let all_pchs = 
       List.fold_left 
				 (fun acc sym_tb -> PChSet.union acc sym_tb.pchs)
				 PChSet.empty 
				 (List.map (fun (pr, statement) -> symtb_of_stmt statement) prstmts)
     in
     PChSet.fold 
       (fun pch acc -> 
				let vs1 = VarSet.add (Var (string_of_pch pch)) acc in
				let ar_pch = PChMap.find pch (armp_of_sys sys) in 
				List.fold_left 
					(fun acc j -> VarSet.add (cvar pch j) acc) vs1 (1--ar_pch)
       )
       all_pchs VarSet.empty

let polmp_complete polmp all_vars all_cvars allprs = 
  let bot_plc = [ { cond=BeTrue; readers=allprs } ] in 
  VarSet.fold  
    (fun vr mp -> 
     if not (VarMap.mem vr mp) then
       VarMap.add vr bot_plc mp 
     else mp
    )
    (VarSet.union all_vars all_cvars) polmp 

let get_ref_vars polmp = 
  VarMap.fold 
    (fun vr plc acc -> VarSet.union acc (fvs_plc plc)) polmp VarSet.empty

let var_updpts (Sys (prstmts, _)) all_vars = 
  let rec get_upd_pt statement var_pts = 
    match statement with 
    | SSkip _ -> var_pts
    | SAssg (pt, x, _) -> 
       let orig_pts = VarMap.find x var_pts in 
       VarMap.add x (PtSet.add pt orig_pts) var_pts
    | SOt _ -> var_pts
    | SIn (pt, _, xlst) -> 
       List.fold_left 
				 (fun acc x -> VarMap.add x (PtSet.add pt (VarMap.find x acc)) acc)
				 var_pts xlst
    | SSeq (stmt1, stmt2) 
		| SIf (_, _, stmt1, stmt2) ->
			 ((get_upd_pt stmt1 var_pts) |> (get_upd_pt stmt2)) 
    | SWhile (_, _, statement) -> get_upd_pt statement var_pts
  in
  List.fold_left 
    (fun var_pts (_, statement) -> get_upd_pt statement var_pts)
    (VarSet.fold 
       (fun x var_pts -> VarMap.add x (PtSet.empty) var_pts)
       all_vars
       VarMap.empty)
    prstmts

let is_remote (Var vrstr) = String.contains vrstr '@'
let vr_of_remvar (Var vrstr) = 
  let k = String.index vrstr '@' in (Var (String.sub vrstr 0 k))

let vrset_fr_lst xlst = List.fold_right VarSet.add xlst VarSet.empty 

let no_upd sys pt_lvs polmp gmp all_vars = 
  let var_pts = var_updpts sys all_vars in 
  GLocsMap.for_all 
    (fun ptlst _ -> 
     List.for_all 
       (fun pt -> 
				let lvs_pt = PtsMap.find pt pt_lvs in 
				let fvs = 
					VarSet.fold 
						(fun x acc -> 
						 let fvs = fvs_plc0 (VarMap.find x polmp) in 
						 let remote_fvs = VarSet.elements (VarSet.filter is_remote fvs) in
						 let rem_fvs = List.map vr_of_remvar remote_fvs in 
						 VarSet.union acc (vrset_fr_lst rem_fvs))
						lvs_pt
						VarSet.empty
				in
				VarSet.for_all 
					(fun x' -> 
					 let pts_of_upd = VarMap.find x' var_pts in 
					 List.for_all 
						 (fun pt' -> pt' = pt || (not (PtSet.mem pt' pts_of_upd))) ptlst
					)
					fvs
       )
       ptlst
    )
    gmp

let shared_prs plc = 
  List.fold_left 
    (fun acc conj -> List.filter (fun pr -> List.mem pr conj.readers) acc)
    (List.hd plc).readers (List.tl plc)
  
let nshared_prs plc allprs = 
  List.filter (fun pr -> not (List.mem pr (shared_prs plc))) allprs

let nip pol_mp_full allprs = 
  VarMap.for_all 
    (fun vr plc -> 
     let nshared = nshared_prs plc allprs in 
     List.for_all 
       (fun nsh_pr -> 
				let fvs = fvs_plc0 plc in 
				List.for_all
					(fun fv -> 
					 let plc_fv = VarMap.find fv pol_mp_full in 
					 List.mem nsh_pr (shared_prs plc_fv)
					)
					(VarSet.elements fvs)
       )
       nshared
    )
    pol_mp_full

let well_typed_sys
			ctx gmp pt_eqs pt_pt_brs pt_cond pt_lvs polmp_in sys allprs 
  =
  let pt_sctx = sctx_inf sys in 
  let all_vars = all_vars sys in 
  let all_cvars = all_cvars sys in 
  let polmp_full = polmp_complete polmp_in all_vars all_cvars allprs in 
  let (polmp_var, polmp_ch) = 
    VarMap.partition (fun vr _ -> VarSet.mem vr all_vars) polmp_full 
  in
	let val_mp = get_val_fm_map pt_eqs pt_pt_brs pt_cond in 
  if not (no_upd sys pt_lvs polmp_var gmp all_vars) then
		false 
  else 
    let (polmp_var', polmp_ch') = 
      (del_rem_polmp polmp_var, del_rem_polmp polmp_ch) 
    in 
    if not (nip (uplus_polmp polmp_var' polmp_ch') allprs) then
			false
    else
      let ref_vars = get_ref_vars polmp_full in
      match sys with 
      | Sys (prstmts, _) -> 
				 List.for_all 
					 (fun (pr, statement) -> 
						let local_vars = fvs_stmt statement in 
						let pol_mp = 
							VarMap.filter (fun vr _ -> VarSet.mem vr local_vars) polmp_var'
						in
						let local_ref_vars = VarSet.inter ref_vars local_vars in 
						well_typed ctx val_mp pt_lvs pol_mp polmp_ch' 
											 pt_sctx statement (Pt ("f_" ^ (string_of_prin pr))) 
											 local_ref_vars allprs 
					 )
					 prstmts

