open Utils
open Lexer
open Ast
open Parser 

type full_act = 
  | FASkip 
  | FAAssg of (var * aexp)
  | FAOt of (pch * (aexp list))
  | FAIn of (pch * (var list))
  | FABrt 
  | FABrf 

type succ_tup = pt * full_act * pt

let rec l_succ statement fpt =
  match statement with 
  | SSkip pt -> [(pt, FASkip, fpt)]
  | SAssg (pt, x, ae) -> [(pt, FAAssg (x, ae), fpt)]
  | SOt (pt, c, aelst) -> [(pt, FAOt (c, aelst), fpt)]
  | SIn (pt, c, xlst) -> [(pt, FAIn (c, xlst), fpt)]
  | SSeq (statement1, statement2) -> 
     (l_succ statement1 (fst statement2)) @ (l_succ statement2 fpt)
  | SIf (pt, b, statement1, statement2) -> 
     [(pt, FABrt, fst statement1); (pt, FABrf, fst statement2)] @ 
       (l_succ statement1 fpt) @ (l_succ statement2 fpt)
  | SWhile (pt, b, statement) -> 
     [(pt, FABrt, fst statement); (pt, FABrf, fpt)] @ (l_succ statement pt)
	       
let string_of_act f_act = 
  match f_act with 
  | FASkip -> "skip"
  | FAAssg (x, ae) -> string_of_var x ^ " <- " ^ string_of_aexp ae
  | FAOt (PCh cstr, aelst) -> cstr ^ "!" ^ "(" ^ (string_of_aelst aelst) ^ ")"
  | FAIn (PCh cstr, vrlst) -> cstr ^ "?" ^ "(" ^ (string_of_vrlst vrlst ", ") ^ ")"
  | FABrt -> "brt" 
  | FABrf -> "brf"

let string_of_lsucc lsuccs = 
  let string_of_lsucc_tup (pt, act, pt') = 
    "(" ^ (string_of_pt pt) ^ ", " ^ (string_of_act act) ^ ", " ^ (string_of_pt pt') 
  in 
  List.fold_left 
    (fun acc tup -> acc ^ "\n" ^ string_of_lsucc_tup tup)
    (string_of_lsucc_tup (List.hd lsuccs))
    (List.tl lsuccs)
    
type g_node = { glocs: pt list; mutable gsuccs: g_succ list }
 and g_succ = { acts: full_act list; procs: int list; gsucc: g_node }

let string_of_acts actlst = 
  List.fold_left 
    (fun acc act -> acc ^ ", " ^ (string_of_act act)) 
    (string_of_act (List.hd actlst))
    (List.tl actlst)
    
module PtLists =
  struct
    type t = pt list
    let rec compare ptlst1 ptlst2 =
      match ptlst1 with 
      | [] -> if ptlst2 = [] then 0 else -1 
      | pt1 :: ptlst1' -> (
				match ptlst2 with 
				| [] -> 1
				| pt2 :: ptlst2' -> 
					 let c = Pts.compare pt1 pt2 in 
					 if c <> 0 then c else compare ptlst1' ptlst2'
      )
  end

module GLocsMap = Map.Make(PtLists) 

let string_of_glocs glocs = 
  List.fold_left 
    (fun acc (Pt ptstr) -> acc ^ ", " ^ ptstr) 
    (string_of_pt (List.hd glocs)) (List.tl glocs)
    
let string_of_intlst ints = 
  List.fold_left 
    (fun acc i -> acc ^ ", " ^ (string_of_int i)) 
    (string_of_int (List.hd ints))	(List.tl ints)

(* get the ggraph in the DOT format *) 
let string_of_g_graph gnode = 
  let rec string_of_gnodes gnode acc_nodes acc_edges visited i =
    let glocs_str = string_of_glocs gnode.glocs in
    List.fold_left 
      (fun (acc_nodes', acc_edges', visited', j) suc ->
       try 
				 let k = GLocsMap.find (suc.gsucc.glocs) visited' in 
				 let edge = 
					 "n" ^ (string_of_int i) ^ " -> " ^ "n" ^ (string_of_int k) ^ " [label=\"" ^ 
						 string_of_acts suc.acts ^ " # " ^ string_of_intlst suc.procs ^ "\"];"  
				 in 
				 (acc_nodes', acc_edges' ^ "\n" ^ edge, visited', j)
       with Not_found -> 
				 let edge = 
					 "n" ^ (string_of_int i) ^ " -> " ^ "n" ^ (string_of_int (j + 1)) ^ " [label=\"" ^ 
						 string_of_acts suc.acts ^ " # " ^ string_of_intlst suc.procs ^ "\"];"  
				 in
				 string_of_gnodes 
					 (suc.gsucc) 
					 acc_nodes'
					 (acc_edges' ^ "\n" ^ edge)
					 (GLocsMap.add suc.gsucc.glocs (j + 1) visited') 
					 (j + 1)
      )
      (acc_nodes ^ "\n" ^ "n" ^ (string_of_int i) ^ " [label=\"" ^ glocs_str ^ "\"];", 
       acc_edges, 
       visited, 
       i)
      gnode.gsuccs
  in  
  let glmap0 = GLocsMap.(empty |> add gnode.glocs 0) in 
  "digraph G {\n" ^ 
    "size = \"7.5, 12\";\n" ^ 
      (let (str, str', _, num') = 
				 (string_of_gnodes gnode ("") ("") (glmap0) 0) in str ^ str') ^
				"\n}"

(* gnode is the predecessor *)
let upd_graph gmap gnode acts procs glocs = 
  try 
    let gnode' = GLocsMap.find glocs gmap in 
    gnode.gsuccs <- 
      gnode.gsuccs @ [{ acts = acts; procs = procs; gsucc = gnode' }]; 
    (true, gmap, gnode')
  with 
    Not_found ->
    let gnode' = { glocs = glocs; gsuccs = [] } in
    gnode.gsuccs <-
      gnode.gsuccs @ [{ acts = acts; procs = procs; gsucc = gnode' }]; 
    (false, GLocsMap.add glocs gnode' gmap, gnode')
      
let rec succ_from lsucc pt = 
  match lsucc with 
  | (pt', act, pt'') :: lsucc' -> 
     if pt = pt' 
     then ([(act, pt'')] @ (succ_from lsucc' pt))
     else succ_from lsucc' pt
  | [] -> []

let rec upd_lst l i e = 
  match l with 
  | e' :: l' -> 
     if i = 0 then e :: l' else e' :: (upd_lst l' (i - 1) e)
  | [] -> raise (Failure "index out of bound in list update")    

(* lsuccs is a list of process-local successor relations *)
let rec get_g_graph ichs gmap gnode lsuccs glocs = 
  let all_locs = gnode.glocs in 
  if glocs = [] 
  then gmap 
  else
    (* i is index of first element of glocs in all_locs *)
    let i = (List.length all_locs - List.length glocs) in 
    let act_pt'_lst = succ_from (List.nth lsuccs i) (List.hd glocs) in 
    let upd_one gmp act pt' = 
      let (mapped, newmap, gnode') = 
				upd_graph gmp gnode [act] [i] (upd_lst all_locs i pt') 
      in 
      if not mapped 
      then get_g_graph ichs newmap gnode' lsuccs gnode'.glocs
      else gmp
    in
    let upd_two gmp act1 act2 pt1 pt2 j = 
      let (mapped, newmap, gnode') = 
				upd_graph gmp gnode [act1; act2] [i; j] 
									(upd_lst (upd_lst all_locs i pt1) j pt2)
      in
      if not mapped 
      then (j + 1, get_g_graph ichs newmap gnode' lsuccs gnode'.glocs)
      else (j + 1, gmp)
    in
    let gmap' = 
      List.fold_left 
				(fun gmp (act, pt') ->
				 match act with 
				 | FASkip | FAAssg (_, _) | FABrt | FABrf  -> upd_one gmp act pt' 
				 | FAOt (c, _) when (not (List.mem c ichs)) -> upd_one gmp act pt'
				 | FAIn (c, _) when (not (List.mem c ichs)) -> upd_one gmp act pt'
				 | FAOt (c, aelst) ->
						let (i_res, gmp_res) = 
							List.fold_left 
								(fun (j, gmp') pt'' -> 
								 let act_pt'_lst' = succ_from (List.nth lsuccs j) pt'' in 
								 if (List.length act_pt'_lst' = 1) 
								 then
									 let (act', pt''') = (List.hd act_pt'_lst') in 
									 match act' with 
									 | FAIn (c', _) when c' = c -> upd_two gmp' act act' pt' pt''' j
									 | _ -> (j + 1, gmp')
								 else (j + 1, gmp')
								)
								(i + 1, gmp)
								(List.tl glocs)
						in gmp_res
				 | FAIn (c, vrlst) ->
						let (i_res, gmp_res) = 
							List.fold_left 
								(fun (j, gmp') pt'' ->
								 let act_pt'_lst' = succ_from (List.nth lsuccs j) pt'' in 
								 if (List.length act_pt'_lst' = 1)
								 then
									 let (act', pt''') = (List.hd act_pt'_lst') in
									 match act' with 
									 | FAOt (c', _) when c' = c -> upd_two gmp' act act' pt' pt''' j
									 | _ -> (j + 1, gmp')
								 else (j + 1, gmp')
								)
								(i + 1, gmp)
								(List.tl glocs)
						in gmp_res
				)
				gmap
				act_pt'_lst
    in get_g_graph ichs gmap' gnode lsuccs (List.tl glocs)
		   
let g_graph_of_sys sys = 
  let gnode_init (Sys (lst, ichs)) = {
      glocs = 
				List.map (fun e -> match e with | (_, statement) -> fst statement) lst;
      gsuccs = []
    } 
  in 
  let gnode0 = gnode_init sys in 
  let gmap0 = GLocsMap.(empty |> add gnode0.glocs gnode0) in
  match sys with
  |  (Sys (lst, ichs)) -> 
      let lsuccs = 
				List.map 
					(fun (pr, statement) -> 
					 l_succ statement (Pt ("f_" ^ (string_of_prin pr))))
					lst 
      in
      (gnode0, get_g_graph ichs gmap0 gnode0 lsuccs gnode0.glocs)

