open Utils
			 
type sys = 
  | Sys of ((prin * stmt) list) * (pch list)
 and prin = 
   | Prin of string
 and stmt = 
   | SSkip of pt 
   | SAssg of pt * var * aexp
   | SOt of pt * pch * (aexp list)
   | SIn of pt * pch * (var list)
   | SSeq of stmt * stmt
   | SIf of pt * bexp * stmt * stmt
   | SWhile of pt * bexp * stmt
 and var = 
   | Var of string
 and pch = 
   | PCh of string
 and aexp = 
   | AeVal of int
   | AeVar of var
   | AePlus of aexp * aexp
   | AeMinus of aexp * aexp
   | AeMod of aexp * aexp
   | AeFun of string * (aexp list)
 and bexp = 
   | BeTrue 
   | BeFalse 
   | BeEq of aexp * aexp
   | BeNEq of aexp * aexp
   | BeNot of bexp
   | BeAnd of bexp * bexp
   | BeOr of bexp * bexp
   | BeImpl of bexp * bexp 
   | BeEx of (var * bexp)
							 
let string_of_pts pts =
	match pts with
	| [] -> ""
	| pt :: pts' -> (List.fold_left
										 (fun acc pt -> acc ^ ";" ^ (string_of_pt pt))
										 (string_of_pt pt)
										 pts')	

let string_of_var (Var vrstr) = vrstr
let string_of_pch (PCh cstr) = cstr 

module Vars = 
  struct 
    type t = var 
    let compare var1 var2 = 
      Pervasives.compare (string_of_var var1) (string_of_var var2)
  end

module VarSet = Set.Make(Vars)

module PChs = 
  struct
    type t = pch 
    let compare pch1 pch2 = 
      Pervasives.compare (string_of_pch pch1) (string_of_pch pch2)
  end

module PChSet = Set.Make(PChs)

type sym_tb_t = { vars: VarSet.t; pchs: PChSet.t }

module PChMap = Map.Make(PChs)

let rec fvs_a ae = 
  match ae with 
  | AeVal _ -> VarSet.empty
  | AeVar x -> VarSet.singleton x
  | AePlus (a1, a2) | AeMinus (a1, a2) | AeMod (a1, a2) -> 
					  VarSet.union (fvs_a a1) (fvs_a a2)
  | AeFun (fname, alst) -> 
     List.fold_left 
       (fun acc ae -> VarSet.union acc (fvs_a ae)) VarSet.empty alst

let rec fvs_b be = 
  match be with 
   | BeTrue | BeFalse -> VarSet.empty 
   | BeEq (ae1, ae2) | BeNEq (ae1, ae2) -> 
      VarSet.union (fvs_a ae1) (fvs_a ae2)
   | BeNot be' -> fvs_b be'
   | BeAnd (be1, be2) | BeOr (be1, be2) | BeImpl (be1, be2) -> 
      VarSet.union (fvs_b be1) (fvs_b be2)
   | BeEx (x, be') ->  VarSet.filter (fun x' -> x' <> x) (fvs_b be')

let rec fvs_stmt = function 
  | SSkip _ -> VarSet.empty
  | SAssg  (_, x, ae) -> VarSet.add x (fvs_a ae)
  | SOt (_, _, aelst) ->
     List.fold_left
       (fun acc ae -> VarSet.union acc (fvs_a ae)) VarSet.empty aelst
  | SIn (_, _, xlst) -> List.fold_right VarSet.add xlst VarSet.empty
  | SSeq (statement1, statement2) ->
     VarSet.union (fvs_stmt statement1) (fvs_stmt statement2)
  | SIf (_, be, statement1, statement2) ->
     let fvs1 = fvs_stmt statement1 in
     let fvs2 = fvs_stmt statement2 in
     VarSet.union (fvs_b be) (VarSet.union fvs1 fvs2)
  | SWhile (_, be, statement) ->
     VarSet.union (fvs_b be) (fvs_stmt statement)		 

let rec simplify_be be =
	match be with
	| BeTrue | BeFalse -> be
	| BeEq (ae1, ae2) ->
		 if ae1 = ae2 then BeTrue else be
	| BeNEq (ae1, ae2) ->
		 if ae1 = ae2 then BeFalse else be 
	| BeNot be' ->
		 (
			 match simplify_be be' with 
			 | BeTrue -> BeFalse
			 | BeFalse -> BeTrue
			 | _ -> BeNot (simplify_be be') 
		 )
	| BeAnd (be1, be2) ->
		 let simp_be1 = simplify_be be1 in
		 let simp_be2 = simplify_be be2 in 
		 if simp_be1 = BeFalse || simp_be2 = BeFalse then
			 BeFalse
		 else if simp_be1 = BeTrue then
			 simp_be2
		 else if simp_be2 = BeTrue then
			 simp_be1
		 else
			 BeAnd (simp_be1, simp_be2) 
	| BeOr (be1, be2) ->
		 let simp_be1 = simplify_be be1 in
		 let simp_be2 = simplify_be be2 in 		 
		 if simp_be1 = BeTrue || simp_be2 = BeTrue then
			 BeTrue
		 else if simp_be1 = BeFalse then
			 simp_be2
		 else if simp_be2 = BeFalse then
			 simp_be1
		 else
			 BeOr (simp_be1, simp_be2) 
	| BeImpl (be1, be2) ->
		 let simp_be1 = simplify_be be1 in
		 let simp_be2 = simplify_be be2 in 	
		 if simp_be1 = BeFalse then
			 BeTrue
		 else if simp_be1 = BeTrue then 
			 simp_be2 
		 else 
			 BeImpl (simp_be1, simp_be2) 
	| BeEx (x, be') -> 
		 let simp_be' = simplify_be be' in 
		 if not (VarSet.mem x (fvs_b simp_be')) then 
			 simp_be' 
		 else
			 BeEx (x, simp_be') 
	
let rec symtb_of_stmt statement = 
  match statement with 
  | SSkip _ -> { vars=VarSet.empty; pchs=PChSet.empty } 
  | SAssg (_, x, ae) -> 
     { vars=VarSet.union (VarSet.singleton x) (fvs_a ae); pchs=PChSet.empty}
  | SOt (_, c, aelst) -> 
     { vars=List.fold_left (VarSet.union) (VarSet.empty) (List.map fvs_a aelst);
       pchs=PChSet.singleton c }
  | SIn (_, c, xlst) ->
     { vars=List.fold_right VarSet.add xlst VarSet.empty;
       pchs=PChSet.singleton c }
  | SSeq (statement1, statement2) ->
     let symtb1 = symtb_of_stmt statement1 in 
     let symtb2 = symtb_of_stmt statement2 in 
     { vars=VarSet.union symtb1.vars symtb2.vars; 
       pchs=PChSet.union symtb1.pchs symtb2.pchs }
  | SIf (_, be, statement1, statement2) -> 
     let symtb1 = symtb_of_stmt statement1 in 
     let symtb2 = symtb_of_stmt statement2 in 
     { vars=VarSet.union (fvs_b be) (VarSet.union symtb1.vars symtb2.vars);
       pchs=PChSet.union symtb1.pchs symtb2.pchs }
  | SWhile (_, be, statement) ->
     let symtb = symtb_of_stmt statement in 
     { vars=VarSet.union (fvs_b be) symtb.vars; pchs=symtb.pchs }

let string_of_vars vars = 
  VarSet.fold (fun x acc -> string_of_var x ^ " " ^ acc) vars ""
let string_of_pchs pchs = 
  PChSet.fold (fun c acc -> string_of_pch c ^ " " ^ acc) pchs ""
let string_of_symtb { vars=vars; pchs=pchs } = 
  "variables: \n" ^ string_of_vars vars ^ "\n" ^ 
  "polyadic channels: \n" ^ string_of_pchs pchs

let raise_ar_err c = 
  raise (Failure 
	   ("channel " ^ (string_of_pch c) ^ 
	      " is used with different polarities"))

let armp_of_pchs statement = 
  let check_upd ar c mp = 
    try 
      let ar' = PChMap.find c mp in 
      if ar <> ar' then raise_ar_err c else mp
    with Not_found -> PChMap.add c ar mp
  in				    
  let rec get_armp statement mp = 
    match statement with 
    | SSkip _ -> mp
    | SAssg (_, x, ae) -> mp
    | SOt (_, c, aelst) -> 
       let ar = List.length aelst in check_upd ar c mp
    | SIn (_, c, xlst) -> 
       let ar = List.length xlst in check_upd ar c mp
    | SSeq (statement1, statement2) -> 
       let mp1 = get_armp statement1 mp in get_armp statement2 mp1
    | SIf (_, _, statement1, statement2) -> 
       let mp1 = get_armp statement1 mp in get_armp statement2 mp1
    | SWhile (_, _, statement') -> get_armp statement' mp 
  in
  get_armp statement (PChMap.empty)

let armp_of_sys (Sys (prstmts, _)) = 
  List.fold_left 
    (fun acc (pr, statement) -> 
     let new_mp = armp_of_pchs statement in 
     PChMap.merge 
       (fun c ar1_opt ar2_opt -> 
	match ar1_opt, ar2_opt with 
	| Some ar1, Some ar2 -> if ar1 = ar2 then ar1_opt else raise_ar_err c
	| Some ar1, None -> ar1_opt 
	| None, Some ar2 -> ar2_opt 
	| _ -> ar1_opt
       )
       acc new_mp
    )
    PChMap.empty
    prstmts

let rec pts_of_stmt statement = (
  match statement with 
  | SSkip loc -> [loc] 
  | SAssg (loc, _, _) -> [loc]
  | SOt (loc, _, _) -> [loc]
  | SIn (loc, _, _) -> [loc]
  | SSeq (statement1, statement2) ->
     pts_of_stmt statement1 @ pts_of_stmt statement2
  | SIf (loc, _, statement1, statement2) -> 
     loc :: pts_of_stmt statement1 @ pts_of_stmt statement2
  | SWhile (loc, _, statement) -> loc :: pts_of_stmt statement
)

let ptslst_of_sys (Sys (prstmt_lst, _)) = 
  List.map (fun (pr, statement) -> pts_of_stmt statement) prstmt_lst 

let string_of_prin pr = match pr with | Prin prstr -> prstr 

(* give list of all program points in given system, incl. 
   the final program points *) 
let pts_of_sys (Sys (prstmt_lst, _)) = 
  (List.map 
     (fun (pr, statement) -> 
      pts_of_stmt statement @[(Pt ("f_" ^ (string_of_prin pr)))])
     prstmt_lst) |> 
    List.concat 

let rec fst statement = 
  match statement with 
  | SSkip pt -> pt
  | SAssg (pt, x, ae) -> pt
  | SOt (pt, c, aelst) -> pt
  | SIn (pt, c, xlst) -> pt
  | SSeq (statement1, _) -> fst statement1
  | SIf (pt, _, _, _) -> pt
  | SWhile (pt, _, _) -> pt
				     
let make_indent n = 
  let rec make_indent' m acc = 
    if m = 0 then acc else make_indent' (m - 1) (acc ^ " ")
  in make_indent' n ""

let rec string_of_aexp ae = 
  match ae with 
  | AeVal n -> string_of_int n 
  | AeVar vr -> string_of_var vr 
  | AePlus (ae1, ae2) -> (string_of_aexp ae1) ^ " + " ^ (string_of_aexp ae2)
  | AeMinus (ae1, ae2) -> (string_of_aexp ae1) ^ " - " ^ (string_of_aexp ae2)
  | AeMod (ae1, ae2) -> (string_of_aexp ae1) ^ " % " ^ (string_of_aexp ae2)
  | AeFun (fname, aelst) -> fname ^ "(" ^ string_of_aelst aelst ^ ")"
and string_of_aelst aelst = 
  List.fold_left 
    (fun acc e -> acc ^ ", " ^ (string_of_aexp e)) 
    (string_of_aexp (List.hd aelst)) 
    (List.tl aelst)

let rec string_of_bexp be = 
  match be with 
  | BeTrue -> "true" 
  | BeFalse -> "false"
  | BeEq (ae1, ae2) -> string_of_aexp ae1 ^ " = " ^ string_of_aexp ae2
  | BeNEq (ae1, ae2) -> string_of_aexp ae1 ^ " != " ^ string_of_aexp ae2
  | BeNot be' -> "not " ^ string_of_bexp be' 
  | BeAnd (be1, be2) -> string_of_bexp be1 ^ " and " ^ string_of_bexp be2 
  | BeOr (be1, be2) -> string_of_bexp be1 ^ " or " ^ string_of_bexp be2
  | BeImpl (be1, be2) -> string_of_bexp be1 ^ " => " ^ string_of_bexp be2 
  | BeEx (x, be) -> "exists " ^ string_of_var x ^ ":" ^ string_of_bexp be

let rec string_of_be_paren be = 
  match be with 
  | BeTrue -> "true" 
  | BeFalse -> "false"
  | BeEq (ae1, ae2) -> "(" ^ string_of_aexp ae1 ^ " = " 
											 ^ string_of_aexp ae2 ^ ")"
  | BeNEq (ae1, ae2) -> "(" ^ string_of_aexp ae1 ^ " != "
												^ string_of_aexp ae2 ^ ")"
  | BeNot be' -> "(not " ^ string_of_be_paren be' ^ ")"
  | BeAnd (be1, be2) -> "(" ^ string_of_be_paren be1 ^ " and "
												^ string_of_be_paren be2 ^ ")"
  | BeOr (be1, be2) -> "(" ^ string_of_be_paren be1 ^ " or "
											 ^ string_of_be_paren be2 ^ ")"
  | BeImpl (be1, be2) -> "(" ^ string_of_be_paren be1 ^ " => "
												 ^ string_of_be_paren be2 ^ ")"
  | BeEx (x, be) -> "(" ^ "exists " ^ string_of_var x ^ ":"
										^ string_of_be_paren be ^ ")"

let string_of_belst belst = 
  if List.length belst = 0 
  then ""
  else
    List.fold_left 
      (fun acc e -> acc ^ ", " ^ (string_of_bexp e))
      (string_of_bexp (List.hd belst))
      (List.tl belst) 

let string_of_vrlst vrlst sep =
  List.fold_left 
    (fun acc e -> acc ^ sep ^ (string_of_var e)) 
    (string_of_var (List.hd vrlst)) 
    (List.tl vrlst)
    
let rec string_of_stmt statement indent = 
  let idt = (make_indent indent) in 
  match statement with 
  | SSkip (Pt ptstr) -> idt ^ ptstr ^ " skip"
  | SAssg (Pt ptstr, Var vrstr, ae)-> 
     idt ^ ptstr ^ " " ^ vrstr ^ " := " ^ (string_of_aexp ae)
  | SOt (Pt ptstr, PCh pchstr, aelst) -> 
     idt ^ ptstr ^ " " ^ "send(" ^ pchstr ^ ", " ^ (string_of_aelst aelst) ^ ")"
  | SIn (Pt ptstr, PCh pchstr, vrlst) ->
     idt ^ ptstr ^ " " ^ "recv(" ^ pchstr ^ ", " ^ (string_of_vrlst vrlst ", ") ^ ")"
  | SSeq (statement1, statement2) ->
     string_of_stmt statement1 indent ^ ";\n" ^ string_of_stmt statement2 indent
  | SIf (Pt ptstr, be, statement1, statement2) ->
     idt ^ ptstr ^ " if " ^ (string_of_bexp be) ^ "\n" ^ 
       idt ^ "  then \n" ^ (string_of_stmt statement1 (2 * indent)) ^ "\n" ^ 
	 idt ^ "  else \n" ^ (string_of_stmt statement2 (2 * indent)) ^ "\n" ^ 
	   idt ^ " fi"
  | SWhile (Pt ptstr, be, statement) -> 
     idt ^ ptstr ^ " while " ^ (string_of_bexp be) ^ " do\n" ^ 
       (string_of_stmt statement (2 * indent)) ^ "\n" ^ idt ^ " od"

let rec string_of_pchlst pchs = 
  List.fold_left (fun acc pchan -> acc^" "^(string_of_pch pchan)) 
		 (string_of_pch (List.hd pchs)) (List.tl pchs)
		 
let string_of_sys sys indent = 
  let rec string_of_procs l indent = (
    match l with 
    | (pr, statement) :: l' -> 
       let opt_par = (if l' = [] then "\n" else "\n||\n") in 
       (make_indent indent) ^
	 (string_of_prin pr) ^ ":" ^ "\n" ^
	   (string_of_stmt statement indent) ^ opt_par ^
	     (string_of_procs l' indent)
    | _ -> ""
  ) in 
  match sys with 
  | Sys (l, ichs) -> 
     "internal " ^ (string_of_pchlst ichs) ^ "\n\n" ^ (string_of_procs l indent)	       
