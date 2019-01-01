open Utils
open Lexer
open Ast

let string_of_tklst (l : token list) = 
  List.fold_left (fun acc tk -> acc ^ (string_of_tk tk) ^ " ") "" l 

exception Parsing_error of string

let raise_parse_err sc tk tklst_exp = 
  raise (Parsing_error 
	   ("encountering " ^ (string_of_tk tk) ^ 
	      " while expecting token in " ^ (string_of_tklst tklst_exp) ^
		"on line " ^ (string_of_int sc.stm.line_num)))
		
let match_token sc tk tklst = 
  if (List.mem tk tklst) then () else (raise_parse_err sc tk tklst)
let match_next sc tklst = match_token sc (next_token sc) tklst
					
let rec parse_aexp sc = 
  parse_add_expr' sc (parse_mod_expr sc) 
and parse_add_expr' sc add_expr = 
  let tk = next_token sc in 
  match tk with 
  | TkBinOp Plus -> 
     let mod_expr = parse_mod_expr sc in 
     parse_add_expr' sc (AePlus (add_expr, mod_expr))
  | TkBinOp Minus -> 
     let mod_expr = parse_mod_expr sc in 
     parse_add_expr' sc (AeMinus (add_expr, mod_expr))
  | TkRParen | TkComma | TkEq | TkNEq | TkAnd | TkOr | TkImpl | TkSemi 
  | TkThen | TkElse | TkFi | TkDo | TkOd | TkPar | TkEnd | TkPImpl -> 
						    buf_token sc tk; add_expr
  | _ -> 
     raise_parse_err sc tk 
		     [TkBinOp Plus; TkBinOp Minus; TkRParen; TkComma; 
		      TkEq; TkNEq; TkAnd; TkOr; TkImpl; TkSemi; 
		      TkThen; TkElse; TkFi; TkDo; TkOd; TkPar; TkEnd; TkPImpl]
and parse_mod_expr sc = 
  parse_mod_expr' sc (parse_arith_term sc) 
and parse_mod_expr' sc mod_expr = 
  let tk = next_token sc in 
  match tk with 
  | TkBinOp Mod -> 
     let arith_term = parse_arith_term sc in 
     parse_mod_expr' sc (AeMod (mod_expr, arith_term))
  | TkBinOp Plus | TkBinOp Minus | TkRParen | TkComma 
  | TkEq | TkNEq | TkAnd | TkOr | TkImpl | TkSemi 
  | TkThen | TkElse | TkFi | TkDo | TkOd | TkPar | TkEnd | TkPImpl -> 
						    buf_token sc tk; mod_expr
  | _ -> 
     raise_parse_err sc tk 
		     [TkBinOp Mod; TkBinOp Plus; TkBinOp Minus; 
		      TkRParen; TkComma; TkEq; TkNEq; TkAnd; TkOr; TkImpl; 
		      TkSemi; TkThen; TkElse; TkFi; TkDo; TkOd; TkPar; TkEnd; TkPImpl]
and parse_arith_term sc = 
  let tk = next_token sc in 
  match tk with 
  | TkInt n -> AeVal n 
  | TkLParen ->
     let aexp = parse_aexp sc in match_next sc [TkRParen]; aexp
  | TkId idstr -> (
    let tk' = next_token sc in 
    match tk' with 
    | TkLParen -> 
       let aelst = parse_aexp_list sc [] in 
       match_next sc [TkRParen]; AeFun (idstr, aelst) 
    | _ -> buf_token sc tk'; (AeVar (Var idstr))
  )
  | _ -> raise_parse_err sc tk [TkInt 0; TkLParen; TkId "..."]
and parse_aexp_list sc acc = 
  let ae = parse_aexp sc in 
  let tk = next_token sc in 
  match tk with 
  | TkComma -> parse_aexp_list sc (acc @ [ae])
  | TkRParen -> buf_token sc tk; (acc @ [ae])
  | _ -> raise_parse_err sc tk [TkComma; TkRParen]

let rec parse_bexp sc = 
  let or_expr = parse_or_expr sc in 
  let impl_expr' = parse_impl_expr' sc in 
  match impl_expr' with 
  | Some imple -> BeImpl (or_expr, imple)
  | None -> or_expr
and parse_impl_expr' sc = 
  let tk = next_token sc in 
  match tk with 
  | TkImpl -> Some (parse_bexp sc)
  | TkRParen | TkThen | TkDo | TkSemi | TkEnd | TkPImpl -> buf_token sc tk; None
  | _ -> raise_parse_err sc tk 
			 [TkImpl; TkRParen; TkThen; TkDo; TkSemi; TkEnd; TkPImpl]
and parse_or_expr sc = parse_or_expr' sc (parse_and_expr sc)
and parse_or_expr' sc or_expr = 
  let tk = next_token sc in 
  match tk with 
  | TkOr -> 
     let and_expr = parse_and_expr sc in 
     parse_or_expr' sc (BeOr (or_expr, and_expr))
  | TkRParen | TkThen | TkDo | TkSemi | TkImpl | TkEnd | TkPImpl -> 
						  buf_token sc tk; or_expr
  | _ -> raise_parse_err sc tk 
			 [TkOr; TkRParen; TkThen; TkDo; TkSemi; TkImpl; 
			  TkEnd; TkPImpl]
and parse_and_expr sc = 
  parse_and_expr' sc (parse_bool_term sc)
and parse_and_expr' sc and_expr = 
  let tk = next_token sc in
  match tk with 
  | TkAnd -> 
     let bool_term = parse_bool_term sc in
     parse_and_expr' sc (BeAnd (and_expr, bool_term))
  | TkOr | TkRParen | TkThen | TkDo | TkSemi | TkImpl | TkEnd | TkPImpl -> 
							 buf_token sc tk; and_expr
  | _ -> 
     raise_parse_err 
       sc tk 
       [TkAnd; TkOr; TkRParen; TkThen; TkDo; TkSemi; TkImpl; TkEnd; TkPImpl]
and parse_bool_term sc = 
  let tk = next_token sc in 
  match tk with 
  | TkTrue -> BeTrue 
  | TkFalse -> BeFalse 
  | TkEt | TkEf | TkEbot -> raise (Failure "Et, Ef, or Ebot unsupported") 									 
  | TkNot -> 
     let inner = parse_bool_term sc in BeNot inner
  | TkLParen ->
     let bexp = parse_bexp sc in 
     match_next sc [TkRParen]; bexp
  | _ -> 
     let _ = buf_token sc tk in 
     let aexp1 = parse_aexp sc in 
     let tkcop = next_token sc in
     match tkcop with 
     | TkEq -> 
	let aexp2 = parse_aexp sc in (BeEq (aexp1, aexp2))
     | TkNEq ->
	let aexp2 = parse_aexp sc in (BeNEq (aexp1, aexp2))
     | _ -> raise_parse_err sc tkcop [TkEq; TkNEq]
			    
let rec parse_var_list sc acc = 
  let tk = next_token sc in 
  match tk with 
  | TkId varstr -> (
    let tk = next_token sc in 
    match tk with 
    | TkComma -> parse_var_list sc (acc @ [Var varstr])
    | TkRParen -> buf_token sc tk; (acc @ [Var varstr])
    | _ -> raise_parse_err sc tk [TkComma; TkRParen]
  )
  | _ -> raise_parse_err sc tk [(TkId "...")]

let rec parse_stmts sc : stmt = 
  let basic_stmt = parse_stmt sc in
  let stmt_rem = parse_stmts' sc in 
  match stmt_rem with 
  | None -> basic_stmt
  | Some rem -> SSeq (basic_stmt, rem)
and parse_stmts' sc = 
  let tk = next_token sc in 
  match tk with 
  | TkSemi -> Some (parse_stmts sc)
  | TkPar | TkElse | TkFi | TkOd | TkEnd -> buf_token sc tk; None
  | _ -> raise_parse_err sc tk [TkSemi; TkPar; TkElse; TkFi; TkOd; TkEnd]
and parse_stmt sc = 
  let tk = next_token sc in 
  match tk with 
  | TkId ptstr -> (* program point *)
     (
       let tk = next_token sc in 
       match tk with 
       (* skip *)
       | TkSkip -> SSkip (Pt ptstr)
       (* assignment *)
       | TkId varstr -> (
				 match_next sc [TkAssg]; 
				 SAssg (Pt ptstr, Var varstr, parse_aexp sc)
       )
       (* output *)
       | TkOt -> (
				 match_next sc [TkLParen];
				 let tk = next_token sc in 
				 match tk with 
				 | TkId pchstr -> 
						let _ = match_next sc [TkComma] in 
						let aelst = (parse_aexp_list sc []) in 
						let _ = match_next sc [TkRParen] in 
						SOt (Pt ptstr, PCh pchstr, aelst)
				 | _ -> raise_parse_err sc tk [(TkId "...")]
       )
       (* input *)
       | TkIn -> (
				 match_next sc [TkLParen];
				 let tk = next_token sc in 
				 match tk with 
				 | TkId pchstr ->
						let _ = match_next sc [TkComma] in 
						let varlst = (parse_var_list sc []) in 
						let _ = match_next sc [TkRParen] in 
						SIn (Pt ptstr, PCh pchstr, varlst)
				 | _ -> raise_parse_err sc tk [(TkId "...")]
       )
       (* if *)
       | TkIf -> (
				 let cond = parse_bexp sc in 
				 let _ = match_next sc [TkThen] in 
				 let statement1 = parse_stmts sc in 
				 let _ = match_next sc [TkElse] in 
				 let statement2 = parse_stmts sc in 
				 let _ = match_next sc [TkFi] in 
				 SIf (Pt ptstr, cond, statement1, statement2)
       )
       (* while *)
       | TkWhile -> (
				 let cond = parse_bexp sc in 
				 let _ = match_next sc [TkDo] in 
				 let statement = parse_stmts sc in 
				 let _ = match_next sc [TkOd] in 
				 SWhile (Pt ptstr, cond, statement)
       )
       | _ -> raise_parse_err sc tk [TkSkip; TkOt; TkIn; TkIf; TkWhile]
     )
  | _ -> raise_parse_err sc tk [TkId "..."]

let rec parse_procs sc = 
  let tk = next_token sc in
  match tk with 
  | (TkId idstr) -> 
     let _ = match_next sc [TkColon] in 
     let statement = parse_stmts sc in 
     let tk' = next_token sc in (
       match tk' with 
       | TkPar -> [(Prin idstr, statement)] @ (parse_procs sc)
       | TkEnd -> buf_token sc tk'; [(Prin idstr, statement)]     
       | _ -> raise_parse_err sc tk' [TkPar; TkEnd]
     )
  | _ -> raise_parse_err sc tk [(TkId "...")]

let parse_internal_chs sc = 
  let rec do_parse_internal_chs sc acc = 
    let tk = next_token sc in (
      match tk with 
      | TkId cstr -> do_parse_internal_chs sc (acc @ [(PCh cstr)])
      | TkRParen -> acc
      | _ -> raise_parse_err sc tk [TkId "..."; TkRParen]
    )
  in 
  match_next sc [TkLParen]; do_parse_internal_chs sc []
						  
let parse_sys sc = 
  let _ = match_next sc [TkBegin] in 
  let _ = match_next sc [TkInternal] in
  let internal_chs = parse_internal_chs sc in 
  let procs = parse_procs sc in 
  let _ = match_next sc [TkEnd] in 
  (Sys (procs, internal_chs))

let rec parse_br_pt_lst sc pt_br = 
	let brtk = next_token sc in
	let brfm = (
		match brtk with 
		| TkEt -> BrFormulas.Et 
		| TkEf -> BrFormulas.Ef 
		| TkEbot -> BrFormulas.Ebot 
		| _ -> raise_parse_err sc brtk [TkEt; TkEf; TkEbot] 
	) in 
	let _ = match_next sc [TkTilde] in 
	let pt_of_br = next_token sc in
	let pt_str = (
		match pt_of_br with
		| TkId idstr -> idstr
		| _ -> raise_parse_err sc pt_of_br [TkId "..."] 
	) in 
	let pt_br' = (PtsMap.add (Pt pt_str) brfm pt_br) in 
	let sep = next_token sc in 
	match sep with 
	| TkComma -> parse_br_pt_lst sc pt_br' 
	| TkColon -> pt_br' 
	| _ -> raise (Failure "Incorrect format for branching list") 

let rec parse_asst sc ptbr_be_lst = 
	let _ = match_next sc [TkLParen] in
	let pt_br = parse_br_pt_lst sc PtsMap.empty in
	let be = parse_bexp sc in
	let _ = match_next sc [TkRParen] in
	let sep = next_token sc in
	match sep with
	| TkComma -> parse_asst sc (ptbr_be_lst @ [(pt_br, be)])
	| TkSemi -> buf_token sc sep; ptbr_be_lst @ [(pt_br, be)] 
	| TkEnd -> buf_token sc sep; ptbr_be_lst @ [(pt_br, be)] 
	| _ -> raise_parse_err sc sep [TkComma; TkSemi; TkEnd] 

let rec parse_assertions sc = 
	let tk = next_token sc in
	match tk with
	| TkId idstr ->
		 let _ = match_next sc [TkMappedTo] in
		 let ptbr_be_lst = parse_asst sc [] in
		 let sep = next_token sc in
		 (
			 match sep with
			 | TkSemi -> ((Pt idstr), ptbr_be_lst) :: (parse_assertions sc) 
			 | TkEnd -> buf_token sc sep; [((Pt idstr), ptbr_be_lst)] 
			 | _ -> raise_parse_err sc sep [TkSemi; TkEnd] 
		 )
	| _ -> raise_parse_err sc tk [TkId "..."] 
			
(* let rec parse_assertions sc =  *)
(*   let tk = next_token sc in ( *)
(*     match tk with  *)
(*     | TkId idstr ->  *)
(*        let _ = match_next sc [TkMappedTo] in  *)
(*        let be = parse_bexp sc in  *)
(*        let tk' = next_token sc in ( *)
(* 				 match tk' with  *)
(* 				 | TkSemi -> (Pt idstr, be) :: parse_assertions sc  *)
(* 				 | TkEnd -> buf_token sc tk'; [(Pt idstr, be)]  *)
(* 				 | _ -> raise_parse_err sc tk' [TkSemi; TkAssertions] *)
(*        ) *)
(*     | _ -> raise_parse_err sc tk [TkId "..."] *)
(*   ) *)

let parse_inv_asst sc = 
  let _ = match_next sc [TkBegin] in 
  let _ = match_next sc [TkInvariants] in 
  let invs = parse_assertions sc in 
  let _ = match_next sc [TkEnd] in 
  let _ = match_next sc [TkInvariants] in 
  let _ = match_next sc [TkBegin] in 
  let _ = match_next sc [TkAssertions] in 
  let assts = parse_assertions sc in 
  let _ = match_next sc [TkEnd] in 
  let _ = match_next sc [TkAssertions] in 
  (invs, assts)

(* strings of invariants and assertions *)

let string_of_assertion_body ptbr_be_lst =
	let rec string_of_single_asst (pt_br, be) = 
		let pt_br_str = 
			string_of_ptsmap pt_br string_of_pt string_of_br "~" "," 
		in 
		("(" ^ pt_br_str ^ " : " ^ (string_of_be_paren be) ^ ")") 
	in
	string_of_list ptbr_be_lst string_of_single_asst ", "
	
let string_of_assertion (Pt ptstr, ptbr_be_lst) = 
	(ptstr ^ " -> " ^ string_of_assertion_body ptbr_be_lst) 

let string_of_assertions assts =
	"assertions\n" ^ (string_of_list assts string_of_assertion ";\n")

let string_of_invariants invs =
	"invariants\n" ^ (string_of_list invs string_of_assertion ";\n") 

(* let string_of_assertion (Pt ptstr, be) = ptstr ^ " -> " ^ (string_of_bexp be) *)
							    
(* let string_of_invariants invs =  *)
(*   "invariants\n" ^  *)
(*     List.fold_left *)
(*       (fun acc inv -> acc ^ "\n" ^ (string_of_assertion inv)) "" invs *)

(* let string_of_assertions assts =  *)
(*   "assertions\n" ^  *)
(*     List.fold_left *)
(*       (fun acc asst -> acc ^ "\n" ^ (string_of_assertion asst)) "" assts *)
		
type conj_t = { cond: bexp; readers: prin list }
type policy_t = conj_t list

module VarMap = Map.Make(Vars)

let parse_policies sc =
  let rec do_parse_prlst prlst = 
    let tk = next_token sc in (
    match tk with 
    | TkId prstr -> do_parse_prlst (prlst @ [Prin prstr])
    | TkRParen -> buf_token sc tk; prlst
    | _ -> raise_parse_err sc tk [TkId "..."; TkRParen] 
    )
  in
  let rec do_parse_prs prs = 
    let tk = next_token sc in (
      match tk with 
      | TkId prstr -> do_parse_prs (prs @ [Prin prstr])
      | TkComma -> do_parse_prs prs
      | TkCurlyRP -> buf_token sc tk; prs
      | _ -> raise_parse_err sc tk [TkId "..."; TkComma; TkRParen]
    )
  in
  let rec do_parse_policy plc =
    let conj = 
      let _ = match_next sc [TkLParen] in 
      let be = parse_bexp sc in 
      let _ = match_next sc [TkPImpl] in 
      let _ = match_next sc [TkCurlyLP] in 
      let prlst = do_parse_prs [] in 
      let _ = match_next sc [TkCurlyRP] in
      let _ = match_next sc [TkRParen] in 
      { cond=be; readers=prlst }
    in
    let tk = next_token sc in (
    match tk with 
    | TkWedge -> do_parse_policy (plc @ [conj])
    | TkId _ | TkEnd -> buf_token sc tk; (plc @ [conj])
    | _ -> raise_parse_err sc tk [TkWedge; TkId "..."; TkEnd]
    )
  in
  let rec do_parse_policies polmp = 
    let tk = next_token sc in (
    match tk with 
    | TkId varstr -> 
       let _ = match_next sc [TkMappedTo] in 
       let newmp = VarMap.add (Var varstr) (do_parse_policy []) polmp in 
       do_parse_policies newmp 
    | TkEnd -> buf_token sc tk; polmp
    | _ -> raise_parse_err sc tk [TkId "..."; TkEnd] 
    )
  in
  let _ = match_next sc [TkBegin] in 
  let _ = match_next sc [TkPolicies] in 
  let _ = match_next sc [TkPrincipals] in 
  let _ = match_next sc [TkLParen] in 
  let prlst = do_parse_prlst [] in 
  let _ = match_next sc [TkRParen] in 
  let polmp = do_parse_policies (VarMap.empty) in
  let _ = match_next sc [TkEnd] in 
  let _ = match_next sc [TkPolicies] in
  (prlst, polmp)

let string_of_prlst prs sep = 
  if List.length prs = 0 
  then ""
  else
    List.fold_left 
      (fun acc pr -> acc ^ sep ^ (string_of_prin pr)) 
      (string_of_prin (List.hd prs))
      (List.tl prs)

let string_of_policy plc = 
  let string_of_conj conj = 
    string_of_bexp conj.cond ^ " ==> {" ^ (string_of_prlst conj.readers ", ") ^ "}"
  in (* policies are not allowed to be empty *)
  List.fold_left 
    (fun acc conj -> acc ^ " /\\\n" ^ string_of_conj conj)
    (string_of_conj (List.hd plc))
    (List.tl plc)

let string_of_polmp polmp = 
  VarMap.fold 
    (fun u plc acc -> 
     acc ^ "\n" ^ string_of_var u ^ " -> \n" ^ string_of_policy plc)
    polmp
    ""

(*
let () = 
  let stm = open_stream "exfile" in
  try 
    let sc = { last_token=None; stm=stm } in 
    let sys = parse_sys sc in 
    let (invs, assts) = parse_inv_asst sc in 
    let (allprs, polmp) = parse_policies sc in 
    print_endline (string_of_sys sys 2);          (* write the result to stdout *)
    print_endline ("\n" ^ string_of_invariants invs); 
    print_endline ("\n" ^ string_of_assertions assts); 
    print_endline ("\nprincipals ( " ^ (string_of_prlst allprs ", ") ^ " )"); 
    print_endline ("\npolicies\n" ^ string_of_polmp polmp);
    flush stdout                (* write on the underlying device *)
  with 
  | End_of_file -> 
     close_in stm.chan                  (* close the input channel *) 
  | e ->                      
     close_in_noerr stm.chan;           (* emergency closing *)
     raise e                      	(* exit with error: files are closed but
                                    	channels are not flushed *)	  
 *)
