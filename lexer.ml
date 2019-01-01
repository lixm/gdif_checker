open Printf

type token =
  | TkInt of int         		(* an integer *)
  | TkBinOp of binop 	(* a binary operator *)
  | TkLParen             	(* an opening parenthesis *) 
  | TkRParen             	(* a closing parenthesis *)     
  | TkCurlyLP			(* a curly opening parenthesis *)
  | TkCurlyRP			(* a curly closing parenthesis *)
  | TkId of string				(* an identifier *)
  | TkBegin
  | TkEnd
  | TkTrue
  | TkFalse
  | TkAnd
  | TkOr
  | TkNot
  | TkSkip 
  | TkAssg                  (* := *)
  | TkOt
  | TkIn
  | TkIf
  | TkThen
  | TkElse
  | TkFi
  | TkWhile
  | TkDo
  | TkOd
  | TkSemi      		(* ; *)
  | TkComma			(* , *)
  | TkColon        	(* : *)
  | TkEq              	(* = *)
  | TkNEq	      	(* != *)
  | TkPar
  | TkInternal
  | TkInvariants
  | TkAssertions
  | TkPolicies
  | TkPrincipals
  | TkMappedTo
  | TkImpl
  | TkWedge             (* /\ for policies *)
  | TkPImpl             (* ==> for policies *)
  | TkEt
  | TkEf
  | TkEbot
	| TkTilde
 and binop = 
   | Plus 
   | Minus
   | Mod

let rec string_of_tk tk = 
  match tk with 
  | TkInt n -> "int("^(string_of_int n)^")"
  | TkBinOp Plus -> "+"
  | TkBinOp Minus -> "-" 
  | TkBinOp Mod -> "Mod"
  | TkLParen -> "LParen"
  | TkRParen -> "RParen"
  | TkCurlyLP -> "CurlyLParen"
  | TkCurlyRP -> "CurlyRParen"
  | TkId idstr -> "id("^idstr^")"
  | TkBegin -> "BEGIN"
  | TkEnd -> "END"
  | TkTrue -> "True" 
  | TkFalse -> "False"
  | TkAnd  -> "And"
  | TkOr -> "Or"
  | TkNot -> "Not"
  | TkSkip -> "Skip"
  | TkAssg -> ":="
  | TkOt -> "Send"
  | TkIn -> "Recv"
  | TkIf -> "If"
  | TkThen -> "Then"
  | TkElse -> "Else"
  | TkFi -> "Fi"
  | TkWhile -> "While"
  | TkDo -> "Do"
  | TkOd -> "Od"
  | TkSemi -> "Semi"
  | TkComma -> "Comma"
  | TkColon -> "Colon"
  | TkEq -> "Eq"
  | TkNEq -> "NEq"
  | TkPar -> "Parallel"
  | TkInternal -> "internal"
  | TkInvariants -> "invariants"
  | TkAssertions -> "assertions"
  | TkPolicies -> "policies"
  | TkPrincipals -> "principals"
  | TkMappedTo -> "->"
  | TkImpl -> "=>"
  | TkWedge -> "/\\"
  | TkPImpl -> "==>" 
  | TkEt -> "tt"
  | TkEf -> "ff"
  | TkEbot -> "??"
	| TkTilde -> "~" 

let is_digit c = 
  let code = Char.code c in 
  code >= Char.code('0') && code <= Char.code('9')

let is_alpha c = 
  let code = Char.code c in
  (code >= Char.code('A') && code <= Char.code('Z')) ||
    (code >= Char.code('a') && code <= Char.code('z'))

type stream = { mutable chr: char option; mutable line_num: int; chan: in_channel }

let open_stream file = { chr=None; line_num=1; chan=open_in file }
let close_stream stm = close_in stm.chan
let read_char stm = 
  match stm.chr with
    None -> let c = input_char stm.chan in
            if c = '\n' then stm.line_num <- stm.line_num + 1 else (); 
	    c
  | Some c -> stm.chr <- None; c
let unread_char stm c = stm.chr <- Some c

type scanner = { mutable last_token: token option; stm: stream }

exception Lexing_error of string

let raise_lex_err sc msg = 
  raise (Lexing_error (msg ^ " on line " ^ (string_of_int sc.stm.line_num)))

let rec skip_blank_chars stm = 
  let c = read_char stm in
  if c = ' ' || c = '\t' || c = '\r' || c = '\n'
  then skip_blank_chars stm
  else unread_char stm c; ()

let scan sc =   
  let stm = sc.stm in 
  let c = read_char stm in
  let rec scan_iden acc = 
    let nc = read_char stm in
    if is_alpha nc || is_digit nc || nc='_' || nc='.' || nc='@' || nc='?' 
    then scan_iden (acc ^ (Char.escaped nc))
    else 
      let _ = unread_char stm nc in
      if acc = "BEGIN" then TkBegin
      else if acc = "END" then TkEnd 
      else if acc = "internal" then TkInternal
      else if acc = "true" then TkTrue
      else if acc = "false" then TkFalse
      else if acc = "and"  then TkAnd
      else if acc = "or" then TkOr 
      else if acc = "not" then TkNot						 
      else if acc = "skip" then TkSkip
      else if acc = "send" then TkOt
      else if acc = "recv" then TkIn														 
      else if acc = "if" then TkIf
      else if acc = "then" then TkThen
      else if acc = "else" then TkElse
      else if acc = "fi" then TkFi
      else if acc = "while" then TkWhile
      else if acc = "do" then TkDo
      else if acc = "od" then TkOd
      else if acc = "invariants"  then TkInvariants
      else if acc = "assertions" then TkAssertions
      else if acc = "policies" then TkPolicies
      else if acc = "principals" then TkPrincipals
      else if acc = "tt" then TkEt
      else if acc = "ff" then TkEf
      else if acc = "??" then TkEbot
      else TkId acc
  in
  let rec scan_int acc = 
    let nc = read_char stm in
    if is_digit nc
    then scan_int (acc ^ (Char.escaped nc))
    else 
      let _ = unread_char stm nc in
      TkInt (int_of_string acc)
  in
  if (is_alpha c || c='?') then scan_iden (Char.escaped c) 
  else if is_digit c then scan_int (Char.escaped c)
	else if c = '~' then TkTilde 
  else if c = '+' then TkBinOp Plus
  else if c = '-' 
  then 
    let lookahead = read_char stm in 
    if lookahead = '>' 
    then TkMappedTo 
    else let _ = unread_char stm lookahead in (TkBinOp Minus)
  else if c = '%' then TkBinOp Mod
  else if c = ',' then TkComma
  else if c = ';' then TkSemi
  else if c = '(' then TkLParen
  else if c = ')' then TkRParen
  else if c = '{' then TkCurlyLP
  else if c = '}' then TkCurlyRP
  else if c = '=' then
    let lookahead = read_char stm in 
    if lookahead = '>' then TkImpl
    else if lookahead = '=' then
      let lookahead' = read_char stm in 
      if lookahead' = '>' then TkPImpl
      else raise_lex_err sc ("== not followed by >")
    else
      let _ = unread_char stm lookahead in TkEq
  else if c = '/' 
  then 
    let lookahead = read_char stm in 
    if lookahead = '\\' 
    then TkWedge 
    else raise_lex_err sc ("a / is not followed by a \\")
  else if (c = '|' && read_char stm = '|') then 
    TkPar
  else if (c = '!' && read_char stm = '=') then 
    TkNEq 
  else if c = ':' then 
    let lookahead = read_char stm  in 
    if lookahead = '=' then 
      TkAssg
    else 
      let _ = unread_char stm lookahead in TkColon
  else 
    raise_lex_err sc "couldn't identify the token"
		  
let next_token sc = 
  match sc.last_token with
  | None -> (skip_blank_chars sc.stm; scan sc)
  | Some t -> sc.last_token <- None; t

let buf_token sc tk = sc.last_token <- Some tk
					    

