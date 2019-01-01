
type pt =
	| Pt of string

let string_of_pt (Pt ptstr) = ptstr

module Pts = 
  struct 
    type t = pt 
    let compare pt1 pt2 = 
      Pervasives.compare (string_of_pt pt1) (string_of_pt pt2)
  end

module PtsMap = Map.Make(Pts)

module PtSet = Set.Make(Pts)

module BrFormulas = 
  struct 
    type t = 
      | Et 
      | Ef 
      | Ebot 

    let compare brfm1 brfm2 = 
      match brfm1 with 
      | Et -> (
				match brfm2 with 
				| Et -> 0
				| Ef | Ebot -> 1 
      )
      | Ef -> (
				match brfm2 with 
				| Et -> -1
				| Ef -> 0
				| Ebot -> 1
      )
      | Ebot -> (
				match brfm2 with 
				| Et | Ef -> -1 
				| Ebot -> 0 
      )
											
  end

module BrFmSet = Set.Make(BrFormulas)

let string_of_br br = 
  match br with
  | BrFormulas.Et -> "tt"
  | BrFormulas.Ef -> "ff"
  | BrFormulas.Ebot -> "?"
												 
let zip_exn l1 l2 = 
	let rec do_zip_exn l1 l2 acc = 
		match l1 with 
		| [] -> (
			match l2 with 
			| [] -> acc 
			| _ -> raise (Failure "Lists have different length")
		)
		| hd1 :: l1' -> (
			match l2 with 
			| [] -> raise (Failure "Lists have different length")
			| hd2 :: l2' -> (do_zip_exn l1' l2' (acc @ [(hd1, hd2)]))
		)
	in do_zip_exn l1 l2 []

let string_of_list lst str_of_ele sep = 
	match lst with
	| [] -> ""
	| e :: lst' -> 
		 List.fold_left
			 (fun acc e -> acc ^ sep ^ (str_of_ele e))
			 (str_of_ele e) lst' 

let string_of_ptsmap mp str_of_key str_of_val inner_sep outer_sep =
	let kv_str k v = str_of_key k ^ inner_sep ^ str_of_val v in 
	try		
		let (k_min, v_min) = PtsMap.min_binding mp in 
		PtsMap.fold
			(fun k v acc -> acc ^ outer_sep ^ (kv_str k v)) 
			(PtsMap.remove k_min mp) (kv_str k_min v_min)  
	with
		Not_found -> ""
		
