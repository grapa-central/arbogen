(* Exact-size random generation based on the recursive method. *)

let randbits bit_gen nbits =
  let rec gen acc nbits =
    let bits = bit_gen () in
    if nbits <= 30 then
      let bits = bits land ((1 lsl nbits) - 1) in
      Z.logor (Z.of_int bits) (Z.shift_left acc nbits)
    else
      gen (Z.logor (Z.of_int bits) (Z.shift_left acc 30)) (nbits - 30)
  in
  gen Z.zero nbits

let rand_bigint bit_gen bound =
  if Z.leq bound Z.zero then raise (Invalid_argument "random_bigint");
  let nbits = 1 + Z.log2 bound in
  let rec gen () =
    let r = randbits bit_gen nbits in
    if r >= bound then gen () else r
  in
  gen ()

let rec printSpec (expr: int Grammar.expression) =
  match expr with
  | Z i -> Printf.printf "Z %d" i
  | Union(op1, op2) -> print_string "Union("; (printSpec op1); print_string ", "; (printSpec op2); print_string ")"
  | Product(op1, op2) ->print_string "Product("; (printSpec op1); print_string ", "; (printSpec op2); print_string ")"
  | Reference r -> Printf.printf "Reference %d" r
  | _ -> () (* not handled *)

let rec binom0 = fun n p ->
  if (Z.gt p n) || (Z.lt n  (Z.of_int 0)) ||  (Z.lt p (Z.of_int 0)) then
    Z.of_int 0
  else
  if (Z.equal p (Z.of_int 0)) then
    Z.of_int 1
  else
    let new_n = Z.sub n (Z.of_int 1) in
    let new_p = Z.sub p (Z.of_int 1) in
    Z.add (binom0 new_n p) (binom0 new_n new_p);;

let generateZ z n =
  match z with
  | Grammar.Z 0 -> Tree.Node ("Z0", [])
  | Grammar.Z i when n == i -> Tree.Node ("Z"^(string_of_int i), [])
  | _ -> print_string "not handled in generateZ\n"; Tree.Node ("Unknown", [])

let rec unranking (grammar:Grammar.t) count id n bp rZ = (*rZ rang as a bigint*) 
  match grammar.rules.(id) with (*on recupere le premier element de l'array rule qui correspond à la regle*)
  | Grammar.Z 0 -> Tree.Node (grammar.names.(id), [])
  | Grammar.Z i when n == i -> Tree.Node (grammar.names.(id), [])
  | Grammar.Union (Reference(a), Reference(b)) -> 
  				if rZ < count.(a).(n) then unranking grammar count a n bp rZ
  				else unranking grammar count b n bp (Z.sub rZ count.(a).(n))
  | Grammar.Union (Reference(a), Z(b)) -> 
  				if rZ < count.(a).(n) then unranking grammar count a n bp rZ
  				else generateZ (Grammar.Z(b)) n
  | Grammar.Union (Z(a), Reference(b)) -> let countZ = (Z.sub count.(id).(n)  count.(b).(n)) in 
  				if rZ < countZ then generateZ (Grammar.Z(a)) n
  				else unranking grammar count b n bp (Z.sub rZ countZ)
  | Grammar.Product (Reference(a), Reference(b)) -> 
          			let i = ref 0 in 
          			let order = ref 0 in
     				let s = ref (Z.mul count.(a).(!i) count.(b).(n-(!i))) in
          			while (Z.leq (!s) rZ) do
            			if (bp<>(-1)) && (!order=1) then
              				(s := (Z.add !s (Z.mul (binom0 (Z.of_int n) (Z.of_int !i ) )(Z.mul count.(a).(n-(!i)) count.(b).(!i))));
                                        order:= 0)
            			else
					(i := !i + 1;
					order:=1;
					s := (Z.add !s (Z.mul (binom0 (Z.of_int n) (Z.of_int !i ) ) (Z.mul count.(a).(!i)  count.(b).(n-(!i))))))
				done;
				let i2 = (Z.sub (Z.of_int !i) !s) in
				let i3 = (Z.div i2 (binom0 (Z.of_int n) (Z.of_int !i ))) in
				let bc = count.(b).(n- !i) in
				let i4 = (Z.(mod) i3 bc) in
				Tree.Node (grammar.names.(id),
					[unranking grammar count a (!i) bp (Z.div i3 bc) ;
					unranking grammar count b (n-(!i)) bp i4])
  | Grammar.Product (Z(a), Reference(b)) -> let countZ = (Z.sub count.(id).(n)  count.(b).(n-a)) in 
			        Tree.Node (grammar.names.(id),  [generateZ (Grammar.Z(a)) a; unranking grammar count b bp (n-a) (Z.sub rZ countZ) ])

  | _ -> print_string "not handled in generator\n"; Tree.Node ("Unknown", [])


let rec generator (grammar:Grammar.t) count id n bp =
     match grammar.rules.(id) with (*on recupere le id-ieme element de l'array rules qui correspond à la regle*)
       | Grammar.Z 0 -> Tree.Node ("Z0", [])
       | Grammar.Z i when n == i -> Tree.Node ("Z"^(string_of_int i), [])
       | Grammar.Union (Reference(a), Reference(b)) -> 
                let randZ = (rand_bigint Random.bits count.(id).(n)) in
        	if randZ < count.(a).(n) then (generator grammar count a n bp)
       		else (generator grammar count b n bp)
       | Grammar.Union (Reference(a), Z(b)) ->
                let randZ = (rand_bigint Random.bits count.(id).(n))  in
                if randZ < count.(a).(n) then generator grammar count a n bp
                else generateZ (Grammar.Z(b)) n
       | Grammar.Union (Z(a), Reference(b)) -> let countZ = (Z.sub count.(id).(n)  count.(b).(n)) in
                let randZ = (rand_bigint Random.bits count.(id).(n))  in
                if randZ < countZ then generateZ (Grammar.Z(a)) n
                else generator grammar count b n bp
       | Grammar.Product (Reference(a), Reference(b)) -> 
                let randZ = (rand_bigint Random.bits count.(id).(n)) in
                let i = ref 0 in
                let order = ref 0 in
                let s = ref (Z.mul count.(a).(!i) count.(b).(n-(!i))) in
                while (Z.leq (!s) randZ) do
                  if (bp<>(-1)) && (!order ==1) then
                    (s := (Z.add !s (Z.mul count.(a).(n-(!i)) count.(b).(!i)));
                     order:= 0)
                  else
                  (i := !i + 1;
                  order:=1;
                  s := (Z.add !s (Z.mul count.(a).(!i)  count.(b).(n-(!i)))))
                done;
		Tree.Node ((string_of_int !i)^(string_of_int (n-(!i)))^"OP1", [generator grammar count a (!i) bp; generator grammar count b (n-(!i)) bp])
       | Grammar.Product (Z(a), Reference(b)) -> Tree.Node ("OP2"^(string_of_int a)^(string_of_int (n-a)),  [generateZ (Grammar.Z(a)) a; generator grammar count b (n-a) bp])
						  
       | _ -> print_string "not handled in generator\n"; Tree.Node ("Unknown", [])

let print_tab tab = 
	let rec aux tab i = 
		match tab with
		| [] -> ()
		| h::q -> let (_, x) = h in Printf.printf "Tree %d generated %d times\n" i x; aux q (i+1)
	in aux tab 1

let rec sameChildren c1 c2 =
	match(c1,c2) with 
	| ([],[]) -> true
	| ((Tree.Node (x1,children1)::[]),(Tree.Node (x2,children2)::[])) -> if (String.equal x1 x2) then (sameChildren children1 children2) else false
	| ((Tree.Node (x1,children1)::q1),(Tree.Node (x2,children2)::q2)) -> if (String.equal x1 x2) then (sameChildren children1 children2) && (sameChildren q1 q2) else false
	| (_,_) -> false


and sameTrees tree1 tree2 =
	match (tree1, tree2) with
	| (Tree.Node (x1, childrenT1), Tree.Node (x2, childrenT2)) -> if ((String.equal x1 x2) && (sameChildren childrenT1 childrenT2)) then true else false

let rec auxTestUniform tab tree =
	match tab with 
	| [] -> [(tree, 1)]
	| ((Tree.Node (t,c)), nb)::q -> if (sameTrees (Tree.Node (t,c)) tree) then (tree, (nb+1))::q else ((Tree.Node (t,c)), nb)::(auxTestUniform q tree)

let testUniform (grammar:Grammar.t) count id n bp nbGen =
	let tab = ref [] in
	let i = ref 0 in
	while !i < nbGen do
		let tree = generator grammar count id n bp in
		tab := auxTestUniform !tab tree;
		i := !i +1
	done;
	print_tab !tab

let execTime (grammar:Grammar.t) count id n bp outputFile =
	let out = open_out outputFile in
	let rec aux y = 
		let time = Unix.gettimeofday () in
		for _ = 0 to 20 do
			let _ = generator grammar count id y bp in ()
		done;
		Printf.fprintf out "%d %f\n" y ((Unix.gettimeofday () -. time) /. 20.0);
		if (y -100) >= 0 then aux (y -100) else ()
	in aux n;
	close_out out
