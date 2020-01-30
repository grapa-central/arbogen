(* Exact-size random generation based on the recursive method. *)

(*let deref expr =
  match expr with 
    | Reference a -> a 
    | a -> a*)
(*let rec generator (grammar:Grammar.t) count id n  =
  match grammar.rules.(id) with (*on recupere le premier element de l'array rule qui correspond à la regle*)
   | Grammar.Z 0 -> Tree.Node (grammar.names.(id), [])
   | Grammar.Z 1 when n == 1 -> Tree.Node (grammar.names.(id), [])
   | Grammar.Union (Reference(a),_) when Random.float 1. <= (float_of_int (count.(a).(n)/count.(id).(n))) -> generator grammar count a n (*proba étant 
                                        la fonction qui sera definit par
                                        Katia et Firat*)
   | Grammar.Union (_,Reference(b)) -> generator grammar count b n
   | Grammar.Reference a -> generator grammar count a n
  (* | Product a b when a == Z 1 -> generator expr n b *)
   | Grammar.Product (Reference(a),Reference(b)) -> generator_prod grammar (Grammar.Product(Reference(a),Reference(b))) 0 (count.(a).(0)*count.(b).(n)/count.(id).(n)) n (Random.float 1.0) id count
   | _ -> generator grammar count id n


(*l'appel sera : generator_prod expr 0 proba(a,0)*proba(b,n)/proba(expr.(1).(0),n)*)
and generator_prod grammar expr k s n u id count= 
  match expr with
  | Grammar.Product(Reference(a),Reference(b)) when u > float_of_int s -> generator_prod grammar (Grammar.Product((Reference(a),Reference(b)))) (k+1) (s+count.(a).(k)*count.(b).(n-k)/count.(id).(n)) n u id count
                   
  | Grammar.Product (Reference(a),Reference(b)) -> Tree.Node (grammar.names.(id), [(generator grammar count a k); (generator grammar count b (n-k))])
  | _ -> generator_prod grammar expr k s n u id count*)

let rec printSpec (expr: int Grammar.expression) =
   match expr with
   | Z i -> Printf.printf "Z %d" i
   | Union(op1, op2) -> print_string "Union("; (printSpec op1); print_string ", "; (printSpec op2); print_string ")"
   | Product(op1, op2) ->print_string "Product("; (printSpec op1); print_string ", "; (printSpec op2); print_string ")"
   | Reference r -> Printf.printf "Reference %d" r
   | _ -> () (* not handled *)

let generateZ z n = 
   match z with
	| Grammar.Z 0 -> Tree.Node ("Z0", [])
	| Grammar.Z i when n == i -> Tree.Node ("Z"^(string_of_int i), []) 
	| _ -> print_string "not handled in generateZ\n"; Tree.Node ("Unknown", []) 


let rec generator (grammar:Grammar.t) count id n = 
   match grammar.rules.(id) with (*on recupere le premier element de l'array rule qui correspond à la regle*)
	   | Grammar.Z 0 -> Tree.Node (grammar.names.(id), [])
	   | Grammar.Z i when n == i -> Tree.Node (grammar.names.(id), []) 
	   | Grammar.Union (Reference(a), Reference(b)) -> let randInt = Random.int (Z.to_int (count.(id).(n))) in 
							let randZ = Z.of_int randInt in 
							if randZ < count.(a).(n) then generator grammar count a n
							else generator grammar count b n
	   | Grammar.Union (Reference(a), Z(b)) -> let randInt = Random.int (Z.to_int (count.(id).(n))) in 
							let randZ = Z.of_int randInt in 
							if randZ < count.(a).(n) then generator grammar count a n
							else generateZ (Grammar.Z(b)) n
	   | Grammar.Union (Z(a), Reference(b)) -> let countZ = (Z.sub count.(id).(n)  count.(a).(n)) in		
							let randInt = Random.int (Z.to_int (count.(id).(n))) in 
							let randZ = Z.of_int randInt in 
							if randZ < countZ then generateZ (Grammar.Z(a)) n
							else generator grammar count b n 
	   | Grammar.Product (Reference(a), Reference(b)) -> let randInt = (Random.int (Z.to_int (count.(id).(n)))) in 
							let randZ = Z.of_int randInt in 
							let i = ref 0 in 
							let s = ref (Z.add count.(a).(!i) count.(b).(n-(!i))) in 
							while (Z.leq (!s) randZ) do
								i := !i + 1;
								s := (Z.add !s (Z.add count.(a).(!i)  count.(b).(n-(!i))))
							done;
							Tree.Node (grammar.names.(id), [generator grammar count a (!i); generator grammar count b (n-(!i))])
	   | Grammar.Product (Z(a), Reference(b)) -> Tree.Node (grammar.names.(id),  [generateZ (Grammar.Z(a)) a; generator grammar count b (n-a)])

	   | _ -> print_string "not handled in generator\n"; Tree.Node ("Unknown", []) 

	  
	    


(*
let rec generator (grammar:Grammar.t) count id n  =(* print_int n ;printSpec grammar.rules.(id); print_string "\n";*)
   let e = (if n==1 then (1.0) else (0.0)) in
   match grammar.rules.(id) with (*on recupere le premier element de l'array rule qui correspond à la regle*)
	   | Grammar.Z 0 -> Tree.Node (grammar.names.(id), [])
	   | Grammar.Z i when n == i -> Tree.Node (grammar.names.(id), [])
	   | Grammar.Union (Reference(a),Reference(_)) when (Random.float 1.0) > (Z.to_float (count.(a).(n)) /. Z.to_float(count.(id).(n))) -> generator grammar count a n 
	   | Grammar.Union (Reference(_),Reference(b)) -> generator grammar count b n
	   | Grammar.Union (Reference(a),Z(_)) when Random.float 1.0 >(Z.to_float (count.(a).(n)) /. Z.to_float (count.(id).(n)))  -> generator grammar count a n 
           | Grammar.Union (Reference(_),Z(_)) -> Tree.Node (grammar.names.(id), []) 
           | Grammar.Union (Z(_),Reference(_))  when  Random.float 1.0 >  (e /. Z.to_float (count.(id).(n))) -> Tree.Node (grammar.names.(id), [])  
	   | Grammar.Union (_,Reference(b)) -> generator grammar count b n
	   | Grammar.Reference a -> generator grammar count a n
  (* | Product a b when a == Z 1 -> generator expr n b *)
	   | Grammar.Product (Reference(a),Reference(b)) -> generator_prod grammar (Grammar.Product(Reference(a),Reference(b))) 0   (Z.to_float (Z.mul  count.(a).(0) count.(b).(n)) /. Z.to_float( count.(id).(n)) )  n (Random.float 1.0) id count
	   | Grammar.Product (Z (a),Reference(b)) -> generator_prod grammar (Grammar.Product(Z (a),Reference(b))) 0  (0.0) n (Random.float 1.0) id count
	   | Grammar.Product (Reference(a),Z(b)) -> let e = (if n==1 then 1 else 0) in generator_prod grammar (Grammar.Product(Reference(a),Z(b))) 0  ( ((Z.to_float count.(a).(0)) *. (float_of_int e)) /. (Z.to_float count.(id).(n)) ) n (Random.float 1.0) id count
    
	   | _ -> Printf.printf "erreur in generation (not handled case)\n"; Tree.Node (grammar.names.(id), []) 
   *) 

(*
and generator_prod grammar expr k s n u id count= 
  match expr with
  | Grammar.Product(Reference(a),Reference(b)) when  u > s-> generator_prod grammar (Grammar.Product((Reference(a),Reference(b)))) (k+1) (s +. (( Z.to_float count.(a).(k) ) *. ( Z.to_float count.(b).(n-k ) /. count.(id).(n) )) n u id count
                   
  | Grammar.Product (Reference(a),Reference(b)) -> Tree.Node (grammar.names.(id), [generator grammar count a k; generator grammar count b (n-k)])
  | Grammar.Product(Z (a),Reference(b)) when u > s -> let e = (if n==1 then 1 else 0) in generator_prod grammar (Grammar.Product((Z(a),Reference(b)))) (k+1) (s +.  e *. ( Z.to_float count.(b).(n-k ) /. count.(id).(n) ) n u id count
                   
  | Grammar.Product (Z (_),Reference(b)) -> Tree.Node (grammar.names.(id), [Tree.Node (grammar.names.(id), []); generator grammar count b (n-k)])

  | Grammar.Product(Reference(a),Z (b)) when u > s ->let e = (if n==1 then 1 else 0) in generator_prod grammar (Grammar.Product((Reference(a),Z(b)))) (k+1) (s +.  ( Z.to_float count.(a).(k) ) *.  e /. count.(id).(n) )   n u id count
                   
  | Grammar.Product (Reference(a),Z (_)) -> Tree.Node (grammar.names.(id), [(generator grammar count a k); Tree.Node (grammar.names.(id), [])])
  | _ -> Printf.printf "erreur in generation (not handled case)\n"; Tree.Node (grammar.names.(id), [])
*)

(*l'appel sera : generator_prod expr 0 proba(a,0)*proba(b,n)/proba(expr.(1).(0),n)*)
(*
and generator_prod grammar expr k s n u id count=  Printf.printf "k = %d, n = %d, s = %f, u = %f\n" k n s u;
  match expr with
  | Grammar.Product(Reference(a),Reference(b)) when  u > s-> generator_prod grammar (Grammar.Product((Reference(a),Reference(b)))) (k+1)  (Z.to_float(Z.add  (Z.of_float s) (Z.div (Z.mul (count.(a).(k)) (count.(b).(n-k))) (count.(id).(n))))) n u id count
                   
  | Grammar.Product (Reference(a),Reference(b)) -> Tree.Node (grammar.names.(id), [generator grammar count a k; generator grammar count b (n-k)])
  | Grammar.Product(Z (a),Reference(b)) when u > s -> let e = (if n==1 then 1 else 0) in generator_prod grammar (Grammar.Product((Z(a),Reference(b)))) (k+1)  (Z.to_float(Z.add (Z.of_float s) (Z.div (Z.mul (Z.of_int e) (count.(b).(n-k))) (count.(id).(n))))) n u id count
                   
  | Grammar.Product (Z (_),Reference(b)) -> Tree.Node (grammar.names.(id), [Tree.Node (grammar.names.(id), []); generator grammar count b (n-k)])

  | Grammar.Product(Reference(a),Z (b)) when u > s ->let e = (if n==1 then 1 else 0) in generator_prod grammar (Grammar.Product((Reference(a),Z(b)))) (k+1)  (Z.to_float(Z.add (Z.of_float s) (Z.div (Z.mul (count.(a).(k)) (Z.of_int e)) (count.(id).(n))))) n u id count
                   
  | Grammar.Product (Reference(a),Z (_)) -> Tree.Node (grammar.names.(id), [(generator grammar count a k); Tree.Node (grammar.names.(id), [])])
  | _ -> Printf.printf "erreur in generation (not handled case)\n"; Tree.Node (grammar.names.(id), [])

*)

(*
let rec unranking grammar count id n r =
  match grammar.(0).(id) with (*on recupere le premier element de l'array rule qui correspond à la regle*)
   | Z 0 -> Tree.Node (names.(id), [])
   | Z 1 when n == 1 -> Tree.Node (names.(id), [Tree.Node (0, []),Tree.Node (0, [])])
   | Union a b when r < count(a).(0) -> unranking grammar count deref(a) n r 
   | Union a b -> unranking grammar count deref(b) n r-count(a).(0)
   | Reference a -> unranking grammar deref(a) n r
  (* | Product a b when a == Z 1 -> generator expr n b *)
   | Product a b -> unranking_prod (Product a b) 0 (count[deref(a)][0]*count[deref(b)][n]) n r id 

let rec binom0 = fun n p ->
  if p > n || n < 0 || p < 0 then
    0
  else
    if p = 0 then
      1
    else
      binom0 (n-1) p + binom0 (n-1) (p-1);;
(*l'appel sera : generator_prod expr 0 proba(a,0)*proba(b,n)/proba(expr.(1).(0),n)*)
and unranking_prod grammar expr k s n r id = 
  match expr with
  | Product a b when r > s -> unranking_prod (Product a b) (k+1) (s+((binom0(n,k)*count[deref(a)][k]*count[deref(b)][n-k])/count[id][n])) n r id;
                   
  | Product a b -> {i2=i-s
                    l= i2 mod binom0(n,k)
                    i3=i2/binom0(n,k)
                    bc=count.(b).(n-j)
Tree.Node (names.(id), [unranking(a,k,i3/bc), unranking(b,n-k,i3 mod bc) ])
*)
