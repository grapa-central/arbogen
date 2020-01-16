(*let deref expr =
  match expr with 
    | Reference a -> a 
    | a -> a*)
let rec generator (grammar:Grammar.t) count id n  =
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
  | _ -> generator_prod grammar expr k s n u id count

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
