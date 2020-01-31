(* Exact-size random generation based on the recursive method. *)

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

let rec unranking (grammar:Grammar.t) count id n bp r =
  match grammar.rules.(id) with (*on recupere le premier element de l'array rule qui correspond à la regle*)
  | Grammar.Z 0 -> Tree.Node (grammar.names.(id), [])
  | Grammar.Z i when n == i -> Tree.Node (grammar.names.(id), [])
  | Grammar.Union (Reference(a), Reference(b)) ->
  				let rZ = Z.of_int r in
  				if rZ < count.(a).(n) then unranking grammar count a n bp r
  				else unranking grammar count b n bp r
  | Grammar.Union (Reference(a), Z(b)) ->
  				let rZ = Z.of_int r in
  				if rZ < count.(a).(n) then unranking grammar count a n bp r
  				else generateZ (Grammar.Z(b)) n
  | Grammar.Union (Z(a), Reference(b)) -> let countZ = (Z.sub count.(id).(n)  count.(a).(n)) in
  				let rZ = Z.of_int r in
  				if rZ < countZ then generateZ (Grammar.Z(a)) n
  				else unranking grammar count b n bp r
  | Grammar.Product (Reference(a), Reference(b)) ->
  				let rZ = Z.of_int r in
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
          let  i2 = (Z.sub (Z.of_int !i) !s) in
          let i3 = (Z.div i2 (binom0 (Z.of_int n) (Z.of_int !i ) )) in
          let bc = count.(b).(n- !i) in
          let i4 = (Z.(mod) i3 bc) in
          Tree.Node (grammar.names.(id),
                     [unranking grammar count a (!i) bp (Z.to_int (Z.div i3 bc)) ;
                      unranking grammar count b (n-(!i)) bp (Z.to_int i4)])
  | Grammar.Product (Z(a), Reference(b)) -> Tree.Node (grammar.names.(id),  [generateZ (Grammar.Z(a)) a; unranking grammar count b bp (n-a) r ])

  | _ -> print_string "not handled in generator\n"; Tree.Node ("Unknown", [])


let rec generator (grammar:Grammar.t) count id n bp =
     match grammar.rules.(id) with (*on recupere le premier element de l'array rule qui correspond à la regle*)
       | Grammar.Z 0 -> Tree.Node (grammar.names.(id), [])
       | Grammar.Z i when n == i -> Tree.Node (grammar.names.(id), [])
       | Grammar.Union (Reference(a), Reference(b)) -> let randInt = Random.int (Z.to_int (count.(id).(n))) in
                let randZ = Z.of_int randInt in
         if randZ < count.(a).(n) then
           (generator grammar count a n bp)
         else (generator grammar count b n bp)
       | Grammar.Union (Reference(a), Z(b)) -> let randInt = Random.int (Z.to_int (count.(id).(n))) in
                let randZ = Z.of_int randInt in
                if randZ < count.(a).(n) then generator grammar count a n bp
                else generateZ (Grammar.Z(b)) n
       | Grammar.Union (Z(a), Reference(b)) -> let countZ = (Z.sub count.(id).(n)  count.(a).(n)) in
                let randInt = Random.int (Z.to_int (count.(id).(n))) in
                let randZ = Z.of_int randInt in
                if randZ < countZ then generateZ (Grammar.Z(a)) n
                else generator grammar count b n bp
       | Grammar.Product (Reference(a), Reference(b)) -> let randInt = (Random.int (Z.to_int (count.(id).(n)))) in
                let randZ = Z.of_int randInt in
                let i = ref 0 in
                let order = ref 0 in
                let s = ref (Z.mul count.(a).(!i) count.(b).(n-(!i))) in
                while (Z.leq (!s) randZ) do
                  if (bp<>(-1)) && (!order =1) then
                    (s := (Z.add !s (Z.mul count.(a).(n-(!i)) count.(b).(!i)));
                     order:= 0)
                  else
                  (i := !i + 1;
                  order:=1;
                  s := (Z.add !s (Z.mul count.(a).(!i)  count.(b).(n-(!i)))))
                done;
                Tree.Node (grammar.names.(id), [generator grammar count a (!i) bp ; generator grammar count b (n-(!i)) bp])
       | Grammar.Product (Z(a), Reference(b)) -> Tree.Node (grammar.names.(id),  [generateZ (Grammar.Z(a)) a; generator grammar count b (n-a) bp])

       | _ -> print_string "not handled in generator\n"; Tree.Node ("Unknown", [])
