(* Algorithms for counting the number of elements of combinatorial classes. *)

(* type specs : {names: string array; rules: int expression array} *)

let rec count arrays (specs: Grammar.t) (expr: int Grammar.expression) (y: int) (iName: int) (canSet: bool) =
  match expr with
  | Z i -> let res = (if (i == y) then Z.of_int 1 else Z.of_int 0) in
    if canSet then (Array.set (Array.get arrays iName) y res; res)
    else res

  | Union(op1, op2) -> let op1_y = count arrays specs op1 y iName false in
    let op2_y = count arrays specs op2 y iName false in
    let res = (Z.add op1_y op2_y) in
    if canSet then (Array.set (Array.get arrays iName) y res; res)
    else res

  | Product(op1, op2) -> let sum = ref (Z.of_int 0) in
    for k = 0 to y do
      let op1_k = count arrays specs op1 k iName false in
      let op2_n_k = count arrays specs op2 (y-k) iName false in
      sum := (Z.add !sum (Z.mul op1_k op2_n_k) )
    done;
    if canSet then ((Array.set (Array.get arrays iName) y !sum; !sum))
    else !sum

  | Reference r -> if ( (Z.equal (Array.get (Array.get arrays r) y) (Z.of_int (-2))) )
    then Z.of_int 0
    else (
      if (Z.equal (Array.get (Array.get arrays r) y) (Z.of_int (-1)) ) then
        Array.set (Array.get arrays r) y (Z.of_int (-2));
      let tmp = Array.get (Array.get arrays r) y in
      if(Z.geq tmp (Z.of_int 0)) then tmp
      else count arrays specs (Array.get specs.rules r) y r true
    )
  | _ -> (Z.of_int (-1)) (* not handled *)

(*
let rec count_bis arrays (specs: Grammar.t) (expr: int Grammar.expression) (iName: int) (y: int) = (* counting arrays[iName][y] *)
    begin
      match (expr) with
      | Z i -> let tmp = (Array.get (Array.get arrays iName) y) in
        if (not (Z.equal tmp (Z.pred (Z.of_int 0))) ) then tmp
        else
          let res = (if(i == y) then Z.of_int 1 else Z.of_int 0) in
          Printf.printf "Z : arrays[%d][taille:%d] = %s\n" iName y (Z.to_string res);
          if( Z.gt (Array.get (Array.get arrays iName) y) res ) then
            (Array.set (Array.get arrays iName) y res; res)
          else res

      | Product(op1, op2) ->
        let res = (let sum = ref (Z.of_int 0) in
                   for k = 0 to y do
                     let op1_k = count_bis arrays specs op1 iName k in
                     let op2_n_k = count_bis arrays specs op2 iName (y-k) in
                     let new_sum = (Z.add !sum (Z.mul op1_k  op2_n_k) ) in
                     Printf.printf "n = %d P : %s + %s * %s = %s\n" y (Z.to_string !sum) (Z.to_string op1_k) (Z.to_string op2_n_k) (Z.to_string new_sum);
                     sum := new_sum
                   done;
                   !sum) in
        Printf.printf "Product : arrays[%d][taille:%d] = %s\n" iName y (Z.to_string res);
        if( Z.lt (Array.get (Array.get arrays iName) y) res) then
          (Array.set (Array.get arrays iName) y res; res)
        else res

      | Union(op1,op2) ->
        let res  = (let op1_y = (count_bis arrays specs op1 iName y) in
                    let op2_y = (count_bis arrays specs op2 iName y) in
                    (Z.add op1_y op2_y) ) in
        Printf.printf "Union : arrays[%d][taille:%d] = %s\n" iName y (Z.to_string res);
        if( Z.lt (Array.get (Array.get arrays iName) y) res) then
          (Array.set (Array.get arrays iName) y res; res)
        else res

      | Reference r -> let tmp = (Array.get (Array.get arrays r) y) in
        if (not (Z.equal tmp (Z.pred (Z.of_int 0))) ) then tmp
        else
          let res = count_bis arrays specs (Array.get specs.rules r) r y in
          Printf.printf "Reference : arrays[%d][taille:%d] = %s\n" iName y (Z.to_string res);
          if( Z.lt (Array.get (Array.get arrays iName) y) res) then
            (Array.set (Array.get arrays iName) y res; res)
          else res

      | Seq(_) -> (Z.pred (Z.of_int 0)) (* not handled yet *)
    end
*)

let rec hasAtMostAtomeSizeZero (expr: int Grammar.expression) =
	match expr with
	| Z 0 -> true
	| Z _ -> false
	| Product(op1,op2) -> (hasAtMostAtomeSizeZero op1) && (hasAtMostAtomeSizeZero op2)
	| _ -> true

let rec countUnionProductZero arrays (specs: Grammar.t) (expr: int Grammar.expression) (iName: int) =
   match expr with
   | Z n -> if(n==0) then Z.of_int 1 else Z.of_int 0
   | Union(op1, op2) -> let countOp1 = countUnionProductZero arrays specs op1 iName in
			   let countOp2 = countUnionProductZero arrays specs op2 iName in
			      (Z.add countOp1  countOp2)
   | Product(op1, op2) -> if(hasAtMostAtomeSizeZero expr)
     then
       (let countOp1 = countUnionProductZero arrays specs op1 iName in
        let countOp2 = countUnionProductZero arrays specs op2 iName in
        (Z.mul countOp1  countOp2))
     else Z.of_int 0
   | Reference r -> if( not (Z.equal (Array.get (Array.get arrays r) 0) (Z.of_int (-1))) )
     then	(Array.get (Array.get arrays r) 0)
     else
       begin
         countSizeZero arrays specs (Array.get specs.rules r) r;
         if( not (Z.equal (Array.get (Array.get arrays r)  0) (Z.of_int (-1))) )
         then
           (Array.get (Array.get arrays r)  0)
         else
           (print_string "should not happen countUnionZero\n"; (Z.of_int (-1)) )
			end
   | _ -> (Z.of_int (-1)) (* not handled *)



and countSizeZero arrays (specs: Grammar.t) (expr: int Grammar.expression) (iName: int) =
  match expr with
  | Z n -> if(n == 0)
    then ( Array.set (Array.get arrays iName) 0 (Z.of_int 1) )
    else ( Array.set (Array.get arrays iName) 0 (Z.of_int 0) )

   | Union(_, _) -> let count = (countUnionProductZero arrays specs expr iName) in 
			   ((Array.set (Array.get arrays iName) 0 count))
   | Product(_,_) -> let count = (countUnionProductZero arrays specs expr iName) in
			    ((Array.set (Array.get arrays iName) 0 count))
   | _ -> () (* not handled *)


let rec printSpec (expr: int Grammar.expression) =
   match expr with
   | Z i -> Printf.printf "Z %d" i
   | Union(op1, op2) -> print_string "Union("; (printSpec op1); print_string ", "; (printSpec op2); print_string ")"
   | Product(op1, op2) ->print_string "Product("; (printSpec op1); print_string ", "; (printSpec op2); print_string ")"
   | Reference r -> Printf.printf "Reference %d" r
   | _ -> () (* not handled *)


let countAll (specs: Grammar.t) n =
   let specSize = (Array.length specs.names) in

   let (countArrays: Z.t array array) = ( Array.make_matrix specSize (n+1) (Z.of_int (-1)) ) in
   (* countArrays[i][y] = count(specs.names[i], y), if = -1 not yet computed, if = -2 is currently computing*)
   for j = 0 to (specSize-1) do (* printing names *)

      Printf.printf "names[%d] = %s\n" j (Array.get specs.names j);
   done;

   for j = 0 to (specSize-1) do (* counting number of objets of size 0 for each spec in specs *)
      countSizeZero countArrays specs (Array.get specs.rules j) j
   done;

   for j = 0 to (specSize-1) do (* printing number of objets of size 0 for each spec in specs *)
     Printf.printf "count[%d][0] = %s\n" j (Z.to_string (Array.get (Array.get countArrays j) 0))
   done;
   for j = 0 to (specSize-1) do (* printing specs in AST form *)
      Printf.printf "%s ::= " (Array.get specs.names j); (printSpec (Array.get specs.rules j)); print_string "\n"
   done;
  (for y = 1 to n do
     (for iName = 0 to (specSize-1) do (* counting *)
        let (expr: int Grammar.expression) = (Array.get specs.rules iName) in
        let tmp = (Array.get (Array.get countArrays iName) y) in (* tmp = count[iName][y] (= -1 or >= 0) *)

        if(Z.equal tmp (Z.of_int (-1))) then
          Array.set (Array.get countArrays iName) y (Z.of_int (-2)); (* if tmp = -1 set count[iName][y] to -2 (currently computing) *)
        let _ = if (Z.geq tmp (Z.of_int 0)) then  tmp
          else (count countArrays specs (expr) y iName true) in () (* if tmp >=0 count already computed *)
      done);
    done);
    (*
    (for iName = 0 to (specSize-1) do (* counting *)
     (for y = 1 to n do
        let (expr: int Grammar.expression) = (Array.get specs.rules iName) in
        let _ = (count_bis countArrays specs (expr) iName y) in ()
      done);
   done);*)
   countArrays (* returning the count matrix *)
