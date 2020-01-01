(* Algorithms for counting the number of elements of combinatorial classes. *)

(* type specs : {names: string array; rules: int expression array} *)

let rec count arrays (specs: Grammar.t) (expr: int Grammar.expression) (y: int) (iName: int) (canSet: bool) =	 
       match expr with
       | Z i -> let res = (if (i == y) then 1 else 0) in 
		if canSet then (Array.set (Array.get arrays iName) y res; res)
		else res
       | Union(op1, op2) -> let op1_y = count arrays specs op1 y iName false in
			    let op2_y = count arrays specs op2 y iName false in 
			    let res = op1_y + op2_y in
			    if canSet then (Array.set (Array.get arrays iName) y res; res) 
			    else res
       | Product(op1, op2) -> let sum = ref 0 in 
			      for k = 0 to y do 
			         let op1_k = count arrays specs op1 k iName false in
				 let op2_n_k = count arrays specs op2 (y-k) iName false in
				 sum := (!sum + op1_k * op2_n_k)
			      done;
			      if canSet then ((Array.set (Array.get arrays iName) y !sum; !sum))
			      else !sum
			      
       | Reference r -> if ( (Array.get (Array.get arrays r) y == -2) ) then 0 
			else (
			   if (Array.get (Array.get arrays r) y == -1) then Array.set (Array.get arrays r) y (-2);
			   let tmp = Array.get (Array.get arrays r) y in 
			   if(tmp >= 0) then tmp else count arrays specs (Array.get specs.rules r) y r true
                        )

       | _ -> -1 (* not handled *)	
 

 

let rec hasAtMostAtomeSizeZero (expr: int Grammar.expression) = 
	match expr with
	| Z 0 -> true
	| Z _ -> false
	| Product(op1,op2) -> (hasAtMostAtomeSizeZero op1) && (hasAtMostAtomeSizeZero op2)
	| _ -> true

let rec countUnionProductZero arrays (specs: Grammar.t) (expr: int Grammar.expression) (iName: int) =
   match expr with
   | Z n -> if(n == 0) then 1 else 0
   | Union(op1, op2) -> let countOp1 = countUnionProductZero arrays specs op1 iName in
			   let countOp2 = countUnionProductZero arrays specs op2 iName in
			      (countOp1 + countOp2)
   | Product(op1, op2) -> if(hasAtMostAtomeSizeZero expr) then
			  	(let countOp1 = countUnionProductZero arrays specs op1 iName in
			     	let countOp2 = countUnionProductZero arrays specs op2 iName in
			        	(countOp1 * countOp2)
                                )
			  else 0
   | Reference r -> if( (Array.get (Array.get arrays r) 0) != -1) then 
			(Array.get (Array.get arrays r) 0) else
			begin
			   countSizeZero arrays specs (Array.get specs.rules r) r;
			    if( (Array.get (Array.get arrays r) 0) != -1) then
				(Array.get (Array.get arrays r) 0)  else
				(print_string "should not happen countUnionZero\n"; 
				(-1) ) 
			end	
   | _ -> -1 (* not handled *)
			

and countSizeZero arrays (specs: Grammar.t) (expr: int Grammar.expression) (iName: int) = 
   match expr with
   | Z n -> if(n == 0) then ( (Array.set (Array.get arrays iName) 0 1)) else (Array.set (Array.get arrays iName) 0 0)
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
   let (countArrays: int array array) = (Array.make_matrix specSize (n+1) (-1)) in
   (* countArrays[i][y] = count(specs.names[i], y), if = -1 not yet computed, if = -2 is currently computing*)
   
   for j = 0 to (specSize-1) do (* printing names *)  
      Printf.printf "names[%d] = %s\n" j (Array.get specs.names j);
   done;

   for j = 0 to (specSize-1) do (* counting number of objets of size 0 for each spec in specs *) 
      countSizeZero countArrays specs (Array.get specs.rules j) j
   done;

   for j = 0 to (specSize-1) do (* printing number of objets of size 0 for each spec in specs *) 
      Printf.printf "count[%d][0] = %d\n" j (Array.get (Array.get countArrays j) 0)
   done;
   for j = 0 to (specSize-1) do (* printing specs in AST form *) 
      Printf.printf "%s ::= " (Array.get specs.names j); (printSpec (Array.get specs.rules j)); print_string "\n"
   done; 
   (for iName = 0 to (specSize-1) do (* counting *)
      (for y = 1 to n do
	let (expr: int Grammar.expression) = (Array.get specs.rules iName) in
	let tmp = (Array.get (Array.get countArrays iName) y) in (* tmp = count[iName][y] (= -1 or >= 0) *)
	if(tmp == -1) then Array.set (Array.get countArrays iName) y (-2); (* if tmp = -1 set count[iName][y] to -2 (currently computing) *)
      	let _ = if (tmp >= 0) then tmp else (count countArrays specs (expr) y iName true) in () (* if tmp >=0 count already computed *)
      done);
   done);
   countArrays (* returning the count matrix *)


