(* Algorithms for counting the number of elements of combinatorial classes. *)

(* type specs : {names: string array; rules: int expression array} *)

let rec countUP arrays (specs: Grammar.t) (expr: int Grammar.expression) (iName: int) (y: int) = 
     begin
        match expr with
	| Z _ -> count arrays specs expr iName y
	| Union(op1, op2) -> let op1_y = (count arrays specs op1 iName y) in
			        let op2_y = (count arrays specs op2 iName y) in
				let res = op1_y + op2_y in Printf.printf "%d + %d = %d\n" op1_y op2_y (op1_y + op2_y); res
	| Product(op1,op2) -> let sum = ref 0 in
	    		        for k = 0 to y do
				   let op1_k = count arrays specs op1 iName k in
				   let op2_n_k = count arrays specs op2 iName (y-k) in
				   Printf.printf "n = %d P : %d + %d * %d = %d\n" y !sum op1_k op2_n_k (!sum + op1_k * op2_n_k);
				   sum := (!sum + op1_k * op2_n_k)
			        done;
			        !sum
				
	| Reference r -> let tmp = (Array.get (Array.get arrays r) y) in
  			 if tmp != -1 then tmp 
			 else let res = count arrays specs (Array.get specs.rules r) r y in res
	| _ -> print_string "countUnion not handled\n"; -1

     end


and count arrays (specs: Grammar.t) (expr: int Grammar.expression) (iName: int) (y: int) = (* counting arrays[iName][y] *)
     begin
        match (expr) with
        | Z i -> let tmp = (Array.get (Array.get arrays iName) y) in
		 if tmp != -1 then tmp 
		 else
		 let res = (if(i == y) then 1 else 0) in
	            Printf.printf "Z : arrays[%d][taille:%d] = %d\n" iName y res;
		    if( Array.get (Array.get arrays iName) y < res) then 
	               (Array.set (Array.get arrays iName) y res; res)
	            else res

        | Product(_, _) -> let res = countUP arrays specs expr iName y in
			       Printf.printf "Product : arrays[%d][taille:%d] = %d\n" iName y res;
			       if( Array.get (Array.get arrays iName) y < res) then 
			          (Array.set (Array.get arrays iName) y res; res)
			       else res

        |Union(_, _) -> let res = countUP arrays specs expr iName y in
			    Printf.printf "Union : arrays[%d][taille:%d] = %d\n" iName y res;
			    if( Array.get (Array.get arrays iName) y < res) then 
			       (Array.set (Array.get arrays iName) y res; res)
			    else res

	| Reference r -> let tmp = (Array.get (Array.get arrays r) y) in
  		         if tmp != -1 then tmp 
			 else 
			 let res = count arrays specs (Array.get specs.rules r) r y in 
			    Printf.printf "Reference : arrays[%d][taille:%d] = %d\n" iName y res;
			    if( Array.get (Array.get arrays iName) y < res) then 
			       (Array.set (Array.get arrays iName) y res; res)
			    else res 

	| Seq(_) -> -1 (* not handled yet *)
     end

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

let countAll (specs: Grammar.t) n = 
   let specSize = (Array.length specs.names) in
   let (countArrays: int array array) = (Array.make_matrix specSize (n+1) (-1)) in
   (* countArrays[i][y] = count(specs.names[i], y), if = -1 not yet computed *)
   
   for j = 0 to (specSize-1) do (* printing names *)  
      Printf.printf "names[%d] = %s\n" j (Array.get specs.names j);
   done;

   for j = 0 to (specSize-1) do (* counting number of objets of size 0 for each spec in specs *) 
      countSizeZero countArrays specs (Array.get specs.rules j) j
   done;

   for j = 0 to (specSize-1) do (* printing number of objets of size 0 for each spec in specs *) 
      Printf.printf "count[%d][0] = %d\n" j (Array.get (Array.get countArrays j) 0)
   done;

   (for iName = 0 to (specSize-1) do (* counting *)
      (for y = 1 to n do
	let (expr: int Grammar.expression) = (Array.get specs.rules iName) in
      	let _ = (count countArrays specs (expr) iName y) in ()
      done);
   done);
   countArrays


