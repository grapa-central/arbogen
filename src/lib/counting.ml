(* Algorithms for counting the number of elements of combinatorial classes. *)

(* type specs : {names: string array; rules: int expression array} *)

let getAtomeInfo (expr: int Grammar.expression) =
  match expr with
  | Z i -> (true,i)
  | _ -> (false,-1)

let isAtome (expr: int Grammar.expression) =
   match expr with
   | Z _ -> true
   | _ -> false

let rec count arrays (specs: Grammar.t) (expr: int Grammar.expression) (y: int) (iName: int) (canSet: bool) =
  if y == (-1) then (Z.of_int 0)
  else
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

    let (isAtome, aSize) = (getAtomeInfo op1) in
    if isAtome then (* optimizing product if atome as left operand *)
	 let op1_k = count arrays specs op1 aSize iName false in
         let op2_n_k = count arrays specs op2 (y-aSize) iName false in
         sum := (Z.add !sum (Z.mul op1_k op2_n_k) )
    else (
       for k = 0 to y do
         let op1_k = count arrays specs op1 k iName false in
         let op2_n_k = count arrays specs op2 (y-k) iName false in
         sum := (Z.add !sum (Z.mul op1_k op2_n_k) )
       done
    );
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
  | _ -> Printf.printf "case not handled in count\n"; (Z.of_int (-1)) (* not handled *)

let rec printSpec (expr: int Grammar.expression) =
   match expr with
   | Z i -> Printf.printf "Z %d" i
   | Union(op1, op2) -> print_string "Union("; (printSpec op1); print_string ", "; (printSpec op2); print_string ")"
   | Product(op1, op2) ->print_string "Product("; (printSpec op1); print_string ", "; (printSpec op2); print_string ")"
   | Reference r -> Printf.printf "Reference %d" r
   | _ -> () (* not handled *)



let rec consProductWithList opList =
   match opList with
   | h1::h2::[] -> Grammar.Product(h1, h2)
   | h1::q -> Grammar.Product(h1, (consProductWithList q))
   | [] -> print_string "should not happen in consPWL\n"; (Grammar.Z (-1))

let rec getListWithAtomesOnLeft opList =
   match opList with
   | [] -> []
   | h::q -> if (isAtome h) then h::(getListWithAtomesOnLeft q)
	     else List.append (getListWithAtomesOnLeft q) (h::[])

let rec getProductListOfOperands (expr: int Grammar.expression) =
   match expr with
   | Product(op1, op2) -> let listOp1 = getProductListOfOperands op1 in
			  let listOp2 = getProductListOfOperands op2 in
			  List.append listOp1 listOp2
   | _ -> expr::[]

let rec getOptimisedExpr (expr: int Grammar.expression) = (* optimizing Product by putting all atomes (ie Grammar.Z) to the left *)
   match expr with
   | Union(op1, op2) -> Grammar.Union((getOptimisedExpr op1), (getOptimisedExpr op2))
   | Product(_,_) -> let operands = getListWithAtomesOnLeft (getProductListOfOperands expr) in
			 consProductWithList operands
   | _ -> expr


let rec isEqualExpr (exprA: int Grammar.expression) (exprB: int Grammar.expression) =
   match (exprA, exprB) with
   | (Z i, Z y) -> if (i == y) then true else false
   | (Reference i, Reference y) -> if (i == y) then true else false
   | (Union(op1A, op2A), Union(op1B, op2B)) -> let left = (isEqualExpr op1A op1B) in
					       let right = (isEqualExpr op2A op2B) in (* We do not check op1A == op2B && op2A == op1B *)
					       if (left && right) then true else false
   | (Product(op1A, op2A), Product(op1B, op2B)) -> let left = (isEqualExpr op1A op1B) in
					           let right = (isEqualExpr op2A op2B) in
					           if (left && right) then true else false
   | (_,_) -> false (* not handled *)



let rename (specs: Grammar.t) (expr: int Grammar.expression) mapSeq=
   match expr with
     | Union(_,_) -> let specsSize = (Array.length specs.names) in
       let isDuplicate = ref false in
       let duplicateRef = ref (-1) in
       for i = 0 to (specsSize -1) do
         let tmp = (isEqualExpr (Array.get specs.rules i) expr) in
         if (tmp && (!isDuplicate == false)) then (isDuplicate := tmp; duplicateRef := i)
       done;
       if (!isDuplicate) then
         (!duplicateRef, !isDuplicate)
       else
         (let newName = ("_rename_" ^(string_of_int specsSize)) in
		      let tmpArray = (Array.make 1 newName) in
		      let tmpArrayExpr = (Array.make 1 expr) in
                      specs.names <- (Array.append specs.names tmpArray);
		      specs.rules <- (Array.append specs.rules tmpArrayExpr);
		      (specsSize, true))
   | Product(_,_) -> let specsSize = (Array.length specs.names) in
     let isDuplicate = ref false in
     let duplicateRef = ref (-1) in

     for i = 0 to (specsSize -1) do
       let tmp = (isEqualExpr (Array.get specs.rules i) expr) in
       if (tmp && (!isDuplicate == false)) then (isDuplicate := tmp; duplicateRef := i)
     done;

     if (!isDuplicate) then
       (!duplicateRef, !isDuplicate)
     else (
       let newName = ("_rename_" ^(string_of_int specsSize)) in
       let tmpArray = (Array.make 1 newName) in
       let tmpArrayExpr = (Array.make 1 expr) in
       specs.names <- (Array.append specs.names tmpArray);
       specs.rules <- (Array.append specs.rules tmpArrayExpr);
       (specsSize, true))

   | Seq e ->
     let specsSize = (Array.length specs.names) in
     let valueFind = ref (-1) in
     let duplicateRef = ref (-1) in
     let alreadyExist = ref false in
     let result_find = Hashtbl.find_opt mapSeq e in

     alreadyExist := ( match result_find with
         | None -> false
         | Some e -> valueFind:= e; true );

     if (!alreadyExist) then
       (duplicateRef := !valueFind;
        (!duplicateRef, true))
     else(
       let newName = ("_rename_" ^(string_of_int specsSize))  in
       let tmpArray = (Array.make 1 newName) in
       let exp = Grammar.Union(Z 0, Grammar.Product( e , Reference specsSize)) in
       let tmpArrayExpr = (Array.make 1 (exp)) in
       specs.rules <- (Array.append specs.rules tmpArrayExpr);
       specs.names <- (Array.append specs.names tmpArray);
       Hashtbl.add mapSeq e specsSize;
       (specsSize, true))
   | _ -> ((-1), false)

  let renameSpec (specs: Grammar.t) (expr: int Grammar.expression) my_hash =
   match expr with
   | Z _ -> expr
   | Reference _ -> expr
   | Union(op1, op2) -> let (referenceNumberOp1, renamingOp1) = rename specs op1 my_hash in
			let (referenceNumberOp2, renamingOp2) = rename specs op2 my_hash in
			(match (renamingOp1, renamingOp2) with
			| (true, true) ->
			   Union(Reference referenceNumberOp1, Reference referenceNumberOp2);
 			| (true, false) ->
      Union(Reference referenceNumberOp1, op2);
    | (false, true) ->
      Union(op1, Reference referenceNumberOp2)
    | (false, false) ->
			   expr)
   | Product(op1, op2) ->
      let (referenceNumberOp1, renamingOp1) = rename specs op1 my_hash in
      let (referenceNumberOp2, renamingOp2) = rename specs op2 my_hash in
      (match (renamingOp1, renamingOp2) with
      | (true, true) ->
        Product(Reference referenceNumberOp1, Reference referenceNumberOp2);
      | (true, false) ->
        Product(Reference referenceNumberOp1, op2);
      | (false, true) -> Product(op1, Reference referenceNumberOp2)
      | (false, false) ->
        expr)
   | Seq _ ->
     let (referenceNumberE, _) = rename specs expr my_hash in Reference referenceNumberE


let renameSpecs (specs: Grammar.t) =
  let i = ref 0 in
  let my_hash = Hashtbl.create 1 in
   while (!i < (Array.length specs.names)) do
      (let renamed = (renameSpec specs (Array.get specs.rules !i) my_hash) in
      (Array.set specs.rules !i renamed);
      i := !i + 1)
   done

let countAll (specs: Grammar.t) n =
   renameSpecs specs;
   let specSize = (Array.length specs.names) in

   let (countArrays: Z.t array array) = ( Array.make_matrix specSize (n+1) (Z.of_int (-1)) ) in

   print_string "Renamed spec :\n";
   for j = 0 to (specSize-1) do (* printing specs in AST form *)
      Printf.printf "%s ::= " (Array.get specs.names j); (printSpec (Array.get specs.rules j)); print_string "\n"
   done;

   print_string "\nOptimised spec : (for Product)\n";
   for j = 0 to (specSize-1) do (* printing specs in AST form *)
      let nexpr = (getOptimisedExpr (Array.get specs.rules j)) in
      (Array.set specs.rules j nexpr);
      Printf.printf "%s ::= " (Array.get specs.names j); (printSpec (Array.get specs.rules j)); print_string "\n"
   done;
   print_string "\n";	
  (for y = 0 to n do
     (for iName = 0 to (specSize-1) do (* counting *)
        let (expr: int Grammar.expression) = (Array.get specs.rules iName) in
        let tmp = (Array.get (Array.get countArrays iName) y) in (* tmp = count[iName][y] (= -1 or >= 0) *)

        if(Z.equal tmp (Z.of_int (-1))) then
          Array.set (Array.get countArrays iName) y (Z.of_int (-2)); (* if tmp = -1 set count[iName][y] to -2 (currently computing) *)
        let _ = if (Z.geq tmp (Z.of_int 0)) then  tmp
          else (count countArrays specs (expr) y iName true) in () (* if tmp >=0 count already computed *)
      done);
    done);
   (countArrays, specs) (* returning the count matrix and the modified specs*)

let execTime (specs: Grammar.t) n outputFile =
	let out = open_out outputFile in
	let rec aux y = 
		let time = Unix.gettimeofday () in
		let (_,_) = countAll specs y in
		Printf.fprintf out "%d %f\n" y (Unix.gettimeofday () -. time);
		if (y -100) >= 0 then aux (y -100) else ()
	in aux n;
	close_out out

let memoryUsage (specs: Grammar.t) n outputFile =
	let out = open_out outputFile in
	let rec aux y = 
		let (startMinor, startPromoted, startMajor) = Gc.counters () in
		let startMemoryUsage = (startMinor +. startMajor -. startPromoted) *. 8.0 in
		let (_,_) = countAll specs y in
		let (endMinor, endPromoted, endMajor) = Gc.counters () in
		let endMemoryUsage = (endMinor +. endMajor -. endPromoted) *. 8.0 in
		Printf.fprintf out "%d %f\n" y (endMemoryUsage -. startMemoryUsage);
		if (y -100) >= 0 then aux (y -100) else ()
	in aux n;
	close_out out

let memoryUsageDivByNumberOfRules (specs: Grammar.t) n outputFile = 
	let out = open_out outputFile in
	let nbRules = (float_of_int (Array.length specs.rules)) in
	let rec aux y = 
		let (startMinor, startPromoted, startMajor) = Gc.counters () in
		let startMemoryUsage = (startMinor +. startMajor -. startPromoted) *. 8.0 in
		let (_,_) = countAll specs y in
		let (endMinor, endPromoted, endMajor) = Gc.counters () in
		let endMemoryUsage = (endMinor +. endMajor -. endPromoted) *. 8.0 in
		Printf.fprintf out "%d %f\n" y ((endMemoryUsage -. startMemoryUsage) /. nbRules);
		if (y -100) >= 0 then aux (y -100) else ()
	in aux n;
	close_out out

