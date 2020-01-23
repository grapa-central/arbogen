
// grammar file for binary trees (counting leaves and internal nodes)
// with parameters to obtain trees of size about 100000

set min 1000000
set max 2000000
set try 5000

UB ::= Unary + Binary
Unary ::= <z> + Unary * Unary * <z> + Unary * <z> + Unary * Unary * <z> * Unary * <z> *Unary
Binary ::= <z> + Binary * Binary * <z>
