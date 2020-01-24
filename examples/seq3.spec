
// grammar file for binary trees (counting leaves and internal nodes)
// with parameters to obtain trees of size about 100000

set min 10000
set max 20000
set try 10000

A ::=  SEQ(A) * <z>
B ::=  SEQ(A) * <z> * <z>
