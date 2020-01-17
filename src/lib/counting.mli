
val count: (Z.t array array) -> Grammar.t -> int Grammar.expression -> int -> int -> bool -> Z.t

val countAll: Grammar.t -> int -> (Z.t array array) * Grammar.t

val countSizeZero: (Z.t array array) -> Grammar.t -> int Grammar.expression -> int -> unit

val countUnionProductZero: (Z.t array array) -> Grammar.t -> int Grammar.expression -> int -> Z.t
