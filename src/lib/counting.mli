
val count: (Z.t array array) -> Grammar.t -> int Grammar.expression -> int -> int -> bool -> Z.t

val countAll: Grammar.t -> int -> (Z.t array array) * Grammar.t

val execTime: Grammar.t -> int -> string -> unit

val memoryUsage: Grammar.t -> int -> string -> unit

val memoryUsageDivByNumberOfRules: Grammar.t -> int -> string -> unit
