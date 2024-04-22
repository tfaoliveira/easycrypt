open EcPath
open EcAst
open EcEnv

val module_uses : env -> mpath -> module_type -> mem_restr

val equal    : env -> mem_restr -> mem_restr -> bool
val subset   : env -> mem_restr -> mem_restr -> bool
val disjoint : env -> mem_restr -> mem_restr -> bool
val is_mem   : env -> bool -> global -> mem_restr -> bool
val has_quantum : env -> mem_restr -> bool
