open EcPath
open EcAst
(* Nothing is allowed *)
val mer_empty : mem_restr

(* the full memory *)
val mer_full   : mem_restr


val mer_union : mem_restr -> mem_restr -> mem_restr
val mer_inter : mem_restr -> mem_restr -> mem_restr
val mer_diff  : mem_restr -> mem_restr -> mem_restr

val mer_vars : Sglob.t -> mem_restr
val mer_classicals : Sx.t -> mem_restr
val mer_quantums   : Sx.t -> mem_restr

val mer_globfun : functor_params -> xpath -> mem_restr
val mer_globfuns : functor_params -> Sx.t -> mem_restr
