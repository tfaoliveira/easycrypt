(* -------------------------------------------------------------------- *)
open EcParsetree
open EcSMatching



(* -------------------------------------------------------------------- *)
val trans_stmt : pim_regexp -> regexp_instr

val trans_block : pim_block -> regexp_instr
