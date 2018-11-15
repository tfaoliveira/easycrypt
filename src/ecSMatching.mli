open EcGenRegexp
open EcPattern
open EcModules
open EcMaps
open EcEnv

type regexp_instr = regexp1_instr gen_regexp


and regexp1_instr =
  | RAssign    of pattern * pattern
  | RSample    of pattern * pattern
  | RCall      of pattern * pattern * pattern
  | RIf        of pattern * regexp_instr * regexp_instr
  | RWhile     of pattern * regexp_instr


module RegexpStmt : sig
  type regexp  = regexp_instr
  type subject = instr list
  type matches = subject Mstr.t

  val search : regexp -> subject -> LDecl.hyps -> (EcPattern.map * matches) option
end
