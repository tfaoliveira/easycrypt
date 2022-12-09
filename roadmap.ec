(*
module M = {
  proc h() = {
  @L:
  }

  proc f() = {
  @L1:
  }

  proc g() = {
  @L2:
  }
}.

equiv [M.f ~ M.g : pre ==> post | {
  (L1, L2) --> assertion
  ...
}].
*)



(*
  - faire un petite exemple qui fixe la syntaxe

  - modifier PST
      - ecParsetree.ml
        - instructions: pinstr
        - PFequivF(pre, (f, g), post), labels) -> assert: prhl

  - étendre parseur
      - ecParser.mly (menhir)
         - formule: sform_u [equiv étendu]
         - procedures: base_instr [instructions]

  - modifier AST
      - ecCoreModule.ml
        - instructions: instr
        - hash-consing + constructeurs / destructeurs
        - substitutions (no-op) ?
      - ecCoreFol.ml
        - equivF[proc] / equivS[stmt]

  - adapter typeur
      - ecTyping.ml
         - trans_form_or_pattern
         - transinstr
      - étendre environnement avec les labels

  - implémeter les règles de la logique (+ parser)
      - phl/* [un fichier par tactique]

  - exemples

  - profits
*)
