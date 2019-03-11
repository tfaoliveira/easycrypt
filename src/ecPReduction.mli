open EcPattern



val reduce_local_opt  : EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                        Psubst.p_subst -> pattern -> Name.t ->
                        pbindings option -> pattern option

val p_can_eta         : EcEnv.LDecl.hyps -> EcIdent.Mid.key ->
                        pattern * pattern list -> bool
val can_eta           : EcIdent.Mid.key -> EcFol.form * EcFol.form list ->
                        bool

val h_red_pattern_opt : (EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                         EcPattern.pattern -> EcPattern.pattern -> bool) ->
                        EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                        Psubst.p_subst -> pattern -> pattern option

val h_red_axiom_opt   : (EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                         EcPattern.pattern -> EcPattern.pattern -> bool) ->
                        EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                        Psubst.p_subst -> axiom -> pattern option
