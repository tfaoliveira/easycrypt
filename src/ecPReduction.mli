open EcPattern



val reduce_local_opt  : EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                        Name.t -> pattern option

val p_can_eta         : EcEnv.LDecl.hyps -> EcIdent.Mid.key ->
                        pattern * pattern list -> bool
val can_eta           : EcIdent.Mid.key -> EcFol.form * EcFol.form list ->
                        bool

val h_red_pattern_opt : ?verbose:bool ->
                        (EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                         EcPattern.pattern -> EcPattern.pattern -> bool) ->
                        EcEnv.LDecl.hyps -> EcReduction.reduction_info ->
                        Psubst.p_subst -> pattern -> pattern option
