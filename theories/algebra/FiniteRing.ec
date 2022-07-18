(* ==================================================================== *)
require import AllCore List Ring Int IntMin IntDiv RingStruct FinType ZModP.
require import Bigalg SubRing RingModule Real RealExp Quotient.
require (*--*) Subtype.
(*---*) import StdOrder.IntOrder.


(* ==================================================================== *)
abstract theory SubFinite.
  type t, st.

  op p : t -> bool.

  clone import FinType as FT with
    type t <= t.

  clone import Subtype as Sub with
    type T  <- t ,
    type sT <- st,
    pred P  <- p.

  import Sub.

  op senum = map insubd (filter p enum).

  clone import FinType as SFT with
    type t  <= st,
    op enum <- senum
    proof *.

  realize enum_spec.
  proof.
    move => x; rewrite /senum count_map count_filter /predI /preim.
    rewrite -(enum_spec (val x)); apply/eq_count.
    move => y; rewrite /pred1 /=; split => [[<<- in_sub_y]|->>].
    + by rewrite val_insubd in_sub_y.
    by rewrite valKd /= valP.
  qed.
end SubFinite.


(* ==================================================================== *)
abstract theory FiniteZModule.
  type t.

  clone import ZModule as ZMod with
    type t <= t.

  clone import FinType.FinType as FinType with
    type t <= t.
end FiniteZModule.

(* -------------------------------------------------------------------- *)
abstract theory FiniteComRing.
  type t.

  clone import ComRing as CR with
    type t <= t.

  clone include FiniteZModule with
    type t      <- t,
    theory ZMod <- CR.

  lemma card_gt1: 1 < FinType.card.
  proof.
    rewrite /FinType.card ltzE /=; have <-: size [CR.zeror; CR.oner] = 2 by trivial.
    apply/uniq_leq_size => //=; [by rewrite eq_sym; apply/CR.oner_neq0|].
    by move => ? _; apply/FinType.enumP.
  qed.
end FiniteComRing.

(* -------------------------------------------------------------------- *)
abstract theory FiniteIDomain.
  type t.

  clone import IDomain as ID with
    type t <= t.

  clone include FiniteComRing with
    type t    <- t,
    theory CR <- ID.
end FiniteIDomain.

(* -------------------------------------------------------------------- *)
abstract theory FiniteField.
  type t.

  clone import Field as F with
    type t <= t.

  clone include FiniteIDomain with
    type t    <- t,
    theory ID <- F.
end FiniteField.


(* ==================================================================== *)
abstract theory FiniteZModuleStruct.
  type t.

  clone import ZModule as ZMod with
    type t <= t.

  clone import ZModuleStruct as ZModStr with
    type t      <= t,
    theory ZMod <- ZMod.

  clone import FiniteZModule as FZMod with
    type t      <= t,
    theory ZMod <- ZMod.

  lemma gt0_order x :
    0 < order x.
  proof.
    case/ler_eqVlt: (ge0_order x) => // /eq_sym /order0P => inj_intmul.
    by have //: false; move: inj_intmul => /=; apply/FinType.not_injective_int.
  qed.

  import StdBigop.Bigint.

  lemma dvd_order_card x :
    order x %| FinType.card.
  proof.
    have /(_ FinType.enum):
      forall s , exists c ,
        uniq c /\
        (forall y z , y \in c => z \in c => eqv_orbit x y z => y = z) /\
        (mem s <= mem (flatten (map (fun y => map (ZMod.(+) y) (orbit_list x)) c))).
    + elim => [|y s [c] IHs]; [by exists [] => /=; rewrite flatten_nil|].
      move: IHs; pose l:= flatten _; case (y \in l) => [mem_y|Nmem_y]; move => [uniq_ [forall_ mem_incl]].
      - by exists c; split => //; split => // z /= [->>|]; [apply/mem_y|apply/mem_incl].
      exists (y :: c); do!split => // [|z t|z] /=; [|move => [->>|mem_z] [->>|mem_t] //|].
      - move: Nmem_y; apply/contra; rewrite /l => {l mem_incl} mem_y; apply/flatten_mapP.
        exists y; split => //=; apply/mapP; exists zeror; rewrite addr0 /=.
        by apply/orbit_listP; rewrite ?gt0_order // orbit0.
      - rewrite /eqv_orbit orbit_listP ?gt0_order //; move: Nmem_y; rewrite /l -flatten_mapP.
        rewrite negb_exists => /= /(_ t); rewrite mem_t /= mapP negb_exists /= => /(_ (y - t)).
        by rewrite addrA addrAC subrr /= add0r.
      - rewrite eqv_orbit_sym /eqv_orbit orbit_listP ?gt0_order //; move: Nmem_y; rewrite /l -flatten_mapP.
        rewrite negb_exists => /= /(_ z); rewrite mem_z /= mapP negb_exists /= => /(_ (y - z)).
        by rewrite addrA addrAC subrr /= add0r.
      - by apply/forall_.
      rewrite flatten_cons -/l mem_cat; case => [->>|?]; [left|by right; apply/mem_incl].
      apply/mapP; exists zeror; rewrite addr0 /=.
      by apply/orbit_listP; rewrite ?gt0_order // orbit0.
    case => c; pose l:= flatten _; move => [uniq_ [forall_ mem_incl]].
    rewrite /card (perm_eq_size _ l).
    + apply/uniq_perm_eq; [by apply/FinType.enum_uniq| |by move => ?; split; [apply/mem_incl|move => _; apply/FinType.enumP]].
      rewrite /l => {mem_incl l}; apply/uniq_flatten_map => //.
      - by move => y /=; rewrite map_inj_in_uniq; [move => ? ? _ _; apply/addrI|apply/uniq_orbit_list].
      move => y z mem_y mem_z /= /hasP [?] [] /mapP [t] [mem_t ->>] /mapP [u] [mem_u] eq_.
      apply/forall_ => //; move: eq_; rewrite /eqv_orbit addrC -eqr_sub => <-.
      by apply/orbitB; apply/orbit_listP => //; apply/gt0_order.
    rewrite /l size_flatten sumzE (BIA.eq_big_seq _ (fun _ => order x)) /=.
    + by move => ? /mapP [?] [+ ->>]; move => /mapP [?] /= [_ ->>]; rewrite size_map size_orbit_list.
    by rewrite BIA.sumr_const count_predT !size_map intmulz; apply/dvdz_mulr/dvdzz.
  qed.
end FiniteZModuleStruct.

(* -------------------------------------------------------------------- *)
abstract theory FiniteComRingStruct.
  type t.

  clone import ComRing as CR with
    type t <= t.

  clone import ComRingStruct as CRStr with
    type t    <= t,
    theory CR <- CR.

  clone import FiniteComRing as FCR with
    type t    <= t,
    theory CR <- CR.

  clone include FiniteZModuleStruct with
    type t         <- t,
    theory ZMod    <- CR,
    theory ZModStr <- CRStr,
    theory FZMod   <- FCR.

  lemma gt0_char :
    0 < char.
  proof. by rewrite /char; apply/gt0_order. qed.

  lemma gt1_char :
    1 < char.
  proof. by move/ltzE/ler_eqVlt: gt0_char; rewrite eq_sym /= neq1_char. qed.
end FiniteComRingStruct.

(* -------------------------------------------------------------------- *)
abstract theory FiniteIDomainStruct.
  type t.

  clone import IDomain as ID with
    type t <= t.

  clone import IDomainStruct as IDStr with
    type t    <= t,
    theory ID <- ID.

  clone import FiniteIDomain as FID with
    type t    <= t,
    theory ID <- ID.

  clone include FiniteComRingStruct with
    type t       <- t,
    theory CR    <- ID,
    theory CRStr <- IDStr,
    theory FCR   <- FID.

  lemma prime_char :
    prime char.
  proof. by case: char_integral => // eq0; move: gt0_char; rewrite eq0. qed.

  lemma bij_surj ['a,'b] (f : 'a -> 'b) :
    bijective f => 
    surjective f.
  proof. by move => [g] [fgK gfK] x; exists (g x); rewrite gfK. qed.

  lemma bij_inj_surj ['a,'b] (f : 'a -> 'b) :
    bijective f <=>
    (injective f) /\ (surjective f).
  proof.
    split => [bij_|[inj_ surj_]]; [by split; [apply/bij_inj|apply/bij_surj]|].
    exists (fun y => choiceb (fun x => y = f x) witness); split => [x|y].
    + rewrite (eq_choice _ (pred1 x)).
      - by move => x' /=; split => [|->//]; move => /inj_ ->.
      by rewrite (choicebP (pred1 x) witness) //; exists x.
    rewrite -(choicebP (fun x => y = f x) witness) //.
    by case: (surj_ y) => x ->>; exists x.
  qed.

  lemma frobenius_bij :
    prime char =>
    bijective frobenius.
  proof.
    move => prime_char; move: (frobenius_inj prime_char) => inj_; apply/bij_inj_surj.
    rewrite inj_ /= => x; move: (uniq_map_injective _ _ inj_ FID.FinType.enum_uniq) => uniq_.
    move: (uniq_leq_size_perm_eq _ _ uniq_ FID.FinType.enum_uniq _).
    + by move => ? _; apply/FID.FinType.enumP.
    rewrite size_map /= => /perm_eq_mem /(_ x); rewrite FID.FinType.enumP /=.
    by move => /mapP [y] [_ ->>]; exists y.
  qed.
end FiniteIDomainStruct.

(* -------------------------------------------------------------------- *)
abstract theory FiniteFieldStruct.
  type t, ut.

  clone import Field as F with
    type t <= t.

  clone import FieldStruct as FStr with
    type t   <= t,
    theory F <- F.

  clone import FiniteField as FF with
    type t   <= t,
    theory F <- F.

  clone include FiniteIDomainStruct with
    type t       <- t,
    theory ID    <- F,
    theory IDStr <- FStr,
    theory FID   <- FF.

  clone import UZMod_Field as UF with
    type t   <- t,
    type uz  <- ut,
    theory F <- F.

  print UF.

  clone import SubFinite as SFU with
    type t    <- t,
    type st   <- ut,
    op p      <- (fun x => x <> zeror),
    theory FT <- FF.FinType.

  lemma card_unit :
    FF.FinType.card = SFU.SFT.card + 1.
  proof.
    rewrite /card (perm_eq_size  _ _ (perm_to_rem _ _ (FinType.enumP zeror))) /=.
    rewrite addrC; congr; rewrite -(size_map Sub.val); apply/perm_eq_size/uniq_perm_eq.
    + by apply/rem_uniq/FinType.enum_uniq.
    + by apply/uniq_map_injective; [apply/Sub.val_inj|apply/SFT.enum_uniq].
    move => x; case: (x = zeror) => [->>|neqx0].
    + rewrite /senum -map_comp; pose s:= filter _ _.
      case: (eq_in_map (Sub.val \o Sub.insubd) idfun s).
      rewrite /s => + _ {s}; move => -> /=.
      + by move => x /mem_filter /= [neqx0 _]; rewrite /(\o) /idfun /= Sub.val_insubd neqx0.
      by rewrite map_id mem_filter /= rem_filter ?FinType.enum_uniq // mem_filter /predC1.
    rewrite mem_rem_neq // 1?eq_sym // FinType.enumP /=; apply/mapP.
    by exists (Sub.insubd x); rewrite SFT.enumP /= Sub.val_insubd neqx0.
  qed.
end FiniteFieldStruct.


(* ==================================================================== *)
abstract theory SubFiniteZModule.
  type t, st.

  clone import ZModule as ZMod with
    type t <= t.

  clone import SubZModule with
    type t      <= t,
    type st     <= st,
    theory ZMod <- ZMod.

  clone import FiniteZModule as FZMod with
    type t      <= t,
    theory ZMod <- ZMod.

  clone import ZModuleStruct as ZModStr with
    type t      <= t,
    theory ZMod <- ZMod.

  clone import FiniteZModuleStruct as FZModStr with
    type t         <= t,
    theory ZMod    <- ZMod,
    theory ZModStr <- ZModStr,
    theory FZMod   <- FZMod.

  clone include SubFinite with
    type t     <- t,
    type st    <- st,
    op p       <- p,
    theory FT  <- FinType,
    theory Sub <- Sub.

  (*TODO: clone with theory not working here, and neither clone with axiom later..*)
  clone import FiniteZModule as SFZMod with
    type t                  <= st,
    theory ZMod             <- SZMod,
    (*theory FinType          <- SFT.*)
    op FinType.enum         <- senum
    (*axiom FinType.enum_spec <- SFT.enum_spec.*)
    proof *.

  realize FinType.enum_spec by exact SFT.enum_spec.
end SubFiniteZModule.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteComRing.
  type t, st.

  clone import ComRing as CR with
    type t <= t.

  clone import SubComRing with
    type t    <= t,
    type st   <= st,
    theory CR <- CR.

  clone import FiniteComRing as FCR with
    type t    <= t,
    theory CR <- CR.

  clone import ComRingStruct as CRStr with
    type t    <= t,
    theory CR <- CR.

  clone import FiniteComRingStruct as FCRStr with
    type t       <= t,
    theory CR    <- CR,
    theory CRStr <- CRStr,
    theory FCR   <- FCR.

  clone import SubComRingModule as SCRM with
    type t            <= t,
    type st           <= st,
    theory CR         <- CR,
    theory SubComRing <- SubComRing.

  clone include SubFiniteZModule with
    type t          <- t,
    type st         <- st,
    theory ZMod     <- CR,
    theory FZMod    <- FCR,
    theory ZModStr  <- CRStr,
    theory FZModStr <- FCRStr.

  (*TODO: clone with axiom, or theory.*)
  clone import FiniteComRing as SFCR with
    type t          <= st,
    theory CR       <- SCR,
    (*theory FinType  <- SFZMod.FinType.*)
    op FinType.enum <- senum
    (*axiom FinType.enum_spec <- SFZMod.FinType.enum_spec*)
    proof *.

  realize FinType.enum_spec by exact SFZMod.FinType.enum_spec.

  import ComRingModule.

  op enum_lin (vs : t list) =
    map
      (fun ss => lin ss vs)
      (foldr (allpairs (::)) [[]] (nseq (size vs) senum)).

  lemma enum_lin_nil :
    enum_lin [] = [CR.zeror].
  proof. by rewrite /enum_lin /= nseq0 /= BigZMod.big_nil. qed.

  (*TODO: missing stuff about map and allpairs, in hakyber-eclib?*)
  lemma enum_lin_cons v vs :
    enum_lin (v :: vs) =
    allpairs CR.( + ) (map (transpose SCRM.( ** ) v) senum) (enum_lin vs).
  proof.
    rewrite /enum_lin /= addrC nseqS ?size_ge0 //=; pose el := foldr _ _ _.
    elim: senum el => [|x senum IHsenum] el /=; [by rewrite !allpairs0l|].
    rewrite !allpairs_consl map_cat IHsenum -!map_comp; congr => {IHsenum}.
    by apply/eq_map => xs; rewrite /(\o) /= BigZMod.big_cons /predT /idfun.
  qed.

  lemma enum_linP vs v :
    (v \in enum_lin vs) <=> (gen (vf_oflist vs) v).
  proof.
    elim: vs v => [|v vs IHvs] w.
    + by rewrite enum_lin_nil gen_vf_oflist_nil.
    rewrite enum_lin_cons gen_vf_oflist_cons allpairsP; split.
    + case => -[v1 v2] /= |> /mapP [s] |> mem_s /IHvs gen_v2.
      by exists s SCR.oner v2; rewrite gen_v2 scale1r.
    case => [s1 s2 w2] /= |> /(gen_scale _ s2) /IHvs mem_w2.
    exists (s1 ** v, s2 ** w2); rewrite mem_w2 /=.
    by apply/mapP; exists s1 => /=; apply/SFT.enumP.
  qed.

  lemma enum_lin0 :
    enum_lin [] = [CR.zeror].
  proof. by rewrite /enum_lin /= nseq0 /= BigZMod.big_nil. qed.

  lemma size_enum_lin vs :
    size (enum_lin vs) = SFCR.FinType.card ^ (size vs).
  proof.
    elim: vs => [|v vs IHvs] /=.
    + by rewrite expr0 enum_lin0.
    rewrite addrC exprS ?size_ge0 // -IHvs => {IHvs}.
    rewrite /enum_lin !size_map /= addrC nseqS ?size_ge0 //=.
    by rewrite size_allpairs /SFCR.FinType.card size_map.
  qed.

  lemma free_uniq_enum_lin vs :
    uniq vs =>
    free (vf_oflist vs) =>
    uniq (enum_lin vs).
  proof.
    elim: vs => [|v vs IHvs]; [by rewrite enum_lin_nil|].
    rewrite free_vf_oflist_cons enum_lin_cons /=.
    move => |> Nmem_v uniq_ imp_eq0 free_.
    rewrite allpairs_mapl; apply/allpairs_uniq.
    + by apply/SFT.enum_uniq.
    + by apply/IHvs.
    move => s1 s2 v1 v2 mem_s1 mem_s2 /enum_linP gen1 /enum_linP gen2 /=.
    rewrite addrC -eqr_sub -scaleNr -scaleDl => eq_.
    (*TODO: what?*)
    move/(_ (s2 + (-s1))%SCR _): imp_eq0.
    + by rewrite -eq_; apply/gen_add => //; apply/gen_opp.
    by rewrite SCR.subr_eq0 => ->>; move: eq_; rewrite /= SCR.subrr scale0r CR.subr_eq0.
  qed.

  lemma gen_t_enum_lin vs :
    (gen_t (vf_oflist vs)) <=> (forall v , v \in enum_lin vs).
  proof. by rewrite /gen_t; apply/forall_eq => v /=; apply/eqboolP; rewrite enum_linP. qed.
end SubFiniteComRing.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteIDomain.
  type t, st.

  clone import IDomain as ID with
    type t <= t.

  clone import SubIDomain with
    type t    <= t,
    type st   <= st,
    theory ID <- ID.

  clone import FiniteIDomain as FID with
    type t    <= t,
    theory ID <- ID.

  clone import IDomainStruct as IDStr with
    type t    <= t,
    theory ID <- ID.

  clone import FiniteIDomainStruct as FIDStr with
    type t       <= t,
    theory ID    <- ID,
    theory IDStr <- IDStr,
    theory FID   <- FID.

  clone include SubFiniteComRing with
    type t        <- t,
    type st       <- st,
    theory CR     <- ID,
    theory FCR    <- FID,
    theory CRStr  <- IDStr,
    theory FCRStr <- FIDStr.

  clone import FiniteIDomain as SFID with
    type t          <= st,
    theory ID       <- SID,
    op FinType.enum <- senum
    proof *.

  realize FinType.enum_spec by exact SFCR.FinType.enum_spec.
end SubFiniteIDomain.

(* -------------------------------------------------------------------- *)
abstract theory SubFiniteField.
  type t, st, ut.

  clone import Field as F with
    type t <= t.

  clone import SubField with
    type t   <= t,
    type st  <= st,
    theory F <- F.

  clone import FiniteField as FF with
    type t   <= t,
    theory F <- F.

  clone import FieldStruct as FStr with
    type t   <= t,
    theory F <- F.

  clone import FiniteFieldStruct as FFStr with
    type t      <= t,
    type ut     <= ut,
    theory F    <- F,
    theory FStr <- FStr,
    theory FF   <- FF.

  clone include SubFiniteIDomain with
    type t        <- t,
    type st       <- st,
    theory ID     <- F,
    theory FID    <- FF,
    theory IDStr  <- FStr,
    theory FIDStr <- FFStr.

  clone import FiniteField as SFF with
    type t          <= st,
    theory F        <- SF,
    op FinType.enum <- senum
    proof *.

  realize FinType.enum_spec by exact SFID.FinType.enum_spec.

  import SCRM.ComRingModule.

  lemma finite_basis_exists :
    exists vs , uniq vs /\ basis (vf_oflist vs).
  proof.
    have /(_ FF.FinType.card):
      forall n , 0 <= n => n <= FF.FinType.card =>
      exists vs , uniq vs /\ free (vf_oflist vs) /\ n <= size (enum_lin vs);
    last first.
    + rewrite size_ge0 /= => -[vs] |> uniq_ free_ lecn.
      exists vs; rewrite uniq_ /basis free_ /= gen_t_enum_lin => v.
      move: lecn; rewrite uniq_leq_size_perm_eq.
      - by apply/free_uniq_enum_lin.
      - by apply/FF.FinType.enum_uniq.
      - by move => ? _; apply/FF.FinType.enumP.
      by move => /perm_eq_mem ->; apply/FF.FinType.enumP.
    elim => [_|n le0n IHn /ltzE ltnc].
    + by exists []; rewrite free_vf_oflist_nil size_ge0.
    case/(_ _): IHn => [|vs |> uniq_ free_]; [by apply/ltzW|].
    move => /ler_eqVlt [->>|ltnp]; [|by exists vs; rewrite -ltzE].
    move/ltzNge: ltnc; rewrite uniq_leq_size_perm_eq.
    + by apply/free_uniq_enum_lin.
    + by apply/FF.FinType.enum_uniq.
    + by move => ? _; apply/FF.FinType.enumP.
    move => Nperm_eq_; move: (uniq_perm_eq (enum_lin vs) FF.FinType.enum _ _).
    + by apply/free_uniq_enum_lin.
    + by apply/FF.FinType.enum_uniq.
    rewrite Nperm_eq_ /= negb_forall /= => -[v]; rewrite FF.FinType.enumP /= => Nmemv.
    exists (v :: vs); rewrite /= free_vf_oflist_cons uniq_ free_ /=; do!split.
    + by move: Nmemv; apply/contra => memv; apply/enum_linP/gen_p.
    + right => s; case: (s = SCR.zeror) => [->> //=|neqs0].
      - (*TODO: bad clone.*)
        admit.
      rewrite -gen_scale_unit -?enum_linP //.
      (*TODO: bad clone.*)
      admit.
    rewrite !size_enum_lin /= -ltzE addrC exprSr ?size_ge0 //.
    rewrite -subr_gt0 -IntID.mulN1r mulrC -IntID.mulrDl; apply/mulr_gt0.
    + by rewrite subr_gt0; apply/card_gt1.
    by apply/expr_gt0/SFF.FinType.card_gt0.
  qed.

  op n = ilog SFCR.FinType.card FF.FinType.card.

  lemma lt0n :
    0 < n.
  proof.
    rewrite /n.
    admit.
  qed.

  lemma eq_card_pow_n :
    FF.FinType.card = SFF.FinType.card ^ n.
  proof.
    case: finite_basis_exists => vs [uniq_ [free_ /gen_t_enum_lin mem_e]].
    move: (free_uniq_enum_lin _ uniq_ free_) => uniq_e.
    move: (size_enum_lin vs).
    admit.
  qed.
end SubFiniteField.


(* ==================================================================== *)
abstract theory ZModP_FiniteField.
  type t.

  op p : int.

  axiom prime_p : prime p.

  clone import ZModField as ZModP with
    type zmod     <= t,
    op p          <- p,
    axiom prime_p <- prime_p.

  (*TODO: issue in ZModP: should be a clone with theory ZModP.ZModpField.*)
  clone import Field as F with
    type t          <= t,
    op zeror        <= ZModP.zero,
    op oner         <= ZModP.one,
    op (+)          <= ZModP.(+),
    op [-]          <= ZModP.([-]),
    op ( * )        <= ZModP.( * ),
    op invr         <= ZModP.inv,
    lemma addrA     <= ZModP.ZModpField.addrA,
    lemma addrC     <= ZModP.ZModpField.addrC,
    lemma add0r     <= ZModP.ZModpField.add0r,
    lemma addNr     <= ZModP.ZModpField.addNr,
    lemma oner_neq0 <= ZModP.ZModpField.oner_neq0,
    lemma mulrA     <= ZModP.ZModpField.mulrA,
    lemma mulrC     <= ZModP.ZModpField.mulrC,
    lemma mul1r     <= ZModP.ZModpField.mul1r,
    lemma mulrDl    <= ZModP.ZModpField.mulrDl,
    lemma mulVr     <= ZModP.ZModpField.mulVr,
    lemma unitP     <= ZModP.ZModpField.unitP,
    lemma unitout   <= ZModP.ZModpField.unitout,
    lemma mulf_eq0  <= ZModP.ZModpField.mulf_eq0.

  clone import FiniteField as FF with
    type t   <= t,
    theory F <- F.
end ZModP_FiniteField.


(* ==================================================================== *)
abstract theory SubFiniteField_ZMod.
  type t, ut, st.

  clone import Field as F with
    type t <= t.

  clone import FiniteField as FF with
    type t   <= t,
    theory F <- F.

  clone import FieldStruct as FStr with
    type t   <= t,
    theory F <- F.

  clone import FiniteFieldStruct as FFStr with
    type t      <= t,
    type ut     <= ut,
    theory F    <- F,
    theory FStr <- FStr,
    theory FF   <- FF.

  clone import ZModField as ZModP with
    type zmod     <= st,
    op p          <- FStr.char,
    axiom prime_p <- FFStr.prime_char.

(*TODO: the finite import from ZModP_FiniteField is incompatible with the finite from subfinitefield.*)
(*
  clone import ZModP_FiniteField as ZModPFF with
    type t        <= st,
    op p          <- FStr.char,
    axiom prime_p <- FFStr.prime_char,
    theory ZModP  <- ZModP.
*)

  (*TODO: what?*)
(*
  print ofint.
  print F.ofint.
  print ZModPFF.F.ofint.
  print Sub.val.
  print ZModP.Sub.val.
*)

  op is_ofint (x : t) n = (x = F.ofint n).

  op in_zmodP x = exists n , is_ofint x n.

  op insub (x : t) = 
    if in_zmodP x
    then Some (ZModpRing.ofint (argmin idfun (is_ofint x))) 
    else None.

  op val (x : st) = ofint (Sub.val x).

  op wsT = zeror.

  clone import SubField as SF with
    type t       <= t,
    type st      <= st,
    op p         <- in_zmodP,
    op Sub.insub <- insub,
    op Sub.val   <- val,
    op Sub.wsT   <- wsT,
    theory F     <- F
    proof *.

  realize fieldp.
  proof.
    rewrite /in_zmodP /is_ofint; do 3!split; [split| | |]; rewrite /=.
    + by exists 0; rewrite ofint0.
    + by move => x [nx] ->>; exists (-nx); rewrite ofintN.
    + by move => x y [nx] ->> [ny] ->>; exists (nx + ny); rewrite addrz.
    + by exists 1; rewrite ofint1.
    + by move => x y [nx] ->> [ny] ->>; exists (nx * ny); rewrite mulrz.
    move => x [nx] ->>; move: (mulmV _ nx prime_char).
    case: (nx %% char = 0) => /= [eq_0|_ eq_1].
    + by exists 0; move: (dvd_char nx); rewrite dvdzE eq_0 /= => ->; rewrite invr0 ofint0.
    exists (invm nx char); move: (dvdzE char (nx * invm nx char)); rewrite eq_1 /= => Ndvd.
    apply/(mulrI (ofint nx)).
    + by rewrite -dvd_char; apply/negP => dvd_; apply/Ndvd/dvdz_mulr.
    rewrite mulrz divrr //.
    + by rewrite -dvd_char; apply/negP => dvd_; apply/Ndvd/dvdz_mulr.
    rewrite eq_sym -ofint1 -dvd2_char dvdzE -modzDm eq_1 -{1}(modz_small 1 char).
    + by rewrite /= ltr_normr; left; apply/gt1_char.
    by rewrite modzDm.
  qed.

  realize Sub.insubN.
  proof. by rewrite /insub => x ->. qed.

  realize Sub.insubT.
  proof.
    rewrite /insub; move => x in_x; rewrite in_x /=.
    case: in_x => nx; rewrite /is_ofint => ->>.
    admit.
  qed.

  realize Sub.valP.
  proof. by rewrite /in_zmodP /val; move => x; exists (ZModP.Sub.val x). qed.

  realize Sub.valK.
  proof.
    rewrite /pcancel /insub => x.
    have in_x: (in_zmodP (ofint (ZModP.Sub.val x))).
    + by exists (ZModP.Sub.val x).
    rewrite in_x /=; case: in_x => n is_ofint_.
    move: (argminP idfun (is_ofint (val x)) n _ _).
    + admit.
    + by rewrite /val.
    rewrite /val {1}/is_ofint /idfun /= => ?.
    admit.
  qed.

  realize Sub.insubW.
  proof.
    rewrite /insub /wsT.
    admit.
  qed.

  (*TODO: include.*)
  clone import SubFiniteField as SFF with
    type t       <- t,
    type ut      <- ut,
    type st      <- st,
    theory F     <- F,
    theory FF    <- FF,
    theory FStr  <- FStr,
    theory FFStr <- FFStr.

  lemma eq_char_zmodcard :
    char = SFF.FinType.card.
  proof.
    admit.
  qed.

  lemma exists_generator :
    exists (g : t) ,
      iter_frobenius_fixed n g /\
      forall d ,
        0 <= d =>
        d %| n =>
        iter_frobenius_fixed d g =>
        d = n.
  proof.
    admit.
  qed.
end SubFiniteField_ZMod.
