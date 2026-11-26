module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndsRankThreeOfLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DualOfWeights

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutAway
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
theorem UpperTheory.Gal.projectedFormsSystemPart.autAway_alt (PH : _root_.UpperTheory.V.Af.HypothesesH') (hL : _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) (hC : ConjTor) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L]
    [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) {n : ℕ} (hn : 1 ≤ n) (V : s.Lev)
    (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (hτ : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (hS : V.S' = s.S) :
    (hset Q τ₀).AutomorphicHeckeSet ι fun _ ρ => Af.IsIrr (ρ.comp V.pr) → AwayOk s ι (ρ.comp V.pr) := by
  intro lam _ d ξ hξ F hF hK hI
  obtain ⟨e, he⟩ := hξ
  have hTeich : ∃ t, r.IsTeich t := by
    obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
    have : IsAdicComplete (maximalIdeal c.O) c.O := hc
    have : Finite (ResidueField c.O) := hfin
    have : CharP (ResidueField c.O) l := by
      refine (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 ?_
      rw [← map_natCast (residue c.O), residue_eq_zero_iff]
      exact hlm
    have : CharP (c.O ⧸ maximalIdeal c.O) l := inferInstanceAs (CharP (ResidueField c.O) l)
    have : PerfectRing (ResidueField c.O) l := inferInstance
    let j : ResidueField c.O →+* Perfection (c.O ⧸ maximalIdeal c.O) l :=
      Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)
        (RingHom.id (ResidueField c.O))
    let τ : ResidueField c.O →* c.O := (Perfection.teichmuller l (maximalIdeal c.O)).comp j
    have hres (x : ResidueField c.O) : residue c.O (τ x) = x := by
      have hj := (Perfection.lift l (ResidueField c.O) (c.O ⧸ maximalIdeal c.O)).symm_apply_apply
        (RingHom.id (ResidueField c.O))
      exact (Perfection.mk_teichmuller (j x)).trans (RingHom.congr_fun hj x)
    refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hres _, ?_⟩⟩
    rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  obtain ⟨t, ht⟩ := hTeich
  have hop : IsOpen (τ₀.ker : Set (KT n (wt s))) := by
    let f := ι.toRingHom.comp (algebraMap c.O (Qbar l))
    have hf : Function.Injective f := ι.injective.comp Subtype.val_injective
    have hker : ((Matrix.GeneralLinearGroup.map f).comp τ₀).ker = τ₀.ker := by
      refine MonoidHom.ker_comp_of_injective _ _ fun a b hab => ?_
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      exact hf (congrArg (fun x : GL (Fin m) ℂ => (x : Matrix (Fin m) (Fin m) ℂ) i j) hab)
    exact hker ▸ (hτ t ht).1
  have h1 := decompU l L Ω s n hn V Q c m τ₀ ι hop lam d e ξ he F hF hK hI
  refine IsConcreteLE.le_iff.1 (iSup_le fun σ => ?_) h1
  by_cases h0 : YOf Q ι τ₀ e ξ σ.1 = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨Y, hY, hP⟩ := hL l L Ω s n hn V Q c r ι m τ₀ hτ lam d e ξ he σ.1 σ.2 h0
  rw [← hY]
  refine le_iSup (fun Y : {Y : (hset Q τ₀).PartAltAlt ι lam ξ // Af.IsIrr (Y.r.comp V.pr) → AwayOk s ι (Y.r.comp V.pr)} => Y.1.Y)
    ⟨Y, fun hi => ?_⟩
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := hP hi
  refine ⟨π, p1, p2, p3, fun w hw hw0 => ?_⟩
  by_cases hwS : w.under (𝓞 (Lp L)) ∈ V.S'
  swap
  · obtain ⟨B, hB⟩ := p4 w (partUR2Unr l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ.1 σ.2 h0 w hwS)
    exact ImaginaryQuadraticEtaCharacter.sphUnl L n hn π w B hB
  obtain ⟨hwv, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  rw [hS] at hwS
  have hu : w.under (𝓞 (Lp L)) ∈ s.St := by
    rcases hwS with h | h | h
    · refine absurd ?_ hw
      rw [← map_natCast (algebraMap (𝓞 (Lp L)) (𝓞 L))]
      exact h
    · exact h
    · exact absurd h hw0
  refine hC L n hn π p2 (s.w (w.under (𝓞 (Lp L)))) w (hwv _).symm ?_
  refine (ImaginaryQuadraticEtaCharacter.plainIff L n hn π _).1 fun τ hτ' => ?_
  classical
  have hs : ∀ u : s.St, IsSplitAt (s.w u) := fun u => hsp _ (by
    rw [hwv]
    exact s.split _ (Or.inr (Or.inl u.2)))
  choose loc hloc using fun u : s.St => (_root_.UpperTheory.V.Af.local_comp_complex_of_printed_results PH.toClassicalTheorems L n π (s.w u)).1
  obtain ⟨rc, hrc⟩ := PH.toClassicalTheorems.exists_reciprocity_dense (s.hw (w.under (𝓞 (Lp L))))
  have k := _root_.UpperTheory.V.Hi.partUR2Type_alt l L Ω s n hn V Q c ι m τ₀ lam d e ξ he σ.1 σ.2 h0 _ (hτ t ht)
    (Function.update loc ⟨_, hu⟩ τ) (fun u' => p5 _ (hs u') _ (by
      by_cases e : u' = ⟨_, hu⟩
      · subst e
        rwa [Function.update_self]
      · rw [Function.update_of_ne e]
        exact hloc _)) ⟨_, hu⟩ rc hrc
  rw [Function.update_self] at k
  exact typePlain L Ω n hn π _ _ (s.hw _) τ hτ' rc (_root_.UpperTheory.V.Z.Desc.W.isRecT_of_isRecT PH.toClassicalTheorems hrc)
    (fun i => W.pushCh (ι.toRingHom.comp (algebraMap c.O (Qbar l))) ((t i).comp V.pr)) k
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
private theorem coreA (H : _root_.UpperTheory.V.Af.HypothesesH') (hL : _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) (hC : ConjTor) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L]
    [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V}
    {c : Coef l} {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ} {K : (hset Q R.τ₀).Lev}
    (hS : V.S' = s.S) {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ ρ : V.frame.G₀ →* GL (Fin n) (Qbar l), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧
      (Af.IsIrr (ρ.comp V.pr) → AwayOk s ι (ρ.comp V.pr)) ∧ x.IsRep (ρ.comp V.pr) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  have out := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight H.litN L Ω l n c (hset Q R.τ₀) (_root_.UpperTheory.V.Hi.axU_s H.litN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι _
    (_root_.UpperTheory.Gal.projectedFormsSystemPart.autAway_alt H hL hC s hn V Q c r ι R.m R.τ₀ R.type hS) lam (Set.mem_univ _)
    ((_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  let y := AlgHom.liftOfSurjective f hsurj x hx
  have hy (b : B.B) : y (f b) = x b := AlgHom.liftOfSurjective_apply f hsurj x hx b
  have hΛ : y.toRingHom.comp (algebraMap Λ.Λ _) = (x.comp (Λ.toPair B.u)).toRingHom :=
    RingHom.ext fun b => (congrArg y (hlam b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hs, hP, hD, -⟩ := out.pt lam (Set.mem_univ _) y (hΛ ▸ har)
  refine ⟨ρ, hc, hs, hP, ?_⟩
  have hxy : (x : B.B →+* Qbar l) = y.toRingHom.comp f.toRingHom :=
    RingHom.ext fun b => (hy b).symm
  have e3 : x.D = W.GDet.ofRep (W.mat ρ) := by
    change B.u.D.map (x : B.B →+* Qbar l) = _
    rw [hxy]
    exact hD
  change x.D.comap V.pr = _
  rw [e3]
  exact (AlgebraTools.Det.repApi (W.mat ρ)).2.2.2.2.2.2.1 V.pr
theorem UpperTheory.Gal.projectedFormsSystemPart.irrArithPointsAutomorphicAway_of_isJ (H : _root_.UpperTheory.V.Af.HypothesesH') (hL : _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) (hC : ConjTor) (hE : _root_.UpperTheory.V.Z.Ord.EndOrdAlt) (hB : BornJ) :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → IrrArithPointsAutomorphicAway B ι J := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ x h ρ hx ha hρ hi
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  obtain ⟨ρ₀, -, hs, hP, hr⟩ := coreA H hL hC hn hS hJ x h hx ha
  have hss : IsSSRep ρ := by
    intro M hM
    rcases hi.2.2 M le_top hM with rfl | rfl
    · exact ⟨⊤, hi.2.1, isCompl_bot_top⟩
    · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
      rw [(Submodule.mem_bot (Qbar l)).1 hv]
      simp
  have hss₀ : IsSSRep (ρ₀.comp V.pr) := by
    intro M hM
    have hInv : IsInv ρ₀ M := fun g => by
      obtain ⟨g, rfl⟩ := hpr g
      exact hM g
    obtain ⟨M', hM', hcompl⟩ := hs M hInv
    exact ⟨M', fun g => hM' (V.pr g), hcompl⟩
  have e : Af.RepIso (ρ₀.comp V.pr) ρ := by
    have hD := hρ.symm.trans hr
    obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat ρ) (W.mat (ρ₀.comp V.pr)) hss hss₀ fun g => by
      rw [← (AlgebraTools.Det.repApi (W.mat ρ)).2.1 g,
        ← (AlgebraTools.Det.repApi (W.mat (ρ₀.comp V.pr))).2.1 g, hD]
    refine ⟨P, fun g => ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    exact Units.ext (hP g).symm
  have hi₀ : Af.IsIrr (ρ₀.comp V.pr) := by
    obtain ⟨P, hconj⟩ := e.symm'
    refine ⟨hi.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
    let E := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
    have hInv : IsInv ρ (M.comap E.toLinearMap) := fun g v hv => by
      have hmem := hM g _ hv
      change ((ρ₀.comp V.pr) g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec
        ((P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec v) ∈ M at hmem
      change (P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec _ ∈ M
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, hconj g, inv_mul_cancel_right,
        Units.val_mul, ← Matrix.mulVec_mulVec] at hmem
    have hmap : M = (M.comap E.toLinearMap).map E.toLinearMap :=
      (Submodule.map_comap_eq_of_surjective E.surjective M).symm
    rcases hi.2.2 _ le_top hInv with hbot | htop
    · left
      rw [hmap, hbot, Submodule.map_bot]
    · right
      rw [hmap, htop, Submodule.map_top, LinearEquiv.range]
  obtain ⟨π, h1, h2, h3, h4⟩ := hP hi₀
  have h5 : Af.AttC ι ρ π := ⟨hss, h3.2.mono fun w ⟨b, hb, hf⟩ => ⟨b, hb, hf.of_iso e⟩⟩
  refine ⟨⟨π, h1, h2, h5⟩, fun hc => ?_⟩
  have hRing : B.RingProps Λ J := _root_.UpperTheory.V.Hi.ring_props_of_is_j_unitary_hecke_data
    H l L Ω s n hn V Q c r ι B Λ R K hS J hJ
  have born := hB l L Ω s n hn V c r ι B Λ J hRing
    (hE l L Ω s n hn V Q c r ι B Λ R K J hJ) x h ρ hx ha hρ hi hc
  refine ⟨fun v hv hu => (born v hv hu).1, fun π' _ p => ?_⟩
  obtain ⟨t, ht⟩ := ImaginaryQuadraticEtaCharacter.winOf L n hn π'
  refine ⟨t, fun v hv0 hv => ?_⟩
  have k : TU π' v := by
    by_cases hl : ((l : ℕ) : 𝓞 L) ∈ v.asIdeal
    · refine (born v hl fun A hA => ?_).2 π' p
      obtain ⟨κ, k1, k2⟩ := hv.resolve_left (fun a => a hl) A hA
      exact ⟨κ, k1, fun i j e => k2 i j 1 le_rfl (by rw [e])⟩
    · exact tu_same hn h5 p (h4 v hl hv0)
  exact ht v k.1 k.2
end
