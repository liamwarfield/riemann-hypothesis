module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.ExistsRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.SphericalTwists.UnramifiedTwists.SatFrobT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWBridge
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.NarrowSwap
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.QuadBC2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PhiEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.UpCycOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.WeightInfinitesimalCharacters.AdmissibleUnitaryThreePoint
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfLevelIso
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Af
section Rep
variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
end Rep
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {r r' : G F Ω →* GL (Fin n) (Qbar l)}
variable [IsAlgClosure F Ω]
abbrev _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty : Prop := ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (P : _root_.UpperTheory.V.Af.Hypotheses') {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w),
    ∃ rc : IrrGL (k := w.adicCompletion F) → WD h, _root_.UpperTheory.Zero.LLC.IsRecT h rc
end UpperTheory.V.Af
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
theorem exRec'_alt (_N : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (h : IsPlaceOver A w) : ∃ rc, IsRecT h rc := recTExists E Ω A w h
theorem exists_rec_alt_alt_alt : _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty := by
  unfold _root_.UpperTheory.V.Af.Hypotheses'.exists_rec_ty
  intros
  exact _root_.UpperTheory.V.Z.Win.exRec'_alt (by assumption : _root_.UpperTheory.V.Af.Hypotheses').litN _
end UpperTheory.V.Z.Win
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSatFrobT
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.Zero.LLC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues
open Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped commutatorElement
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
private theorem rec_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) (x : IrrGL (k := w.adicCompletion E))
    (α : Fin x.1 → ℂˣ) (hα : HasSatake x.rep α) : rc x = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨a, ha, H⟩ := H
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  have hL := GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified Pr.exh Pr.multi Pr.cos Pr.zel GlobalTheory.RecT.geometricLemma_holds Pr.bz (w.adicCompletion E) x α hα
  rw [Fin.univ_val_map] at hL
  rw [H.langlands _ x hL, segSum, List.map_ofFn, ← SatakeLaw.sumList_ofFn_diag]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
    zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, H.one]
  exact Test.lpOfChar_unrChar ha (α i) _
private theorem rec_algNorm_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      rc (algNorm σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w ((1 - (n : ℝ)) / 2)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  refine ⟨α, hαB.symm, ?_⟩
  have φ := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    rec_diag H (IrrGL.of σ.ρ σ.smooth σ.irred) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
  obtain ⟨a, ha, L⟩ := H
  rw [algNorm, L.nu, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]
private theorem gd_diag {n : ℕ} (c : Fin n → ℂˣ) : Z.Win.Gd (WD.mk (WDRep.diag h c)) := by
  refine ⟨fun s t => ?_, WD.unr_mono0 _ ((WD.unr_mk _).2 (WDRep.unr_diag _))⟩
  have hd : deg (⁅s, t⁆ : Weil h) = 0 := by
    rw [commutatorElement_def, deg_mul, deg_mul, deg_mul, deg_inv, deg_inv]
    ring
  show WD.charPol _ _ = _
  rw [WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hd]
  simp
private theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring
end UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues
open UpperTheory.V.Z.Desc.W.SatakeFrobeniusEigenvalues in
theorem UpperTheory.V.Z.Desc.W.satFrobT_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), Continuous r → ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∀ (σ : SmIrr (GL (Fin n) (w.adicCompletion F))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B →
    (∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion F) → WD h), IsRecT h rc → Z.Win.WDT ι r (rc (algNorm σ))) →
    FrobEig ι r w (algSat n (normV w) B) := by
  intro _ F Ω _ _ _ _ _ l _ ι n r _ w hl σ B hB H A h
  obtain ⟨rc, hrec⟩ := recTExists F Ω A w h
  obtain ⟨α, rfl, e⟩ := rec_algNorm_diag hrec σ B hB
  have hx := (H A h rc hrec).isWDOf (e ▸ gd_diag _)
  have hw := (hx.wdOf_eq hl).trans e
  obtain ⟨t, ht, φ, hφ, N', a, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw, WD.unr_mk]; exact WDRep.unr_diag _), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd] at this
  refine this.symm.trans ?_
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWCsdOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.GalN.V
open NumberField Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp GlobalTheory.HeckeGal
open IsDedekindDomain UpperTheory.V.Af in
theorem UpperTheory.GalN.V.csdOf0_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (F₀ F Ω : Type) [Field F₀] [NumberField F₀] [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω]
    [Algebra F Ω] [IsScalarTower F₀ F Ω] [IsAlgClosure F Ω], IsTotallyReal F₀ → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ),
    1 ≤ n → ∀ (r : G F Ω →* GL (Fin n) (Qbar l)) (c : G F₀ Ω) (P : GL (Fin n) (Qbar l)), IsConjEl c → IsAut ι r →
      IsPairing c r (cycBar F Ω l ^ (1 - (n : ℤ))) P → AutCsd0 ι r := by
  intro hP F₀ F Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r c P hc haut hpair
  obtain ⟨π, hreg, hatt⟩ := ((_root_.UpperTheory.GalN.V.automorphy_bridge_of_printed_hida hP F Ω l ι n r).2.1).1 haut
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  obtain ⟨art, hart⟩ : ∃ art : Neutral.B1.Ideles (maximalRealSubfield F) →* Gab (maximalRealSubfield F) Ω,
      IsGlobalArtin art := hP.toClassicalTheorems.litN.aut.art _ Ω
  have h1 : IsLAdicCharOf (E := F) (Ω := Ω) ι 1 1 := by
    refine ⟨continuous_const, art, 0, hart, fun k _ => ?_, fun x σ _ => ?_⟩
    · simp [HChar.inf]
    · rw [infPow_zero, lPow_zero]
      change (1 : Qbar l) = ι.symm (1 * 1⁻¹) * 1
      simp
  obtain ⟨j, hj⟩ := hc
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hd := _root_.UpperTheory.V.Af.self_dual_complex_of_printed_hida hP F Ω l ι n hn r π hatt 1 1 h1 c' P ⟨j, hj⟩ (by
    intro s s' hs
    rw [MonoidHom.one_comp, mul_one]
    refine hpair s s' (AlgEquiv.ext fun x => ?_)
    exact DFunLike.congr_fun hs x)
  rw [map_one, GlobalTheory.ContraPair.dualIsConjBy_one] at hd
  exact ⟨π, hreg, hd, hatt⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BciNarrowSwap
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.BaseChangeIdentities
theorem bcSpeh_alt : DefiniteN → GlobalTheory.BcSpeh.BcSpeh :=
  fun h => bcSpeh_of ascComp h
end UpperTheory.BaseChangeIdentities
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TUpQuad
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVQuadBC
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
theorem UpperTheory.Gal.SV.quad_base_change_w_of_printed_results (_P : _root_.UpperTheory.V.Af.Hypotheses') : UpperTheory.V.Br.QuadBCw := by
  intro F E _ _ _ _ _ _ _ h2 a ha2 _ π hr
  obtain rfl := ha2.out
  exact (UpperTheory.ConvolutionTheory.R2.quadBC2 F E h2 π hr).imp_right fun ⟨P, hP⟩ => ⟨P, UpperTheory.V.Br.IsBCw.of_isBC hP⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Af UpperTheory.V.Af.Bc in
theorem UpperTheory.V.Sd.up_quad_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.UpQuad := by
  intro hP F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE n _ hn r hr ⟨π, hreg, hatt⟩ hirr
  obtain ⟨P, hBC⟩ := (_root_.UpperTheory.Gal.SV.quad_base_change_w_of_printed_results hP F E hE n hn π hreg).resolve_left
    fun ⟨η, hη, ht⟩ => _root_.UpperTheory.V.Af.Bc.noTwist_of_prints hP F E Ω l ι hE n r π hr hatt hirr η hη ht
  have h := UpperTheory.V.Br.bcAtt0 F E Ω l ι n r π P hBC.toIsBC0
  exact ⟨P, h.1 hreg, h.2 hatt ((Bc.irrBasic.1 _ Unit _ n _).2.1 hirr)⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinApi
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
def AAcrossAlt : Prop :=
  _root_.UpperTheory.V.Af.HypothesesH' → RowT → ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω],
    Module.finrank ℚ K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n →
    (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) →
    ∀ r : G ℚ Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutomorphicOverImagQuad ι r → (∃ θ, IsAlgChar ι θ ∧ DualTw r θ) → IneAb r → Flagged r →
    IsIrr (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) →
    WitA ι (r.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) → WitAQ ι r
def AIsoTwOfAlt : Prop := FlagLaws → WinTw → _root_.UpperTheory.V.Z.Win.AIsoTwAlt
def AUpDownOfAlt : Prop := WeakOfAtt → FlagLaws → Thru false → Thru true → WinUpDown → ImaginaryQuadraticEtaCharacter.WinOf → _root_.UpperTheory.V.Z.Win.AUpDownAlt
def AAcrossOfAlt : Prop := FlagLaws → _root_.UpperTheory.V.Z.Win.AUpDownAlt → _root_.UpperTheory.V.Z.Win.AIsoTwAlt → _root_.UpperTheory.V.Z.Win.AAcrossAlt
end UpperTheory.V.Z.Win
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPhiEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
private theorem chi_map {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] (E : W.GDet n A G) (f : A →+* A') (g : G) :
    (E.map f).chi (MonoidAlgebra.single g 1) = (E.chi (MonoidAlgebra.single g 1)).map f := by
  rw [← (AlgebraTools.Det.mapApi E f).1, MonoidAlgebra.mapRingHom_single, map_one]
theorem UpperTheory.V.Ws.exists_phi_universal_ordinary_det_ring_of_link :
    _root_.UpperTheory.V.Ws.UnramifiedInputs → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), (∃ B : W.UniversalOrdinaryDeterminantRing K.r, True) ∧ ∀ B : W.UniversalOrdinaryDeterminantRing K.r, ∃ φ : B.B →ₐ[c'.O] X.B, K.IsPhi X n B φ := by
  intro U Ω _ _ _ l _ c D T _ _ c' h K X n
  obtain ⟨hs, hq, hk⟩ := phiKer K.V
  obtain ⟨E, hE, hcp, hc⟩ := phiDet (maximalIdeal X.B) (algebraMap X.B X.A) X.inj K.V.pr hs hq (K.rho X n) (K.cpT X n)
    (fun g => (phiCpMap K X n g).2.2.2) (phiCpCont K X n)
    fun U hU hle => hk U hU fun A v hA hv => (phiUnr K X n A v hA hv).trans hle
  obtain ⟨ψ, hψ⟩ := phiPsiEx K X n
  obtain ⟨p, hD, hp⟩ := phiPair K.r X.inj (by norm_num) K.V.pr hs (K.rho X n) E ψ hE hc
    (fun g => (congrArg _ (hcp g)).trans (phiCpRed K X n g)) (phiIsPsi K X n ψ hψ) (phiPol K X n)
    (fun v => ⟨_, rfl, phiFlag K X n ψ hψ v⟩) (phiIne K X n)
  obtain ⟨B₀⟩ := U.b0 l T.L Ω K.s K.V c' 4 K.r X.B ⟨p⟩
  refine ⟨⟨B₀, trivial⟩, fun B => ?_⟩
  obtain ⟨φ, ⟨h1, h2⟩, -⟩ := B.univ X.B p
  refine ⟨φ, fun g => ?_, fun v i g => ?_⟩
  · have e := chi_map B.u.D (φ : B.B →+* X.B) (K.V.pr g)
    rw [h1, hD] at e
    exact e.symm.trans (hcp g)
  · have e := congrArg Units.val (DFunLike.congr_fun (h2 v i) g)
    rw [hp] at e
    exact e.trans (hψ v i g)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BcUpCyc
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Base
private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]
private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]
open UpperTheory.V.Sd in
theorem UpperTheory.V.Z.Bc.upCyc_of_alt (hA : _root_.UpperTheory.V.Af.Hypotheses') (cyc : UpperTheory.V.Z.Bc.CycC) : UpperTheory.V.Sd.UpCyc := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hp n hn r hr ⟨π, hreg, hatt⟩ hirr
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  have key : (∃ η : HChar F, IsNormChar E η ∧ SelfTw (CG.mk π).HasSat η) ∨
      ∃ P : CuspSub E n, (∀ τ m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m) ∧ WeakBC (CG.mk π).HasSat (CG.mk P).HasSat := by
    rcases (cyc F E hp inferInstance n hn).1 _ _ (Or.inl ⟨inferInstance, π, rfl, rfl⟩)
      (fun τ => ⟨_, ParLaws.hasInfChar_infChar (CG.mk π) τ, hreg τ⟩) with h1 | ⟨sat', inf', hc, hw, hi⟩
    · exact Or.inl h1
    · rcases hc with ⟨_, P, rfl, rfl⟩ | ⟨hR, -⟩
      · exact Or.inr ⟨P, hi, hw⟩
      · obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
        exact absurd (hR.isReal v) (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex v))
  rcases key with ⟨η, hη, hT⟩ | ⟨P, hinf, hbc⟩
  · obtain ⟨δ, hδ1, -, hiso, hres⟩ := _root_.UpperTheory.V.Sd.self_twist_galois_of_printed_results hA F Ω l ι n r (CG.mk π).HasSat
      (fun _ _ _ h h' => h.unique h') hr hatt η _ hp.pos hη.2.1 hη.1 hT
    exact (hδ1 (UpperTheory.schur_twist_holds _ _ _ n r _ δ hirr (hres E hη) hiso)).elim
  · refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, (UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ n _).2.1 hirr, ?_⟩
    · have h := hreg (τ.comp (algebraMap F E))
      have hm : π.HasInfChar (τ.comp (algebraMap F E)) ((CG.mk π).infChar (τ.comp (algebraMap F E))) :=
        ParLaws.hasInfChar_infChar (CG.mk π) _
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ _ hm)]
      exact h
    · filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
      obtain ⟨B, hB, hPw⟩ := h1 _ (normV_under (K := F) w)
      obtain ⟨B', hB', hF⟩ := h2
      obtain rfl := hB.unique hB'
      refine ⟨_, hPw, ?_⟩
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w)).1 n r _ hF
      rw [← algSat_pow, ← normV_under] at h3
      exact h3
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumberU3US
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.V.Z.J
section Pt
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
end Pt
section Heads
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base
open UpperTheory.V.Alg UpperTheory.V.Th
end Heads
section Count
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Published
structure Adm3U_s {l : ℕ} [Fact l.Prime] {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (ι : Qbar l ≃+* ℂ) (e N : ℕ) (ρ : G K Ω →* GL (Fin 3) (Qbar l)) : Prop extends toAdm3 : _root_.UpperTheory.V.Af.Adm3Alt ι e N ρ where
  unl : Th.Unl l N ![(e : ℤ), 0, -(e : ℤ)] ρ
def NumberU3U_s : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∃ c A : ℕ,
    ∀ e : ℕ, 1 ≤ e → ∀ N : ℕ, 1 ≤ N → ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal → 7 ≤ p →
      ¬ p ∣ N → ¬ (p : ℤ) ∣ discr K →
    ∀ (Orb : Type) [Fintype Orb] (z : Orb → ℂ), (∀ o, ∃ k : ℕ, 0 < k ∧ z o ^ k = 1) →
      (∀ σ : ℂ ≃+* ℂ, ∃ u : Orb ≃ Orb, ∀ o, z (u o) = σ (z o)) →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c * Fintype.card Orb * ((N : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
        [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (B : ValuationSubring Ω), IsPlaceOver B w →
        ∀ σ : G K Ω, IsFrob B (normV w) σ →
        ∀ X : Orb → Finset (G K Ω →* GL (Fin 3) (Qbar l)),
          (∀ o, ∀ ρ ∈ X o, _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ) →
          (∀ o, ∀ ρ ∈ X o, ∀ ρ' ∈ X o, RepIso ρ ρ' → ρ = ρ') →
          (∀ o, ∀ ρ ∈ X o, (ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ ι.symm (eis3 (normV w) e (z o))) ∧
          ‖((NN : ℤ) : Qbar l)‖ ≤
            ∏ o, ∏ ρ ∈ X o, ‖(ρ σ⁻¹ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - ι.symm (eis3 (normV w) e (z o))‖
end Count
section One
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Base
def OneCharU_s : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N),
    GD Ω K l e ψ → ∀ (ι : Qbar l ≃+* ℂ) (σ : G K Ω) (t : Qbar l),
    t = algebraMap c.O (PadicAlgCl l) ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ) : c.O) + 1 +
      (((Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ K Ω σ))⁻¹ : c.Oˣ) : c.O)) →
    (∀ ρ : G K Ω →* GL (Fin 3) (Qbar l), _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ →
      (ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace ≠ t) →
    Vlen Ω c e ψ ≠ ⊤ ∧ ∃ X : Finset (G K Ω →* GL (Fin 3) (Qbar l)),
      (∀ ρ ∈ X, _root_.UpperTheory.V.Z.J.Adm3U_s ι e N ρ ∨ _root_.UpperTheory.V.Z.Win.Dn.Adm2A ι e (N * (discr K).natAbs) ρ) ∧ (∀ ρ ∈ X, ∀ ρ' ∈ X, Af.RepIso ρ ρ' → ρ = ρ') ∧
      Vn Ω c e ψ ≤ 2 * ∑ ρ ∈ X, vl l ((ρ σ : Matrix (Fin 3) (Fin 3) (Qbar l)).trace - t)
def AdmI_s : Prop :=
  ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)
    {U : (_root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition _ (D.η.comp D.ι) (D.Ψ.comp D.ι)))} {g₁ : G ℚ Ω}, D.Marked g₁ → ∀ (S : D.Ring U g₁) (f : S.R →ₐ[c.O] PadicAlgCl l), IsLocPt f →
    ∀ (hr : HasMult D.η (push f S.r.hom)) (ι : Qbar l ≃+* ℂ), U3.TypeI D.η (push f S.r.hom) → D.IsAutIAlt ι (push f S.r.hom) hr →
      _root_.UpperTheory.V.Z.J.Adm3U_s ι e N (D.rhoK (push f S.r.hom) hr)
end One
end UpperTheory.V.Z.J
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTh
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.isAlgChar_pushCh_th_of_good :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ ι : PadicAlgCl l ≃+* ℂ, Af.IsAlgChar ι (W.pushCh (algebraMap c.O (PadicAlgCl l)) D.th) := by
  intro hP Ω _ _ _ l hl c D h ι
  have hc : AdicCont (maximalIdeal c.O) fun g => (D.th g : c.O) := (GradeZeroInterpolatingElement.facts D h).2.2.2.2.2.2.2.2.2.2.1 0
  refine (_root_.UpperTheory.V.Af.algOfCyc_s hP ℚ Ω l ι).1 _ (auCont c D.th hc) fun w _ => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  obtain ⟨m, hm, hx⟩ := h.xi_ord
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun e => hl.out.ne_one (by simpa [e] using hm)
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ h.psi_open
  have hn : 0 < D.ψ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  refine ⟨A, hA, (D.e : ℤ) + 1, (l - 1) * m * D.ψ.ker.index, by positivity, fun s _ => ?_⟩
  have h1 : D.om s ^ (l - 1) = 1 := DFunLike.congr_fun h.om_pow s
  have h2 : D.ξ s ^ m = 1 := DFunLike.congr_fun hx s
  have h3 : D.ψ s ^ D.ψ.ker.index = 1 := by
    rw [← map_pow]
    exact D.ψ.ker.pow_index_mem s
  have e : D.th s * chiO ℚ Ω l c.O s ^ (-((D.e : ℤ) + 1)) = (D.om s)⁻¹ * D.ξ s * D.ψ s := by
    have e0 : D.th s = chiO ℚ Ω l c.O s * (D.om s)⁻¹ * D.ξ s * (chiO ℚ Ω l c.O s ^ (D.e : ℤ) * D.ψ s) := rfl
    rw [e0, zpow_neg, mul_inv_eq_iff_eq_mul, zpow_add_one]
    ac_rfl
  have e2 : (D.th s * chiO ℚ Ω l c.O s ^ (-((D.e : ℤ) + 1))) ^ ((l - 1) * m * D.ψ.ker.index) = 1 := by
    rw [e, mul_pow, mul_pow, inv_pow, pow_mul' (D.ψ s), h3, pow_mul (D.ξ s), pow_mul' (D.ξ s), h2, pow_mul (D.om s),
      pow_mul (D.om s), h1]
    simp
  rw [← (auChi ℚ Ω c).1]
  have := congrArg (Units.map (algebraMap c.O (PadicAlgCl l)).toMonoidHom) e2
  rw [map_pow, map_mul, map_zpow, map_one] at this
  exact this
end
end
