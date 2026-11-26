module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCoefficientSpaceDualDiscreteSeriesModelPos

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryFundamentalDomainVolumePosFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryFundamentalDomainVolumePosFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.DefVol

theorem fdV_measure_pos_lt_top : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F →
    ∀ (i : Fin D.R.m) (t : T), 0 < R.νV i t (R.fdV i t) ∧ R.νV i t (R.fdV i t) < ⊤ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h i t
  have hm := h.models.νV i t
  have hH : (R.νV i t).IsHaarMeasure := hm.1.1
  have hfd : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := hm.2
  obtain ⟨hs, hp⟩ := h.posDef i
  have hc : GlobalTheory.Unf.CoCpt (Vc D i) := GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite hs (fun τ => Or.inl (hp τ))
  refine ⟨?_, GlobalTheory.Unf.vol_fund_lt_top hc ⟨_, _, hH, hfd⟩⟩
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ (Vc D i))
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ (Vc D i)) (R.νV i t)
  rw [pos_iff_ne_zero]
  intro h0
  have hu := hfd.measure_zero_of_invariant (t := Set.univ) (fun g => Set.smul_set_univ) (by simpa using h0)
  exact (Measure.measure_univ_ne_zero.2 (NeZero.ne (R.νV i t))) hu

end GlobalTheory.DefVol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryFundamentalDomainVolumePosFiniteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFundamentalDomain_volume_pos_finite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), 0 < R.νV i t (R.fdV i t) ∧ R.νV i t (R.fdV i t) < ⊤ := by
  first | exact @GlobalTheory.DefVol.fdV_measure_pos_lt_top | exact GlobalTheory.DefVol.fdV_measure_pos_lt_top | (intros; apply GlobalTheory.DefVol.fdV_measure_pos_lt_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurL2PairingRealFiniteTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurL2PairingRealFiniteTranslate
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem schur_trPair_real_fin : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x y : (R.HW i (sg0 D A)).H), ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL i hLP v x y u hu γ hγ
  have hθ : IsInfFam R.θ := hL.models.inf
  obtain ⟨-, hr, -⟩ := hL.models.HW i (sg0 D A)
  have hHaar : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1
  have hfd : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hL.models.νW i).2
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e x) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ x
      exact this)
  have hTm' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  set J' : Set (GA D (Wc D i)) := {k | k ∈ levW R i ∧ γ⁻¹ * k * γ ∈ levW R i} with hJ'
  have hT1 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e x) :=
    ⟨hTm.aut, hTm.cusp, fun w k hk g => by rw [hTm.lev w k hk.1 g, hLP.2.1 k hk.1], hTm.equiv, hTm.cont⟩
  have hT2 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := by
    have hT3 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e y) :=
      ⟨hTm'.aut, hTm'.cusp, fun w k hk g => by rw [hTm'.lev w k hk.1 g, hLP.2.1 k hk.1], hTm'.equiv, hTm'.cont⟩
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT3 (fun k hk => ?_) (fun w k hk g => ?_)
    · rw [Finset.mem_singleton] at hk
      exact hk ▸ hγ
    · simp only [heckeLin_apply, Finset.sum_singleton, one_mul]
      have e : g * k * γ = g * γ * (γ⁻¹ * k * γ) := by group
      rw [e, hTm'.lev w _ hk.2 (g * γ), hLP.2.1 _ hk.2, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.MultFinite.schurMult (θ := R.θ) (M := R.MW i (sg0 D A)) (J := J') (χ := fun _ => 1) hP
    (R.νW i) (R.fdW i) hθ hHaar hfd _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT1) _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT2)
  have hip := ipM_spec _ _ _ _ _ ⟨c, hc⟩
  obtain ⟨v', hv', hmove⟩ := GlobalTheory.RealPointMove.translate_eq_move D R.θ hθ (Wc D i) _ (R.MW i (sg0 D A)) J' (fun _ => 1) _ hT2
    u hu (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))
  have htr : trPair R i γ x y = dimProd A i * ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := rfl
  have hint : ∀ z, star (val R i v x z) * val R i v y (z * (u * γ)) =
      star ((R.HW i (sg0 D A)).e x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) z) *
        heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y) v' z := fun z => by
    rw [← hmove z]
    simp [val, heckeOn, postOn_apply, heckeLin_apply, mul_assoc]
  simp_rw [hint]
  rw [(hip (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) v').2, htr, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [hv' ρ]

end GlobalTheory.RawLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurL2PairingRealFiniteTranslateStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_l2Pairing_realFiniteTranslate : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x y : (R.HW i (sg0 D A)).H), ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  first | exact @GlobalTheory.RawLift.schur_trPair_real_fin | exact GlobalTheory.RawLift.schur_trPair_real_fin | (intros; apply GlobalTheory.RawLift.schur_trPair_real_fin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLowestKTypeMatrixCoeffSqPos
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLowestKTypeMatrixCoeffSqPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LowCoefPos

theorem integral_lowCoefSq_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ v, IsUnitVec R i v → IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) → 0 < ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i hP v hv hI
  have hθ : IsInfFam R.θ := hL.models.inf
  have : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1

  have hrep : ∀ ρ (x : (R.MW i (sg0 D A)).H ρ), Continuous fun h : GA D (Wc D i) =>
      (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h) x := by
    intro ρ x
    have hmem : ∀ h : GA D (Wc D i), (R.MW i (sg0 D A)).fr ρ * infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) h * ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ UJset ((R.MW i (sg0 D A)).ε ρ) :=
      fun h => GlobalTheory.DualCoef.frame_mem (R.MW i (sg0 D A)) ρ (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Wc D i) h ρ)
    exact (((R.MW i (sg0 D A)).ds ρ).2.2.1.2.2 x).comp_continuous
      ((continuous_const.matrix_mul (GlobalTheory.Mem.VolExists.continuous_infMat (Wc D i).gram (hθ ρ))).matrix_mul
        continuous_const) hmem
  have hc : Continuous (lowCoefSq R i v) := by
    unfold lowCoefSq
    refine (continuous_finsetProd _ fun ρ _ => ?_).norm.pow 2
    exact continuous_const.inner (hrep ρ _)

  have h0 : ∀ h, 0 ≤ lowCoefSq R i v h := fun h => by unfold lowCoefSq; positivity

  have h1 : lowCoefSq R i v 1 = 1 := by
    unfold lowCoefSq
    have e : ∀ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) 1)
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ = 1 := by
      intro ρ
      rw [GlobalTheory.PointAtPlaceHom.infMat_one, GlobalTheory.DualCoef.rep_one, ContinuousLinearMap.one_apply,
        inner_self_eq_norm_sq_to_K, hv ρ]
      simp
    simp [e]

  set O : Set (GA D (Wc D i)) := GlobalTheory.AutMult.toFin (Wc D i) ⁻¹'
    {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)} with hO
  have hOo : IsOpen O := (GlobalTheory.LevelOpen.isOpen_levG _ _ _).preimage (GlobalTheory.AutMult.continuous_toFin _)
  have hOs : O ⊆ realLev R i := by
    intro h hh
    exact ⟨_, (GlobalTheory.AutMult.toInf (Wc D i) h).2, _, hh, (GlobalTheory.AutMult.toInf_mul_toFin h).symm⟩
  have h1O : (1 : GA D (Wc D i)) ∈ O := by
    show ((GlobalTheory.AutMult.toFin (Wc D i) 1 : GfC (Wc D i)) : GA D (Wc D i)) ∈ levG _ (R.βW i) (R.datWp i R.triv)
    rw [map_one]
    exact (levW R i).one_mem
  set U : Set (GA D (Wc D i)) := {h | (1 : ℝ) / 2 < lowCoefSq R i v h} ∩ O with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const hc).inter hOo
  have h1U : (1 : GA D (Wc D i)) ∈ U := ⟨by rw [Set.mem_setOf_eq, h1]; norm_num, h1O⟩
  have hUs : U ⊆ Function.support (lowCoefSq R i v) ∩ realLev R i := by
    intro h hh
    refine ⟨?_, hOs hh.2⟩
    have := hh.1
    rw [Set.mem_setOf_eq] at this
    rw [Function.mem_support]
    linarith
  have hpos : 0 < R.νW i U := hUo.measure_pos _ ⟨1, h1U⟩
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hI]
  exact lt_of_lt_of_le hpos (measure_mono hUs)

end GlobalTheory.LowCoefPos

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLowestKTypeMatrixCoeffSqPosStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_lowestKTypeMatrixCoeff_sq_pos : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ v, IsUnitVec R i v → IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) → 0 < ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := by
  first | exact @GlobalTheory.LowCoefPos.integral_lowCoefSq_pos | exact GlobalTheory.LowCoefPos.integral_lowCoefSq_pos | (intros; apply GlobalTheory.LowCoefPos.integral_lowCoefSq_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisIntegrandFactorisesOnLevelCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisIntegrandFactorisesOnLevelCoset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Pointwise

theorem thetaInner_swap {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (f g : WO S T' → ℂ) :
    thetaIP μ 𝓕 g f = star (thetaIP μ 𝓕 f g) := by
  unfold thetaIP
  rw [Complex.star_def, ← integral_conj]
  congr 1
  funext w
  rw [map_mul, Complex.conj_conj, ← Complex.star_def, mul_comm]

theorem rallisF_point : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), LevFix R i t → FactInf R i t → RealLow R i t → LevProd R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ (w : (R.cV i).W) (x y : (R.HW i (sg0 D A)).H), (∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) → ∀ γ ∈ GfC (Wc D i), ∀ h ∈ realLev R i, dimProd A i * rallisF R i t μ 𝓕 v (jointVec R i t v w) x y (γ * h) = thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * coef R i t μ 𝓕 γ * trPair R i γ x y * (lowCoefSq R i v h : ℂ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hLF hFI hRL hLP μ 𝓕 hμ v hv w x y hS γ hγ h hh
  obtain ⟨u, hu, k, hk, rfl⟩ := hh
  have hkf : k ∈ GfC (Wc D i) := hLP.1 hk
  have hcomm : u * γ = γ * u := (GlobalTheory.AutMult.commute_inf_fin ⟨u, hu⟩ ⟨γ, hγ⟩).eq

  obtain ⟨Pc, hPc⟩ : ∃ Pc, (∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ),
      (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u)
        ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) = Pc := ⟨_, rfl⟩

  have hω : R.ωP i t (1, γ * (u * k)) (jointVec R i t v w) = R.ωP i t (1, u * γ) (jointVec R i t v w) := by
    have e : ((1 : GA D (Vc D i)), γ * (u * k)) = (1, u * γ) * (1, k) := by
      rw [Prod.mk_mul_mk, one_mul, hcomm, mul_assoc]
    rw [e, map_mul, Module.End.mul_apply]
    congr 1
    exact hLF k hk _

  have h1 : thetaIP μ 𝓕 (R.ωP i t (1, γ * (u * k)) (jointVec R i t v w)) (jointVec R i t v w) =
      thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * star Pc * coef R i t μ 𝓕 γ := by
    rw [hω]
    have hF := hFI μ 𝓕 hμ u hu γ hγ (R.ioP i (PiTensorProduct.tprod ℂ v) w) (R.ioP i (PiTensorProduct.tprod ℂ v) w)
    have hR := hRL μ 𝓕 hμ v hv w u hu
    rw [hPc] at hR
    unfold jointVec at hR ⊢
    rw [hF, thetaInner_swap, hR, star_mul', ← thetaInner_swap]

  have hval : ∀ z, val R i v y (z * (γ * (u * k))) = val R i v y (z * (u * γ)) := by
    intro z
    have hmem : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := by
      rw [← (hL.models.HW i (sg0 D A)).2.1]
      exact LinearMap.mem_range_self _ y
    have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hmem
    have hl := hm.lev (fun ρ => v ρ) k hk (z * (u * γ))
    unfold val
    rw [hLP.2.1 k hk, one_mul] at hl
    rw [← hl, hcomm]
    simp only [mul_assoc]
  have h2 := hS u hu γ hγ
  rw [hPc] at h2
  simp only [← hval] at h2

  have hinf : ∀ ρ, infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) (u * k) = infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u := by
    intro ρ
    rw [Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.infMat_mul]
    have hk1 : infHom (Wc D i) k = 1 := hkf
    have e : infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) k = 1 := by
      show ((infHom (Wc D i) k).1).map (R.θ ρ) = 1
      rw [hk1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, Matrix.mul_one]
  have h3 : ((lowCoefSq R i v (u * k) : ℝ) : ℂ) = star Pc * Pc := by
    unfold lowCoefSq
    simp only [hinf]
    rw [hPc]
    push_cast
    rw [Complex.star_def, Complex.conj_mul']
  unfold rallisF
  rw [h1, h3]
  linear_combination (thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * star Pc * coef R i t μ 𝓕 γ) * h2

end GlobalTheory.RawLift.Pointwise

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisIntegrandFactorisesOnLevelCosetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rallisIntegrand_factorises_on_levelCoset : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ (i : Fin D.R.m) (t : T), LevFix R i t → FactInf R i t → RealLow R i t → LevProd R i → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v, IsUnitVec R i v → ∀ (w : (R.cV i).W) (x y : (R.HW i (sg0 D A)).H), (∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ) → ∀ γ ∈ GfC (Wc D i), ∀ h ∈ realLev R i, dimProd A i * rallisF R i t μ 𝓕 v (jointVec R i t v w) x y (γ * h) = thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) * coef R i t μ 𝓕 γ * trPair R i γ x y * (lowCoefSq R i v h : ℂ) := by
  first | exact @GlobalTheory.RawLift.Pointwise.rallisF_point | exact GlobalTheory.RawLift.Pointwise.rallisF_point | (intros; apply GlobalTheory.RawLift.Pointwise.rallisF_point <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def FinSumAt (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ x y,
    HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (a : ℂ) * (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y))
      ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ

theorem jointVec_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (c : ℂ)
    (w : (R.cV i).W) : jointVec R i t v (c • w) = c • jointVec R i t v w := by
  simp only [jointVec, RealDat.ptP, map_smul]

theorem thetaInner_self {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (f : WO S T' → ℂ) :
    thetaIP μ 𝓕 f f = ((∫ z in 𝓕, ‖f z‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  unfold thetaIP
  rw [← integral_complex_ofReal]
  congr 1
  funext z
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

theorem exists_basis_vec (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i)))
    (h : ∃ v w, IsUnitVec R i v ∧ thetaIP μ 𝓕 (jointVec R i t v w) (jointVec R i t v w) ≠ 0) :
    ∃ v, IsUnitVec R i v ∧ ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (k0 : Fin n),
      thetaIP μ 𝓕 (jointVec R i t v (b k0)) (jointVec R i t v (b k0)) ≠ 0 := by
  obtain ⟨v, w, hv, hw⟩ := h
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hw
    have e : jointVec R i t v 0 = 0 := by simpa using jointVec_smul R i t v 0 0
    rw [e]
    simp [thetaIP]
  have hn : 0 < Module.finrank ℂ (R.cV i).W := by
    haveI : Nontrivial (R.cV i).W := ⟨⟨w, 0, hw0⟩⟩
    exact Module.finrank_pos
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := (R.cV i).W)
    (ι := Fin (Module.finrank ℂ (R.cV i).W)) (by simp) (v := fun _ => ((‖w‖⁻¹ : ℝ) : ℂ) • w)
    (s := {⟨0, hn⟩}) (by
      rw [orthonormal_iff_ite]
      rintro ⟨a, ha⟩ ⟨c, hc⟩
      rw [Set.mem_singleton_iff] at ha hc
      subst ha hc
      rw [if_pos rfl]
      show ⟪((‖w‖⁻¹ : ℝ) : ℂ) • w, ((‖w‖⁻¹ : ℝ) : ℂ) • w⟫_ℂ = 1
      rw [inner_self_eq_norm_sq_to_K, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ hwn]
      simp)
  refine ⟨v, hv, _, b, ⟨0, hn⟩, ?_⟩
  rw [hb _ rfl, jointVec_smul, thetaInner_smul_left, thetaInner_smul_right]
  have hc : ((‖w‖⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero hwn
  exact mul_ne_zero (star_ne_zero.2 hc) (mul_ne_zero hc hw)


set_option maxHeartbeats 1000000 in
theorem finSumAt_core (hC : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (hRal : RallisConv D) (i : Fin D.R.m) (t : T) (hAdj : AdjFormula R i t) (hLF : LevFix R i t)
    (hFI : FactInf R i t) (hRL : RealLow R i t) (hLP : LevProd R i) (hTL : TransLaws R i)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : IsRaw R i t th) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕)
    (hvP : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) ≠ 0) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (hv : IsUnitVec R i v)
    (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (R.cV i).W) (k0 : Fin n)
    (hk0 : thetaIP μ 𝓕 (jointVec R i t v (b k0)) (jointVec R i t v (b k0)) ≠ 0)
    (x₀ : (R.HW i (sg0 D A)).H) (hx₀ : x₀ ≠ 0) : FinSumAt R i t th μ 𝓕 := by
  obtain ⟨-, -, -, -, -, tF⟩ := hTL
  have hm := hL.models
  have hνV : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfdV := (hm.νV i t).2
  have hνW : (R.νW i).IsHaarMeasure := (hm.νW i).1.1
  have hfdW := (hm.νW i).2
  have hpos := hL.posDef i

  have hmem : ∀ x, IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e x) := fun x =>
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (by
      have e := (hm.HW i (sg0 D A)).2.1
      show _ ∈ R.Wall i (sg0 D A)
      rw [← e]
      exact LinearMap.mem_range_self _ x)

  have hR : ∀ k x y, Integrable (rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y) (R.νW i) ∧
      ∫ h in R.fdV i t, star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t) =
        ((R.νV i t (R.fdV i t)).toReal : ℂ) *
          ∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i) := by
    intro k x y
    have := hRal R.θ R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hm.inf (hL.thP.ωP i t) hpos.1 hpos.2
      (two_mul_rank_W_lt D i) (R.νV i t) (R.fdV i t) (R.νW i) (R.fdW i) μ 𝓕 hνV hfdV hνW hfdW hμ.1 hμ.2.1 hμ.2.2
      (jointVec R i t v (b k)) (jointVec R i t v (b k)) (val R i v x) (val R i v y)
      (hL.thP.pt_theta i t _) (hL.thP.pt_theta i t _) ((hmem x).aut _) ((hmem x).cusp _) ((hmem y).aut _)
      ((hmem y).cusp _)
    exact ⟨this.2.2.1, this.2.2.2⟩

  have hP := fun k x y => GlobalTheory.T.rallisIntegrand_factorises_on_levelCoset D G Pl0 T A Ks R F hL i t hLF hFI hRL hLP μ 𝓕 hμ v hv (b k) x y
    (GlobalTheory.T.schur_l2Pairing_realFiniteTranslate hC D G Pl0 T A Ks R F hL i hLP v x y)

  have hKo : IsOpen {g : GfC (Wc D i) | (g : GA D (Wc D i)) ∈ levW R i} :=
    GlobalTheory.LevelOpen.isOpen_levG _ _ _
  have hCo := fun k x y => GlobalTheory.T.integral_eq_tsum_realPoints_levelCoset_translates D (Wc D i) (R.νW i) (levW R i) hνW hLP.1 hKo _ (hR k x y).1
  have hmeas : MeasurableSet (realLev R i) := (hCo k0 x₀ x₀).1

  obtain ⟨Pr, hPr, hPc⟩ : ∃ Pr : ℝ, 0 < Pr ∧ dimProd A i = (Pr : ℂ) :=
    ⟨∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℝ),
      Finset.prod_pos fun ρ _ => by exact_mod_cast GlobalTheory.Mem.WeylDimPos.dimK_kapAt_Wc_pos D i _ ρ,
      by unfold dimProd; push_cast; rfl⟩
  have hPne : (Pr : ℂ) ≠ 0 := by exact_mod_cast hPr.ne'
  obtain ⟨nf, hnf⟩ : ∃ nf : Fin n → ℝ, ∀ k, thetaIP μ 𝓕 (jointVec R i t v (b k)) (jointVec R i t v (b k)) = nf k ∧
      0 ≤ nf k :=
    ⟨fun k => ∫ z in 𝓕, ‖jointVec R i t v (b k) z‖ ^ 2 ∂μ, fun k =>
      ⟨thetaInner_self _ _ _, integral_nonneg fun z => by positivity⟩⟩
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ h in realLev R i, lowCoefSq R i v h ∂(R.νW i) := ⟨_, rfl⟩

  have hq : ∀ k x y (γ : GfC (Wc D i)),
      ∫ h in realLev R i, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y ((γ : GA D (Wc D i)) * h) ∂(R.νW i) =
        (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 γ * trPair R i γ x y * (I : ℂ)) := by
    intro k x y γ
    have e : Set.EqOn (fun h => rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y ((γ : GA D (Wc D i)) * h))
        (fun h => ((Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 γ * trPair R i γ x y)) * (lowCoefSq R i v h : ℂ))
        (realLev R i) := by
      intro h hh
      have := hP k x y γ γ.2 h hh
      rw [hPc, (hnf k).1] at this
      simp only
      field_simp
      linear_combination this
    rw [setIntegral_congr_fun hmeas e, integral_const_mul, integral_complex_ofReal, ← hI]
    ring

  have hk : ∀ k x y, HasSum (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y *
        (I : ℂ))) (∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i)) := by
    intro k x y
    convert (hCo k x y).2 using 1
    funext q
    exact (hq k x y q.out).symm

  have hc1 : coef R i t μ 𝓕 1 = 1 := by
    unfold coef
    rw [show ((1 : GA D (Vc D i)), (1 : GA D (Wc D i))) = 1 from rfl, map_one, Module.End.one_apply]
    exact div_self hvP
  have hnf0 : (nf k0 : ℂ) ≠ 0 := by rw [← (hnf k0).1]; exact hk0
  have hx0 : trPair R i 1 x₀ x₀ ≠ 0 := by rw [tF]; exact inner_self_ne_zero.2 hx₀
  have hGint : IntegrableOn (lowCoefSq R i v) (realLev R i) (R.νW i) := by
    have hF : IntegrableOn (fun h => ((nf k0 : ℂ) * trPair R i 1 x₀ x₀)⁻¹ *
        ((Pr : ℂ) * rallisF R i t μ 𝓕 v (jointVec R i t v (b k0)) x₀ x₀ h)) (realLev R i) (R.νW i) :=
      ((hR k0 x₀ x₀).1.integrableOn.const_mul _).const_mul _
    have e : Set.EqOn (fun h => ((nf k0 : ℂ) * trPair R i 1 x₀ x₀)⁻¹ *
        ((Pr : ℂ) * rallisF R i t μ 𝓕 v (jointVec R i t v (b k0)) x₀ x₀ h))
        (fun h => (lowCoefSq R i v h : ℂ)) (realLev R i) := by
      intro h hh
      have := hP k0 x₀ x₀ 1 (GfC (Wc D i)).one_mem h hh
      rw [one_mul, hPc, (hnf k0).1, hc1] at this
      simp only
      rw [this]
      field_simp
    have h3 := (hF.congr_fun e hmeas).re
    change IntegrableOn (fun x => Complex.re (lowCoefSq R i v x : ℂ)) (realLev R i) (R.νW i) at h3
    simpa only [Complex.ofReal_re] using h3
  have hIpos : 0 < I := hI ▸ GlobalTheory.T.integral_lowestKTypeMatrixCoeff_sq_pos D G Pl0 T A Ks R F hL i hLP v hv hGint

  obtain ⟨a₀, ha₀, hA⟩ := hAdj th hth v hv n b
  have hvol := GlobalTheory.T.definiteUnitaryFundamentalDomain_volume_pos_finite D G Pl0 T A Ks R F hL i t
  have hvolpos : 0 < (R.νV i t (R.fdV i t)).toReal := ENNReal.toReal_pos hvol.1.ne' hvol.2.ne
  have hnfs : 0 < ∑ k, nf k := Finset.sum_pos' (fun k _ => (hnf k).2)
    ⟨k0, Finset.mem_univ _, lt_of_le_of_ne (hnf k0).2 fun h => hnf0 (by rw [← h]; simp)⟩
  refine ⟨a₀ * (R.νV i t (R.fdV i t)).toReal * (∑ k, nf k) * I / Pr, by positivity, fun x y => ?_⟩
  rw [hA x y]
  have h2 := (hasSum_sum (s := Finset.univ) fun k _ => hk k x y).mul_left
    ((a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ))
  have hfun : (fun q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) =>
      ((a₀ * (R.νV i t (R.fdV i t)).toReal * (∑ k, nf k) * I / Pr : ℝ) : ℂ) *
        (coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y)) =
      fun q => (a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ) * ∑ k, (Pr : ℂ)⁻¹ * ((nf k : ℂ) *
        coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) := by
    funext q
    have e1 : ∑ k, (Pr : ℂ)⁻¹ * ((nf k : ℂ) * coef R i t μ 𝓕 (q.out : GfC (Wc D i)) *
        trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) = (∑ k, (nf k : ℂ)) * ((Pr : ℂ)⁻¹ *
        coef R i t μ 𝓕 (q.out : GfC (Wc D i)) * trPair R i (q.out : GfC (Wc D i)) x y * (I : ℂ)) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e1]
    push_cast
    field_simp
  have hval : (a₀ : ℂ) * ∑ k, ∫ h in R.fdV i t,
        star (upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v x) h) *
          upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h ∂(R.νV i t) =
      (a₀ : ℂ) * ((R.νV i t (R.fdV i t)).toReal : ℂ) *
        ∑ k, ∫ g, rallisF R i t μ 𝓕 v (jointVec R i t v (b k)) x y g ∂(R.νW i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hR k x y).2]
    ring
  rw [hfun, hval]
  exact h2

theorem finSumAt_of (hC : GlobalTheory.Published.CuspRapidDecay) (R : RealDat D A Ks) (F : Face D A) (hL : Laws R F)
    (hRal : RallisConv D) (i : Fin D.R.m) (t : T) (hAdj : AdjFormula R i t) (hLF : LevFix R i t)
    (hFI : FactInf R i t) (hRL : RealLow R i t) (hVN : VecNe R i t) (hLP : LevProd R i) (hTL : TransLaws R i)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : IsRaw R i t th) (μ : Measure (WO (Vc D i) (Wc D i)))
    (𝓕 : Set (WO (Vc D i) (Wc D i))) (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕) : FinSumAt R i t th μ 𝓕 := by
  by_cases hx : ∃ x₀ : (R.HW i (sg0 D A)).H, x₀ ≠ 0
  · obtain ⟨x₀, hx₀⟩ := hx
    obtain ⟨v, hv, n, b, k0, hk0⟩ := exists_basis_vec R i t μ 𝓕 (hVN μ 𝓕 hμ).2
    exact finSumAt_core hC R F hL hRal i t hAdj hLF hFI hRL hLP hTL th hth μ 𝓕 hμ (hVN μ 𝓕 hμ).1 v hv n b k0 hk0
      x₀ hx₀
  · push_neg at hx
    obtain ⟨-, -, tC, -, -, -⟩ := hTL
    refine ⟨1, one_pos, fun x y => ?_⟩
    have ex : LinearMap.adjoint th x = 0 := by rw [hx x, map_zero]
    have hterm : ∀ q : GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)),
        trPair R i (q.out : GfC (Wc D i)) x y = 0 := fun q => by
      obtain ⟨B, -, hB⟩ := tC _ (q.out).2
      rw [hB, hx x, inner_zero_left]
    simp only [ex, inner_zero_left, hterm, mul_zero]
    exact hasSum_zero

theorem finSum_of_rallis : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → RallisConv D → ∀ i t, AdjFormula R i t → LevFix R i t → FactInf R i t → RealLow R i t → VecNe R i t → LevProd R i → TransLaws R i → FinSum R i t :=
  fun hC _ _ _ _ _ _ _ _ _ _ _ R F hL _ hRal i t hAdj hLF hFI hRL hVN hLP hTL th hth μ 𝓕 hμ =>
    finSumAt_of hC R F hL hRal i t hAdj hLF hFI hRL hVN hLP hTL th hth μ 𝓕 hμ

end GlobalTheory.RawLift

end
