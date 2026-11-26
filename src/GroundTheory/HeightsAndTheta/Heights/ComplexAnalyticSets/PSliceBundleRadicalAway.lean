module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegFixedBallMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLogLogCutHessDeriv
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffFinite

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBundleRadicalAway
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SliceBundleRadicalAway

variable {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (q : Fin n → ℂ) (k : Fin n)

abbrev Base := Localization.Away (Ideal.Quotient.mk J (X k - C (q k)))

def toBase : MvPolynomial (Fin n) ℂ →+* Base J q k :=
  (algebraMap _ (Base J q k)).comp (Ideal.Quotient.mk J)

def rowForm (i : Fin d) : MvPolynomial (Fin d × Fin n) (Base J q k) :=
  ∑ j, X (i, j) * C (toBase J q k (X j - C (q j)))

def coeffMap : MvPolynomial (Fin d × Fin n) ℂ →+* MvPolynomial (Fin d × Fin n) (Base J q k) :=
  eval₂Hom (C.comp ((toBase J q k).comp C)) fun ij =>
    X ij - if ij.2 = k then
      C (IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k)))) * rowForm J d q k ij.1
    else 0

def solveMap :
    MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) →+* MvPolynomial (Fin d × Fin n) (Base J q k) :=
  eval₂Hom (coeffMap J d q k) fun j => C (toBase J q k (X j))

abbrev Quo := MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) ⧸ universalSliceIdeal J d q

instance instCommRingQuo : CommRing (Quo J d q) := Ideal.Quotient.commRing _

def uQuo : Quo J d q :=
  algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) (Quo J d q) (X k - C (C (q k)))

abbrev Tot := Localization.Away (uQuo J d q k)

def toTot : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) →+* Tot J d q k :=
  algebraMap _ _

theorem toTot_apply (x : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) :
    toTot J d q k x = algebraMap (Quo J d q) (Tot J d q k)
      (algebraMap (MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)) (Quo J d q) x) :=
  IsScalarTower.algebraMap_apply _ _ _ x

theorem toTot_eq_zero {x : MvPolynomial (Fin n) (MvPolynomial (Fin d × Fin n) ℂ)}
    (hx : x ∈ universalSliceIdeal J d q) : toTot J d q k x = 0 := by
  rw [toTot_apply, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

def quotToTot : (MvPolynomial (Fin n) ℂ ⧸ J) →+* Tot J d q k :=
  Ideal.Quotient.lift J ((toTot J d q k).comp (MvPolynomial.map C)) fun a ha =>
    toTot_eq_zero J d q k (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

theorem quotToTot_isUnit : IsUnit (quotToTot J d q k (Ideal.Quotient.mk J (X k - C (q k)))) := by
  have e : MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ) (X k - C (q k)) =
      X k - C (C (q k)) := by simp
  rw [quotToTot, Ideal.Quotient.lift_mk, RingHom.comp_apply, e, toTot_apply]
  exact IsLocalization.Away.algebraMap_isUnit (S := Tot J d q k) (uQuo J d q k)

def baseToTot : Base J q k →+* Tot J d q k :=
  IsLocalization.Away.lift (R := MvPolynomial (Fin n) ℂ ⧸ J) (S := Base J q k) (P := Tot J d q k)
    (Ideal.Quotient.mk J (X k - C (q k))) (g := quotToTot J d q k) (quotToTot_isUnit J d q k)

theorem baseToTot_toBase (a : MvPolynomial (Fin n) ℂ) :
    baseToTot J d q k (toBase J q k a) = toTot J d q k (MvPolynomial.map C a) := by
  simp [baseToTot, toBase, quotToTot]

def backMap : MvPolynomial (Fin d × Fin n) (Base J q k) →+* Tot J d q k :=
  eval₂Hom (baseToTot J d q k) fun ij => toTot J d q k (C (X ij))

theorem backMap_rowForm (i : Fin d) : backMap J d q k (rowForm J d q k i) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rowForm, map_sum, map_mul, backMap, eval₂Hom_X', eval₂Hom_C, baseToTot_toBase]
  rw [← toTot_eq_zero J d q k (x := ∑ j, C (X (i, j)) * (X j - C (C (q j))))
    (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, map_sub]

theorem backMap_comp_solveMap : (backMap J d q k).comp (solveMap J d q k) = toTot J d q k := by
  have hc : (backMap J d q k).comp (coeffMap J d q k) = (toTot J d q k).comp C := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coeffMap, backMap, baseToTot_toBase]
    · intro ij
      simp only [RingHom.comp_apply, coeffMap, eval₂Hom_X', map_sub]
      split_ifs
      · rw [map_mul, backMap_rowForm, mul_zero, sub_zero]
        simp [backMap]
      · simp [backMap]
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa [solveMap] using RingHom.congr_fun hc a
  · intro j
    simp [solveMap, backMap, baseToTot_toBase]

theorem coeffMap_comp_mapC :
    (solveMap J d q k).comp (MvPolynomial.map C) = C.comp (toBase J q k) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [solveMap, coeffMap]
  · intro j
    simp [solveMap]

theorem solveMap_gen (i : Fin d) :
    solveMap J d q k (∑ j, C (X (i, j)) * (X j - C (C (q j)))) = 0 := by
  have h : ∀ j, solveMap J d q k (C (X (i, j)) * (X j - C (C (q j)))) =
      (X (i, j) - if j = k then
        C (IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k)))) * rowForm J d q k i
      else 0) * C (toBase J q k (X j - C (q j))) := by
    intro j
    have := RingHom.congr_fun (coeffMap_comp_mapC J d q k) (X j - C (q j))
    have e : MvPolynomial.map (C : ℂ →+* MvPolynomial (Fin d × Fin n) ℂ) (X j - C (q j)) =
        X j - C (C (q j)) := by simp
    rw [RingHom.comp_apply, RingHom.comp_apply, e] at this
    rw [map_mul, this]
    congr 1
    rw [solveMap, eval₂Hom_C, coeffMap, eval₂Hom_X']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun j _ => h j]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [← rowForm, mul_assoc, mul_comm (rowForm J d q k i), ← mul_assoc, ← map_mul]
  have hu : IsLocalization.Away.invSelf (Ideal.Quotient.mk J (X k - C (q k))) *
      toBase J q k (X k - C (q k)) = (1 : Base J q k) := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf (S := Base J q k) (Ideal.Quotient.mk J (X k - C (q k)))
  rw [hu, map_one, one_mul, sub_self]

theorem le_ker_solveMap : universalSliceIdeal J d q ≤ RingHom.ker (solveMap J d q k) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, coeffMap_comp_mapC]
    simp [toBase, Ideal.Quotient.eq_zero_iff_mem.2 ha]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact solveMap_gen J d q k i

end SliceBundleRadicalAway

theorem SliceBundleRadicalAway.proof : SliceBundleRadicalAway.Statement := by
  intro n d J q hJ k f hf
  have : IsReduced (MvPolynomial (Fin n) ℂ ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).1 hJ
  obtain ⟨m, hm⟩ := hf
  have h0 : SliceBundleRadicalAway.solveMap J d q k f = 0 := by
    apply IsNilpotent.eq_zero
    exact ⟨m, by rw [← map_pow]; exact SliceBundleRadicalAway.le_ker_solveMap J d q k hm⟩
  have h1 : SliceBundleRadicalAway.toTot J d q k f = 0 := by
    rw [← SliceBundleRadicalAway.backMap_comp_solveMap J d q k, RingHom.comp_apply, h0, map_zero]
  rw [SliceBundleRadicalAway.toTot_apply] at h1
  obtain ⟨⟨_, e, rfl⟩, he⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (SliceBundleRadicalAway.uQuo J d q k)) (SliceBundleRadicalAway.Tot J d q k) _).1 h1
  refine ⟨e, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq, map_mul, map_pow]
  exact he

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamCritNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Metric Matrix ComplexSets

theorem ParamCritNull.proof : ParamCritNull.Statement := by
  intro n d W A σ r N hW hdim hA hσ hinj hN hZ
  have hg : DifferentiableOn ℂ (fun v => A *ᵥ σ v) (ball (0 : Fin d → ℂ) r) := by
    have hL : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
    exact hL.comp_differentiableOn hσ
  set Ω : Set (Fin d → ℂ) := ball (0 : Fin d → ℂ) r ∩ σ ⁻¹' N with hΩdef
  have hΩ : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage isOpen_ball hN
  rcases Set.eq_empty_or_nonempty Ω with hemp | hne
  · have hsub : {w | w ∈ ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} ⊆ Ω :=
      fun w hw => ⟨hw.1, hw.2.1⟩
    rw [hemp] at hsub
    rw [Set.subset_empty_iff.mp hsub, measure_empty]

  have hsome : ∃ w ∈ ball (0 : Fin d → ℂ) r,
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hrank : ∀ v ∈ Ω, ¬ Function.Injective (fderiv ℂ (fun v => A *ᵥ σ v) v) := by
      intro v hv hinjv
      have h0 := hcon v hv.1
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
      exact h0 (LinearMap.ker_eq_bot.mpr hinjv)
    obtain ⟨y, hy⟩ := IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof d d Ω (fun v => A *ᵥ σ v) hΩ hne
      (hg.mono Set.inter_subset_left) hrank
    have himg : (σ '' {t | t ∈ Ω ∧ A *ᵥ σ t = y}).Infinite :=
      hy.image (hinj.mono fun t ht => ht.1.1)
    have hfin := (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
    refine himg (hfin.subset ?_)
    rintro x ⟨t, ⟨⟨htb, htN⟩, hty⟩, rfl⟩
    exact ⟨hZ t htb htN, hty⟩

  have han : AnalyticOnNhd ℂ (fun w =>
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ))
      (ball (0 : Fin d → ℂ) r) := fun w hw =>
    IndefiniteRowSideFullHecke.ComplexSets.analyticAt_det_fderiv
      (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.analyticAt_of_differentiableOn isOpen_ball hg hw)
  refine measure_mono_null ?_ (ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball
    (convex_ball (0 : Fin d → ℂ) r).isPreconnected han hsome)
  exact fun w hw => ⟨hw.1, hw.2.2⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDivisorBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets

noncomputable section

namespace DivisorBranches

theorem quotient_inf_dim_lt {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := _root_.GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches.quotient_inf_dim_lt (R := R) (I₁ := I₁) (I₂ := I₂) (d := d) h₁ h₂

theorem not_mem_zeroSet_of_le {n : ℕ} {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I')
    {q : Fin n → ℂ} (hq : q ∉ zeroSet I) : q ∉ zeroSet I' :=
  fun h => hq fun f hf => h f (hle hf)

theorem proof (hModel : IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.Statement)
    (hReg : DivisorRegularGeneric.Statement) (hChart : NormalDivisorChartGeneric.Statement)
    (hDouble : NormalDoublePointsGeneric.Statement) (hGood : DivisorGoodPointBranches.Statement) :
    DivisorBranches.Statement := by
  intro n d J u hJ hdim hu
  obtain ⟨M⟩ := hModel n J hJ
  obtain ⟨I₁, hle₁, hdim₁, hI₁⟩ := hReg n d J u hJ hdim hu
  obtain ⟨I₂, hle₂, hdim₂, hI₂⟩ := hChart n d J u M hJ hdim hu
  obtain ⟨I₃, hle₃, hdim₃, hI₃⟩ := hDouble n d J u M hJ hdim hu
  refine ⟨I₁ ⊓ I₂ ⊓ I₃, le_inf (le_inf hle₁ hle₂) hle₃,
    quotient_inf_dim_lt (quotient_inf_dim_lt hdim₁ hdim₂) hdim₃, ?_⟩
  intro q hqJ hqu hqI
  exact hGood n d J u M q hJ hdim hu hqJ hqu
    (hI₁ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_left) hqI))
    (hI₂ q hqJ hqu (not_mem_zeroSet_of_le (inf_le_left.trans inf_le_right) hqI))
    (hI₃ q hqJ hqu (not_mem_zeroSet_of_le inf_le_right hqI))

end DivisorBranches

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamDensIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff

noncomputable section

theorem ParamDensIntegrable.analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem ParamDensIntegrable.proof : ParamDensIntegrable.Statement := by
  intro n d W σ r r' N hσ hrr' hN f φ hf hfN hφ
  set B := Metric.ball (0 : Fin d → ℂ) r with hB
  choose U hUo hZU hφU using hφ
  set V : Set (Fin d → ℂ) := B ∩ σ ⁻¹' (⋂ k, U k) with hV
  have hσc : ContinuousOn σ B := hσ.continuousOn
  have hVo : IsOpen V := hσc.isOpen_inter_preimage Metric.isOpen_ball (isOpen_iInter_of_finite hUo)
  have hσ2 : ContDiffOn ℝ 2 σ B :=
    ((ParamDensIntegrable.analyticOnNhd_of_differentiableOn Metric.isOpen_ball hσ).contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ σ) V := by
    intro k
    exact ((hφU k).of_le (WithTop.coe_le_coe.2 le_top)).comp (hσ2.mono Set.inter_subset_left)
      fun w hw => Set.mem_iInter.1 hw.2 k
  have hmaV : ContinuousOn (ReciprocityTheory.AnForm.maDens fun k => φ k ∘ σ) V :=
    ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ hVo hc2
  have hcont : ContinuousOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w) B := by
    refine continuousOn_of_forall_continuousAt fun w hw => ?_
    by_cases hs : σ w ∈ tsupport f
    · have hwV : w ∈ V := ⟨hw, Set.mem_iInter.2 fun k => hZU k (hN w hw (hfN hs)).1⟩
      exact ((hf.continuousAt).comp (hσc.continuousAt (Metric.isOpen_ball.mem_nhds hw))).mul
        (hmaV.continuousAt (hVo.mem_nhds hwV))
    · have hO : IsOpen (B ∩ σ ⁻¹' (tsupport f)ᶜ) :=
        hσc.isOpen_inter_preimage Metric.isOpen_ball (isClosed_tsupport f).isOpen_compl
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hO.mem_nhds ⟨hw, hs⟩] with w' hw'
      simp [image_eq_zero_of_notMem_tsupport hw'.2]
  have hK : IsCompact (Metric.closedBall (0 : Fin d → ℂ) r') := isCompact_closedBall 0 r'
  have hKB : Metric.closedBall (0 : Fin d → ℂ) r' ⊆ B := Metric.closedBall_subset_ball hrr'
  refine ((hcont.mono hKB).integrableOn_compact hK).of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet ?_
  rintro w ⟨hwB, hwK⟩
  have hf0 : f (σ w) = 0 := by
    by_contra h
    exact hwK (Metric.mem_closedBall.2 (by
      simpa using (hN w hwB (hfN (subset_tsupport f h))).2))
  simp [hf0]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamOffRegularZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem ParamOffRegularZero.proof : ParamOffRegularZero.Statement := by
  intro n d W A σ r N hσ hZN f φ hfN
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set C : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} with hC
  set R : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  have hgd : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, DifferentiableAt ℂ g w := by
    intro w hw
    have hσw : DifferentiableAt ℂ σ w := (hσ w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiableAt.comp w hσw
  have hnull : volume (g '' C) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun w => (fderiv ℂ g w).restrictScalars ℝ) ?_ ?_
    · intro w hw
      exact ((hgd w hw.1).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro w hw
      rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
        LinearMap.det_restrictScalars, hw.2.2, Algebra.norm_complex_apply, map_zero]
  have hz : ∀ y ∉ g '' C, chartDens W A ((σ '' R)ᶜ.indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    classical
    rw [finsum_eq_if]
    split_ifs with hx hs
    · by_cases hxR : x ∈ σ '' R
      · simp [hxR]
      by_cases hf : f x = 0
      · simp [hxR, hf]
      exfalso
      have hxN : x ∈ N := hfN (subset_tsupport f (Function.mem_support.mpr hf))
      obtain ⟨w, hw, rfl⟩ := hZN ⟨hx.1, hxN⟩
      have hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0 := by
        by_contra hne
        exact hxR ⟨w, ⟨hw, hxN, hne⟩, rfl⟩
      exact hy ⟨w, ⟨hw, hxN, hdet⟩, hx.2⟩
    · rfl
    · rfl
  unfold chartInt
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra h
  exact hy (by simpa using hz y h)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

theorem SliceBranches.proof (hI : IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement)
    (hB : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) (hM : SliceMatricesOpen.Statement)
    (hC : ImplicitCurve.Statement) : SliceBranches.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U Λ hUo hUd hΛ
  obtain ⟨N₁, hN₁, hcov₁⟩ := hcov
  obtain ⟨V, hV, hVd⟩ := hI n d J W u p m γ hJ hdim hu hW hp hsl
  have hOp : interior (N₁ ∩ V) ∈ 𝓝 p := interior_mem_nhds.2 (inter_mem hN₁ hV)
  obtain ⟨y, hyO, hyW, hyU⟩ := mem_closure_iff_nhds.1 (hUd hp) _ hOp
  obtain ⟨q, ⟨hqO, hqU⟩, hqW, hqs⟩ := mem_closure_iff_nhds.1 (hVd ⟨hyW, (interior_subset hyO).2⟩)
    (interior (N₁ ∩ V) ∩ U) (inter_mem (isOpen_interior.mem_nhds hyO) (hUo.mem_nhds hyU))
  have hqN : N₁ ∈ 𝓝 q := mem_of_superset (mem_interior_iff_mem_nhds.1 hqO) fun x hx => hx.1
  choose s hs hs0 hsq hsinj using hqs
  obtain ⟨hGo, hGne⟩ := hM n d m (fun b => (γ b).toFun) s
    (fun b => (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds (hs b))) hsinj
  obtain ⟨L, hLG, hLΛ⟩ := (hΛ q ⟨hqW, hqU⟩).inter_open_nonempty _ hGo hGne
  choose r hr φ hφd hφ0 hφ P hP hPφ using fun b =>
    hC n d (γ b).toFun (γ b).radius L (s b) (γ b).differentiableOn (hs b) (hLG b)
  choose ε hεpos hεP using fun b =>
    hB n (d + 1) J u p q m γ hJ hdim hu ⟨N₁, hqN, hcov₁⟩ hdisj b (s b) (hs b) (hsq b) (P b) (hP b)
  have hφ0' : ∀ b, ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) (r b), φ b τ 0 = τ 0 := fun b τ hτ => by
    rw [(hφ b τ hτ).2.1, hs0 b, zero_add]
  let c : Fin m → VarBranch (sliceIdeal J L q) 1 q := fun b =>
    { radius := r b
      radius_pos := hr b
      toFun := fun τ => (γ b).toFun (φ b τ)
      differentiableOn := (γ b).differentiableOn.comp (hφd b) fun τ hτ => (hφ b τ hτ).1
      injOn := fun τ hτ τ' hτ' h => by
        have h0 := congrArg (fun t => t 0) ((γ b).injOn (hφ b τ hτ).1 (hφ b τ' hτ').1 h)
        simp only [hφ0' b τ hτ, hφ0' b τ' hτ'] at h0
        funext i
        rwa [Subsingleton.elim i 0]
      map_zero := by simp only [hφ0 b, hsq b]
      mapsTo := fun τ hτ => by
        rw [zeroSet_sliceIdeal]
        exact ⟨(γ b).mapsTo (hφ b τ hτ).1, by rw [Set.mem_ofPred_eq, (hφ b τ hτ).2.2, hsq b]⟩ }
  have himg : ∀ b, (c b).image ⊆ (γ b).image := by
    rintro b _ ⟨τ, hτ, rfl⟩
    exact ⟨φ b τ, (hφ b τ hτ).1, rfl⟩
  refine ⟨q, ⟨hqW, hqU⟩, L, hLΛ, c, ⟨N₁ ∩ ⋂ b, Metric.ball q (ε b),
    inter_mem hqN (iInter_mem.2 fun b => Metric.ball_mem_nhds q (hεpos b)), ?_⟩,
    fun b b' hbb' x hx => hdisj b b' hbb' ⟨himg b hx.1, himg b' hx.2⟩, fun b => ?_⟩
  · rintro x ⟨hxs, hxN, hxε⟩
    rw [zeroSet_sliceIdeal] at hxs
    obtain ⟨b, t, ht, rfl⟩ : ∃ b, ∃ t ∈ Metric.ball 0 (γ b).radius, (γ b).toFun t = x := by
      simpa [VarBranch.image] using hcov₁ ⟨hxs.1, hxN⟩
    obtain ⟨τ, hτ, rfl⟩ := hPφ b t (hεP b t ht (Set.mem_iInter.1 hxε b))
      (by rw [hxs.2, hsq b])
    exact Set.mem_iUnion.2 ⟨b, τ, hτ, rfl⟩
  · obtain ⟨H, hHd, hH0, hHe⟩ := hord b
    refine ⟨fun τ => H (φ b τ), hHd.comp (hφd b) (fun τ hτ => (hφ b τ hτ).1),
      fun τ hτ => hH0 _ (hφ b τ hτ).1, fun τ hτ => ?_⟩
    show linEval u ((γ b).toFun (φ b τ)) = τ 0 ^ ord b * H (φ b τ)
    have h := hHe _ (hφ b τ hτ).1
    rw [hφ0' b τ hτ] at h
    exact h

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormWindow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimitiveFormWindow.proof : PrimitiveFormWindow.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hp hsep hrel
  obtain ⟨N₀, k, f, hN₀o, hwN₀, hfa, hXN⟩ := hX
  obtain ⟨W₀, hW₀, hW₀iso⟩ := hiso
  have hev := (show ∀ᶠ z in 𝓝 w, z ∈ N₀ from hN₀o.mem_nhds hwN₀).and
    ((show ∀ᶠ z in 𝓝 w, z ∈ W₀ from hW₀).and (hp.and (Filter.eventually_all.2 hrel)))
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hev
  set K : Set (σ → ℂ) := Metric.sphere w ε ∩ (fun z i => f i z) ⁻¹' {0} with hK
  have hsN : Metric.sphere w ε ⊆ N₀ := fun z hz => (hεs (Metric.sphere_subset_closedBall hz)).1
  have hKc : IsCompact K := by
    refine (isCompact_sphere w ε).of_isClosed_subset ?_ Set.inter_subset_left
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_sphere isClosed_singleton
    exact continuousOn_pi.2 fun i => ((hfa i).continuousOn).mono hsN
  have hKX : ∀ z ∈ K, z ∈ X := by
    intro z hz
    have : z ∈ X ∩ N₀ := by
      rw [hXN]
      refine ⟨hsN hz.1, fun i => ?_⟩
      have := congrFun (Set.mem_singleton_iff.1 hz.2) i
      simpa using this
    exact this.1
  have hXK : ∀ z ∈ X, z ∈ Metric.sphere w ε → z ∈ K := by
    intro z hzX hzs
    refine ⟨hzs, ?_⟩
    have : z ∈ X ∩ N₀ := ⟨hzX, hsN hzs⟩
    rw [hXN] at this
    exact Set.mem_singleton_iff.2 (funext this.2)
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, hzK, hAz⟩
    have hzw := (hεs (Metric.sphere_subset_closedBall hzK.1)).2.1
    have hzeq := hW₀iso z ⟨hKX z hzK, hzw⟩ hAz
    have h1 := hzK.1
    rw [hzeq, Metric.mem_sphere, dist_self] at h1
    exact hε.ne h1
  have hclo : IsClosed (A '' K) := (hKc.image A.continuous).isClosed
  have hev2 := (show ∀ᶠ y in 𝓝 (A w), y ∈ (A '' K)ᶜ from hclo.isOpen_compl.mem_nhds hAK).and
    ((Filter.eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          (hq i j).eventually_analyticAt).and hsep)))
  obtain ⟨ρ, hρ, hρs⟩ := Metric.nhds_basis_ball.eventually_iff.1 hev2
  refine ⟨Metric.ball w ε, Metric.ball (A w) ρ, N₀, k, f, Metric.isOpen_ball, Metric.mem_ball_self hε,
    Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self hρ, hN₀o, ?_, hfa, hXN, ?_, ?_, ?_,
    fun j y hy => (hρs hy).2.1 j, fun y hy => (hρs hy).2.2.1, fun i j y hy => (hρs hy).2.2.2.1 i j,
    fun y hy => (hρs hy).2.2.2.2⟩
  · rw [closure_ball w hε.ne']
    exact fun z hz => (hεs hz).1
  · rintro z ⟨hzX, hzc⟩ hzB
    rw [closure_ball w hε.ne'] at hzc
    rcases (Metric.mem_closedBall.1 hzc).lt_or_eq with h | h
    · exact Metric.mem_ball.2 h
    · exact absurd ⟨z, hXK z hzX (Metric.mem_sphere.2 h), rfl⟩ (hρs hzB).1
  · rintro z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.1 hzX
  · rintro i z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.2 i hzX

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

open scoped ENNReal

noncomputable section

theorem ChartMassCompare.proof (h1 : SheetComass.Statement) (h2 : SheetAreaCompare.Statement) :
    ChartMassCompare.Statement := by
  intro n d J A φ R hJ hdim hA hφ
  obtain ⟨C, hC⟩ := h1 n d J A φ R hφ
  obtain ⟨c, hc, hca⟩ := h2 n d J A
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  refine ⟨ENNReal.ofReal C' * c, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc, fun g hg => ?_⟩
  set gB := B.indicator g with hgBdef
  have hgB : Measurable gB := hg.indicator measurableSet_closedBall

  have hpt : ∀ y, chartAbsDens J A gB φ y ≤
      C' * sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y := by
    intro y
    have hfin := (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
    unfold chartAbsDens sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have hxf : x ∈ ComplexSets.fibre J A y := hfin.mem_toFinset.mp hx
    split_ifs with hs
    · dsimp only
      rw [← hxf.2]
      by_cases hxB : x ∈ B
      · have hb := hC x ⟨hxf.1, hxB⟩ _ hs.choose_spec
        rw [abs_mul]
        calc |gB x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ hs.choose) (A *ᵥ x)|
            ≤ |gB x| * (C' * sheetJac hs.choose (A *ᵥ x)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (sheetJac_nonneg _ _))) (abs_nonneg _)
          _ = C' * (|gB x| * sheetJac hs.choose (A *ᵥ x)) := by ring
      · simp [gB, hxB]
    · simp
  have hnn : ∀ y, 0 ≤ chartAbsDens J A gB φ y := fun y =>
    finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs; exacts [abs_nonneg _, le_rfl]
  calc ∫⁻ y, ‖chartAbsDens J A gB φ y‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal C' * ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn y),
          ← ENNReal.ofReal_mul hC'0]
        exact ENNReal.ofReal_le_ofReal ((hpt y).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) hC'0))
    _ = ENNReal.ofReal C' * ∫⁻ y, ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C' * (c * ∫⁻ z in zeroSetEuc J, ‖gB (WithLp.ofLp z)‖ₑ
          ∂(μH[((2 * d : ℕ) : ℝ)])) := by gcongr; exact hca gB hgB
    _ = ENNReal.ofReal C' * c * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ B},
          ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        have hT : MeasurableSet {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B} :=
          measurableSet_closedBall.preimage (PiLp.continuous_ofLp 2 _).measurable
        have hfun : (fun z : EuclideanSpace ℂ (Fin n) => ‖gB (WithLp.ofLp z)‖ₑ) =
            {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B}.indicator
              (fun z => ‖g (WithLp.ofLp z)‖ₑ) := by
          ext z
          by_cases hz : WithLp.ofLp z ∈ B <;> simp [gB, hz, Set.indicator]
        rw [hfun, lintegral_indicator hT, Measure.restrict_restrict hT, Set.inter_comm, mul_assoc]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularInjectivePieces
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

noncomputable section

namespace RegularInjectivePieces

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem local_injective {d : ℕ} {U : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → Fin d → ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
    ∀ w ∈ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0},
      ∃ V : Set (Fin d → ℂ), IsOpen V ∧ w ∈ V ∧
        V ⊆ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧ Set.InjOn g V := by
  have hA : AnalyticOnNhd ℂ g U := analyticOnNhd_of_differentiableOn hU hg
  have hRopen : IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} := by
    have hc : ContinuousOn (fun w => (fderiv ℂ g w).det) U :=
      ContinuousLinearMap.continuous_det.comp_continuousOn hA.fderiv.continuousOn
    exact hc.isOpen_inter_preimage hU isOpen_compl_singleton
  refine ⟨hRopen, fun w hw => ?_⟩
  have hs : HasStrictFDerivAt g
      (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hw.2 : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) :
        (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hA w hw.1).hasStrictFDerivAt
  refine ⟨(hs.toOpenPartialHomeomorph g).source ∩ _, (hs.toOpenPartialHomeomorph g).open_source.inter hRopen,
    ⟨hs.mem_toOpenPartialHomeomorph_source, hw⟩, Set.inter_subset_right, ?_⟩
  have hinj := (hs.toOpenPartialHomeomorph g).injOn
  rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at hinj
  exact hinj.mono Set.inter_subset_left

end RegularInjectivePieces


open RegularInjectivePieces in
theorem RegularInjectivePieces.proof : RegularInjectivePieces.Statement := by
  intro d U g hU hg
  obtain ⟨hRopen, key⟩ := local_injective hU hg
  set R := {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  choose! V hVo hVm hVR hVi using key
  obtain ⟨T, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun w : R => V w) (fun w => hVo w w.2)
  have hUnion : ⋃ w : R, V w = R := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨w, hx⟩ => hVR w w.2 hx, fun hx => ⟨⟨x, hx⟩, hVm x hx⟩⟩
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun i j _ => disjoint_bot_left, ?_,
      fun _ => Set.injOn_empty _⟩
    rw [← hUnion, ← hTU, hT0]
    simp
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    refine ⟨disjointed (fun n => V (f n)),
      MeasurableSet.disjointed (fun n => (hVo _ (f n).2).measurableSet), disjoint_disjointed _, ?_,
      fun n => (hVi _ (f n).2).mono (disjointed_subset _ n)⟩
    rw [iUnion_disjointed]
    calc ⋃ n, V (f n) = ⋃ i ∈ Set.range f, V i :=
        (Set.biUnion_range (f := f) (g := fun i : R => V (i : Fin d → ℂ))).symm
      _ = ⋃ i ∈ T, V i := by rw [hf]
      _ = R := hTU.trans hUnion

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalDivisorChartGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace NormalDivisorChartGeneric

theorem ringKrullDim_le_of_injective_isIntegral {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hinj : Function.Injective f) (hint : f.IsIntegral) : ringKrullDim R ≤ ringKrullDim S := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.IsIntegral R S := ⟨hint⟩
  refine iSup_le fun l => ?_
  have hker : (⊥ : Ideal S).comap (algebraMap R S) ≤ (RelSeries.head l).asIdeal := by
    intro r hr
    have : f r = 0 := hr
    rw [show r = 0 from hinj (by rw [this, map_zero])]
    exact Ideal.zero_mem _
  obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ hker
  have : P.LiesOver (RelSeries.head l).asIdeal := ⟨hPo.symm⟩
  obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  exact le_iSup_of_le L (by rw [hlen])

theorem isIntegral_mk_comp_rename {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J) {B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ)} (hB : M.ideal ≤ B) :
    ((Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom).IsIntegral := by
  set f := (Ideal.Quotient.mk B).comp (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom with hf
  let : Algebra (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) := f.toAlgebra
  have hX : ∀ s, IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B (X s)) := by
    rintro (i | i)
    · have h : Ideal.Quotient.mk B (X (Sum.inl i)) =
          algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (X i) := by
        show _ = f (X i)
        simp [hf]
      rw [h]
      exact isIntegral_algebraMap
    · obtain ⟨P, hPm, hP⟩ := M.integral i
      refine ⟨P, hPm, ?_⟩
      have h := Ideal.Quotient.eq_zero_iff_mem.mpr (hB hP)
      rw [Polynomial.hom_eval₂] at h
      exact h
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  show IsIntegral (MvPolynomial (Fin n) ℂ) (Ideal.Quotient.mk B p)
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : Ideal.Quotient.mk B (C a) =
        algebraMap (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) (C a) := by
      show _ = f (C a)
      simp [hf]
    rw [h]
    exact isIntegral_algebraMap
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hp.add hq
  | mul_X p s hp =>
    rw [map_mul]
    exact hp.mul (hX s)

theorem proof (hUp : NormalModelDivisorChartGeneric.Statement) : NormalDivisorChartGeneric.Statement := by
  intro n d J u M hJ hdim hu
  obtain ⟨B, hleB, hdimB, hB⟩ := hUp n d J u M hJ hdim hu
  refine ⟨B.comap (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m)).toRingHom, ?_, ?_, ?_⟩
  · refine sup_le ?_ ((Ideal.span_le).2 (Set.singleton_subset_iff.2 ?_))
    · exact M.comap_eq.symm.le.trans (Ideal.comap_mono (le_sup_left.trans hleB))
    · exact hleB (Ideal.mem_sup_right (Ideal.subset_span rfl))
  · refine lt_of_le_of_lt ?_ hdimB
    exact ringKrullDim_le_of_injective_isIntegral _ Ideal.quotientMap_injective
      ((isIntegral_quotientMap_iff _).2 (isIntegral_mk_comp_rename M (le_sup_left.trans hleB)))
  · intro q _ hqu hqI w hw hwq
    refine hB w hw (hwq ▸ hqu) fun hwB => hqI fun f hf => ?_
    have h := hwB _ hf
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, eval_rename] at h
    rw [← hwq]
    exact h

end NormalDivisorChartGeneric

end

end GroundTheory.Heights₂.Heights
end
