module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaOpenCone
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.ConeBallLogGapIntegral
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.GaussianSphereMeanIntegral
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibrefactor

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.CroftonFormulaFibreSum
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace ModelDimension.FnCrofton

theorem measurable_matrix_gaussian (m n : ℕ) :
    Measurable (matGauss : (Fin m → Fin n → ℂ) → ℝ≥0∞) := by
  unfold matGauss
  fun_prop

theorem measurable_cntOver_first {n e : ℕ} {S : Set (EuclideanSpace ℂ (Fin n))} (hS : IsSigmaCompact S) :
    Measurable fun π : Fin (e + 1) → Fin n → ℂ => cntOver S π (firstCoordVec (e + 1)) := by
  have H := GlobalTheory.T.measurable_fibre_count_over n (e + 1) S hS
  have H2 := H.comp (measurable_id.prodMk (measurable_const (a := firstCoordVec (e + 1))))
  exact H2

theorem encard_fibrePts_inter {n e : ℕ} (S A : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) :
    (((fibrePts S π ∩ A).encard : ℕ∞) : ℝ≥0∞) = cntOver (S ∩ A) π (firstCoordVec (e + 1)) := by
  unfold cntOver
  congr 2
  ext y
  simp only [fibrePts, ptsOver, Set.mem_inter_iff, Set.mem_setOf_eq]
  tauto

end ModelDimension.FnCrofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMinusConeIntegralIndep
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralFubiniStudySumCone
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSum
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSum
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  intro n e δ h W f hW hf hδ φ hφ hlev
  have hcnt : ∀ s : ℝ≥0∞, Measurable fun π : Fin (e + 1) → Fin n → ℂ =>
      cntOver (coneSet h W ∩ {y | s < φ y}) π (firstCoordVec (e + 1)) := fun s =>
    ModelDimension.FnCrofton.measurable_cntOver_first (isSigmaCompact_cone_inter h W (hlev s).1)
  obtain ⟨hm, hi⟩ := GlobalTheory.T.random_set_sum_expectation (planeMass n e • gaussM (e + 1) n)
    ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W))
    (fun π => fibrePts (coneSet h W) π) φ (gaussM (e + 1) n Set.univ) hφ
    (fun s => by
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      exact hcnt s)
    (fun s => by
      have hA := (hlev s).1
      have T := GlobalTheory.T.crofton_formula_open_cone n e δ h W f hW hf hδ {y | s < φ y} hA (hlev s).2
      simp only [ModelDimension.FnCrofton.encard_fibrePts_inter]
      rw [lintegral_smul_measure, smul_eq_mul, Measure.restrict_apply hA.measurableSet, gaussM,
        lintegral_withDensity_eq_lintegral_mul _ (ModelDimension.FnCrofton.measurable_matrix_gaussian _ _) (hcnt s)]
      have hset : {y | s < φ y} ∩ coneBall h W =
          {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ {y | s < φ y}} := by
        ext y
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, h3, h1⟩
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h3, h1, h2⟩
      rw [hset]
      simpa only [Pi.mul_apply, gaussM] using T)
  refine ⟨hm, ?_⟩
  rw [lintegral_smul_measure, smul_eq_mul] at hi
  exact hi
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaFibreSumStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crofton_formula_fibre_sum : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ φ : EuclideanSpace ℂ (Fin n) → ℝ≥0∞, Measurable φ →
    (∀ s : ℝ≥0∞, IsOpen {y | s < φ y} ∧ IsScaleStable {y | s < φ y}) →
    Measurable (fun π : Fin (e + 1) → Fin n → ℂ => ∑' y : fibrePts (coneSet h W) π, φ y) ∧
      planeMass n e * ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, φ y ∂(gaussM (e + 1) n) =
        gaussM (e + 1) n Set.univ * ∫⁻ y in coneBall h W, φ y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum | exact GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum | (intros; apply GlobalTheory.CompanionTheory.Relay.crofton_formula_fibre_sum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConeBallLogGapIntegral
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConeBallLogGapIntegral
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.cone_ball_log_gap_integral : ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
    ∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) < ⊤ ∧
      (∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))).toReal =
        Real.log (h.norm u) * ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) (coneBall h W)).toReal -
          ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  first | exact @ModelDimension.integral_coneBall_log_gap_eq | exact ModelDimension.integral_coneBall_log_gap_eq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ConeBallLogGapIntegralStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_ball_log_gap_integral : ∀ (n e : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → linForm u ∉ W →
    ∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) < ⊤ ∧
      (∫⁻ y in coneBall h W, logGap h u y ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))).toReal =
        Real.log (h.norm u) * ((Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) (coneBall h W)).toReal -
          ∫ y in coneBall h W, fsLog h u (h.pointOf y) ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.cone_ball_log_gap_integral | exact GlobalTheory.CompanionTheory.Relay.cone_ball_log_gap_integral | (intros; apply GlobalTheory.CompanionTheory.Relay.cone_ball_log_gap_integral <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FubiniStudyLogLeLogNorm
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FubiniStudyLogLeLogNorm
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem fsLog_pointOf_le_log_norm : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)), y ≠ 0 →
  ∑ j, u j * h.pointOf y j ≠ 0 → fsLog h u (h.pointOf y) ≤ Real.log (h.norm u) :=
  fun _ h _ _ _ hne => fsLog_le h hne

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FubiniStudyLogLeLogNormStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fubini_study_log_le_log_norm : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)), y ≠ 0 →
  ∑ j, u j * h.pointOf y j ≠ 0 → fsLog h u (h.pointOf y) ≤ Real.log (h.norm u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsLog_pointOf_le_log_norm | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsLog_pointOf_le_log_norm | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsLog_pointOf_le_log_norm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LogGapMeasurableScaleStable
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LogGapMeasurableScaleStable
set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

noncomputable section

variable {n : ℕ}

theorem continuous_pairing_pointOf (h : HermNorm n) (u : Fin n → ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => ∑ j, u j * h.pointOf y j := by
  have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
    unfold HermNorm.pointOf; fun_prop
  exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)

theorem pairing_pointOf_smul (h : HermNorm n) (u : Fin n → ℂ) (t : ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf (t • y) j = t * ∑ j, u j * h.pointOf y j := by
  have hpt : h.pointOf (t • y) = t • h.pointOf y := by
    simp only [HermNorm.pointOf]
    rw [← Matrix.mulVec_smul]
    congr 1
  rw [hpt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem dualNorm_pointOf_eq (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by
  have hA : IsUnit h.matᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  rw [HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec, EuclideanSpace.norm_eq]

theorem hermNorm_pos (h : HermNorm n) {u : Fin n → ℂ} (hu : u ≠ 0) : 0 < h.norm u := by
  have hne : h.mat *ᵥ u ≠ 0 := by
    intro h0
    apply hu
    have h1 := congrArg (fun v => h.mat⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det] using h1
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rw [HermNorm.norm]
  refine Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => by positivity)
    ⟨i, Finset.mem_univ _, ?_⟩)
  have : 0 < ‖(h.mat *ᵥ u) i‖ := norm_pos_iff.mpr hi
  positivity

theorem lt_logGap_iff (h : HermNorm n) {u : Fin n → ℂ} (hu : u ≠ 0) {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (y : EuclideanSpace ℂ (Fin n)) :
    s < logGap h u y ↔
      ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖ := by
  have hN := hermNorm_pos h hu
  unfold logGap
  by_cases hy : y = 0
  · subst hy
    simp [HermNorm.pointOf]
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hc : 0 < Real.exp (-s.toReal) * h.norm u * ‖y‖ := by positivity
  by_cases hp : ∑ j, u j * h.pointOf y j = 0
  · simp [hy, hp, hs.lt_top, hc]
  · have hpn : 0 < ‖∑ j, u j * h.pointOf y j‖ := norm_pos_iff.mpr hp
    rw [if_neg hy, if_neg hp, ENNReal.lt_ofReal_iff_toReal_lt hs, fsLog, dualNorm_pointOf_eq,
      Real.log_div hpn.ne' hy'.ne', ← Real.log_lt_log_iff hpn hc,
      Real.log_mul (by positivity) hy'.ne', Real.log_mul (Real.exp_pos _).ne' hN.ne', Real.log_exp]
    constructor <;> intro hh <;> linarith

theorem lt_logGap_zero_iff (h : HermNorm n) {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (y : EuclideanSpace ℂ (Fin n)) : s < logGap h 0 y ↔ y ≠ 0 := by
  unfold logGap
  by_cases hy : y = 0
  · simp [hy]
  · simp [hy, hs.lt_top]

theorem logGap_levelSet_top (h : HermNorm n) (u : Fin n → ℂ) :
    {y | (⊤ : ℝ≥0∞) < logGap h u y} = ∅ := by
  ext y
  simp

theorem logGap_levelSet (h : HermNorm n) (u : Fin n → ℂ) (s : ℝ≥0∞) :
    IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  by_cases hs : s = ⊤
  · subst hs
    rw [logGap_levelSet_top]
    exact ⟨isOpen_empty, fun y hy => hy.elim⟩
  by_cases hu : u = 0
  · subst hu
    have hset : {y | s < logGap h 0 y} = {y : EuclideanSpace ℂ (Fin n) | y ≠ 0} :=
      Set.ext fun y => lt_logGap_zero_iff h hs y
    rw [hset]
    exact ⟨isOpen_ne, fun y hy t ht => smul_ne_zero ht hy⟩
  have hset : {y | s < logGap h u y} = {y : EuclideanSpace ℂ (Fin n) |
      ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖} :=
    Set.ext fun y => lt_logGap_iff h hu hs y
  rw [hset]
  refine ⟨isOpen_lt (continuous_pairing_pointOf h u).norm (continuous_const.mul continuous_norm),
    fun y hy t ht => ?_⟩
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hy' : ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖ := hy
  show ‖∑ j, u j * h.pointOf (t • y) j‖ < Real.exp (-s.toReal) * h.norm u * ‖t • y‖
  rw [pairing_pointOf_smul, norm_mul, norm_smul]
  calc ‖t‖ * ‖∑ j, u j * h.pointOf y j‖
      < ‖t‖ * (Real.exp (-s.toReal) * h.norm u * ‖y‖) := mul_lt_mul_of_pos_left hy' ht'
    _ = Real.exp (-s.toReal) * h.norm u * (‖t‖ * ‖y‖) := by ring

theorem logGap_basic : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ),
    Measurable (logGap h u) ∧
      ∀ s : ℝ≥0∞, IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  intro n h u
  exact ⟨measurable_of_Ioi fun s => (logGap_levelSet h u s).1.measurableSet,
    logGap_levelSet h u⟩

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LogGapMeasurableScaleStableStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_gap_measurable_scale_stable : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ),
  Measurable (logGap h u) ∧ ∀ s : ℝ≥0∞, IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.logGap_basic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralFubiniStudySumCone
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem fubini_study_sum_crofton {n e δ : ℕ} (h : HermNorm n) (u : Fin n → ℂ)
    (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (hc : (fibrePts S π).encard = δ)
    (hs : ∑' y : fibrePts S π, logGap h u y < ⊤) :
    (∑' y : fibrePts S π, logGap h u y).toReal = δ * Real.log (h.norm u) - fsSum h u S π := by
  have hfin : (fibrePts S π).Finite := Set.finite_of_encard_eq_coe hc
  have hcard : hfin.toFinset.card = δ := by
    have h1 := hfin.encard_eq_coe_toFinset_card
    rw [hc] at h1
    exact_mod_cast h1.symm
  have hne0 : ∀ y ∈ fibrePts S π, y ≠ 0 := by
    rintro y ⟨-, hy⟩ rfl
    have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) hy
    simp [linProj, firstCoordVec] at h2
  have hsum : ∀ y ∈ fibrePts S π, ∑ j, u j * h.pointOf y j ≠ 0 := by
    intro y hy h0
    have htop : logGap h u y = ⊤ := by simp [logGap, hne0 y hy, h0]
    have hle : logGap h u y ≤ ∑' z : fibrePts S π, logGap h u z :=
      ENNReal.le_tsum (f := fun z : fibrePts S π => logGap h u z) ⟨y, hy⟩
    rw [htop] at hle
    exact absurd hs (not_lt.2 hle)
  have hval : ∀ y ∈ fibrePts S π,
      logGap h u y = ENNReal.ofReal (Real.log (h.norm u) - fsLog h u (h.pointOf y)) := by
    intro y hy
    simp [logGap, hne0 y hy, hsum y hy]
  have hnn : ∀ y ∈ fibrePts S π, 0 ≤ Real.log (h.norm u) - fsLog h u (h.pointOf y) := fun y hy =>
    sub_nonneg.2 (GlobalTheory.T.fubini_study_log_le_log_norm n h u y (hne0 y hy) (hsum y hy))
  haveI : Fintype (fibrePts S π) := hfin.fintype
  have htsum : ∑' z : fibrePts S π, logGap h u z = ∑ y ∈ hfin.toFinset, logGap h u y := by
    rw [tsum_fintype]
    exact (Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) (logGap h u)).symm
  rw [htsum, ENNReal.toReal_sum (fun y hy => by
      rw [hval y (hfin.mem_toFinset.1 hy)]
      exact ENNReal.ofReal_ne_top)]
  rw [Finset.sum_congr rfl (fun y hy => by
      rw [hval y (hfin.mem_toFinset.1 hy), ENNReal.toReal_ofReal (hnn y (hfin.mem_toFinset.1 hy))])]
  rw [Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, fsSum,
    finsum_mem_eq_finite_toFinset_sum _ hfin]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton

private theorem tsum_fibre_pts_eq_sum {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (hfin : (fibrePts S π).Finite) (g : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    ∑' y : fibrePts S π, g y = ∑ y ∈ hfin.toFinset, g y := by
  haveI : Fintype (fibrePts S π) := hfin.fintype
  rw [tsum_fintype]
  exact (Finset.sum_subtype hfin.toFinset (fun y => hfin.mem_toFinset) g).symm

private theorem ne_zero_of_mem_fibre_pts {n e : ℕ} (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ fibrePts S π) : y ≠ 0 := by
  rintro rfl
  obtain ⟨-, h0⟩ := hy
  have h2 := congrArg (fun v : EuclideanSpace ℂ (Fin (e + 1)) => v.ofLp 0) h0
  simp [linProj, firstCoordVec] at h2

theorem GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → GroundTheory.Heights₂.Heights.linForm u ∉ W →
    Integrable (fsSum h u (coneSet h W)) (gaussM (e + 1) n) ∧
      ∫ π, fsSum h u (coneSet h W) π ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * coneIntegral h W e (fsLog h u) := by
  intro n e δ h W f u hW hf hδ hu
  obtain ⟨hLGm, hLGo⟩ := GlobalTheory.T.log_gap_measurable_scale_stable n h u
  obtain ⟨hGm, hGeq⟩ := GlobalTheory.T.crofton_formula_fibre_sum n e δ h W f hW hf hδ (logGap h u) hLGm hLGo
  obtain ⟨hL, hLr⟩ := GlobalTheory.T.cone_ball_log_gap_integral n e h W f u hW hf hu
  obtain ⟨hμ0, hμt⟩ := GlobalTheory.T.gaussian_matrix_measure_pos_finite (e + 1) n
  obtain ⟨hpm0, hpmt⟩ : 0 < planeMass n e ∧ planeMass n e < ⊤ :=
    GroundTheory.Heights₂.Heights.coordBall_mass (chowGroups_le hW hf hδ)
  have hac : gaussM (e + 1) n ≪ (volume : Measure (Fin (e + 1) → Fin n → ℂ)) :=
    withDensity_absolutelyContinuous _ _
  have hcnt : ∀ᵐ π ∂(gaussM (e + 1) n), (fibrePts (coneSet h W) π).encard = δ :=
    hac.ae_le (GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ)
  have hd : (0 : ℝ) < ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  haveI := MeasureTheory.Measure.nullSingletonClass_hausdorff (EuclideanSpace ℂ (Fin n)) hd
  have hφm : Measurable (({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_singleton 0).compl
  have hφo : ∀ s : ℝ≥0∞,
      IsOpen {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} ∧
      IsScaleStable {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} := by
    intro s
    by_cases hs1 : s < 1
    · have hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} =
          {0}ᶜ := by
        ext y
        by_cases hy : y = 0
        · simp [Set.indicator_apply, hy]
        · simp [Set.indicator_apply, hy, hs1]
      rw [hset]
      exact ⟨isOpen_compl_singleton, fun y hy t ht => by simpa [ht] using hy⟩
    · have hset : {y | s < ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y} =
          ∅ := by
        ext y
        by_cases hy : y = 0
        · simp [Set.indicator_apply, hy]
        · simp [Set.indicator_apply, hy, hs1]
      rw [hset]
      exact ⟨isOpen_empty, fun y hy => hy.elim⟩
  obtain ⟨-, hCeq⟩ := GlobalTheory.T.crofton_formula_fibre_sum n e δ h W f hW hf hδ _ hφm hφo
  have hae1 : ∀ᵐ π ∂(gaussM (e + 1) n), ∑' y : fibrePts (coneSet h W) π,
      ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = δ := by
    filter_upwards [hcnt] with π hπ
    have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hπ
    have hcard : hfin.toFinset.card = δ := by
      have h1 := hfin.encard_eq_coe_toFinset_card
      rw [hπ] at h1
      exact_mod_cast h1.symm
    have h1 : ∀ y ∈ hfin.toFinset,
        ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y = 1 := fun y hy =>
      Set.indicator_of_mem (ne_zero_of_mem_fibre_pts _ π y (hfin.mem_toFinset.1 hy)) _
    rw [tsum_fibre_pts_eq_sum _ π hfin, Finset.sum_congr rfl h1, Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  have hball : ∫⁻ y in coneBall h W, ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))).indicator (fun _ => (1 : ℝ≥0∞)) y
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) := by
    rw [lintegral_indicator_const (measurableSet_singleton 0).compl, one_mul,
      Measure.restrict_apply (measurableSet_singleton 0).compl, Set.inter_comm, ← Set.sdiff_eq,
      measure_sdiff_null (measure_singleton 0)]
  rw [lintegral_congr_ae hae1, lintegral_const, hball] at hCeq
  have hHc : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) = δ * planeMass n e := by
    have h2 : gaussM (e + 1) n Set.univ * (δ * planeMass n e) =
        gaussM (e + 1) n Set.univ * Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) := by
      rw [← hCeq]
      ring
    exact ((ENNReal.mul_right_inj hμ0.ne' hμt.ne).1 h2).symm
  have hGfin : ∫⁻ π, ∑' y : fibrePts (coneSet h W) π, logGap h u y ∂(gaussM (e + 1) n) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hpm0.ne'] at hGeq
    exact ENNReal.mul_ne_top hμt.ne hL.ne hGeq.symm
  have hGae := ae_lt_top hGm hGfin
  have hfs : ∀ᵐ π ∂(gaussM (e + 1) n), fsSum h u (coneSet h W) π =
      δ * Real.log (h.norm u) - (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal := by
    filter_upwards [hcnt, hGae] with π h1 h2
    rw [fubini_study_sum_crofton h u _ π h1 h2]
    ring
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hμt⟩
  have hGint := integrable_toReal_of_lintegral_ne_top hGm.aemeasurable hGfin
  have hint : Integrable (fun π => (δ : ℝ) * Real.log (h.norm u) -
      (∑' y : fibrePts (coneSet h W) π, logGap h u y).toReal) (gaussM (e + 1) n) :=
    (integrable_const _).sub hGint
  refine ⟨hint.congr (hfs.mono fun π hπ => hπ.symm), ?_⟩
  rw [integral_congr_ae hfs, integral_sub (integrable_const _) hGint, integral_const,
    integral_toReal hGm.aemeasurable hGae, measureReal_def, smul_eq_mul]
  have hX := congrArg ENNReal.toReal hGeq
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hLr, hHc, ENNReal.toReal_mul, ENNReal.toReal_natCast] at hX
  have hpmr : 0 < (planeMass n e).toReal := ENNReal.toReal_pos hpm0.ne' hpmt.ne
  have hci : coneIntegral h W e (fsLog h u) = (∫ y in coneBall h W, fsLog h u (h.pointOf y)
      ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))) / (planeMass n e).toReal := rfl
  rw [hci]
  have alg : ∀ a p X lg d I : ℝ, p ≠ 0 → p * X = a * (lg * (d * p) - I) →
      a * (d * lg) - X = a * (I / p) := by
    intro a p X lg d I hp hX'
    have hX'' : X = a * (lg * (d * p) - I) / p := by
      rw [eq_div_iff hp, mul_comm]
      exact hX'
    rw [hX'']
    field_simp
    ring
  exact alg _ _ _ _ _ _ hpmr.ne' hX
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IntegralFubiniStudySumConeStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fubini_study_sum_cone : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f → linForm u ∉ W →
    Integrable (fsSum h u (coneSet h W)) (gaussM (e + 1) n) ∧
      ∫ π, fsSum h u (coneSet h W) π ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * coneIntegral h W e (fsLog h u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.fsSum_crofton <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChowFormFibreSpecialization
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChowFormFibreSpecialization
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.chow_form_fibre_specialization : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (π : Fin (e + 1) → Fin n → ℂ) (u₀ : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (fibrePts (coneSet h W) π).encard = δ →
  eval (consGroup u₀ (nrmGroups h e (coefRows h π))) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u (nrmGroups h e (coefRows h π))) g =
      c * ∏ᶠ y ∈ fibrePts (coneSet h W) π, ∑ j, u j * h.pointOf y j := by
  first | exact @PositivityTheory.Xgn.t_xgz_chow_mahler_fibrefactor | exact PositivityTheory.Xgn.t_xgz_chow_mahler_fibrefactor
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChowFormFibreSpecializationStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chow_form_fibre_specialization : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (π : Fin (e + 1) → Fin n → ℂ) (u₀ : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g →
  (fibrePts (coneSet h W) π).encard = δ →
  eval (consGroup u₀ (nrmGroups h e (coefRows h π))) g ≠ 0 →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ u : Fin n → ℂ, eval (consGroup u (nrmGroups h e (coefRows h π))) g =
      c * ∏ᶠ y ∈ fibrePts (coneSet h W) π, ∑ j, u j * h.pointOf y j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.chow_form_fibre_specialization | exact GlobalTheory.CompanionTheory.Relay.chow_form_fibre_specialization | (intros; apply GlobalTheory.CompanionTheory.Relay.chow_form_fibre_specialization <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanNormalizedGroups
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanNormalizedGroups
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups : ∀ (n e : ℕ) (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ),
  IntegrableOn (fun u => G (nrmGroups h e u)) (ballProd h e) →
    Integrable (fun π : Fin (e + 1) → Fin n → ℂ => G (nrmGroups h e (coefRows h π))) (gaussM (e + 1) n) ∧
      ∫ π, G (nrmGroups h e (coefRows h π)) ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * sphereMean h e G := by
  intro n e h G hint
  have hfin := (gaussM_univ_pos_lt_top (e + 1) n).2
  haveI : IsFiniteMeasure (gaussM (e + 1) n) := ⟨hfin⟩
  haveI : IsFiniteMeasure (volume.restrict (ballProd h e)) := ⟨by rw [Measure.restrict_apply_univ]; exact volume_ballProd_lt_top h e⟩
  obtain ⟨a, ha⟩ := ModelDimension.GSph.map_coefRows (e := e) h
  have hmap : Measure.map (coefRows h) (gaussM (e + 1) n) = Measure.map ModelDimension.GSph.scT ((a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)).prod (volume.restrict (ballProd h e))) := by
    rw [ha, ModelDimension.GSph.layer, Measure.prod_smul_left, Measure.map_smul]
    exact ModelDimension.GSph.measurable_scT.aemeasurable
  have h1 : ∀ᵐ x ∂ModelDimension.GSph.ex1, 0 < x :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hp : ∀ᵐ s ∂(ModelDimension.GSph.exP e), ∀ i, 0 < s i := by
    rw [ae_all_iff]
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin e => ModelDimension.GSph.ex1) (i := i)).eventually h1
  have hpos0 : ∀ᵐ s ∂((ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ i, 0 < s i :=
    (withDensity_absolutelyContinuous _ _).ae_le hp
  have hpos : ∀ᵐ s ∂(a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ i, 0 < s i :=
    Measure.ae_smul_measure hpos0 a
  have hne : (volume.restrict (ballProd h e)) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact (volume_ballProd_pos h e).ne'
  have haesm : AEStronglyMeasurable (fun u => G (nrmGroups h e u)) (Measure.map (coefRows h) (gaussM (e + 1) n)) := by
    rw [ha]
    exact ((ModelDimension.GSph.aesm h G hint.1).mono_ac (withDensity_absolutelyContinuous _ _)).smul_measure a
  have hinv : ∀ᵐ s ∂(a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)), ∀ u, (fun u => G (nrmGroups h e u)) (ModelDimension.GSph.scT (s, u)) = (fun u => G (nrmGroups h e u)) u := by
    filter_upwards [hpos] with s hs u
    exact congrArg G (ModelDimension.GSph.nrm_sc h (fun i => Real.sqrt_pos.mpr (hs i)) u)
  have key := ModelDimension.GSph.transfer (gaussM (e + 1) n) (a • (ModelDimension.GSph.exP e).withDensity (ModelDimension.GSph.wt h)) (volume.restrict (ballProd h e)) hne (ModelDimension.GSph.measurable_coefRows h) ModelDimension.GSph.measurable_scT hmap haesm hinv hint
  refine ⟨key.1, ?_⟩
  rw [key.2]
  rfl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SphereMeanNormalizedGroupsStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphere_mean_normalized_groups : ∀ (n e : ℕ) (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ),
  IntegrableOn (fun u => G (nrmGroups h e u)) (ballProd h e) →
    Integrable (fun π : Fin (e + 1) → Fin n → ℂ => G (nrmGroups h e (coefRows h π))) (gaussM (e + 1) n) ∧
      ∫ π, G (nrmGroups h e (coefRows h π)) ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * sphereMean h e G := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups | exact GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups | (intros; apply GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AePolynomialNonvanishingRows
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AePolynomialNonvanishingRows
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem eq_zero_of_hermNorm_eq_zero {n : ℕ} (h : HermNorm n) {u : Fin n → ℂ} (hu : h.norm u = 0) :
    u = 0 := by
  have hs : ∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2 = 0 :=
    (Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => by positivity)).mp hu
  have hz : h.mat *ᵥ u = 0 := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).mp hs i (Finset.mem_univ i)
    simpa using hi
  have := congrArg (fun w => h.mat⁻¹ *ᵥ w) hz
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det] using this

theorem eval_scale_groups {k n δ : ℕ} {q : MvPolynomial (Fin k × Fin n) ℂ} (hq : IsMultiHomog δ q)
    (c : Fin k → ℂ) (v : Fin k × Fin n → ℂ) :
    eval (fun ij => c ij.1 * v ij) q = (∏ i, c i ^ δ) * eval v q := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw := hq (mem_support_iff.mp hd)
  have hrow : ∀ i, ∑ j, d (i, j) = δ := by
    intro i
    have := congrFun hw i
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    simp [groupWeight, Fintype.sum_prod_type, Pi.single_apply, Finset.sum_apply] at this
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb]) (by simp)] at this
    simpa using this
  have hc : ∏ ij : Fin k × Fin n, c ij.1 ^ d ij = ∏ i, c i ^ δ := by
    rw [Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hrow]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem eval_nrmGroups_ne_zero {k n δ : ℕ} (h : HermNorm n) {q : MvPolynomial (Fin k × Fin n) ℂ}
    (hq : IsMultiHomog δ q) {v : Fin k × Fin n → ℂ} (hv : eval v q ≠ 0) :
    eval (nrmGroups h k v) q ≠ 0 := by
  classical
  have e : nrmGroups h k v =
      fun ij => (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) ij.1 * v ij := rfl
  rw [e, eval_scale_groups hq (fun i => ((h.norm fun j => v (i, j) : ℝ) : ℂ)⁻¹) v]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) hv
  rcases Nat.eq_zero_or_pos δ with rfl | hpos
  · simp
  refine pow_ne_zero _ fun hc => hv ?_
  have hn : h.norm (fun j => v (i, j)) = 0 := by simpa using hc
  have hr := eq_zero_of_hermNorm_eq_zero h hn
  have hv' : v = fun ij => (Function.update (1 : Fin k → ℂ) i 0) ij.1 * v ij := by
    funext ⟨a, j⟩
    by_cases ha : a = i
    · subst ha
      simpa using congrFun hr j
    · simp [Function.update_of_ne ha]
  rw [hv', eval_scale_groups hq, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hpos.ne']), zero_mul]

theorem exists_poly_eval_coefRows {n e : ℕ} (h : HermNorm n) {q : MvPolynomial (Fin e × Fin n) ℂ}
    (hq : q ≠ 0) :
    ∃ Q : MvPolynomial (Fin (e + 1) × Fin n) ℂ, Q ≠ 0 ∧
      ∀ π : Fin (e + 1) → Fin n → ℂ, eval (fun ij => π ij.1 ij.2) Q = eval (coefRows h π) q := by
  let f : Fin e × Fin n → MvPolynomial (Fin (e + 1) × Fin n) ℂ :=
    fun ij => ∑ k, C (h.mat⁻¹ ij.2 k) * X (ij.1.succ, k)
  have key : ∀ π : Fin (e + 1) → Fin n → ℂ,
      eval (fun ij => π ij.1 ij.2) (bind₁ f q) = eval (coefRows h π) q := by
    intro π
    have hf : (fun ij => eval (fun ij => π ij.1 ij.2) (f ij)) = coefRows h π := by
      funext ij
      simp [f, coefRows, Matrix.mulVec, dotProduct]
    rw [← hf]
    exact eval₂Hom_bind₁ _ _ _ _
  refine ⟨bind₁ f q, fun hQ => hq (MvPolynomial.funext fun v => ?_), key⟩
  have hv : coefRows h (Fin.cons 0 fun i => h.mat *ᵥ fun j => v (i, j)) = v := by
    funext ij
    simp [coefRows, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det]
  rw [map_zero, ← hv, ← key, hQ, map_zero]

theorem ae_eval_nrmGroups_coefRows_ne_zero :
    ∀ (n e δ : ℕ) (h : HermNorm n) (q : MvPolynomial (Fin e × Fin n) ℂ), q ≠ 0 → IsMultiHomog δ q →
      ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, eval (nrmGroups h e (coefRows h π)) q ≠ 0 := by
  intro n e δ h q hq hδ
  obtain ⟨Q, hQ, key⟩ := exists_poly_eval_coefRows h hq
  filter_upwards [ConeFibreDegree.ae_eval_matrix_ne_zero Q hQ] with π hπ
  rw [key] at hπ
  exact eval_nrmGroups_ne_zero h hδ hπ

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AePolynomialNonvanishingRowsStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_polynomial_nonvanishing_rows : ∀ (n e δ : ℕ) (h : HermNorm n) (q : MvPolynomial (Fin e × Fin n) ℂ), q ≠ 0 → IsMultiHomog δ q →
  ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, eval (nrmGroups h e (coefRows h π)) q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.ae_eval_nrmGroups_coefRows_ne_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMinusConeIntegralIndep
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem log_norm_sub_fsSum_eq {n e : ℕ} (h : HermNorm n) (u : Fin n → ℂ)
    (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin (e + 1) → Fin n → ℂ) (c z : ℂ)
    (hfin : (fibrePts S π).Finite) (hc : c ≠ 0)
    (hz : z = c * ∏ᶠ y ∈ fibrePts S π, ∑ j, u j * h.pointOf y j) (hz0 : z ≠ 0) :
    Real.log ‖z‖ - fsSum h u S π = Real.log ‖c‖ + ∑ y ∈ hfin.toFinset, Real.log ‖y‖ := by
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at hz
  have hprod : ∏ y ∈ hfin.toFinset, ∑ j, u j * h.pointOf y j ≠ 0 :=
    fun h0 => hz0 (by rw [hz, h0, mul_zero])
  have hne := Finset.prod_ne_zero_iff.mp hprod
  have key : ∀ y ∈ hfin.toFinset, fsLog h u (h.pointOf y) =
      Real.log ‖∑ j, u j * h.pointOf y j‖ - Real.log ‖y‖ := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hne _ hy
      show ∑ j, u j * (h.matᵀ *ᵥ (0 : Fin n → ℂ)) j = 0
      simp
    rw [fsLog, ConeFsLog.dualNorm_pointOf,
      Real.log_div (norm_ne_zero_iff.2 (hne y hy)) (norm_ne_zero_iff.2 hy0)]
  rw [fsSum, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_congr rfl key,
    Finset.sum_sub_distrib, hz, norm_mul, norm_prod,
    Real.log_mul (norm_ne_zero_iff.2 hc)
      (Finset.prod_ne_zero_iff.mpr fun y hy => norm_ne_zero_iff.2 (hne y hy)),
    Real.log_prod (fun y hy => norm_ne_zero_iff.2 (hne y hy))]
  ring

theorem defect_eq_of_linForm_notMem : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u u' : Fin n → ℂ),
    IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g → GroundTheory.Heights₂.Heights.linForm u ∉ W → GroundTheory.Heights₂.Heights.linForm u' ∉ W →
      mahler h e (specFirst g u) - coneIntegral h W e (fsLog h u) =
        mahler h e (specFirst g u') - coneIntegral h W e (fsLog h u') := by
  intro n e δ h W g u u' hW hg hδ hu hu'
  have hq := SpecFirstNe.full ℂ n e W g u hW hg hu
  have hq' := SpecFirstNe.full ℂ n e W g u' hW hg hu'
  have hh := SpecFirstHomog.proof n e δ g u hδ
  have hh' := SpecFirstHomog.proof n e δ g u' hδ
  obtain ⟨hΓ0, hΓ⟩ := GlobalTheory.T.gaussian_matrix_measure_pos_finite (e + 1) n
  have hΓr : (gaussM (e + 1) n Set.univ).toReal ≠ 0 := (ENNReal.toReal_pos hΓ0.ne' hΓ.ne).ne'
  have hae : ∀ᵐ π : Fin (e + 1) → Fin n → ℂ,
      Real.log ‖eval (nrmGroups h e (coefRows h π)) (specFirst g u)‖ - fsSum h u (coneSet h W) π =
        Real.log ‖eval (nrmGroups h e (coefRows h π)) (specFirst g u')‖ -
          fsSum h u' (coneSet h W) π := by
    filter_upwards [GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W g hW hg hδ, GlobalTheory.T.ae_polynomial_nonvanishing_rows n e δ h _ hq hh,
      GlobalTheory.T.ae_polynomial_nonvanishing_rows n e δ h _ hq' hh'] with π hcount h1 h2
    rw [EvalSpecFirst.proof] at h1 h2 ⊢
    rw [EvalSpecFirst.proof]
    obtain ⟨c, hc, hfac⟩ := GlobalTheory.T.chow_form_fibre_specialization n e δ h W g π u hW hg hδ hcount h1
    have hfin : (fibrePts (coneSet h W) π).Finite := Set.finite_of_encard_eq_coe hcount
    rw [log_norm_sub_fsSum_eq h u _ π c _ hfin hc (hfac u) h1,
      log_norm_sub_fsSum_eq h u' _ π c _ hfin hc (hfac u') h2]
  have haeG := (withDensity_absolutelyContinuous (volume : Measure (Fin (e + 1) → Fin n → ℂ))
    matGauss).ae_le hae
  obtain ⟨i1, e1⟩ := GlobalTheory.T.sphere_mean_normalized_groups n e h (fun w => Real.log ‖eval w (specFirst g u)‖)
    (MahlerIntegrand.proof n e δ h _ hq hh)
  obtain ⟨i1', e1'⟩ := GlobalTheory.T.sphere_mean_normalized_groups n e h (fun w => Real.log ‖eval w (specFirst g u')‖)
    (MahlerIntegrand.proof n e δ h _ hq' hh')
  obtain ⟨i2, e2⟩ := GlobalTheory.T.integral_fubini_study_sum_cone n e δ h W g u hW hg hδ hu
  obtain ⟨i2', e2'⟩ := GlobalTheory.T.integral_fubini_study_sum_cone n e δ h W g u' hW hg hδ hu'
  have hint := integral_congr_ae (μ := gaussM (e + 1) n) haeG
  rw [integral_sub i1 i2, integral_sub i1' i2', e1, e2, e1', e2'] at hint
  apply mul_left_cancel₀ hΓr
  rw [mul_sub, mul_sub]
  exact hint

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMinusConeIntegralIndepStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_minus_cone_integral_indep : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (g : MvPolynomial (Fin (e + 1) × Fin n) ℂ) (u u' : Fin n → ℂ),
  IsProjPrime W → IsChowForm W (e + 1) g → IsMultiHomog δ g → linForm u ∉ W → linForm u' ∉ W →
    mahler h e (specFirst g u) - coneIntegral h W e (fsLog h u) =
      mahler h e (specFirst g u') - coneIntegral h W e (fsLog h u') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.defect_eq_of_linForm_notMem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMeasureOfProduct
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMeasureOfProduct
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem mahler_pow_mul {n e : ℕ} (h : HermNorm n) {q g : MvPolynomial (Fin e × Fin n) ℂ}
    (hq : q ≠ 0) (hg : g ≠ 0) (a : ℕ) :
    mahler h e (q ^ a * g) = (a : ℝ) * mahler h e q + mahler h e g := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', mul_assoc, mahlerMul n e h _ _ hq (mul_ne_zero (pow_ne_zero _ hq) hg), ih]
    push_cast
    ring

theorem mahler_C_mul_prod_pow : ∀ (n e : ℕ) (h : HermNorm n) {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin e × Fin n) ℂ) (d : ι → ℕ) (a : ι → ℕ) (c : ℂ), c ≠ 0 → (∀ i ∈ s, q i ≠ 0 ∧ IsMultiHomog (d i) (q i)) → mahler h e (C c * ∏ i ∈ s, q i ^ a i) = Real.log ‖c‖ + ∑ i ∈ s, (a i : ℝ) * mahler h e (q i) := by
  classical
  intro n e h ι s q d a c hc hq
  revert hq
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [mahler_C]
  · intro i s hi ih hq
    have hrest : ∀ j ∈ s, q j ≠ 0 ∧ IsMultiHomog (d j) (q j) := fun j hj => hq j (Finset.mem_insert_of_mem hj)
    have hne : C c * ∏ j ∈ s, q j ^ a j ≠ 0 :=
      mul_ne_zero (by simpa using hc) (Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hrest j hj).1)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, mul_left_comm (C c) (q i ^ a i),
      mahler_pow_mul h (hq i (Finset.mem_insert_self i s)).1 hne (a i), ih hrest]
    ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMeasureOfProductStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_measure_of_product : ∀ (n e : ℕ) (h : HermNorm n) {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin e × Fin n) ℂ) (d : ι → ℕ) (a : ι → ℕ) (c : ℂ), c ≠ 0 → (∀ i ∈ s, q i ≠ 0 ∧ IsMultiHomog (d i) (q i)) → mahler h e (C c * ∏ i ∈ s, q i ^ a i) = Real.log ‖c‖ + ∑ i ∈ s, (a i : ℝ) * mahler h e (q i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.mahler_C_mul_prod_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHolds
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial

theorem mahlerDefect_eq_sum {n e δ : ℕ} (h : HermNorm n) {Z : ProjCycle ℂ n}
    {f : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hd : IsChowCycleData Z e δ f) :
    ∃ (c : ℂ) (g : Ideal (MvPolynomial (Fin n) ℂ) → MvPolynomial (Fin (e + 1) × Fin n) ℂ)
      (d : Ideal (MvPolynomial (Fin n) ℂ) → ℕ),
      (∀ W ∈ Z.support, IsChowForm W (e + 1) (g W) ∧ IsMultiHomog (d W) (g W)) ∧
      ∀ u : Fin n → ℂ, IsAdmissible Z u →
        mahlerDefect h e Z f u = Real.log ‖c‖ + ∑ W ∈ Z.support, (Z W : ℝ) *
          (mahler h e (specFirst (g W) u) - coneIntegral h W e (fsLog h u)) := by
  obtain ⟨c, hc, g, hg, hf⟩ := hd.chow
  have hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr hc)
      (Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1)
  have hhom : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W) := hf ▸ hd.homog
  obtain ⟨d, hdW, -⟩ := exists_degrees_of_chowFormCycle (Nat.succ_pos e) Z c g hg hhom hf0
  refine ⟨c, g, d, fun W hW => ⟨hg W hW, hdW W hW⟩, fun u hu => ?_⟩
  have hspec : specFirst f u = C c * ∏ W ∈ Z.support, specFirst (g W) u ^ Z W := by
    rw [hf]
    simp only [specFirst, map_mul, map_prod, map_pow, bind₁_C_right]
  have hq : ∀ W ∈ Z.support, specFirst (g W) u ≠ 0 ∧ IsMultiHomog (d W) (specFirst (g W) u) :=
    fun W hW => ⟨SpecFirstNe.full ℂ n e W (g W) u (hd.prime W hW) (hg W hW) (hu W hW),
      SpecFirstHomog.proof n e (d W) (g W) u (hdW W hW)⟩
  rw [mahlerDefect, hspec, GlobalTheory.T.mahler_measure_of_product n e h Z.support (fun W => specFirst (g W) u) d (fun W => Z W) c hc hq,
    cycleIntegral]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem defectConstDim (e : ℕ) : DefectConstDim e := by
  intro n δ h Z f u u' hd hu hu'
  obtain ⟨c, g, d, hg, hsum⟩ := mahlerDefect_eq_sum h hd
  have hW : ∀ W ∈ Z.support, (Z W : ℝ) * (mahler h e (specFirst (g W) u) - coneIntegral h W e (fsLog h u)) =
      (Z W : ℝ) * (mahler h e (specFirst (g W) u') - coneIntegral h W e (fsLog h u')) := fun W hW => by
    have := GlobalTheory.T.mahler_minus_cone_integral_indep n e (d W) h W (g W) u u' (hd.prime W hW) (hg W hW).1 (hg W hW).2 (hu W hW)
      (hu' W hW)
    rw [this]
  rw [hsum u hu, hsum u' hu', Finset.sum_congr rfl hW]

theorem mahlerSection : GroundTheory.Heights₂.Heights.MahlerSection.Statement := by
  intro n e δ h Z f u hp hc hm ha
  exact GroundTheory.Heights₂.Heights.AutoClose.MahlerSectionOfConst e (defectConstDim e) n δ h Z f u ⟨hp, hc, hm⟩ ha

end GlobalTheory.CompanionTheory.Ar.Short
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHoldsStatement
open MvPolynomial NumberField Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ArithBezout
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Short ReciprocityTheory.ChartRestriction.G.T0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_section_statement_holds : GroundTheory.Heights₂.Heights.MahlerSection.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.mahlerSection | exact GlobalTheory.CompanionTheory.Ar.Short.mahlerSection | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.mahlerSection <;> assumption)
end
