module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSmoothOfChartDerivativesAtIdentity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidlyDecreasingKernelMulAdjointConjCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidlyDecreasingKernelMulAdjointConjCoefficient
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

namespace RapidCoef

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem norm_toL_mul_le (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    ‖toL (A * B)‖ ≤ a * ‖toL A‖ * ‖toL B‖ := by
  have h : ∀ (C : Matrix (Fin a) (Fin a) (Cinf E)) i j, ‖C i j‖ ≤ ‖toL C‖ := fun C i j =>
    (norm_le_pi_norm (toL C i) j).trans (norm_le_pi_norm (toL C) i)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  change ‖(A * B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  calc ‖∑ l, A i l * B l j‖ ≤ ∑ l, ‖A i l * B l j‖ := norm_sum_le _ _
    _ ≤ ∑ _l : Fin a, ‖toL A‖ * ‖toL B‖ := Finset.sum_le_sum fun l _ =>
        (norm_mul_le _ _).trans (mul_le_mul (h A i l) (h B l j) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp [mul_assoc]

theorem continuous_smul_adj : Continuous fun q : Cinf E × Lie E a => toL (q.1 • (Matrix.of q.2).adjugate) := by
  change Continuous fun q : Cinf E × Matrix (Fin a) (Fin a) (Cinf E) => q.1 • q.2.adjugate
  fun_prop

theorem continuous_conj (M : Matrix (Fin a) (Fin a) (Cinf E)) :
    Continuous fun q : Lie E a × Lie E a => toL (Matrix.of q.1 * M * Matrix.of q.2) := by
  change Continuous fun q : Matrix (Fin a) (Fin a) (Cinf E) × Matrix (Fin a) (Fin a) (Cinf E) => q.1 * M * q.2
  fun_prop

theorem inv_val_eq (y : GL (Fin a) (Cinf E)) :
    (y⁻¹).val = (fun v => (y.val.det v)⁻¹) • y.val.adjugate := by
  symm
  apply Units.eq_inv_of_mul_eq_one_left
  rw [mul_smul_comm, Matrix.mul_adjugate, smul_smul]
  have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  have : (fun v => (y.val.det v)⁻¹) * y.val.det = 1 := by
    funext v
    exact inv_mul_cancel₀ ((Pi.isUnit_iff.1 hu) v).ne_zero
  rw [this, one_smul]

end RapidCoef


open RapidCoef in
theorem isRapidInf_mul_adCoef : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ →
      ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ := by
  intro E _ _ _ a X _ ν k γ hr p
  obtain ⟨hk, hγ, hint⟩ := hr
  haveI : SecondCountableTopology (Lie E a) := inferInstance
  haveI : BorelSpace (Lie E a) := inferInstance
  haveI : OpensMeasurableSpace (Lie E a × Lie E a) := inferInstance
  haveI : OpensMeasurableSpace (Cinf E × Lie E a) := inferInstance
  have hA : Measurable fun x => toL (γ x).val := hγ
  have hdet : Measurable fun x => ((γ x).val).det := contDiff_det.continuous.measurable.comp hA
  have hc : Measurable fun x => (fun v => (((γ x).val).det v)⁻¹ : Cinf E) :=
    Measurable.of_eval fun v => ((measurable_pi_apply v).comp hdet).inv
  have hinv : Measurable fun x => toL (γ x)⁻¹.val := by
    have : (fun x => toL (γ x)⁻¹.val) =
        (fun q : Cinf E × Lie E a => toL (q.1 • (Matrix.of q.2).adjugate)) ∘
          fun x => ((fun v => (((γ x).val).det v)⁻¹ : Cinf E), toL (γ x).val) := by
      funext x; simp only [Function.comp_apply, inv_val_eq]; rfl
    rw [this]
    exact continuous_smul_adj.measurable.comp (hc.prodMk hA)
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin a) (Fin a) (Cinf E), M = Matrix.of (lieBasis E a p.2) := ⟨_, rfl⟩
  have e : ∀ y : GL (Fin a) (Cinf E), adCoef y p = lieCoord E a p.1 (toL ((y⁻¹).val * M * y.val)) :=
    fun y => by subst hM; rfl
  have hconj : Measurable fun x => toL ((γ x)⁻¹.val * M * (γ x).val) := by
    have h := (continuous_conj M).measurable.comp (hinv.prodMk hA)
    exact h
  have had : Measurable fun x => adCoef (γ x) p := by
    have h := (lieCoord E a p.1).continuous.measurable.comp hconj
    have h' : (fun x => adCoef (γ x) p) = fun x => lieCoord E a p.1 (toL ((γ x)⁻¹.val * M * (γ x).val)) :=
      funext fun x => e (γ x)
    rw [h']
    exact h
  have hh : Measurable fun x => height (γ x) := by
    unfold height
    exact (measurable_const.add hA.norm).add hinv.norm
  have hh1 : ∀ y : GL (Fin a) (Cinf E), 1 ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]
  have hA_le : ∀ y : GL (Fin a) (Cinf E), ‖toL y.val‖ ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]
  have hI_le : ∀ y : GL (Fin a) (Cinf E), ‖toL (y⁻¹).val‖ ≤ height y := fun y => by
    unfold height; linarith [norm_nonneg (toL y.val)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = ‖lieCoord E a p.1‖ * ((a : ℝ) * (a * ‖toL M‖)) := ⟨_, rfl⟩
  have hbd : ∀ y : GL (Fin a) (Cinf E), ‖adCoef y p‖ ≤ C * height y ^ 2 := fun y => by
    have h0 : 0 ≤ height y := zero_le_one.trans (hh1 y)
    have h1 : ‖toL ((y⁻¹).val * M * y.val)‖ ≤ a * (a * ‖toL (y⁻¹).val‖ * ‖toL M‖) * ‖toL y.val‖ :=
      (norm_toL_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) (Nat.cast_nonneg _)) (norm_nonneg _))
    have h2 : a * (a * ‖toL (y⁻¹).val‖ * ‖toL M‖) * ‖toL y.val‖ ≤ a * (a * height y * ‖toL M‖) * height y :=
      mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hI_le y) (Nat.cast_nonneg _)) (norm_nonneg _)) (Nat.cast_nonneg _))
        (hA_le y) (norm_nonneg _) (by positivity)
    rw [e]
    calc ‖lieCoord E a p.1 (toL ((y⁻¹).val * M * y.val))‖ ≤ ‖lieCoord E a p.1‖ * ‖toL ((y⁻¹).val * M * y.val)‖ :=
          (lieCoord E a p.1).le_opNorm _
      _ ≤ ‖lieCoord E a p.1‖ * (a * (a * height y * ‖toL M‖) * height y) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg _)
      _ = C * height y ^ 2 := by rw [hC]; ring
  refine ⟨hk.mul had, hγ, fun N => ?_⟩
  refine ((hint (N + 2)).const_mul C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((hk.mul had).norm.mul (hh.pow_const N)).aestronglyMeasurable
  · have hpos : 0 ≤ height (γ x) ^ N := pow_nonneg (zero_le_one.trans (hh1 _)) N
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hpos), norm_mul]
    calc ‖k x‖ * ‖adCoef (γ x) p‖ * height (γ x) ^ N
        ≤ ‖k x‖ * (C * height (γ x) ^ 2) * height (γ x) ^ N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbd _) (norm_nonneg _)) hpos
      _ = C * (‖k x‖ * height (γ x) ^ (N + 2)) := by ring

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidlyDecreasingKernelMulAdjointConjCoefficientStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ →
      ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ := by
  first | exact @GlobalTheory.JSW.isRapidInf_mul_adCoef | exact GlobalTheory.JSW.isRapidInf_mul_adCoef | (intros; apply GlobalTheory.JSW.isRapidInf_mul_adCoef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFderivRealLieChartEqSumKernelOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFderivChartEqOf
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

noncomputable section

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem fderiv_chart_rmul (φ : Sm E a) (g : GA E a) (y : GL (Fin a) (Cinf E)) (W : Lie E a) :
    fderiv ℝ (chart φ.1 g) (toL y.val) (rmul (toL y.val) W) =
      lieD (toL ((y⁻¹).val * Matrix.of W * y.val)) φ.1 (g * infGL E a y) := by
  rw [← chart_val (lieD _ φ.1), chart_lieD φ.2 _ g (val_mem_invSet y)]
  congr 1
  change Matrix.of W * y.val = y.val * ((y⁻¹).val * Matrix.of W * y.val)
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

theorem lieD_eq_sum (V : Lie E a) (F : GA E a → ℂ) (h : GA E a) :
    lieD V F h = ∑ i, (lieCoord E a i V) * lieD (lieBasis E a i) F h := by
  conv_lhs => rw [← sum_lieCoord V]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [lieD, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Complex.real_smul]
  rfl

theorem smul_fderiv_chart_comp (φ : Sm E a) (g : GA E a) (y : GL (Fin a) (Cinf E)) (c : ℂ) :
    c • (fderiv ℝ (chart φ.1 g) (toL y.val)).comp (rmul (toL y.val)) =
      ∑ p, (c * adCoef y p * (lie E a (lieBasis E a p.1) φ).1 (g * infGL E a y)) • lieCoord E a p.2 := by
  refine ContinuousLinearMap.coe_injective ((lieBasis E a).ext fun r => ?_)
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, fderiv_chart_rmul, CuspRep.lie_apply]
  rw [lieD_eq_sum, Fintype.sum_prod_type, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single r]
  · simp only [lieCoord, adCoef, ContinuousLinearMap.coe_comp', Function.comp_apply, LinearMap.coe_toContinuousLinearMap',
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, Complex.ofRealCLM_apply, Complex.ofReal_one,
      smul_eq_mul, mul_one]
    ring
  · intro j _ hj
    simp [lieCoord, Module.Basis.repr_self, Finsupp.single_apply, hj]
  · simp

theorem integral_fderiv_chart_eq_of {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (hrc : ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ) (φ : Sm E a)
    (hb : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) (g : GA E a) :
    ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
      ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 := by
  have hint : ∀ p, Integrable (fun x => (k x * adCoef (γ x) p) *
      (lie E a (lieBasis E a p.1) φ).1 (g * infGL E a (γ x))) ν := by
    intro p
    obtain ⟨C, hC⟩ := hb p.1
    exact (hrc p).integrable (lie E a (lieBasis E a p.1) φ).2 ⟨C, 0, fun y => by simpa using hC _⟩
  simp_rw [smul_fderiv_chart_comp]
  rw [integral_finsetSum _ fun p _ => (hint p).smul_const _]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_const]
  rfl

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFderivRealLieChartEqSumKernelOperators
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem integral_fderiv_chart_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a,
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
        ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 :=
  fun E _ _ _ a X _ ν k γ hk φ hb g =>
    integral_fderiv_chart_eq_of ν k γ (fun p => GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient E a X ν k γ hk p) φ hb g

end GlobalTheory.JSW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralFderivRealLieChartEqSumKernelOperatorsStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_fderiv_realLieChart_eq_sum_kernelOperators : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a,
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      ∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν =
        ∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2 := by
  first | exact @GlobalTheory.JSW.integral_fderiv_chart_eq | exact GlobalTheory.JSW.integral_fderiv_chart_eq | (intros; apply GlobalTheory.JSW.integral_fderiv_chart_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivatives
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivatives
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

theorem norm_toL_mul_le {E : Type} [Field E] [NumberField E] {a : ℕ} (A : Matrix (Fin a) (Fin a) (Cinf E)) (B : Lie E a) :
    ‖toL (A * Matrix.of B)‖ ≤ a * (‖toL A‖ * ‖B‖) := by
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  show ‖(A * Matrix.of B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k, ‖A i k * Matrix.of B k j‖ ≤ ‖toL A‖ * ‖B‖ := fun k => by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
    · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
    · exact (norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)
  calc ∑ k, ‖A i k * Matrix.of B k j‖ ≤ ∑ _k : Fin a, ‖toL A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp

theorem norm_fderiv_chart_le : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  intro E _ _ _ a φ hC
  choose C hC using hC
  set D : ℝ := ∑ i, max (C i) 0 * ‖lieCoord E a i‖ with hDdef
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hlie : ∀ (X : Lie E a) (h : GA E a), ‖lieD X φ.1 h‖ ≤ D * ‖X‖ := by
    intro X h
    have e : lieD X φ.1 h = ∑ i, ((lieBasis E a).coord i X) • lieD (lieBasis E a i) φ.1 h := by
      conv_lhs => rw [← sum_lieCoord X]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lieD, map_sum, map_smul]
    rw [e, hDdef, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    have h1 : ‖(lieBasis E a).coord i X‖ ≤ ‖lieCoord E a i‖ * ‖X‖ := by
      have : ‖lieCoord E a i X‖ = ‖(lieBasis E a).coord i X‖ := by simp [lieCoord]
      rw [← this]; exact (lieCoord E a i).le_opNorm X
    have h2 : ‖lieD (lieBasis E a i) φ.1 h‖ ≤ max (C i) 0 := by
      have := hC i h
      rw [GlobalTheory.CuspRep.lie_apply] at this
      exact this.trans (le_max_left _ _)
    calc ‖(lieBasis E a).coord i X‖ * ‖lieD (lieBasis E a i) φ.1 h‖
        ≤ (‖lieCoord E a i‖ * ‖X‖) * max (C i) 0 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨a * D, fun g y => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun W => ?_
  set X : Lie E a := toL ((y⁻¹).val * Matrix.of W) with hX
  have e := chart_lieD φ.2 X g (val_mem_invSet y)
  have eW : rmul X (toL y.val) = W := by
    change y.val * ((y⁻¹).val * Matrix.of W) = Matrix.of W
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [eW, chart_val] at e
  rw [← e]
  calc ‖lieD X φ.1 (g * infGL E a y)‖ ≤ D * ‖X‖ := hlie _ _
    _ ≤ D * (a * (‖toL (y⁻¹).val‖ * ‖W‖)) := mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) hD
    _ = a * D * ‖toL (y⁻¹).val‖ * ‖W‖ := by ring

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormFderivChartLeOfBoundedLieDerivativesStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  first | exact @GlobalTheory.JSW.norm_fderiv_chart_le | exact GlobalTheory.JSW.norm_fderiv_chart_le | (intros; apply GlobalTheory.JSW.norm_fderiv_chart_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOne
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW Topology

namespace GlobalTheory.JSW.KerDeriv

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
def rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := rmul
      map_add' := fun y z => ContinuousLinearMap.ext fun x => Matrix.mul_add (Matrix.of x) (Matrix.of y) (Matrix.of z)
      map_smul' := fun c y => ContinuousLinearMap.ext fun x => Matrix.mul_smul (Matrix.of x) c (Matrix.of y) }

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_rmul_le (y : Lie E a) : ‖rmul y‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ :=
  (rmulL (E := E) (a := a)).le_opNorm y

omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_mul_le (x y : Lie E a) :
    ‖toL (Matrix.of x * Matrix.of y)‖ ≤ ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ * ‖y‖ * ‖x‖ :=
  (rmulL (E := E) (a := a)).le_opNorm₂ y x


omit [_root_.NumberField.IsTotallyComplex E] in
theorem eventually_inv_bdd :
    ∀ᶠ Y in 𝓝 (oneL E a), Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < ‖oneL E a‖ + 1 := by
  have hc : ContinuousAt (fun Y : Lie E a => toL (Matrix.of Y)⁻¹) (oneL E a) := by
    have h := continuousAt_matrix_inv (1 : Matrix (Fin a) (Fin a) (Cinf E)) (by
      rw [Matrix.det_one]
      exact NormedRing.inverse_continuousAt (1 : (Cinf E)ˣ))
    exact h
  have h1 : toL (Matrix.of (oneL E a))⁻¹ = oneL E a := by simp
  have h0 : ‖toL (Matrix.of (oneL E a))⁻¹‖ < ‖oneL E a‖ + 1 := by rw [h1]; exact lt_add_one _
  have h2 := hc.norm.eventually (gt_mem_nhds h0)
  exact Filter.Eventually.and (isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)) h2

theorem norm_chart_le (φ : GA E a → ℂ) (g : GA E a) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (Y : Lie E a) :
    ‖chart φ g Y‖ ≤ max C 0 := by
  unfold chart
  split_ifs
  · exact le_max_of_le_left (hC _)
  · simp

theorem measurable_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) : Measurable (chart φ g) := by
  classical
  have h := ContinuousOn.measurable_piecewise (hφ g).continuousOn (continuousOn_const (c := (0 : ℂ)))
    isOpen_invSet.measurableSet
  convert h using 1
  funext Y
  by_cases hY : Y ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hY]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hY]
    have hY' : ¬ IsUnit (Matrix.of Y) := hY
    simp [chart, hY']

theorem hasFDerivAt_chart_kerOp_of_bound {X : Type} [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hD : ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖)
    (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) := by
  obtain ⟨hkm, hγm, hint⟩ := hk
  obtain ⟨Cφ, hCφ⟩ := hφ
  obtain ⟨CD, hCD⟩ := hD
  set M := ‖(rmulL : Lie E a →L[ℝ] Lie E a →L[ℝ] Lie E a)‖ with hM
  set B := ‖oneL E a‖ + 1 with hB
  have hM0 : 0 ≤ M := norm_nonneg _
  have hB0 : 0 ≤ B := by positivity
  set s : Set (Lie E a) := {Y | Y ∈ invSet E a ∧ ‖toL (Matrix.of Y)⁻¹‖ < B} with hs_def
  have hs : s ∈ 𝓝 (oneL E a) := eventually_inv_bdd
  set F : Lie E a → X → ℂ := fun Y x => k x * chart φ.1 g (rmul (toL (γ x).val) Y) with hF
  set F' : Lie E a → X → (Lie E a →L[ℝ] ℂ) := fun Y x =>
    k x • (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)).comp (rmul (toL (γ x).val)) with hF'
  have hγL : Measurable fun x => toL (γ x).val := hγm
  have heq : chart (kerOp ν k γ φ.1) g =ᶠ[𝓝 (oneL E a)] fun Y => ∫ x, F Y x ∂ν := by
    filter_upwards [isOpen_invSet.mem_nhds (isUnit_one : oneL E a ∈ invSet E a)] with Y hY
    obtain ⟨u, hu⟩ := hY
    have hY' : Y = toL u.val := hu.symm
    subst hY'
    rw [chart_val]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    change k x * φ.1 (g * infGL E a u * infGL E a (γ x)) = k x * chart φ.1 g (rmul (toL (γ x).val) (toL u.val))
    rw [mul_assoc, ← map_mul, ← chart_val φ.1 g (u * γ x)]
    rfl
  have e1 : ∀ x, rmul (toL (γ x).val) (oneL E a) = toL (γ x).val := fun x => one_mul (γ x).val
  have hF'1 : F' (oneL E a) =
      fun x => k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) := by
    funext x; simp only [hF', e1]
  refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
  rw [← hF'1]

  have hmeasF : ∀ Y, AEStronglyMeasurable (F Y) ν := fun Y => by
    refine (hkm.aestronglyMeasurable).mul ?_
    refine ((measurable_chart φ.2 g).comp ?_).aestronglyMeasurable
    exact ((rmulL (E := E) (a := a)).flip Y).continuous.measurable.comp hγL
  have hmeasF' : AEStronglyMeasurable (F' (oneL E a)) ν := by
    rw [hF'1]
    refine hkm.aestronglyMeasurable.smul ?_
    exact (ContinuousLinearMap.compL ℝ (Lie E a) (Lie E a) ℂ).aestronglyMeasurable_comp₂
      ((measurable_fderiv ℝ (chart φ.1 g)).comp hγL).aestronglyMeasurable
      ((rmulL (E := E) (a := a)).continuous.measurable.comp hγL).aestronglyMeasurable

  have hint0 : Integrable (F (oneL E a)) ν := by
    refine Integrable.mono' ((hint 0).mul_const (max Cφ 0)) (hmeasF _) (ae_of_all _ fun x => ?_)
    simp only [hF, norm_mul, pow_zero, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_chart_le φ.1 g hCφ _) (norm_nonneg _)

  set K := max CD 0 * M * B * M with hK
  have hbound : ∀ᵐ x ∂ν, ∀ Y ∈ s, ‖F' Y x‖ ≤ ‖k x‖ * height (γ x) ^ 2 * K := by
    refine ae_of_all _ fun x Y hY => ?_
    have hu : IsUnit (Matrix.of Y) := hY.1
    set y := hu.unit * γ x with hy
    have hyv : rmul (toL (γ x).val) Y = toL y.val := by
      rw [hy, Units.val_mul, IsUnit.unit_spec]; rfl
    have hyi : toL (y⁻¹).val = toL (Matrix.of (toL (γ x)⁻¹.val) * Matrix.of (toL (hu.unit⁻¹).val)) := by
      rw [hy, _root_.mul_inv_rev, Units.val_mul]; rfl
    have hui : ‖toL (hu.unit⁻¹).val‖ ≤ B := by
      rw [Matrix.coe_units_inv, IsUnit.unit_spec]; exact hY.2.le
    have hg1 : ‖toL (γ x).val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x)⁻¹.val)]
    have hg2 : ‖toL (γ x)⁻¹.val‖ ≤ height (γ x) := by
      unfold height; linarith [norm_nonneg (toL (γ x).val)]
    have hL : ‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ ≤ max CD 0 * (M * B * height (γ x)) := by
      rw [hyv]
      refine (hCD g y).trans ?_
      have h1 : ‖toL (y⁻¹).val‖ ≤ M * B * height (γ x) := by
        rw [hyi]
        refine (norm_mul_le _ _).trans ?_
        gcongr
      calc CD * ‖toL (y⁻¹).val‖ ≤ max CD 0 * ‖toL (y⁻¹).val‖ := by gcongr; exact le_max_left _ _
        _ ≤ _ := by gcongr
    have hR : ‖rmul (toL (γ x).val)‖ ≤ M * height (γ x) := (norm_rmul_le _).trans (mul_le_mul_of_nonneg_left hg1 hM0)
    calc ‖F' Y x‖ ≤ ‖k x‖ * (‖fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y)‖ * ‖rmul (toL (γ x).val)‖) := by
          simp only [hF', norm_smul]
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖k x‖ * ((max CD 0 * (M * B * height (γ x))) * (M * height (γ x))) := by
          have hh0 : 0 ≤ height (γ x) := (norm_nonneg _).trans hg1
          gcongr
      _ = ‖k x‖ * height (γ x) ^ 2 * K := by rw [hK]; ring
  have hdiff : ∀ᵐ x ∂ν, ∀ Y ∈ s, HasFDerivAt (F · x) (F' Y x) Y := by
    refine ae_of_all _ fun x Y hY => ?_
    have hmem : rmul (toL (γ x).val) Y ∈ invSet E a := IsUnit.mul hY.1 (γ x).isUnit
    have h1 : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) (rmul (toL (γ x).val) Y))
        (rmul (toL (γ x).val) Y) :=
      ((contDiffAt_chart φ.2 g hmem).differentiableAt (by simp)).hasFDerivAt
    exact (h1.comp Y (rmul (toL (γ x).val)).hasFDerivAt).const_mul (k x)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs (Filter.Eventually.of_forall hmeasF) hint0 hmeasF'
    hbound ((hint 2).mul_const K) hdiff

end GlobalTheory.JSW.KerDeriv

namespace GlobalTheory.JSW

theorem hasFDerivAt_chart_kerOp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type)
    [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      HasFDerivAt (chart (kerOp ν k γ φ.1) g)
        (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) :=
  fun E _ _ _ a _ _ ν k γ hk φ hφ hL g =>
    KerDeriv.hasFDerivAt_chart_kerOp_of_bound ν k γ hk φ hφ (GlobalTheory.T.norm_fderiv_chart_le_of_bounded_lieDerivatives E a φ hL) g

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasFDerivAtRealLieChartKernelOperatorAtOneStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFDerivAt_realLieChart_kernelOperator_at_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, (∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) →
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) → ∀ g,
      HasFDerivAt (chart (kerOp ν k γ φ.1) g)
        (∫ x, k x • (fderiv ℝ (chart φ.1 g) (toL (γ x).val)).comp (rmul (toL (γ x).val)) ∂ν) (oneL E a) := by
  first | exact @GlobalTheory.JSW.hasFDerivAt_chart_kerOp | exact GlobalTheory.JSW.hasFDerivAt_chart_kerOp | (intros; apply GlobalTheory.JSW.hasFDerivAt_chart_kerOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedContinuousCuspidalAutomorphicZeroAddSmu
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedContinuousCuspidalAutomorphicZeroAddSmu
noncomputable section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_unip_adele {r : ℕ} : Continuous fun x : BlockIx a r → Ad E => (unip x : GA E a) := by
  have hn : Continuous fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

theorem isBCC_zero_and_add : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    IsBCC (0 : GA E a → ℂ) ∧
    ∀ (c : ℂ) (F G : GA E a → ℂ), IsBCC F → IsBCC G → IsBCC (c • F + G) := by
  intro E _ _ _ a
  refine ⟨⟨continuous_const, ⟨0, fun g => by simp⟩, ?_, fun _ _ => rfl⟩, ?_⟩
  · intro r _ _ _ _ μ 𝓕 _ _ g
    simp
  · intro c F G hF hG
    obtain ⟨CF, hCF⟩ := hF.bdd
    obtain ⟨CG, hCG⟩ := hG.bdd
    refine ⟨(hF.cont.const_smul c).add hG.cont, ⟨‖c‖ * CF + CG, fun g => ?_⟩, ?_, fun γ g => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      refine (norm_add_le _ _).trans (add_le_add ?_ (hCG g))
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hCF g) (norm_nonneg c)
    · intro r h0 h1 _ _ μ 𝓕 hμ hFd g
      haveI := hμ
      have hfin := covol_lt_top μ 𝓕 hFd
      have hint : ∀ H : GA E a → ℂ, IsBCC H → IntegrableOn (fun x => H (unip x * g)) 𝓕 μ := by
        intro H hH
        obtain ⟨C, hC⟩ := hH.bdd
        have hc : Continuous fun x : BlockIx a r → Ad E => H (unip x * g) :=
          hH.cont.comp (continuous_unip_adele.mul continuous_const)
        haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
        exact Integrable.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall fun x => hC _)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [integral_add ((hint F hF).const_mul c) (hint G hG), integral_const_mul,
        hF.cusp r h0 h1 μ 𝓕 hμ hFd g, hG.cusp r h0 h1 μ 𝓕 hμ hFd g]
      simp
    · simp only [Pi.add_apply, Pi.smul_apply, hF.left, hG.left]

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedContinuousCuspidalAutomorphicZeroAddSmuStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), IsBCC (0 : GA E a → ℂ) ∧
    ∀ (c : ℂ) (F G : GA E a → ℂ), IsBCC F → IsBCC G → IsBCC (c • F + G) := by
  first | exact @GlobalTheory.JSW.isBCC_zero_and_add | exact GlobalTheory.JSW.isBCC_zero_and_add | (intros; apply GlobalTheory.JSW.isBCC_zero_and_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalArchimedeanKernelConvolutionOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalArchimedeanKernelConvolutionOperator
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW.KerCusp

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_unip {r : ℕ} : Continuous (fun x : BlockIx a r → Ad E => (unip x : GA E a)) := by
  have hn : Continuous (fun x : BlockIx a r → Ad E => (nilM x : Matrix (Fin a) (Fin a) (Ad E))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [nilM, Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add hn
  · exact continuous_const.sub hn

theorem measurable_integrand {r : ℕ} [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    {X : Type} [MeasurableSpace X] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)} (hk : Measurable k)
    (hγ : Measurable (fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E)))) (φ : Sm E a)
    (hc : Continuous φ.1) (g : GA E a) :
    Measurable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) := by
  let Φ : invSet E a → (BlockIx a r → Ad E) → ℂ := fun y u => chart φ.1 (unip u * g) y.1
  have hΦ : Measurable (Function.uncurry Φ) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun u => ?_) (fun y => ?_)
    · exact ((φ.2 (unip u * g)).continuousOn).restrict
    · have e : Φ y = fun u => φ.1 (unip u * g * infGL E a y.2.unit) := by
        funext u; exact dif_pos y.2
      rw [e]
      exact (hc.comp ((continuous_unip.mul continuous_const).mul continuous_const)).measurable
  have hy : Measurable (fun x : X => (⟨toL (γ x).val, val_mem_invSet (γ x)⟩ : invSet E a)) :=
    Measurable.subtype_mk hγ
  have e : (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) => k x * φ.1 (unip u * g * infGL E a (γ x))) =
      fun p => k p.2 * Function.uncurry Φ (⟨toL (γ p.2).val, val_mem_invSet (γ p.2)⟩, p.1) := by
    funext p
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, Φ, chart_val]
  rw [e]
  exact (hk.comp measurable_snd).mul (hΦ.comp ((hy.comp measurable_snd).prodMk measurable_fst))

end GlobalTheory.JSW.KerCusp

namespace GlobalTheory.JSW

theorem isCuspidal_kerOp : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, IsBCC φ.1 →
      IsCuspidal (kerOp ν k γ φ.1) := by
  intro E _ _ _ a X _ ν _ k γ hk φ hφ r h0 h1 _ _ μ 𝓕 hμ hF g
  haveI := hμ
  have hfin := covol_lt_top μ 𝓕 hF
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := hφ.bdd
  have hk0 : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
  have hm := KerCusp.measurable_integrand (r := r) hk.1 hk.2.1 φ hφ.cont g
  have hint : Integrable (Function.uncurry fun (u : BlockIx a r → Ad E) (x : X) =>
      k x * φ.1 (unip u * g * infGL E a (γ x))) ((μ.restrict 𝓕).prod ν) := by
    refine Integrable.mono' ((integrable_const C).mul_prod hk0) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨u, x⟩
    simp only [Function.uncurry_apply_pair, norm_mul]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  change ∫ u in 𝓕, (∫ x, k x * φ.1 (unip u * g * infGL E a (γ x)) ∂ν) ∂μ = 0
  rw [integral_integral_swap hint]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans (integral_zero X ℂ)
  rw [integral_const_mul]
  have e : ∀ u : BlockIx a r → Ad E, unip u * g * infGL E a (γ x) = unip u * (g * infGL E a (γ x)) :=
    fun u => mul_assoc _ _ _
  simp only [e]
  rw [hφ.cusp r h0 h1 μ 𝓕 hμ hF _, mul_zero]

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalArchimedeanKernelConvolutionOperatorStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_archimedeanKernelConvolutionOperator : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, IsBCC φ.1 →
      IsCuspidal (kerOp ν k γ φ.1) := by
  first | exact @GlobalTheory.JSW.isCuspidal_kerOp | exact GlobalTheory.JSW.isCuspidal_kerOp | (intros; apply GlobalTheory.JSW.isCuspidal_kerOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mem_mspanR_of_mem {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ π.V) : φ.1 ∈ mspanR π :=
  Submodule.mem_sInf.2 fun _ hS => hS.1 φ h

theorem mspanR_rt {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) (h : GA E a) :
    (fun g => F (g * h)) ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem mspanR_kerOp {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) :
    kerOp ν k γ F ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.2 F (Submodule.mem_sInf.1 hF S hS) X _ ν inferInstance k γ hk

theorem word_nil (φ : Sm E a) : GlobalTheory.GLFin.word [] φ = φ := by simp [GlobalTheory.GLFin.word]

theorem word_cons (X : Lie E a) (l : List (Lie E a)) (φ : Sm E a) :
    GlobalTheory.GLFin.word (X :: l) φ = lie E a X (GlobalTheory.GLFin.word l φ) := by simp [GlobalTheory.GLFin.word]

theorem word_append (l : List (Lie E a)) (X : Lie E a) (φ : Sm E a) :
    GlobalTheory.GLFin.word (l ++ [X]) φ = GlobalTheory.GLFin.word l (lie E a X φ) := by
  simp [GlobalTheory.GLFin.word, List.map_append, List.prod_append]

theorem word_single (X : Lie E a) (φ : Sm E a) : GlobalTheory.GLFin.word [X] φ = lie E a X φ := by simp [GlobalTheory.GLFin.word]

def adH (h : GA E a) (X : Lie E a) : Lie E a :=
  toL ((GeneralLinearGroup.map (pInf E) h)⁻¹.val * Matrix.of X * (GeneralLinearGroup.map (pInf E) h).val)

theorem lie_rt (h : GA E a) (X : Lie E a) (φ : Sm E a) :
    lie E a X (rt E a h φ) = rt E a h (lie E a (adH h X) φ) := by
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have eh : h = infGL E a y * finGL E a k := (infGL_mul_finGL h).symm
  have e1 := GlobalTheory.CapAdInv.rt_lie y ((y⁻¹).val * Matrix.of X * y.val)
  have e2 : toL (y.val * ((y⁻¹).val * Matrix.of X * y.val) * (y⁻¹).val) = X := by
    simp [mul_assoc]
  rw [e2] at e1
  have e3 := lie_rt_fin (adH h X) k
  have key : lie E a X * rt E a h = rt E a h * lie E a (adH h X) := by
    have e4 : rt E a h = rt E a (infGL E a y) * rt E a (finGL E a k) := by rw [← map_mul, ← eh]
    rw [e4, ← mul_assoc, ← e1, mul_assoc]
    change _ * (lie E a (adH h X) * _) = _
    rw [e3, ← mul_assoc]
  exact LinearMap.congr_fun key φ

theorem word_rt (h : GA E a) : ∀ (l : List (Lie E a)) (φ : Sm E a),
    GlobalTheory.GLFin.word l (rt E a h φ) = rt E a h (GlobalTheory.GLFin.word (l.map (adH h)) φ)
  | [], φ => by simp [GlobalTheory.GLFin.word]
  | X :: l, φ => by rw [word_cons, word_rt h l, lie_rt, List.map_cons, word_cons]


variable (E a) in
def bccSub : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | IsBCC F}
  zero_mem' := (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).1
  add_mem' {F G} hF hG := by simpa using (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).2 1 F G hF hG
  smul_mem' c F hF := by simpa using (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).2 c F 0 hF (GlobalTheory.T.isBoundedContinuousCuspidalAutomorphic_zero_add_smul E a).1

def dSub (π : CuspSub E a) : Submodule ℂ (Sm E a) :=
  ⨅ l : List (Lie E a), (mspanR π ⊓ bccSub E a).comap ((Sm E a).subtype ∘ₗ GlobalTheory.GLFin.word l)

theorem mem_dSub {π : CuspSub E a} {φ : Sm E a} :
    φ ∈ dSub π ↔ ∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π ∧ IsBCC (GlobalTheory.GLFin.word l φ).1 := by
  simp only [dSub, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_inf, LinearMap.comp_apply,
    Submodule.subtype_apply]
  rfl

theorem lie_mem_dSub {π : CuspSub E a} {φ : Sm E a} (h : φ ∈ dSub π) (X : Lie E a) : lie E a X φ ∈ dSub π :=
  mem_dSub.2 fun l => by rw [← word_append]; exact mem_dSub.1 h _

theorem isBCC_rt {F : GA E a → ℂ} (hF : IsBCC F) (h : GA E a) : IsBCC (fun g => F (g * h)) := by
  refine ⟨hF.cont.comp (continuous_mul_const h), ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hF.bdd
    exact ⟨C, fun g => hC (g * h)⟩
  · intro r h0 h1 _ _ μ 𝓕 hμ hF' g
    simpa only [mul_assoc] using hF.cusp r h0 h1 μ 𝓕 hμ hF' (g * h)
  · intro γ g
    simpa only [mul_assoc] using hF.left γ (g * h)

theorem rt_mem_dSub {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ dSub π) (h : GA E a) : rt E a h φ ∈ dSub π :=
  mem_dSub.2 fun l => by
    rw [word_rt]
    obtain ⟨h1, h2⟩ := mem_dSub.1 hφ (l.map (adH h))
    exact ⟨mspanR_rt h1 h, isBCC_rt h2 h⟩

theorem isBCC_of_mem (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (h : φ ∈ π.V) : IsBCC φ.1 :=
  ⟨(π.cusp φ h).1.continuous, hB.of_isUnitary hπ h, (π.cusp φ h).2, (π.cusp φ h).1.left⟩

theorem word_mem (π : CuspSub E a) : ∀ (l : List (Lie E a)) {φ : Sm E a}, φ ∈ π.V → GlobalTheory.GLFin.word l φ ∈ π.V
  | [], _, h => by rw [word_nil]; exact h
  | X :: l, _, h => by rw [word_cons]; exact π.stable (.lie X) _ (word_mem π l h)

theorem mem_dSub_of_mem (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) {φ : Sm E a}
    (h : φ ∈ π.V) : φ ∈ dSub π :=
  mem_dSub.2 fun l => ⟨mem_mspanR_of_mem (word_mem π l h), isBCC_of_mem hB hπ (word_mem π l h)⟩

theorem isBCC_kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) (φ : Sm E a) (hφ : IsBCC φ.1) :
    IsBCC (kerOp ν k γ φ.1) := by
  refine ⟨(GlobalTheory.T.kernelOperator_integrable_continuous_smooth E a X ν k γ hk φ hφ.cont hφ.bdd).2,
    ?_, GlobalTheory.T.isCuspidal_archimedeanKernelConvolutionOperator E a X ν k γ hk φ hφ, ?_⟩
  · obtain ⟨C, hC⟩ := hφ.bdd
    have hi : Integrable (fun x => ‖k x‖) ν := by simpa using hk.2.2 0
    refine ⟨C * ∫ x, ‖k x‖ ∂ν, fun g => ?_⟩
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hi.const_mul C) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · intro γ' g
    simp only [kerOp, mul_assoc, hφ.left]

theorem hasFDerivAt_kerOp {X : Type} [MeasurableSpace X] (ν : Measure X) (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E))
    (hk : IsRapidInf ν k γ) (φ : Sm E a) (hb : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C)
    (hd : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) (g : GA E a) :
    HasFDerivAt (chart (kerOp ν k γ φ.1) g)
      (∑ p, kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1 g • lieCoord E a p.2)
      (oneL E a) := by
  rw [← GlobalTheory.T.integral_fderiv_realLieChart_eq_sum_kernelOperators E a X ν k γ hk φ hd g]
  exact GlobalTheory.T.hasFDerivAt_realLieChart_kernelOperator_at_one E a X ν k γ hk φ hb hd g

theorem kerOp_mem_dSub {π : CuspSub E a} {φ : Sm E a} (hφ : φ ∈ dSub π) {X : Type} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)) (hk : IsRapidInf ν k γ) :
    ∃ ψ ∈ dSub π, ψ.1 = kerOp ν k γ φ.1 := by
  let K : Set (GA E a → ℂ) := {f | ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ)
    (γ : X → GL (Fin a) (Cinf E)) (φ : Sm E a), IsRapidInf ν k γ ∧ φ ∈ dSub π ∧ f = kerOp ν k γ φ.1}
  have hder : ∀ f ∈ K, ∃ fs : Fin (Module.finrank ℝ (Lie E a)) × Fin (Module.finrank ℝ (Lie E a)) → GA E a → ℂ,
      (∀ p, fs p ∈ K) ∧ ∀ g, HasFDerivAt (chart f g) (∑ p, fs p g • lieCoord E a p.2) (oneL E a) := by
    rintro _ ⟨X, _, ν, _, k, γ, φ, hk, hφ, rfl⟩
    have hb : ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := by simpa [word_nil] using (mem_dSub.1 hφ []).2.bdd
    have hd : ∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C := fun i => by
      simpa [word_single] using (mem_dSub.1 hφ [lieBasis E a i]).2.bdd
    exact ⟨fun p => kerOp ν (fun x => k x * adCoef (γ x) p) γ (lie E a (lieBasis E a p.1) φ).1,
      fun p => ⟨X, _, ν, inferInstance, _, γ, _, GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient E a X ν k γ hk p, lie_mem_dSub hφ _, rfl⟩,
      hasFDerivAt_kerOp ν k γ hk φ hb hd⟩
  have hSm : ∀ f ∈ K, f ∈ Sm E a := GlobalTheory.T.mem_smooth_of_chart_derivatives_at_identity E a K fun f hf => by
    obtain ⟨fs, h1, h2⟩ := hder f hf
    exact ⟨_, inferInstance, fs, fun p => lieCoord E a p.2, h1, h2⟩
  have hspan : Submodule.span ℂ K ≤ Sm E a := Submodule.span_le.2 hSm
  have hlie : ∀ f ∈ Submodule.span ℂ K, ∀ (h : f ∈ Sm E a) (Y : Lie E a),
      (lie E a Y ⟨f, h⟩).1 ∈ Submodule.span ℂ K := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      intro h Y
      obtain ⟨fs, h1, h2⟩ := hder f hf
      have e : (lie E a Y ⟨f, h⟩).1 = ∑ p, (lieCoord E a p.2 Y) • fs p := by
        funext g
        rw [CuspRep.lie_apply, lieD, (h2 g).fderiv]
        simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
          smul_eq_mul, mul_comm]
      rw [e]
      exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span (h1 p))
    | zero =>
      intro h Y
      have : (⟨0, h⟩ : Sm E a) = 0 := rfl
      rw [this, map_zero]
      exact Submodule.zero_mem _
    | add f f' hf hf' ihf ihf' =>
      intro h Y
      have : (⟨f + f', h⟩ : Sm E a) = ⟨f, hspan hf⟩ + ⟨f', hspan hf'⟩ := rfl
      rw [this, map_add (f := _)]
      exact Submodule.add_mem _ (ihf _ Y) (ihf' _ Y)
    | smul c f hf ihf =>
      intro h Y
      have : (⟨c • f, h⟩ : Sm E a) = c • ⟨f, hspan hf⟩ := rfl
      rw [this, map_smul]
      exact Submodule.smul_mem _ c (ihf _ Y)
  have hword : ∀ (l : List (Lie E a)) (ψ : Sm E a), ψ.1 ∈ Submodule.span ℂ K →
      (GlobalTheory.GLFin.word l ψ).1 ∈ Submodule.span ℂ K := by
    intro l
    induction l with
    | nil => intro ψ h; rwa [word_nil]
    | cons Y l ih => intro ψ h; rw [word_cons]; exact hlie _ (ih ψ h) _ Y
  have hgood : Submodule.span ℂ K ≤ mspanR π ⊓ bccSub E a := Submodule.span_le.2 (by
    rintro _ ⟨X, _, ν, _, k, γ, φ, hk, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := mem_dSub.1 hφ []
    rw [word_nil] at h1 h2
    exact ⟨mspanR_kerOp h1 ν k γ hk, isBCC_kerOp ν k γ hk φ h2⟩)
  have hmem : kerOp ν k γ φ.1 ∈ K := ⟨X, _, ν, inferInstance, k, γ, φ, hk, hφ, rfl⟩
  exact ⟨⟨_, hSm _ hmem⟩, mem_dSub.2 fun l => hgood (hword l _ (Submodule.subset_span hmem)), rfl⟩

theorem mspanR_le (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) :
    mspanR π ≤ (dSub π).map (Sm E a).subtype := by
  refine sInf_le ⟨fun φ hφ => ⟨φ, mem_dSub_of_mem hB hπ hφ, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩ h
    exact ⟨rt E a h φ, rt_mem_dSub hφ h, rfl⟩
  · rintro _ ⟨φ, hφ, rfl⟩ X _ ν _ k γ hk
    obtain ⟨ψ, h1, h2⟩ := kerOp_mem_dSub hφ ν k γ hk
    exact ⟨ψ, h1, h2⟩

theorem mspanR_words (hB : GlobalTheory.Published.CuspFormsBoundedGL) {π : CuspSub E a} (hπ : π.IsUnitary) :
    ∀ F ∈ mspanR π, ∃ φ : Sm E a, φ.1 = F ∧
      ∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π ∧ IsBCC (GlobalTheory.GLFin.word l φ).1 := by
  intro F hF
  obtain ⟨φ, hφ, rfl⟩ := mspanR_le hB hπ hF
  exact ⟨φ, rfl, mem_dSub.1 hφ⟩

theorem mspanR_smooth : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    GlobalTheory.Published.CuspFormsBoundedGL → ∀ π : CuspSub E a, π.IsUnitary → ∀ F ∈ mspanR π, ∃ φ : Sm E a, φ.1 = F ∧
      (∀ l, (GlobalTheory.GLFin.word l φ).1 ∈ mspanR π) ∧ IsCuspidal F ∧ ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C := by
  intro E _ _ _ a hB π hπ F hF
  obtain ⟨φ, rfl, h⟩ := mspanR_words hB hπ F hF
  have h0 := (h []).2
  rw [word_nil] at h0
  exact ⟨φ, rfl, fun l => (h l).1, h0.cusp, h0.bdd⟩

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBoundStatement
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormRapidKernelSmoothSpan_smooth_cuspidal_bounded : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), GlobalTheory.Published.CuspFormsBoundedGL → ∀ (π : CuspSub E a), π.IsUnitary → ∀ F ∈ GlobalTheory.JSW.mspanR π, ∃ φ : Sm E a, φ.1 = F ∧ (∀ l : List (Lie E a), (GlobalTheory.GLFin.word l φ).1 ∈ GlobalTheory.JSW.mspanR π) ∧ IsCuspidal F ∧ ∃ C : ℝ, ∀ g, ‖F g‖ ≤ C := by
  first | exact @GlobalTheory.JSW.mspanR_smooth | exact GlobalTheory.JSW.mspanR_smooth | (intros; apply GlobalTheory.JSW.mspanR_smooth <;> assumption)
end
