module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactUnitaryKernelConcentratedNearOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalLowerDegreeKernelTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalLowerDegreeKernelTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KFourier

theorem orth_translate_lowV {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (p κ : KG ε → ℂ) (hκ : κ ∈ lowV ε i)
    (h : ∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) (k : KG ε) :
    ∫ x, star (p x) * κ (x⁻¹ * k) ∂(muK ε) = 0 := by
  cases i with
  | zero =>
    have h0 : κ = 0 := by simpa [lowV] using hκ
    subst h0
    simp
  | succ i =>
    have hq : (fun x : KG ε => star (κ (x⁻¹ * k))) ∈ lowV ε (i + 1) := by
      have h1 : κ ∈ polyV ε i := hκ
      have h2 := mul_right_mem k h1
      have h3 := inv_mem h2
      exact star_mem h3
    have h4 := h _ hq
    have h5 : ∫ x, star (star (κ (x⁻¹ * k)) * p x) ∂(muK ε) = 0 := by
      have := congrArg star h4
      rw [star_zero] at this
      rw [← this]
      exact integral_conj
    rw [← h5]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [star_mul', star_star]
    ring

end GlobalTheory.KFourier
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalLowerDegreeKernelTranslatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_lowerDegree_kernel_translates : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (p κ : KG ε → ℂ), κ ∈ lowV ε i → (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → ∀ k : KG ε, ∫ x, star (p x) * κ (x⁻¹ * k) ∂(muK ε) = 0 := by
  first | exact @GlobalTheory.KFourier.orth_translate_lowV | exact GlobalTheory.KFourier.orth_translate_lowV | (intros; apply GlobalTheory.KFourier.orth_translate_lowV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.L2normLeIntegralKernelMulTranslateDiff
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.L2normLeIntegralKernelMulTranslateDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

variable {n : ℕ}

theorem continuous_integral_paramK {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : KG ε → KG ε → E} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun x => ∫ k, F x k ∂(muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  have h := continuous_parametric_integral_of_continuous (μ := muK ε) hF (isCompact_univ (X := KG ε))
  simpa only [Measure.restrict_univ] using h

theorem integrable_prod_of_continuousK {ε : Fin n → Bool} {F : KG ε × KG ε → ℂ} (hF : Continuous F) :
    Integrable F ((muK ε).prod (muK ε)) := by
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  haveI : SecondCountableTopology (KG ε) :=
    TopologicalSpace.Subtype.secondCountableTopology (KG ε : Set (UJ ε))
  exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem norm_integral_star_mul_le_sqrtK {ε : Fin n → Bool} {f g : KG ε → ℂ} (hf : Continuous f)
    (hg : Continuous g) :
    ‖∫ x, star (f x) * g x ∂(muK ε)‖ ≤
      Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(muK ε)) * Real.sqrt (∫ x, ‖g x‖ ^ 2 ∂(muK ε)) := by
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re1 : ∀ h : KG ε → ℂ, (∫ x, star (h x) * h x ∂(muK ε)).re = ∫ x, ‖h x‖ ^ 2 ∂(muK ε) := by
    intro h; simp_rw [hsq]; rw [integral_complex_ofReal, Complex.ofReal_re]
  have H := GlobalTheory.norm_integral_star_mul_sq_le (muK ε) f g hf.aestronglyMeasurable hg.aestronglyMeasurable
    (integrable_of_continuousK (by fun_prop)) (integrable_of_continuousK (by fun_prop))
  rw [re1 f, re1 g] at H
  rw [← Real.sqrt_mul (integral_nonneg fun x => by positivity)]
  have := Real.abs_le_sqrt H
  rwa [abs_of_nonneg (norm_nonneg _)] at this


set_option maxHeartbeats 1600000 in
theorem sqrt_integral_normSq_le_integral_kernel_mul_translate :
    ∀ {n : ℕ} (ε : Fin n → Bool) (p : KG ε → ℂ) (κ : KG ε → ℝ), Continuous p → Continuous κ →
      (∀ k, 0 ≤ κ k) → ∫ k, κ k ∂(muK ε) = 1 →
      (∀ k, ∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε) = 0) →
      Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) ≤
        ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
  intro n ε p κ hp hκ hκ0 hκ1 horth
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  have hsq : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have hA0 : 0 ≤ ∫ x, ‖p x‖ ^ 2 ∂(muK ε) := integral_nonneg fun x => by positivity
  have hAc : ∫ x, star (p x) * p x ∂(muK ε) = ((∫ x, ‖p x‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
    simp_rw [hsq]; exact integral_complex_ofReal
  have htr : ∀ x, ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) = ∫ k, (κ (x⁻¹ * k) : ℂ) * p k ∂(muK ε) := by
    intro x
    have := integral_mul_left_eq_self (μ := muK ε) (fun k => (κ (x⁻¹ * k) : ℂ) * p k) x
    simpa only [inv_mul_cancel_left] using this
  have hzero : ∫ x, star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) ∂(muK ε) = 0 := by
    simp_rw [htr]
    have e1 : ∀ x, star (p x) * ∫ k, (κ (x⁻¹ * k) : ℂ) * p k ∂(muK ε) =
        ∫ k, star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k) ∂(muK ε) := fun x => (integral_const_mul _ _).symm
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun x k => star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k))
        ((muK ε).prod (muK ε)) :=
      integrable_prod_of_continuousK (F := fun z : KG ε × KG ε => star (p z.1) * ((κ (z.1⁻¹ * z.2) : ℂ) * p z.2))
        (by fun_prop)
    rw [integral_integral_swap hint]
    have e2 : ∀ k, ∫ x, star (p x) * ((κ (x⁻¹ * k) : ℂ) * p k) ∂(muK ε) =
        (∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε)) * p k := by
      intro k; rw [← integral_mul_const]; congr 1; funext x; ring
    simp_rw [e2, horth, zero_mul, integral_zero]
  have hκ1c : ∫ k, (κ k : ℂ) ∂(muK ε) = 1 := by rw [integral_complex_ofReal, hκ1, Complex.ofReal_one]
  have hinner : ∀ x, ∫ k, (κ k : ℂ) * (p x - p (x * k)) ∂(muK ε) =
      p x - ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) := by
    intro x
    have i1 : Integrable (fun k => (κ k : ℂ) * p x) (muK ε) := integrable_of_continuousK (by fun_prop)
    have i2 : Integrable (fun k => (κ k : ℂ) * p (x * k)) (muK ε) := integrable_of_continuousK (by fun_prop)
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hκ1c, one_mul]
  have hcontT : Continuous (fun x => ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε)) :=
    continuous_integral_paramK (F := fun x k => (κ k : ℂ) * p (x * k)) (by fun_prop)
  have hkey : ((∫ x, ‖p x‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) =
      ∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε) := by
    have e1 : ∀ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) =
        ∫ x, star (p x) * ((κ k : ℂ) * (p x - p (x * k))) ∂(muK ε) := by
      intro k; rw [← integral_const_mul]; congr 1; funext x; ring
    simp_rw [e1]
    have hint : Integrable (Function.uncurry fun x k => star (p x) * ((κ k : ℂ) * (p x - p (x * k))))
        ((muK ε).prod (muK ε)) :=
      integrable_prod_of_continuousK
        (F := fun z : KG ε × KG ε => star (p z.1) * ((κ z.2 : ℂ) * (p z.1 - p (z.1 * z.2)))) (by fun_prop)
    rw [← integral_integral_swap hint]
    have e2 : ∀ x, ∫ k, star (p x) * ((κ k : ℂ) * (p x - p (x * k))) ∂(muK ε) =
        star (p x) * p x - star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε) := by
      intro x; rw [integral_const_mul, hinner, mul_sub]
    simp_rw [e2]
    have iA : Integrable (fun x => star (p x) * p x) (muK ε) := integrable_of_continuousK (by fun_prop)
    have iB : Integrable (fun x => star (p x) * ∫ k, (κ k : ℂ) * p (x * k) ∂(muK ε)) (muK ε) :=
      integrable_of_continuousK ((continuous_star.comp hp).mul hcontT)
    rw [integral_sub iA iB, hzero, sub_zero, hAc]
  have hCS : ∀ k, ‖∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖ ≤
      Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) :=
    fun k => norm_integral_star_mul_le_sqrtK (g := fun x => p x - p (x * k)) hp (by fun_prop)
  have hIc : Continuous (fun k => ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)) :=
    continuous_integral_paramK (F := fun k x => star (p x) * (p x - p (x * k))) (by fun_prop)
  have hDc : Continuous (fun k => ∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) :=
    continuous_integral_paramK (F := fun k x => ‖p x - p (x * k)‖ ^ 2) (by fun_prop)
  have hmain : ∫ x, ‖p x‖ ^ 2 ∂(muK ε) ≤ Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
      ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
    have e : ∫ x, ‖p x‖ ^ 2 ∂(muK ε) =
        (∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε)).re := by
      rw [← hkey, Complex.ofReal_re]
    have hl : Continuous (fun k => ‖(κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖) := by
      fun_prop
    have hr : Continuous (fun k => κ k * (Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
        Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)))) := by fun_prop
    calc ∫ x, ‖p x‖ ^ 2 ∂(muK ε)
        ≤ ‖∫ k, (κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε) ∂(muK ε)‖ := by
          rw [e]; exact Complex.re_le_norm _
      _ ≤ ∫ k, ‖(κ k : ℂ) * ∫ x, star (p x) * (p x - p (x * k)) ∂(muK ε)‖ ∂(muK ε) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ k, κ k * (Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) *
            Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε))) ∂(muK ε) := by
          refine integral_mono (hl.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (hr.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) fun k => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hκ0 k)]
          exact mul_le_mul_of_nonneg_left (hCS k) (hκ0 k)
      _ = _ := by rw [← integral_const_mul]; congr 1; funext k; ring
  rcases hA0.lt_or_eq with hpos | hz
  · have hs : 0 < Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) := Real.sqrt_pos.2 hpos
    refine le_of_mul_le_mul_left ?_ hs
    rw [Real.mul_self_sqrt hA0]
    exact hmain
  · rw [← hz, Real.sqrt_zero]
    exact integral_nonneg fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _)

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.L2normLeIntegralKernelMulTranslateDiffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_integral_norm_sq_le_integral_kernel_mul_translate : ∀ {n : ℕ} (ε : Fin n → Bool) (p : KG ε → ℂ) (κ : KG ε → ℝ), Continuous p → Continuous κ → (∀ k, 0 ≤ κ k) → ∫ k, κ k ∂(muK ε) = 1 → (∀ k, ∫ x, star (p x) * (κ (x⁻¹ * k) : ℂ) ∂(muK ε) = 0) → Real.sqrt (∫ x, ‖p x‖ ^ 2 ∂(muK ε)) ≤ ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.sqrt_integral_normSq_le_integral_kernel_mul_translate | exact GlobalTheory.KFourier.sqrt_integral_normSq_le_integral_kernel_mul_translate | (intros; apply GlobalTheory.KFourier.sqrt_integral_normSq_le_integral_kernel_mul_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpanningLieAlgebraCoefSqBound
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpanningLieAlgebraCoefSqBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KGap

theorem entry_sq_le_hs {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖Y i j‖ ^ 2 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs
  calc ‖Y i j‖ ^ 2 ≤ ∑ j', ‖Y i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖Y i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖Y i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖Y i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)

theorem hs_nonneg' {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs Y := by
  unfold Formalism.REAL.hs; positivity

theorem sup_norm_sq_le_hs {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ^ 2 ≤ Formalism.REAL.hs Y := by
  have h : ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ≤ Real.sqrt (Formalism.REAL.hs Y) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    exact Real.le_sqrt_of_sq_le (entry_sq_le_hs Y i j)
  calc ‖(Matrix.of.symm Y : Fin n → Fin n → ℂ)‖ ^ 2 ≤ Real.sqrt (Formalism.REAL.hs Y) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = Formalism.REAL.hs Y := Real.sq_sqrt (hs_nonneg' Y)

theorem spanning_coef_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ C : ℝ, 0 ≤ C ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y := by
  intro n ε r X hX
  let Tm : (Fin r → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun c => Matrix.of.symm (∑ j, (c j : ℂ) • X j)
      map_add' := by
        intro a b; funext i k
        simp [add_smul, Finset.sum_add_distrib, Matrix.sum_apply]
      map_smul' := by
        intro t a; funext i k
        simp [Matrix.sum_apply, Finset.mul_sum, mul_assoc] }
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Tm.rangeRestrict (LinearMap.range_rangeRestrict Tm)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range Tm).subtype (Submodule.ker_subtype _)
  let L : (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin r → ℝ) := g ∘ₗ P
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨r * ‖Lc‖ ^ 2, by positivity, ?_⟩
  intro Y hY
  obtain ⟨c0, hc0⟩ := hX Y hY
  have hYW : Matrix.of.symm Y ∈ LinearMap.range Tm := ⟨c0, by simp [Tm, hc0]⟩
  have hPY : P (Matrix.of.symm Y) = ⟨_, hYW⟩ := by
    have := LinearMap.congr_fun hP ⟨_, hYW⟩
    simpa using this
  refine ⟨L (Matrix.of.symm Y), ?_, ?_⟩
  · have h1 := LinearMap.congr_fun hg (P (Matrix.of.symm Y))
    have h2 : Tm (L (Matrix.of.symm Y)) = Matrix.of.symm Y := by
      have := congrArg Subtype.val h1
      change Tm (g (P (Matrix.of.symm Y))) = _ at this
      change Tm (g (P (Matrix.of.symm Y))) = _
      rw [hPY] at this ⊢
      exact this
    ext i j
    have h3 := congrFun (congrFun h2 i) j
    simpa [Tm, Matrix.sum_apply] using h3.symm
  · set v := Matrix.of.symm Y with hv
    have hb : ∀ j, (L v) j ^ 2 ≤ ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := by
      intro j
      have h1 : ‖(L v) j‖ ≤ ‖L v‖ := norm_le_pi_norm (L v) j
      have h2 : ‖L v‖ ≤ ‖Lc‖ * ‖v‖ := Lc.le_opNorm v
      have h3 : |(L v) j| ≤ ‖Lc‖ * ‖v‖ := by
        rw [← Real.norm_eq_abs]; exact h1.trans h2
      rw [← mul_pow]
      exact sq_le_sq' (by linarith [abs_le.mp h3]) (abs_le.mp h3).2
    have hv2 : ‖v‖ ^ 2 ≤ Formalism.REAL.hs Y := sup_norm_sq_le_hs Y
    calc ∑ j, (L v) j ^ 2 ≤ ∑ _j : Fin r, ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := Finset.sum_le_sum fun j _ => hb j
      _ = r * ‖Lc‖ ^ 2 * ‖v‖ ^ 2 := by simp; ring
      _ ≤ r * ‖Lc‖ ^ 2 * Formalism.REAL.hs Y := by gcongr

end GlobalTheory.KGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSpanningLieAlgebraCoefSqBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spanning_lieAlgebra_coef_sq_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ C : ℝ, 0 ≤ C ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y := by
  first | exact @GlobalTheory.KGap.spanning_coef_bound | exact GlobalTheory.KGap.spanning_coef_bound | (intros; apply GlobalTheory.KGap.spanning_coef_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PolyTranslationL2Bound
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PolyTranslationL2Bound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

theorem sq_intervalIntegral_unit_le (h : ℝ → ℝ) (hc : Continuous h) :
    (∫ s in (0:ℝ)..1, h s) ^ 2 ≤ ∫ s in (0:ℝ)..1, h s ^ 2 := by
  set c := ∫ s in (0:ℝ)..1, h s with hcdef
  have hnn : 0 ≤ ∫ s in (0:ℝ)..1, (h s - c) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one (fun s _ => sq_nonneg _)
  have hexp : ∫ s in (0:ℝ)..1, (h s - c) ^ 2 = (∫ s in (0:ℝ)..1, h s ^ 2) - 2 * c * c + c ^ 2 := by
    have e1 : (fun s => (h s - c) ^ 2) = fun s => (h s ^ 2 - (2 * c) * h s) + c ^ 2 := by
      funext s; ring
    rw [e1, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    · simp
      exact Or.inl rfl
    · exact (hc.pow 2).intervalIntegrable _ _
    · exact (continuous_const.mul hc).intervalIntegrable _ _
    · exact ((hc.pow 2).sub (continuous_const.mul hc)).intervalIntegrable _ _
    · exact continuous_const.intervalIntegrable _ _
  nlinarith

theorem norm_sub_expK_sq_le : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ Y : Mx n, inK ε Y → ∫ x, ‖φ x - φ (x * expK ε Y 1)‖ ^ 2 ∂(muK ε) ≤ ∫ x, ‖rder ε [Y] φ x‖ ^ 2 ∂(muK ε) := by
  intro n ε d φ hφ Y hY
  obtain ⟨hRmem, hRder⟩ := rder_mem_and_hasDerivAt ε d φ hφ Y hY
  set R := rder ε [Y] φ with hRdef
  have hRc : Continuous R := continuous_of_mem hRmem
  have hφc : Continuous φ := continuous_of_mem hφ
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  have hEG := group_exponential_facts n ε Y hY.1
  have hEK := hEG.2.2.2 hY
  let e : ℝ → KG ε := fun t => expK ε Y t
  have he_add : ∀ s t, e (s + t) = e s * e t := fun s t => by
    apply Subtype.ext
    show ((expK ε Y (s + t) : KG ε) : UJ ε) = (expK ε Y s : UJ ε) * (expK ε Y t : UJ ε)
    rw [hEK.1, hEK.1, hEK.1]
    exact hEG.2.1 s t
  have he0 : e 0 = 1 := by
    apply Subtype.ext
    show ((expK ε Y 0 : KG ε) : UJ ε) = 1
    rw [hEK.1]; exact hEG.1
  have he_cont : Continuous e := hEK.2
  have hder' : ∀ k s, HasDerivAt (fun t => φ (k * e t)) (R (k * e s)) s := by
    intro k s
    have h1 := hRder (k * e s)
    have h2 : HasDerivAt (fun t => φ (k * e s * expK ε Y (t - s))) (R (k * e s)) s :=
      HasDerivAt.comp_sub_const (f := fun t => φ (k * e s * expK ε Y t)) s s (by rw [sub_self]; exact h1)
    have hfun : (fun t => φ (k * e s * expK ε Y (t - s))) = fun t => φ (k * e t) := by
      funext t
      show φ (k * e s * e (t - s)) = φ (k * e t)
      rw [mul_assoc, ← he_add, add_sub_cancel]
    rw [hfun] at h2
    exact h2
  have hgc : ∀ k, Continuous (fun s => R (k * e s)) := fun k =>
    hRc.comp (continuous_const.mul he_cont)
  have hftc : ∀ k, ∫ s in (0:ℝ)..1, R (k * e s) = φ (k * e 1) - φ k := by
    intro k
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder' k s)
      ((hgc k).intervalIntegrable 0 1), he0, mul_one]
  have hpt : ∀ k, ‖φ k - φ (k * e 1)‖ ^ 2 ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ ^ 2 := by
    intro k
    have h1 : ‖φ k - φ (k * e 1)‖ ≤ ∫ s in (0:ℝ)..1, ‖R (k * e s)‖ := by
      rw [norm_sub_rev, ← hftc k]
      exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
    have h2 := sq_intervalIntegral_unit_le (fun s => ‖R (k * e s)‖) ((hgc k).norm)
    calc ‖φ k - φ (k * e 1)‖ ^ 2 ≤ (∫ s in (0:ℝ)..1, ‖R (k * e s)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hRsc : Continuous (fun x => ‖R x‖ ^ 2) := hRc.norm.pow 2
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hRsc.continuousOn
  have hcont2 : Continuous (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2) :=
    hRsc.comp (continuous_fst.mul (he_cont.comp continuous_snd))
  have hI : Integrable (Function.uncurry fun (k : KG ε) (s : ℝ) => ‖R (k * e s)‖ ^ 2)
      ((muK ε).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
      rw [isFiniteMeasure_restrict]; simp
    haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
    have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
      (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    haveI : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
    haveI : SecondCountableTopology (KG ε × ℝ) := inferInstance
    exact Integrable.of_bound hcont2.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC _ (Set.mem_univ _))
  have hswap := integral_integral_swap hI
  have hrhs : ∫ x, (∫ s in (0:ℝ)..1, ‖R (x * e s)‖ ^ 2) ∂(muK ε) = ∫ x, ‖R x‖ ^ 2 ∂(muK ε) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    rw [hswap]
    simp_rw [integral_mul_right_eq_self (μ := muK ε) (fun x => ‖R x‖ ^ 2)]
    rw [setIntegral_const]
    simp
  rw [← hrhs]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun x => by positivity
  · have := hI.integral_prod_left
    simp only [Function.uncurry_apply_pair] at this
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [intervalIntegral.integral_of_le zero_le_one]
  · exact Filter.Eventually.of_forall fun x => hpt x

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.PolyTranslationL2BoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poly_translation_l2_bound : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ Y : Mx n, inK ε Y → ∫ x, ‖φ x - φ (x * expK ε Y 1)‖ ^ 2 ∂(muK ε) ≤ ∫ x, ‖rder ε [Y] φ x‖ ^ 2 ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.norm_sub_expK_sq_le | exact GlobalTheory.KFourier.norm_sub_expK_sq_le | (intros; apply GlobalTheory.KFourier.norm_sub_expK_sq_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivRealLinearDirection
section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivRealLinearDirection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

open Matrix

variable {n : ℕ}

theorem inK_zero' (ε : Fin n → Bool) : inK ε (0 : Mx n) := by
  refine ⟨?_, ?_⟩
  · show (0 : Mx n)ᴴ * Jm ε + Jm ε * 0 = 0
    simp
  · simp

theorem inK_add'' {ε : Fin n → Bool} {X Y : Mx n} (hX : inK ε X) (hY : inK ε Y) : inK ε (X + Y) := by
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨h3, h4⟩ := hY
  refine ⟨?_, ?_⟩
  · have h1' : Xᴴ * Jm ε + Jm ε * X = 0 := h1
    have h3' : Yᴴ * Jm ε + Jm ε * Y = 0 := h3
    show (X + Y)ᴴ * Jm ε + Jm ε * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc Xᴴ * Jm ε + Yᴴ * Jm ε + (Jm ε * X + Jm ε * Y)
        = (Xᴴ * Jm ε + Jm ε * X) + (Yᴴ * Jm ε + Jm ε * Y) := by abel
      _ = 0 := by rw [h1', h3', add_zero]
  · rw [Matrix.add_mul, Matrix.mul_add, h2, h4]

theorem inK_sum_real {ε : Fin n → Bool} {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ) (hX : ∀ j, inK ε (X j)) :
    inK ε (∑ j, (c j : ℂ) • X j) := by
  classical
  refine Finset.sum_induction _ (inK ε) (fun _ _ ha hb => inK_add'' ha hb) (inK_zero' ε) ?_
  intro j _
  exact inK_smul_real ε (hX j) (c j)

def entryDer (ε : Fin n → Bool) (k : KG ε) (a b : Fin n) : Mx n →ₗ[ℝ] ℂ where
  toFun Y := ∑ l, toMK k a l * Y l b
  map_add' Y Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r Y := by
    simp only [Matrix.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Complex.real_smul]
    ring

def entryDerStar (ε : Fin n → Bool) (k : KG ε) (a b : Fin n) : Mx n →ₗ[ℝ] ℂ where
  toFun Y := star (∑ l, toMK k a l * Y l b)
  map_add' Y Z := by
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, star_add]
  map_smul' r Y := by
    simp only [Matrix.smul_apply, RingHom.id_apply, Complex.real_smul]
    simp only [star_sum, Finset.mul_sum, star_mul', Complex.star_def, map_mul, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem hasDerivAt_coord_lin {ε : Fin n → Bool} (c : Fin n × Fin n × Bool) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => coord ε c (k * expK ε Y t)) (D k Y) 0 := by
  obtain ⟨a, b, f⟩ := c
  have hent : ∀ (k : KG ε) (Y : Mx n), inK ε Y → HasDerivAt (fun t : ℝ => (toMK (k * expK ε Y t)) a b)
      (∑ l, toMK k a l * Y l b) 0 := by
    intro k Y hY
    have e : (fun t : ℝ => (toMK (k * expK ε Y t)) a b) =
        fun t : ℝ => ∑ l, toMK k a l * (NormedSpace.exp ((t : ℂ) • Y)) l b := by
      funext t; simp only [toMK_mul, toMK_expK hY, Matrix.mul_apply]
    rw [e]
    exact HasDerivAt.fun_sum fun l _ => (hasDerivAt_exp_entry_real Y l b).const_mul _
  cases f
  · refine ⟨fun k => entryDerStar ε k a b, fun k Y hY => ?_⟩
    have h := (hent k Y hY).star
    have e1 : (fun t : ℝ => coord ε (a, b, false) (k * expK ε Y t)) =
        fun t => star ((toMK (k * expK ε Y t)) a b) := by
      funext t; simp [coord]
    rw [e1]; exact h
  · refine ⟨fun k => entryDer ε k a b, fun k Y hY => ?_⟩
    have e1 : (fun t : ℝ => coord ε (a, b, true) (k * expK ε Y t)) =
        fun t => (toMK (k * expK ε Y t)) a b := by
      funext t; simp [coord]
    rw [e1]; exact hent k Y hY

theorem hasDerivAt_mono_lin {ε : Fin n → Bool} (s : List (Fin n × Fin n × Bool)) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => mono ε s (k * expK ε Y t)) (D k Y) 0 := by
  induction s with
  | nil =>
    refine ⟨0, fun k Y _ => ?_⟩
    simpa [mono] using hasDerivAt_const (0 : ℝ) (1 : ℂ)
  | cons c s ih =>
    obtain ⟨Dc, hc⟩ := hasDerivAt_coord_lin (ε := ε) c
    obtain ⟨Ds, hs⟩ := ih
    refine ⟨fun k => mono ε s k • Dc k + coord ε c k • Ds k, fun k Y hY => ?_⟩
    have h := (hc k Y hY).mul (hs k Y hY)
    have e : (fun t : ℝ => mono ε (c :: s) (k * expK ε Y t)) =
        fun t => coord ε c (k * expK ε Y t) * mono ε s (k * expK ε Y t) := by
      funext t; simp [mono]
    rw [e]
    rw [coord_mul_expK_zero hY, mono_mul_expK_zero hY] at h
    refine h.congr_deriv ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring

theorem hasDerivAt_lin_of_mem {ε : Fin n → Bool} {d : ℕ} {φ : KG ε → ℂ} (hφ : φ ∈ polyV ε d) :
    ∃ D : KG ε → Mx n →ₗ[ℝ] ℂ, ∀ (k : KG ε) (Y : Mx n), inK ε Y →
      HasDerivAt (fun t : ℝ => φ (k * expK ε Y t)) (D k Y) 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, -, rfl⟩ := hx
    exact hasDerivAt_mono_lin s
  | zero =>
    exact ⟨0, fun k Y _ => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, d₁⟩ := hx
    obtain ⟨D₂, d₂⟩ := hy
    exact ⟨D₁ + D₂, fun k Y hY => (d₁ k Y hY).add (d₂ k Y hY)⟩
  | smul a x _ hx =>
    obtain ⟨D, dD⟩ := hx
    exact ⟨a • D, fun k Y hY => by simpa using (dD k Y hY).const_mul a⟩

theorem rder_real_linear {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ) (hφ : φ ∈ polyV ε d)
    {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ) (hX : ∀ j, inK ε (X j)) :
    rder ε [∑ j, (c j : ℂ) • X j] φ = ∑ j, (c j : ℂ) • rder ε [X j] φ := by
  obtain ⟨D, hD⟩ := hasDerivAt_lin_of_mem hφ
  have hr : ∀ (Y : Mx n), inK ε Y → ∀ k, rder ε [Y] φ k = D k Y := by
    intro Y hY k
    rw [rder_cons, rder_nil]
    exact (hD k Y hY).deriv
  funext k
  rw [hr _ (inK_sum_real X c hX) k, Finset.sum_apply]
  have e : (∑ j, (c j : ℂ) • X j) = ∑ j, c j • X j :=
    Finset.sum_congr rfl fun j _ => Complex.coe_smul (c j) (X j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Pi.smul_apply, hr _ (hX j) k, Complex.real_smul, smul_eq_mul]

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryRightDerivRealLinearDirectionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryRightDeriv_real_linear_direction : ∀ {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : KG ε → ℂ), φ ∈ polyV ε d → ∀ {r : ℕ} (X : Fin r → Mx n) (c : Fin r → ℝ), (∀ j, inK ε (X j)) → rder ε [∑ j, (c j : ℂ) • X j] φ = ∑ j, (c j : ℂ) • rder ε [X j] φ := by
  first | exact @GlobalTheory.KFourier.rder_real_linear | exact GlobalTheory.KFourier.rder_real_linear | (intros; apply GlobalTheory.KFourier.rder_real_linear <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryPolynomialSpectralGap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

theorem toMK_injective_of_gap {n : ℕ} (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  exact Subtype.ext (Subtype.ext (Units.ext h))

theorem integrable_real_of_continuousK {n : ℕ} {ε : Fin n → Bool} {f : KG ε → ℝ} (hf : Continuous f) :
    Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem sq_dist_right_translate_le {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n) (hX : ∀ j, inK ε (X j))
    (C : ℝ) (hC : 0 ≤ C)
    (hcoef : ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y)
    {d : ℕ} {p : KG ε → ℂ} (hp : p ∈ polyV ε d) (k : KG ε) :
    ∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε) ≤
      3 * C * Formalism.REAL.hs (toMK k - 1) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) := by
  obtain ⟨Y, hY, hexp, hhs⟩ := compact_exponential_surjective n ε (toMK k) k.2
  have hk : expK ε Y 1 = k := by
    apply toMK_injective_of_gap ε
    show toMK (expK ε Y 1) = toMK k
    rw [toMK_expK hY, Complex.ofReal_one, one_smul, hexp]
  obtain ⟨c, rfl, hc⟩ := hcoef Y hY
  have h1 := GlobalTheory.T.poly_translation_l2_bound ε d p hp _ hY
  rw [hk, GlobalTheory.T.compactUnitaryRightDeriv_real_linear_direction ε d p hp X c hX] at h1
  have hcont : ∀ j, Continuous (rder ε [X j] p) := fun j =>
    continuous_of_mem (rder_mem_and_hasDerivAt ε d p hp (X j) (hX j)).1
  have hpt : ∀ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤
      (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by
    intro x
    rw [Finset.sum_apply]
    calc ‖∑ j, ((c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤ (∑ j, |c j| * ‖rder ε [X j] p x‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          simp [Complex.norm_real]
      _ ≤ (∑ j, |c j| ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by simp [sq_abs]
  have hint : ∀ j, Integrable (fun x => ‖rder ε [X j] p x‖ ^ 2) (muK ε) := fun j =>
    integrable_real_of_continuousK ((hcont j).norm.pow 2)
  have h2 : ∫ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ∂(muK ε) ≤
      (∑ j, c j ^ 2) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) := by
    rw [← integral_finsetSum _ fun j _ => hint j, ← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      ((integrable_finsetSum _ fun j _ => hint j).const_mul _) (Filter.Eventually.of_forall hpt)
  have hE : 0 ≤ ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ C * Formalism.REAL.hs (∑ j, (c j : ℂ) • X j) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) :=
        mul_le_mul_of_nonneg_right hc hE
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hhs hC
        nlinarith

theorem spectral_gap_rder : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) →
    (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
    ∀ i : ℕ, 1 ≤ i → ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) →
    c * (i : ℝ) ^ α * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) := by
  intro n ε r X hX hspan
  obtain ⟨C3, hC3, hcoef⟩ := GlobalTheory.T.exists_spanning_lieAlgebra_coef_sq_bound ε X hspan
  obtain ⟨C4, hC4, hker⟩ := GlobalTheory.T.exists_compactUnitaryKernel_concentrated_near_one ε
  set A : ℝ := 3 * C3 * C4 ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 / (A + 1), 1 / 2, by positivity, by norm_num, ?_⟩
  intro i hi p hp horth
  set E := ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) with hEdef
  have hE : 0 ≤ E := Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  obtain ⟨κ, hκc, hκ0, hκ1, hκmem, hκb⟩ := hker m
  have hpc : Continuous p := continuous_of_mem hp
  have horth' := GlobalTheory.T.orthogonal_lowerDegree_kernel_translates ε (m + 1) p (fun k => (κ k : ℂ)) hκmem horth
  have h1 := GlobalTheory.T.sqrt_integral_norm_sq_le_integral_kernel_mul_translate ε p κ hpc hκc hκ0 hκ1 horth'
  set P := ∫ x, ‖p x‖ ^ 2 ∂(muK ε) with hPdef
  have hP : 0 ≤ P := integral_nonneg fun x => by positivity
  have hint : Integrable (fun k => κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1))) (muK ε) := by
    refine integrable_real_of_continuousK ?_
    refine (hκc.mul continuous_const).mul (Real.continuous_sqrt.comp ?_)
    unfold Formalism.REAL.hs
    fun_prop
  have h2 : ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) ≤
      ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _))
      hint (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hκ0 k)
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := sq_dist_right_translate_le ε X hX C3 hC3 hcoef hp k
    nlinarith [show 0 ≤ Formalism.REAL.hs (toMK k - 1) from by unfold Formalism.REAL.hs; positivity]
  have h3 : ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) =
      Real.sqrt (3 * C3 * E) * ∫ k, κ k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) := by
    rw [← integral_const_mul]; congr 1; funext k; ring
  have hmi : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hmi] at hκb
  set I : ℝ := ((m + 1 : ℕ) : ℝ) with hIdef
  have hI : 1 ≤ I := by rw [hIdef]; exact_mod_cast Nat.succ_pos m
  have hsq : Real.sqrt P ≤ Real.sqrt (3 * C3 * E) * (C4 * I ^ (-(1 / 4 : ℝ))) := by
    calc Real.sqrt P ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left hκb (Real.sqrt_nonneg _)
  have hq : 0 ≤ I ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hPle : P ≤ 3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg P) hsq 2
    rw [Real.sq_sqrt hP, mul_pow, Real.sq_sqrt (by positivity), mul_pow] at h
    linarith
  have hpow : (I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    norm_num
  have hIp : 0 ≤ I ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have key : I ^ (1 / 2 : ℝ) * P ≤ A * E := by
    calc I ^ (1 / 2 : ℝ) * P ≤ I ^ (1 / 2 : ℝ) * (3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hPle hIp
      _ = A * E * ((I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ)) := by rw [hA]; ring
      _ = A * E := by rw [hpow, mul_one]
  have hA1 : 0 < A + 1 := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ hA1]
  nlinarith

end GlobalTheory.KFourier

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryPolynomialSpectralGapStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitary_polynomial_spectral_gap : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ ∀ i : ℕ, 1 ≤ i → ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → c * (i : ℝ) ^ α * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.spectral_gap_rder | exact GlobalTheory.KFourier.spectral_gap_rder | (intros; apply GlobalTheory.KFourier.spectral_gap_rder <;> assumption)
end
