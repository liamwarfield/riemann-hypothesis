module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfG
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

theorem amgm {k x y : ℝ} (hk : 0 < k) : x * y ≤ (x ^ 2 / k + k * y ^ 2) / 2 := by
  have h : 0 ≤ (x - k * y) ^ 2 / k := by positivity
  have e : (x - k * y) ^ 2 / k = x ^ 2 / k - 2 * (x * y) + k * y ^ 2 := by
    field_simp
    ring
  linarith

theorem I_zero {α : Type*} [MeasurableSpace α] {μ : Measure α} {k : α → ℝ} {g u : α → ℂ}
    {w : α → ℝ≥0∞} {q : ℝ} (hk : ∀ᵐ a ∂μ, 0 < k a) (hw : ∀ᵐ a ∂μ, w a < ⊤) (hq1 : q < 1)
    (hq0 : 0 ≤ q) (hkm : AEMeasurable k μ) (hgm : AEMeasurable g μ) (hum : AEMeasurable u μ)
    (hwm : AEMeasurable w μ)
    (hI : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ < ⊤)
    (hJ : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ ≤
      ENNReal.ofReal q * ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ)
    (h0 : ∫ a, ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ) ∂μ = 0) :
    ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ = 0 := by
  have hWm : AEMeasurable (fun a => (w a).toReal) μ := hwm.ennreal_toReal
  have hF1m : AEMeasurable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    (hkm.mul (hgm.norm.pow_const 2)).mul hWm
  have hF2m : AEMeasurable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ((hum.norm.pow_const 2).div hkm).mul hWm
  have hF1nn : 0 ≤ᵐ[μ] fun a => k a * ‖g a‖ ^ 2 * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (mul_nonneg ha.le (sq_nonneg _)) ENNReal.toReal_nonneg
  have hF2nn : 0 ≤ᵐ[μ] fun a => ‖u a‖ ^ 2 / k a * (w a).toReal := by
    filter_upwards [hk] with a ha
    exact mul_nonneg (div_nonneg (sq_nonneg _) ha.le) ENNReal.toReal_nonneg
  have hA : ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (mul_nonneg ha.le (sq_nonneg _)), ENNReal.ofReal_toReal hwa.ne]
  have hB : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a) * w a ∂μ =
      ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hk, hw] with a ha hwa
    rw [ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) ha.le), ENNReal.ofReal_toReal hwa.ne]
  rw [hA] at hI hJ ⊢
  rw [hB] at hJ
  have hJfin : ∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ < ⊤ :=
    lt_of_le_of_lt hJ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI)
  have hF1i : Integrable (fun a => k a * ‖g a‖ ^ 2 * (w a).toReal) μ :=
    ⟨hF1m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF1nn).2 hI⟩
  have hF2i : Integrable (fun a => ‖u a‖ ^ 2 / k a * (w a).toReal) μ :=
    ⟨hF2m.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hF2nn).2 hJfin⟩
  have hint1 : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (k a * ‖g a‖ ^ 2 * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF1nn hF1m.aestronglyMeasurable
  have hint2 : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ =
      (∫⁻ a, ENNReal.ofReal (‖u a‖ ^ 2 / k a * (w a).toReal) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hF2nn hF2m.aestronglyMeasurable
  have hPm : AEStronglyMeasurable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    ((hum.mul (Complex.continuous_conj.measurable.comp_aemeasurable hgm)).mul
      (Complex.measurable_ofReal.comp_aemeasurable hWm)).aestronglyMeasurable
  have hPbd : ∀ᵐ a ∂μ, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ≤
      (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 := by
    filter_upwards [hk] with a ha
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ENNReal.toReal_nonneg]
    have h1 := amgm (k := k a) (x := ‖u a‖) (y := ‖g a‖) ha
    have hW0 : 0 ≤ (w a).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right h1 hW0]
  have hbdi : Integrable (fun a => (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2) μ :=
    (hF2i.add hF1i).div_const 2
  have hPi : Integrable (fun a => u a * conj (g a) * ((w a).toReal : ℂ)) μ :=
    Integrable.mono' hbdi hPm hPbd
  have hF1c : Integrable (fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ)) μ := hF1i.ofReal
  have hsplit : (fun a => ((k a : ℂ) * g a - u a) * conj (g a) * ((w a).toReal : ℂ)) =
      fun a => ((k a * ‖g a‖ ^ 2 * (w a).toReal : ℝ) : ℂ) - u a * conj (g a) * ((w a).toReal : ℂ) := by
    funext a
    rw [sub_mul, sub_mul, mul_assoc (k a : ℂ) (g a) (conj (g a)), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [hsplit, integral_sub hF1c hPi, integral_complex_ofReal, sub_eq_zero] at h0
  have hn : 0 ≤ ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := integral_nonneg_of_ae hF1nn
  have hle : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ ≤
      ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
    calc ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ
        = ‖((∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hn]
      _ = ‖∫ a, u a * conj (g a) * ((w a).toReal : ℂ) ∂μ‖ := by rw [h0]
      _ ≤ ∫ a, ‖u a * conj (g a) * ((w a).toReal : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ a, (‖u a‖ ^ 2 / k a * (w a).toReal + k a * ‖g a‖ ^ 2 * (w a).toReal) / 2 ∂μ :=
          integral_mono_ae hPi.norm hbdi hPbd
      _ = ((∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ) + ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ) / 2 := by
          rw [integral_div, integral_add hF2i hF1i]
  have hJr : ∫ a, ‖u a‖ ^ 2 / k a * (w a).toReal ∂μ ≤ q * ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ := by
    rw [hint1, hint2]
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hJ
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq0] at this
  have hz : ∫ a, k a * ‖g a‖ ^ 2 * (w a).toReal ∂μ = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hq1.le) hn]
  rw [hint1] at hz
  exact ((ENNReal.toReal_eq_zero_iff _).1 hz).resolve_right hI.ne

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoG
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PolyGrowthStatementPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PG

open MvPolynomial

variable {D : ℕ}

noncomputable def lineHom (a w : Fin D → ℂ) : MvPolynomial (Fin D) ℂ →ₐ[ℂ] Polynomial ℂ :=
  aeval fun i => Polynomial.C (a i) + Polynomial.C (w i) * Polynomial.X

theorem eval_lineHom (a w : Fin D → ℂ) (F : MvPolynomial (Fin D) ℂ) (s : ℂ) :
    (lineHom a w F).eval s = eval (fun i => a i + w i * s) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [lineHom]
  | add p q hp hq => rw [map_add (f := _), Polynomial.eval_add, hp, hq, MvPolynomial.eval_add]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    simp [lineHom]

end ReciprocityTheory.ChartRestriction.G.AR.Up.PG
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IntegralStatementPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf

noncomputable section

section Cone

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

def cone (a : ι → E) : MvPolynomial ι R →ₐ[R] Polynomial E :=
  aeval fun i => Polynomial.C (a i) * Polynomial.X

theorem cone_homog (a : ι → E) {f : MvPolynomial ι R} {d : ℕ} (hf : f.IsHomogeneous d) :
    cone a f = Polynomial.monomial d (aeval a f) := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i ∈ m.support, m i = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  have hp : (m.prod fun i k => (Polynomial.C (a i) * Polynomial.X) ^ k) =
      Polynomial.C (m.prod fun i k => a i ^ k) * Polynomial.X ^ d := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow,
      Finset.prod_pow_eq_pow_sum, hd]
  rw [cone, aeval_monomial, aeval_monomial, hp, Polynomial.algebraMap_apply, ← mul_assoc,
    ← Polynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_cone (a : ι → E) (f : MvPolynomial ι R) (n : ℕ) :
    (cone a f).coeff n = aeval a (homogeneousComponent n f) := by
  classical
  conv_lhs => rw [← sum_homogeneousComponent f]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Polynomial.finsetSum_coeff]
  simp_rw [cone_homog a (homogeneousComponent_isHomogeneous _ f), Polynomial.coeff_monomial_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero]

theorem aeval_mul_homog (q : ι → E) (t : E) {G : MvPolynomial ι R} {m : ℕ} (hG : G.IsHomogeneous m) :
    aeval (fun i => q i * t) G = t ^ m * aeval q G := by
  have h := congrArg ((Polynomial.aeval t : Polynomial E →ₐ[E] E).restrictScalars R)
    (cone_homog (R := R) q hG)
  rw [cone, MvPolynomial.comp_aeval_apply] at h
  simp only [AlgHom.restrictScalars_apply, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
    Polynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h, mul_comm]

theorem eval_mul_homog {K : Type*} [CommRing K] (q : ι → K) (t : K) {G : MvPolynomial ι K} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => q i * t) G = t ^ m * eval q G := by
  simpa using aeval_mul_homog (R := K) q t hG

end Cone

open MvPolynomial in
theorem exists_cons_one_ne {K : Type*} [Field K] [Infinite K] {n m : ℕ}
    {G : MvPolynomial (Fin (n + 1)) K} (hG : G.IsHomogeneous m) (h0 : G ≠ 0) :
    ∃ c : Fin n → K, eval (Fin.cons 1 c) G ≠ 0 := by
  by_contra! h
  apply h0
  have hX : (X 0 * G : MvPolynomial (Fin (n + 1)) K) = 0 := by
    apply MvPolynomial.funext
    intro p
    rw [map_mul, eval_X, map_zero]
    by_cases hp : p 0 = 0
    · rw [hp, zero_mul]
    · have hq : p = fun i => (Fin.cons 1 (fun k => p k.succ / p 0) : Fin (n + 1) → K) i * p 0 := by
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · simp
        · simp [div_mul_cancel₀ _ hp]
      have : eval p G = 0 := by
        rw [hq]
        rw [eval_mul_homog _ _ hG, h, mul_zero]
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hX).resolve_left (X_ne_zero _)

section Int

open MvPolynomial

variable {R E : Type*} [CommRing R] [CommRing E] [Algebra R E] {ι : Type*}

end Int

section Homog

open Polynomial

theorem prod_pow_natDegree_coeff' {B : Type*} [CommRing B] {ι : Type*} (s : Finset ι)
    (v : ι → B[X]) (d : ι → ℕ) (hv : ∀ i, (v i).natDegree ≤ 1) :
    (∏ i ∈ s, v i ^ d i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, v i ^ d i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (v i).coeff 1 ^ d i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨hDegree, hCoeff⟩ := ih
    have haDegree : (v a ^ d a).natDegree ≤ d a := by
      simpa using natDegree_pow_le_of_le (d a) (hv a)
    have haCoeff : (v a ^ d a).coeff (d a) = (v a).coeff 1 ^ d a := by
      simpa using coeff_pow_of_natDegree_le (m := d a) (hv a)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨natDegree_mul_le.trans (add_le_add haDegree hDegree), ?_⟩
    rw [coeff_mul_add_eq_of_natDegree_le haDegree hDegree, haCoeff, hCoeff]

end Homog

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
end
