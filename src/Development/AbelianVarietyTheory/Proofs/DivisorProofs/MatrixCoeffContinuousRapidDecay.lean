module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoefficient
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory.RealWeil

theorem continuous_matrixCoeff_rhoFun : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  intro n g g'
  have hp : Continuous (fun w : Fin n ⊕ Fin n → ℝ => pPart w) := by
    unfold pPart; fun_prop
  have hq : Continuous (fun w : Fin n ⊕ Fin n → ℝ => qPart w) := by
    unfold qPart; fun_prop
  refine continuous_of_dominated (bound := fun x => SchwartzMap.seminorm ℂ 0 0 g * ‖g' x‖) ?_ ?_ ?_ ?_
  · intro w
    exact (((continuous_phase w).mul (g.continuous.comp (continuous_id.add continuous_const))).mul
      (continuous_star.comp g'.continuous)).aestronglyMeasurable
  · intro w
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, norm_mul, norm_phase, one_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℂ g _) (norm_nonneg _)
  · exact (SchwartzMap.integrable g').norm.const_mul _
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [rhoFun, phase]
    fun_prop

end GlobalTheory.RealWeil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoefficientStatement
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_matrix_coefficient : ∀ (n : ℕ) (g g' : Sch (Fin n)), Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) := by
  first | exact @GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | exact GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun | (intros; apply GlobalTheory.RealWeil.continuous_matrixCoeff_rhoFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecaySecondPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecaySecondPart
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
open scoped FourierTransform ContDiff RealInnerProductSpace Real

noncomputable section

namespace GlobalTheory.RealWeil.CoefQDecay

variable {n : ℕ}

def prodTrans (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => g (x + p) * starRingEnd ℂ (g' x)

theorem contDiff_prodTrans (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (prodTrans g g' p) := by
  have h1 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => g (x + p)) :=
    g.smooth'.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) :=
    Complex.conjCLE.contDiff.comp g'.smooth'
  exact h1.mul h2

theorem norm_integral_eq (g g' : Sch (Fin n)) (w : Fin n ⊕ Fin n → ℝ) :
    ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ = ‖𝓕 (prodTrans g g' (pPart w)) (-qPart w)‖ := by
  have e : (fun x => rhoFun w ⇑g x * starRingEnd ℂ (g' x)) = fun x =>
      Complex.exp (((π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) *
        (𝐞 (-⟪x, -qPart w⟫) • prodTrans g g' (pPart w) x) := by
    funext x
    simp only [rhoFun, phase, prodTrans, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    have h : Complex.exp (((2 * π * ⟪qPart w, x⟫ + π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((π * ⟪pPart w, qPart w⟫ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * π * -⟪x, -qPart w⟫ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [inner_neg_right, neg_neg, real_inner_comm]
      push_cast
      ring
    rw [h]
    ring
  rw [e, integral_const_mul, Real.fourier_eq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

def derivBound (g g' : Sch (Fin n)) (j : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i g *
    ‖iteratedFDeriv ℝ (j - i) g' x‖

theorem norm_iteratedFDeriv_prodTrans_le (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖ ≤ derivBound g g' j x := by
  have h1 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => g (x + p)) :=
    g.smooth'.comp (contDiff_id.add contDiff_const)
  have h2 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) :=
    Complex.conjCLE.contDiff.comp g'.smooth'
  refine (norm_iteratedFDeriv_mul_le h1 h2 x (n := j) (by exact_mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have e1 : ‖iteratedFDeriv ℝ i (fun x : EuclideanSpace ℝ (Fin n) => g (x + p)) x‖ ≤
      SchwartzMap.seminorm ℝ 0 i g := by
    rw [iteratedFDeriv_comp_add_right]
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g i (x + p)
  have e2 : ‖iteratedFDeriv ℝ (j - i) (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) x‖ =
      ‖iteratedFDeriv ℝ (j - i) g' x‖ := by
    have e : (fun x : EuclideanSpace ℝ (Fin n) => starRingEnd ℂ (g' x)) =
        (Complex.conjLIE : ℂ → ℂ) ∘ (g' : EuclideanSpace ℝ (Fin n) → ℂ) := rfl
    rw [e]
    exact Complex.conjLIE.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) _ x _
  rw [e2]
  gcongr

theorem integrable_derivBound (g g' : Sch (Fin n)) (j : ℕ) : Integrable (derivBound g g' j) := by
  unfold derivBound
  refine MeasureTheory.integrable_finsetSum _ fun i _ => ?_
  have := SchwartzMap.integrable_pow_mul_iteratedFDeriv volume g' 0 (j - i)
  simp only [pow_zero, one_mul] at this
  exact this.const_mul _

theorem integrable_prodTrans (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖) := by
  refine (integrable_derivBound g g' j).mono'
    ((contDiff_prodTrans g g' p).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact norm_iteratedFDeriv_prodTrans_le g g' p j x

theorem integral_prodTrans_le (g g' : Sch (Fin n)) (p : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    ∫ x, ‖iteratedFDeriv ℝ j (prodTrans g g' p) x‖ ≤ ∫ x, derivBound g g' j x :=
  integral_mono (integrable_prodTrans g g' p j) (integrable_derivBound g g' j)
    (fun x => norm_iteratedFDeriv_prodTrans_le g g' p j x)

theorem fourier_bound (g g' : Sch (Fin n)) (p ξ : EuclideanSpace ℝ (Fin n)) (N m : ℕ) (hm : m ≤ N) :
    ‖ξ‖ ^ m * ‖𝓕 (prodTrans g g' p) ξ‖ ≤
      2 ^ m * ∑ j ∈ Finset.range (N + 1), ∫ x, derivBound g g' j x := by
  have h'f : ∀ (k' m' : ℕ), (k' : ℕ∞) ≤ 0 → (m' : ℕ∞) ≤ (m : ℕ∞) →
      Integrable (fun v => ‖v‖ ^ k' * ‖iteratedFDeriv ℝ m' (prodTrans g g' p) v‖) := by
    intro k' m' hk' _
    have hk0 : k' = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hk'
    subst hk0
    simpa using integrable_prodTrans g g' p m'
  have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := prodTrans g g' p) (K := 0)
    (N := m) ((contDiff_prodTrans g g' p).of_le (by exact_mod_cast le_top)) h'f (k := 0) (n := m)
    le_rfl le_rfl ξ
  have hsum : (∑ q ∈ Finset.range (0 + 1) ×ˢ Finset.range (m + 1),
      ∫ v, ‖v‖ ^ q.1 * ‖iteratedFDeriv ℝ q.2 (prodTrans g g' p) v‖)
      = ∑ j ∈ Finset.range (m + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖ := by
    rw [Finset.sum_product]; simp
  rw [hsum, norm_iteratedFDeriv_zero] at key
  simp only [pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add] at key
  refine key.trans ?_
  gcongr
  calc ∑ j ∈ Finset.range (m + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖
      ≤ ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j (prodTrans g g' p) v‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
          (fun _ _ _ => integral_nonneg fun _ => norm_nonneg _)
    _ ≤ ∑ j ∈ Finset.range (N + 1), ∫ x, derivBound g g' j x :=
        Finset.sum_le_sum fun j _ => integral_prodTrans_le g g' p j

theorem one_add_pow_le (t : ℝ) (ht : 0 ≤ t) (N : ℕ) : (1 + t) ^ N ≤ 2 ^ N * (1 + t ^ N) := by
  have h1 : 1 + t ≤ 2 * max 1 t := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 t) ^ N ≤ 1 + t ^ N := by
    rcases le_total 1 t with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg ht N]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg ht N]
  calc (1 + t) ^ N ≤ (2 * max 1 t) ^ N := pow_le_pow_left₀ (by linarith) h1 N
    _ = 2 ^ N * (max 1 t) ^ N := mul_pow _ _ _
    _ ≤ 2 ^ N * (1 + t ^ N) := by gcongr

end GlobalTheory.RealWeil.CoefQDecay

theorem GlobalTheory.RealWeil.coef_qDecay : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ,
    ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖qPart w‖) ^ N ≤ C := by
  intro n g g' N
  open GlobalTheory.RealWeil.CoefQDecay in
  set T := ∑ j ∈ Finset.range (N + 1), ∫ x, derivBound g g' j x with hT
  refine ⟨2 ^ N * (T + 2 ^ N * T), fun w => ?_⟩
  rw [GlobalTheory.RealWeil.CoefQDecay.norm_integral_eq]
  set F := ‖𝓕 (GlobalTheory.RealWeil.CoefQDecay.prodTrans g g' (pPart w)) (-qPart w)‖ with hF
  have h0 := GlobalTheory.RealWeil.CoefQDecay.fourier_bound g g' (pPart w) (-qPart w) N 0 (Nat.zero_le _)
  have hN := GlobalTheory.RealWeil.CoefQDecay.fourier_bound g g' (pPart w) (-qPart w) N N le_rfl
  rw [norm_neg] at hN
  simp only [pow_zero, one_mul] at h0
  have hq := GlobalTheory.RealWeil.CoefQDecay.one_add_pow_le ‖qPart w‖ (norm_nonneg _) N
  have hF0 : 0 ≤ F := norm_nonneg _
  calc F * (1 + ‖qPart w‖) ^ N ≤ F * (2 ^ N * (1 + ‖qPart w‖ ^ N)) := by gcongr
    _ = 2 ^ N * (F + ‖qPart w‖ ^ N * F) := by ring
    _ ≤ 2 ^ N * (T + 2 ^ N * T) := by gcongr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecaySecondPartStatement
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coeff_decay_second_part : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖qPart w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.RealWeil.coef_qDecay | exact GlobalTheory.RealWeil.coef_qDecay | (intros; apply GlobalTheory.RealWeil.coef_qDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecayFirstPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecayFirstPart
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory

theorem one_add_pow_le_two_pow_mul (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (1 + a) ^ N ≤ 2 ^ N * (1 + a ^ N) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ ≤ 2 ^ N * (1 + a ^ N) := by
        have : 0 ≤ a ^ N := pow_nonneg ha N
        nlinarith [pow_pos (two_pos : (0:ℝ) < 2) N]
  · calc (1 + a) ^ N ≤ (2 * a) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
      _ = 2 ^ N * a ^ N := mul_pow _ _ _
      _ ≤ 2 ^ N * (1 + a ^ N) := by
        gcongr
        linarith

theorem one_add_norm_le_mul_of_add {E : Type*} [NormedAddCommGroup E] (x p : E) :
    1 + ‖p‖ ≤ (1 + ‖x + p‖) * (1 + ‖x‖) := by
  have h : ‖p‖ ≤ ‖x + p‖ + ‖x‖ := by
    have := norm_sub_le (x + p) x
    simpa using this
  nlinarith [norm_nonneg (x + p), norm_nonneg x, mul_nonneg (norm_nonneg (x + p)) (norm_nonneg x)]

theorem matrixCoeff_pPart_decay : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ,
    ∀ w : Fin n ⊕ Fin n → ℝ,
      ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖pPart w‖) ^ N ≤ C := by
  intro n g g' N
  set A : ℝ := 2 ^ (N, 0).1 * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) g with hA
  have hg : ∀ y, (1 + ‖y‖) ^ N * ‖g y‖ ≤ A := fun y => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, 0)) (k := N) (n := 0)
      le_rfl le_rfl g y
    rwa [norm_iteratedFDeriv_zero] at this
  set h : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (1 + ‖x‖) ^ N * ‖g' x‖ with hh
  have hint : Integrable h := by
    have i1 := (g'.integrable_pow_mul volume 0).add (g'.integrable_pow_mul volume N)
    refine (i1.const_mul (2 ^ N)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((continuous_const.add continuous_norm).pow N |>.mul g'.continuous.norm).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      simp only [hh, pow_zero, one_mul]
      calc (1 + ‖x‖) ^ N * ‖g' x‖ ≤ (2 ^ N * (1 + ‖x‖ ^ N)) * ‖g' x‖ :=
            mul_le_mul_of_nonneg_right (one_add_pow_le_two_pow_mul _ (norm_nonneg _) N) (norm_nonneg _)
        _ = 2 ^ N * (‖g' x‖ + ‖x‖ ^ N * ‖g' x‖) := by ring
  refine ⟨A * ∫ x, h x, fun w => ?_⟩
  set c : ℝ := (1 + ‖pPart w‖) ^ N with hc
  have hc0 : 0 ≤ c := by positivity
  have hpt : ∀ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c ≤ A * h x := fun x => by
    have e : ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ = ‖g (x + pPart w)‖ * ‖g' x‖ := by
      simp [rhoFun, norm_phase]
    rw [e, hc]
    have hp := pow_le_pow_left₀ (by positivity) (one_add_norm_le_mul_of_add x (pPart w)) N
    rw [mul_pow] at hp
    calc ‖g (x + pPart w)‖ * ‖g' x‖ * (1 + ‖pPart w‖) ^ N
        ≤ ‖g (x + pPart w)‖ * ‖g' x‖ * ((1 + ‖x + pPart w‖) ^ N * (1 + ‖x‖) ^ N) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((1 + ‖x + pPart w‖) ^ N * ‖g (x + pPart w)‖) * h x := by simp only [hh]; ring
      _ ≤ A * h x := mul_le_mul_of_nonneg_right (hg _) (by positivity)
  calc ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c
      ≤ (∫ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖) * c :=
        mul_le_mul_of_nonneg_right (norm_integral_le_integral_norm _) hc0
    _ = ∫ x, ‖rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * c := (integral_mul_const _ _).symm
    _ ≤ ∫ x, A * h x :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          (hint.const_mul A) (Filter.Eventually.of_forall hpt)
    _ = A * ∫ x, h x := integral_const_mul _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecayFirstPartStatement
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coeff_decay_first_part : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖pPart w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.matrixCoeff_pPart_decay | exact GlobalTheory.matrixCoeff_pPart_decay | (intros; apply GlobalTheory.matrixCoeff_pPart_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffContinuousRapidDecay
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap

namespace GlobalTheory
namespace MatrixCoeff

theorem norm_le_max_parts (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) : ‖w‖ ≤ max ‖pPart w‖ ‖qPart w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rcases i with j | j
  · exact le_max_of_le_left (by
      have := PiLp.norm_apply_le (pPart w) j
      simpa [pPart] using this)
  · exact le_max_of_le_right (by
      have := PiLp.norm_apply_le (qPart w) j
      simpa [qPart] using this)

theorem one_add_norm_pow_le_parts (n N : ℕ) (w : Fin n ⊕ Fin n → ℝ) :
    (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N + (1 + ‖qPart w‖) ^ N := by
  have h := norm_le_max_parts n w
  rcases le_total ‖pPart w‖ ‖qPart w‖ with h' | h'
  · rw [max_eq_right h'] at h
    have : (1 + ‖w‖) ^ N ≤ (1 + ‖qPart w‖) ^ N := by gcongr
    linarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖pPart w‖) N]
  · rw [max_eq_left h'] at h
    have : (1 + ‖w‖) ^ N ≤ (1 + ‖pPart w‖) ^ N := by gcongr
    linarith [pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ‖qPart w‖) N]

end MatrixCoeff

open MatrixCoeff

theorem matrixCoeff_continuous_rapidDecay : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖w‖) ^ N ≤ C := by
  intro n g g'
  refine ⟨GlobalTheory.T.continuous_matrix_coefficient n g g', fun N => ?_⟩
  obtain ⟨C1, h1⟩ := GlobalTheory.T.matrix_coeff_decay_first_part n g g' N
  obtain ⟨C2, h2⟩ := GlobalTheory.T.matrix_coeff_decay_second_part n g g' N
  refine ⟨C1 + C2, fun w => ?_⟩
  have := one_add_norm_pow_le_parts n N w
  have hn : 0 ≤ ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ := norm_nonneg _
  calc _ ≤ ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * ((1 + ‖pPart w‖) ^ N + (1 + ‖qPart w‖) ^ N) :=
        mul_le_mul_of_nonneg_left this hn
    _ ≤ C1 + C2 := by rw [mul_add]; exact add_le_add (h1 w) (h2 w)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffContinuousRapidDecayStatement
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coeff_continuous_rapid_decay : ∀ (n : ℕ) (g g' : Sch (Fin n)),
    Continuous (fun w : Fin n ⊕ Fin n → ℝ => ∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)) ∧
    ∀ N : ℕ, ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.matrixCoeff_continuous_rapidDecay | exact GlobalTheory.matrixCoeff_continuous_rapidDecay | (intros; apply GlobalTheory.matrixCoeff_continuous_rapidDecay <;> assumption)
end
