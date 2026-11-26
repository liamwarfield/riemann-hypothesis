module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.DiagonalIntegrandVanishesProof
noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace UpperTheory.Esk.DiagonalIntegrandLemmas

def D (A s : ℝ) : ℝ → ℂ := fun x => (A : ℂ) * x + (s : ℂ) * Complex.I

theorem D_apply (A s x : ℝ) : D A s x = (A : ℂ) * x + (s : ℂ) * Complex.I := rfl

theorem D_re (A s x : ℝ) : (D A s x).re = A * x := by simp [D]

theorem D_im (A s x : ℝ) : (D A s x).im = s := by simp [D]

theorem sq_norm_D (A s x : ℝ) : ‖D A s x‖ ^ 2 = A ^ 2 * x ^ 2 + s ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, D_re, D_im]; ring

theorem D_ne {A s : ℝ} (hs : s ≠ 0) (x : ℝ) : D A s x ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  rw [D_im] at this
  exact hs (by simpa using this)

theorem cont_D (A s : ℝ) : Continuous (D A s) := by
  unfold D
  exact (continuous_const.mul Complex.continuous_ofReal).add continuous_const

theorem one_le_norm_D {A s : ℝ} (hs : 1 ≤ s) (x : ℝ) : 1 ≤ ‖D A s x‖ := by
  have h := Complex.abs_im_le_norm (D A s x)
  rw [D_im, abs_of_pos (by linarith)] at h
  linarith

theorem bound {A s : ℝ} (hA : A ≠ 0) (hs : 1 ≤ s) {k : ℕ} (hk : 4 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖(D A s x ^ k)⁻¹‖ ≤ K / (1 + x ^ 2) ^ 2 := by
  set m := min (A ^ 2) 1 with hm
  have hm0 : 0 < m := lt_min (by positivity) one_pos
  refine ⟨(m ^ 2)⁻¹, by positivity, fun x => ?_⟩
  have h1 : m * (1 + x ^ 2) ≤ ‖D A s x‖ ^ 2 := by
    rw [sq_norm_D]
    have a1 := mul_le_mul_of_nonneg_right (min_le_left (A ^ 2) 1) (sq_nonneg x)
    have a2 := min_le_right (A ^ 2) 1
    nlinarith
  have h2 : ‖D A s x‖ ^ 4 ≤ ‖D A s x‖ ^ k := pow_le_pow_right₀ (one_le_norm_D hs x) hk
  have h3 : (m * (1 + x ^ 2)) ^ 2 ≤ ‖D A s x‖ ^ k := by
    calc (m * (1 + x ^ 2)) ^ 2 ≤ (‖D A s x‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
      _ = ‖D A s x‖ ^ 4 := by ring
      _ ≤ _ := h2
  rw [norm_inv, norm_pow]
  calc (‖D A s x‖ ^ k)⁻¹ ≤ ((m * (1 + x ^ 2)) ^ 2)⁻¹ := inv_anti₀ (by positivity) h3
    _ = (m ^ 2)⁻¹ / (1 + x ^ 2) ^ 2 := by rw [mul_pow, mul_inv, div_eq_mul_inv]

theorem integrable_of_bound {f : ℝ → ℂ} (hf : Continuous f) {K : ℝ} (_hK : 0 ≤ K)
    (h : ∀ x, ‖f x‖ ≤ K / (1 + x ^ 2)) : Integrable f := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hf.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [← div_eq_mul_inv]
  exact h x

theorem le_one_add_sq (x : ℝ) (K : ℝ) (hK : 0 ≤ K) : K / (1 + x ^ 2) ^ 2 ≤ K / (1 + x ^ 2) :=
  div_le_div_of_nonneg_left hK (by positivity) (by nlinarith [sq_nonneg x])

theorem integrable_D {A s : ℝ} (hA : A ≠ 0) (hs : 1 ≤ s) {k : ℕ} (hk : 4 ≤ k) :
    Integrable fun x => (D A s x ^ k)⁻¹ := by
  obtain ⟨K, hK, h⟩ := bound hA hs hk
  refine integrable_of_bound (((cont_D A s).pow k).inv₀ fun x => pow_ne_zero _ (D_ne (by linarith) x)) hK
    fun x => (h x).trans (le_one_add_sq x K hK)

theorem tendsto_norm_D {A s : ℝ} (hA : A ≠ 0) {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (fun x => ‖D A s x‖) l atTop := by
  refine tendsto_atTop_mono (fun x => ?_) (hl.const_mul_atTop (abs_pos.2 hA))
  have h := Complex.abs_re_le_norm (D A s x)
  rw [D_re, abs_mul] at h
  exact h

theorem tendsto_inv_D {A s : ℝ} (hA : A ≠ 0) {l : Filter ℝ} (hl : Tendsto (fun x : ℝ => |x|) l atTop)
    (n : ℕ) : Tendsto (fun x => (D A s x ^ (n + 1))⁻¹) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine (tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp
    (tendsto_norm_D (s := s) hA hl))).congr fun x => ?_
  simp [norm_inv, norm_pow]

theorem integral_D {A s : ℝ} (hA : A ≠ 0) (hs : 1 ≤ s) (n : ℕ) (hn : 4 ≤ n + 2) :
    ∫ x, (D A s x ^ (n + 2))⁻¹ = 0 := by
  have hs0 : s ≠ 0 := by linarith
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA
  have hn' : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hderiv : ∀ x, HasDerivAt (fun x => (-((n : ℂ) + 1) * A)⁻¹ * (D A s x ^ (n + 1))⁻¹)
      ((D A s x ^ (n + 2))⁻¹) x := by
    intro x
    have hD : HasDerivAt (D A s) (A : ℂ) x := by
      have := (((hasDerivAt_id x).ofReal_comp).const_mul (A : ℂ)).add_const ((s : ℂ) * Complex.I)
      simp only [id, Complex.ofReal_one, mul_one] at this
      exact this
    have h2 := ((hD.pow (n + 1)).fun_inv (pow_ne_zero _ (D_ne hs0 x))).const_mul (-((n : ℂ) + 1) * A)⁻¹
    refine h2.congr_deriv ?_
    have hx := D_ne (A := A) hs0 x
    simp only [Pi.pow_apply, Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  have key := integral_of_hasDerivAt_of_tendsto hderiv (integrable_D hA hs hn)
    (by simpa using (tendsto_inv_D (s := s) hA tendsto_abs_atBot_atTop n).const_mul (-((n : ℂ) + 1) * A)⁻¹)
    (by simpa using (tendsto_inv_D (s := s) hA tendsto_abs_atTop_atTop n).const_mul (-((n : ℂ) + 1) * A)⁻¹)
  rw [key, sub_self]

end UpperTheory.Esk.DiagonalIntegrandLemmas

open UpperTheory.Esk UpperTheory.Esk.DiagonalIntegrandLemmas

theorem UpperTheory.Esk.diagonal_integrand_vanishes_proof : UpperTheory.Esk.DiagonalIntegrandVanishes := by
  intro k hk g hb hc hne
  have hdet : g.val.det = g 0 0 * g 1 1 := by rw [det_eq, hb]; ring
  have hdet0 : g 0 0 * g 1 1 ≠ 0 := hdet ▸ g.det_ne_zero
  have ha : g 0 0 ≠ 0 := left_ne_zero_of_mul hdet0
  have hd : g 1 1 ≠ 0 := right_ne_zero_of_mul hdet0
  have hden : ∀ z : ℂ, den g z = ((g 1 1 : ℝ) : ℂ) := fun z => by simp [den, hc]
  have hnum : ∀ z : ℂ, num g z = ((g 0 0 : ℝ) : ℂ) * z := fun z => by simp [num, hb]
  have him : ∀ z : P, (g • z).1.im * z.1.im = g 0 0 * g 1 1 * (z.1.im ^ 2 / (g 1 1 * g 1 1)) := by
    intro z
    rw [coe_smul, im_div, hden, Complex.normSq_ofReal, hdet]; ring
  rcases lt_or_gt_of_ne hdet0 with hneg | hpos
  ·
    refine ⟨0, continuous_const, fun x y hy => ?_, integrable_zero _ _ _, by simp, by simp, Or.inl rfl⟩
    have : ¬ (0 < (pt x y hy).1.im * (g • pt x y hy).1.im) := by
      rw [mul_comm, him]
      have : 0 ≤ (pt x y hy).1.im ^ 2 / (g 1 1 * g 1 1) := div_nonneg (sq_nonneg _) (mul_self_nonneg _)
      nlinarith
    simp [q1, this]
  · set r : ℝ := g 0 0 / g 1 1 with hr
    have hr0 : 0 < r := by
      rw [hr]; rcases lt_or_gt_of_ne hd with h | h
      · exact div_pos_of_neg_of_neg (by nlinarith) h
      · exact div_pos (by nlinarith) h
    have hr1 : 1 - r ≠ 0 := by
      intro h; apply hne; rw [hr] at h
      field_simp at h; linarith
    have hs : (1 : ℝ) ≤ 1 + r := by linarith
    set c : ℂ := ((g 1 1 : ℝ) : ℂ) ^ k * ((|g.val.det| ^ (-(k : ℝ) / 2) : ℝ) : ℂ) with hcdef
    set E : ℂ := ((k : ℂ) - 1) / (4 * Real.pi) * (2 * Complex.I * (r : ℂ)) ^ k * c with hE
    have hc0 : c ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hd)) ?_
      have : 0 < |g.val.det| ^ (-(k : ℝ) / 2) :=
        Real.rpow_pos_of_pos (abs_pos.2 g.det_ne_zero) _
      exact_mod_cast this.ne'
    have hE0 : E ≠ 0 := by
      have hk1 : (k : ℂ) - 1 ≠ 0 := by
        have : (1 : ℂ) ≠ k := by exact_mod_cast (by omega : (1 : ℕ) ≠ k)
        exact sub_ne_zero.2 this.symm
      have hpi : (4 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
      exact mul_ne_zero (mul_ne_zero (div_ne_zero hk1 hpi)
        (pow_ne_zero _ (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hr'))) hc0
    have hs0 : (1 + r) ≠ 0 := by linarith
    refine ⟨fun x => E * (D (1 - r) (1 + r) x ^ k)⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact continuous_const.mul (((cont_D _ _).pow k).inv₀ fun x => pow_ne_zero _ (D_ne hs0 x))
    · intro x y hy
      have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
      have hd' : ((g 1 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
      have hz : (pt x y hy).1 = (y : ℂ) * ((x : ℂ) + Complex.I) := rfl
      have hw : (g • pt x y hy).1 = (r : ℂ) * ((y : ℂ) * ((x : ℂ) + Complex.I)) := by
        rw [coe_smul, hnum, hden, hz, hr]
        push_cast
        field_simp
      have hcw : conj (g • pt x y hy).1 = (r : ℂ) * ((y : ℂ) * ((x : ℂ) - Complex.I)) := by
        rw [hw]; simp [map_mul, Complex.conj_ofReal, sub_eq_add_neg]
      have hpos' : 0 < (pt x y hy).1.im * (g • pt x y hy).1.im := by
        rw [mul_comm, him]
        have : 0 < (pt x y hy).1.im ^ 2 / (g 1 1 * g 1 1) := by
          have : (pt x y hy).1.im ≠ 0 := (pt x y hy).2
          exact div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this))) (mul_self_pos.2 hd)
        exact mul_pos hpos this
      have hratio : ((g • pt x y hy).1 - conj (g • pt x y hy).1) / ((pt x y hy).1 - conj (g • pt x y hy).1)
          = (2 * Complex.I * (r : ℂ)) / D (1 - r) (1 + r) x := by
        rw [hcw, hw, hz, D_apply]
        have e1 : (r : ℂ) * ((y : ℂ) * ((x : ℂ) + Complex.I)) - (r : ℂ) * ((y : ℂ) * ((x : ℂ) - Complex.I))
            = (y : ℂ) * (2 * Complex.I * (r : ℂ)) := by ring
        have e2 : (y : ℂ) * ((x : ℂ) + Complex.I) - (r : ℂ) * ((y : ℂ) * ((x : ℂ) - Complex.I))
            = (y : ℂ) * (((1 - r : ℝ) : ℂ) * (x : ℂ) + ((1 + r : ℝ) : ℂ) * Complex.I) := by
          push_cast; ring
        rw [e1, e2, mul_div_mul_left _ _ hy']
      simp only [q1, if_pos hpos', j1, hden]
      rw [hratio, div_pow, hE, hcdef]
      ring
    · obtain ⟨K, hK, h⟩ := bound hr1 hs hk
      refine integrable_of_bound (continuous_const.mul (((cont_D _ _).pow k).inv₀
        fun x => pow_ne_zero _ (D_ne hs0 x))) (mul_nonneg (norm_nonneg E) hK) fun x => ?_
      rw [norm_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left ((h x).trans (le_one_add_sq x K hK)) (norm_nonneg E)
    · obtain ⟨K, hK, h⟩ := bound hr1 hs hk
      have hcont : Continuous fun x : ℝ => Real.log (1 + x ^ 2) :=
        (continuous_const.add (continuous_pow 2)).log fun x => (by positivity : (0:ℝ) < 1 + x ^ 2).ne'
      refine integrable_of_bound ((Complex.continuous_ofReal.comp hcont).mul (continuous_const.mul
        (((cont_D _ _).pow k).inv₀ fun x => pow_ne_zero _ (D_ne hs0 x))))
        (mul_nonneg (norm_nonneg E) hK) fun x => ?_
      have hl0 : 0 ≤ Real.log (1 + x ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg x])
      have hl1 : Real.log (1 + x ^ 2) ≤ 1 + x ^ 2 := by
        have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + x ^ 2)
        linarith
      have hp : (0 : ℝ) < 1 + x ^ 2 := by positivity
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl0]
      calc Real.log (1 + x ^ 2) * (‖E‖ * ‖(D (1 - r) (1 + r) x ^ k)⁻¹‖)
          ≤ (1 + x ^ 2) * (‖E‖ * (K / (1 + x ^ 2) ^ 2)) :=
            mul_le_mul hl1 (mul_le_mul_of_nonneg_left (h x) (norm_nonneg E)) (by positivity) hp.le
        _ = ‖E‖ * K / (1 + x ^ 2) := by field_simp
    · obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
      rw [integral_const_mul, integral_D hr1 hs n hk, mul_zero]
    · exact Or.inr fun x => mul_ne_zero hE0 (inv_ne_zero (pow_ne_zero _ (D_ne hs0 x)))
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.CayleyTransformProof
noncomputable section

open MeasureTheory Set Complex Metric
open scoped ComplexConjugate Real

namespace UpperTheory.Esk.CayleyTransform

def cay (w : ℂ) : ℂ := Complex.I * (1 + w) / (1 - w)

theorem im_cay (w : ℂ) (hw : w ≠ 1) : (cay w).im = (1 - normSq w) / normSq (1 - w) := by
  have hn : normSq (1 - w) ≠ 0 := (normSq_pos.2 (sub_ne_zero.2 hw.symm)).ne'
  rw [cay, Complex.div_im]
  simp only [normSq_apply, mul_im, mul_re, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im] at hn ⊢
  field_simp
  ring

theorem hasDerivAt_cay (w : ℂ) (hw : w ≠ 1) : HasDerivAt cay (2 * Complex.I / (1 - w) ^ 2) w := by
  have h1 : (1 - w) ≠ 0 := sub_ne_zero.2 hw.symm
  have := (((hasDerivAt_id w).const_add 1).const_mul Complex.I).div ((hasDerivAt_id w).const_sub 1) h1
  have hf : cay = (fun y => Complex.I * (1 + id y)) / (fun x => 1 - id x) := by
    funext x; simp [cay]
  rw [hf]
  refine this.congr_deriv ?_
  show (Complex.I * 1 * (1 - w) - Complex.I * (1 + w) * -1) / (1 - w) ^ 2 = 2 * Complex.I / (1 - w) ^ 2
  ring

theorem det_cay (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = normSq c := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

theorem ne_one_of_mem (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 := by
  rintro rfl; simp at hw

theorem normSq_lt_of_mem (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : normSq w < 1 := by
  rw [mem_ball_zero_iff] at hw
  rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]

theorem image_cay : cay '' ball (0 : ℂ) 1 = {t : ℂ | 0 < t.im} := by
  ext t
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 := ne_one_of_mem w hw
    have h2 := normSq_lt_of_mem w hw
    simp only [mem_ofPred_eq]
    rw [im_cay w h1]
    exact div_pos (by linarith) (normSq_pos.2 (sub_ne_zero.2 h1.symm))
  · intro ht
    simp only [mem_ofPred_eq] at ht
    have hd : t + Complex.I ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    refine ⟨(t - Complex.I) / (t + Complex.I), ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hd)]
      rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
      simp only [normSq_apply, add_re, add_im, sub_re, sub_im, I_re, I_im]
      nlinarith
    · have h3 : 1 - (t - Complex.I) / (t + Complex.I) ≠ 0 := by
        rw [one_sub_div hd]; simp [hd]
      rw [cay, div_eq_iff h3]
      field_simp
      ring

theorem injOn_cay : InjOn cay (ball (0 : ℂ) 1) := by
  intro a ha b hb hab
  have h1 : 1 - a ≠ 0 := sub_ne_zero.2 (ne_one_of_mem a ha).symm
  have h2 : 1 - b ≠ 0 := sub_ne_zero.2 (ne_one_of_mem b hb).symm
  simp only [cay] at hab
  rw [div_eq_div_iff h1 h2] at hab
  have : Complex.I * (2 * (a - b)) = 0 := by linear_combination hab
  simpa [sub_eq_zero] using this

theorem step2 (g : ℂ → ℂ) (hg : IntegrableOn g {t : ℂ | 0 < t.im}) :
    IntegrableOn (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w)) (ball 0 1) ∧
    ∫ t in {t : ℂ | 0 < t.im}, g t = ∫ w in ball (0 : ℂ) 1, ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w) := by
  have hs : MeasurableSet (ball (0 : ℂ) 1) := measurableSet_ball
  have hf' : ∀ w ∈ ball (0 : ℂ) 1, HasFDerivWithinAt cay
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ)
      (ball 0 1) w := fun w hw =>
    ((hasDerivAt_cay w (ne_one_of_mem w hw)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hdet : ∀ w ∈ ball (0 : ℂ) 1,
      |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ).det|
        = 4 / normSq (1 - w) ^ 2 := by
    intro w hw
    rw [det_cay, abs_of_nonneg (normSq_nonneg _), map_div₀, map_pow, map_mul]
    simp [normSq_apply]
    norm_num
  have hpt : EqOn (fun w => |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ).det| • g (cay w))
      (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) * g (cay w)) (ball 0 1) := by
    intro w hw
    simp only
    rw [hdet w hw, Complex.real_smul]
  rw [← image_cay] at hg ⊢
  constructor
  · exact ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hf' injOn_cay g).1 hg).congr_fun
      hpt hs
  · rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs hf' injOn_cay]
    exact setIntegral_congr_fun hs hpt

theorem step1 (h : P → ℂ) (h0 : ∀ z : P, z.1.im < 0 → h z = 0) (hi : Integrable h) :
    IntegrableOn (fun t : ℂ => ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t) {t : ℂ | 0 < t.im} ∧
    ∫ z, h z = ∫ t in {t : ℂ | 0 < t.im}, ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t := by
  set S : Set ℂ := {t | t.im ≠ 0} with hSdef
  have hS : MeasurableSet S := (isOpen_ne_fun continuous_im continuous_const).measurableSet
  set g : ℂ → ℂ := fun t => ((1 / t.im ^ 2 : ℝ) : ℂ) * ext1 h t with hg
  have hρ : Measurable (fun z : S => ENNReal.ofReal (1 / z.1.im ^ 2)) := by fun_prop
  have hfin : ∀ᵐ z ∂(Measure.comap (Subtype.val : S → ℂ) volume), ENNReal.ofReal (1 / z.1.im ^ 2) < ⊤ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  set h' : S → ℂ := fun z => h ⟨z.1, z.2⟩ with hh'
  have key : (fun z : S => (ENNReal.ofReal (1 / z.1.im ^ 2)).toReal • h' z) = g ∘ Subtype.val := by
    funext z
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hz : (z : ℂ).im ≠ 0 := z.2
    simp [g, ext1, hz, h', Complex.real_smul]
  have hi' : Integrable h'
      ((Measure.comap (Subtype.val : S → ℂ) volume).withDensity fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := hi
  have iS : IntegrableOn g S := by
    rw [integrableOn_iff_comap_subtypeVal hS, ← key]
    exact (integrable_withDensity_iff_integrable_smul' hρ hfin).1 hi'
  have hsub : {t : ℂ | 0 < t.im} ⊆ S := fun t ht => ne_of_gt ht
  refine ⟨iS.mono_set hsub, ?_⟩
  have e1 : ∫ z, h z = ∫ z : S, h' z ∂((Measure.comap (Subtype.val : S → ℂ) volume).withDensity
      fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := rfl
  rw [e1, integral_withDensity_eq_integral_toReal_smul hρ hfin, key]
  change ∫ z : S, g z ∂(Measure.comap Subtype.val volume) = _
  rw [integral_subtype_comap hS g]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f := g) hS hsub ?_
  intro t ⟨ht1, ht2⟩
  have hlt : t.im < 0 := lt_of_le_of_ne (not_lt.1 ht2) ht1
  simp [g, ext1, h0 ⟨t, ht1⟩ hlt]

theorem step3 (F : ℂ → ℂ) (hF : IntegrableOn F (ball 0 1)) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2)) (Ioo 0 1 ×ˢ Ioo (-π) π) ∧
    ∫ w in ball (0 : ℂ) 1, F w = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π, (p.1 : ℂ) * F (circleMap 0 p.1 p.2) := by
  have hp : MeasurePreserving Complex.measurableEquivRealProd.symm volume volume :=
    Complex.volume_preserving_equiv_real_prod.symm
  have hSm : MeasurableSet (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := measurableSet_Ioo.prod measurableSet_Ioo
  have he : ∀ q : ℝ × ℝ, ‖Complex.measurableEquivRealProd.symm q‖ = √(q.1 ^ 2 + q.2 ^ 2) := by
    intro q
    change ‖Complex.equivRealProd.symm q‖ = _
    rw [Complex.equivRealProd_symm_apply, Complex.norm_def, Complex.normSq_add_mul_I]
  have hsub : polarCoord.symm '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) ⊆
      Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    rintro _ ⟨p, hp', rfl⟩
    simp only [mem_preimage, mem_ball_zero_iff]
    rw [measurableEquivRealProd_symm_polarCoord_symm_apply, norm_polarCoord_symm, abs_of_pos hp'.1.1]
    exact hp'.1.2
  have hae : polarCoord.symm '' (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) =ᵐ[volume]
      Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1 := by
    filter_upwards [polarCoord_source_ae_eq_univ] with q hq
    have hq' : q ∈ polarCoord.source := hq.mpr (by trivial)
    constructor
    · exact fun h => hsub h
    · intro hqT
      have hm := polarCoord.map_source hq'
      refine ⟨polarCoord q, ⟨⟨hm.1, ?_⟩, hm.2⟩, polarCoord.left_inv hq'⟩
      change Complex.measurableEquivRealProd.symm q ∈ ball (0 : ℂ) 1 at hqT
      rw [mem_ball_zero_iff, he] at hqT
      simpa using hqT
  have hG : IntegrableOn (F ∘ Complex.measurableEquivRealProd.symm)
      (Complex.measurableEquivRealProd.symm ⁻¹' ball 0 1) :=
    (hp.integrableOn_comp_preimage Complex.measurableEquivRealProd.symm.measurableEmbedding).2 hF
  have hG' := hG.mono_set hsub
  have hder : ∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π,
      HasFDerivWithinAt polarCoord.symm (fderivPolarCoordSymm p) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) p :=
    fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt
  have hinj : InjOn polarCoord.symm (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) :=
    polarCoord.symm.injOn.mono (fun p hp => show p ∈ polarCoord.target from ⟨hp.1.1, hp.2⟩)
  have hpt : EqOn (fun p : ℝ × ℝ => |(fderivPolarCoordSymm p).det| •
      (F ∘ Complex.measurableEquivRealProd.symm) (polarCoord.symm p))
      (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2)) (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
    intro p hp
    simp only
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1.1, Function.comp_apply,
      measurableEquivRealProd_symm_polarCoord_symm_apply, Complex.polarCoord_symm_apply,
      Complex.real_smul]
    congr 2
    rw [circleMap, zero_add, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  constructor
  · exact ((integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hSm hder hinj _).1 hG').congr_fun
      hpt hSm
  · rw [← hp.setIntegral_preimage_emb Complex.measurableEquivRealProd.symm.measurableEmbedding F (ball 0 1),
      ← setIntegral_congr_set hae,
      integral_image_eq_integral_abs_det_fderiv_smul volume hSm hder hinj]
    exact setIntegral_congr_fun hSm hpt

end UpperTheory.Esk.CayleyTransform

open UpperTheory.Esk.CayleyTransform in
theorem UpperTheory.Esk.cayley_transform_proof : UpperTheory.Esk.B2 := by
  intro h h0 hi
  obtain ⟨i1, e1⟩ := step1 h h0 hi
  obtain ⟨i2, e2⟩ := step2 _ i1
  set F : ℂ → ℂ := fun w => ((4 / (1 - normSq w) ^ 2 : ℝ) : ℂ) * ext1 h (cay w) with hF
  have eqD : EqOn (fun w => ((4 / normSq (1 - w) ^ 2 : ℝ) : ℂ) *
      (((1 / (cay w).im ^ 2 : ℝ) : ℂ) * ext1 h (cay w))) F (ball 0 1) := by
    intro w hw
    have hw1 : normSq w < 1 := by
      rw [mem_ball_zero_iff] at hw
      rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    have hne : w ≠ 1 := by rintro rfl; simp at hw1
    have hn : 0 < normSq (1 - w) := normSq_pos.2 (sub_ne_zero.2 hne.symm)
    have h1 : 0 < 1 - normSq w := by linarith
    simp only [F]
    rw [im_cay w hne, ← mul_assoc, ← ofReal_mul]
    congr 2
    field_simp
  have i3 := i2.congr_fun eqD measurableSet_ball
  obtain ⟨i4, e4⟩ := step3 F i3
  have eqS : EqOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F (circleMap 0 p.1 p.2))
      (fun p : ℝ × ℝ => ((4 * p.1 / (1 - p.1 ^ 2) ^ 2 : ℝ) : ℂ) *
        ext1 h (Complex.I * (1 + circleMap 0 p.1 p.2) / (1 - circleMap 0 p.1 p.2)))
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π) := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hc : normSq (circleMap 0 r θ) = r ^ 2 := by
      rw [normSq_eq_norm_sq, norm_circleMap_zero, abs_of_pos hr.1]
    simp only [F, hc, cay]
    push_cast
    ring
  refine ⟨i4.congr_fun eqS (measurableSet_Ioo.prod measurableSet_Ioo), ?_⟩
  rw [e1, e2, setIntegral_congr_fun measurableSet_ball eqD, e4]
  exact setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) eqS
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicBallVolumeProof
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HyperbolicBallVolume

open UpperTheory.Esk

def F (y : ℝ) : ℝ := (1 + y ^ (-(1 / 2 : ℝ))) / (1 + y) ^ 2

theorem F_int : IntegrableOn F (Ioi 0) := by
  have hm : Measurable F := by unfold F; fun_prop
  have h1 : IntegrableOn F (Ioo 0 2) := by
    have hg : IntegrableOn (fun y : ℝ => 1 + y ^ (-(1 / 2 : ℝ))) (Ioo 0 2) :=
      (integrableOn_const (by simp)).add ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).2 (by norm_num))
    refine hg.mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy0 : 0 < y := hy.1
    have hp : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hy0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity)]
    unfold F
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg y]
  have h2 : IntegrableOn F (Ioi 1) := by
    have hg : IntegrableOn (fun y : ℝ => 2 * y ^ (-2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2
    refine hg.mono' hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : 0 < y := by linarith
    have hp : y ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by norm_num)
    have hp0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hy0.le _
    have e : y ^ (-2 : ℝ) = 1 / y ^ 2 := by
      rw [Real.rpow_neg hy0.le, one_div]; norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold F; positivity), e]
    unfold F
    rw [div_le_iff₀ (by positivity)]
    have : 2 ≤ 2 * (1 / y ^ 2) * (1 + y) ^ 2 := by
      rw [mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; nlinarith
    linarith
  exact (h1.union h2).mono_set (fun y (hy : 0 < y) => by
    by_cases h : y < 2
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr (show (1 : ℝ) < y by linarith))

def A : ℝ≥0∞ := ∫⁻ x : ℝ, ENNReal.ofReal ((1 + x ^ 2)⁻¹)

theorem A_lt : A < ∞ := integrable_inv_one_add_sq.lintegral_lt_top

theorem x_int {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ENNReal.ofReal ((1 + (y * x) ^ 2)⁻¹) = ENNReal.ofReal y⁻¹ * A := by
  have h := Real.map_volume_mul_left hy.ne'
  have hm : Measurable fun x : ℝ => ENNReal.ofReal ((1 + x ^ 2)⁻¹) := by fun_prop
  calc ∫⁻ x : ℝ, ENNReal.ofReal ((1 + (y * x) ^ 2)⁻¹)
      = ∫⁻ x, ENNReal.ofReal ((1 + x ^ 2)⁻¹) ∂(Measure.map (y * ·) volume) :=
        (lintegral_map hm (measurable_const_mul y)).symm
    _ = ENNReal.ofReal y⁻¹ * A := by
        rw [h, lintegral_smul_measure, smul_eq_mul, abs_of_pos (inv_pos.2 hy), A]

theorem kap_pt {x y : ℝ} (hy : 0 < y) :
    kap iP (pt x y hy.ne') = 4 * y / ((y * x) ^ 2 + (1 + y) ^ 2) := by
  have hn : ‖iP.1 - conj (pt x y hy.ne').1‖ ^ 2 = (y * x) ^ 2 + (1 + y) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [iP, pt]; ring
  have him : 0 < iP.1.im * (pt x y hy.ne').1.im := by simp [iP, pt, hy]
  rw [kap, if_pos him, hn]
  simp [iP, pt]

theorem kap_neg (w : P) (hw : w.1.im < 0) : kap iP w = 0 := by
  rw [kap, if_neg]
  simp [iP]; linarith

theorem kap_sq_le {x y : ℝ} (hy : 0 < y) :
    kap iP (pt x y hy.ne') ^ 2 ≤ 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ := by
  rw [kap_pt hy]
  set D := (y * x) ^ 2 + (1 + y) ^ 2
  have hD1 : 1 + (y * x) ^ 2 ≤ D := by simp only [D]; nlinarith
  have hD2 : (1 + y) ^ 2 ≤ D := by simp only [D]; nlinarith [sq_nonneg (y * x)]
  have hp : 0 < 1 + (y * x) ^ 2 := by positivity
  have hq : 0 < (1 + y) ^ 2 := by positivity
  have e : 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ = (4 * y) ^ 2 / ((1 + (y * x) ^ 2) * (1 + y) ^ 2) := by
    field_simp; ring
  rw [e, div_pow]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc (1 + (y * x) ^ 2) * (1 + y) ^ 2 ≤ D * D := mul_le_mul hD1 hD2 hq.le (by positivity)
    _ = D ^ 2 := by ring

def H (w : P) : ℝ≥0∞ := ENNReal.ofReal (kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))))

theorem H_meas (hc : Continuous fun p : P × P => kap p.1 p.2) : Measurable H := by
  have h1 : Measurable fun w : P => kap iP w :=
    (hc.comp (continuous_const.prodMk continuous_id)).measurable
  have h2 : Measurable fun w : P => |w.1.im| :=
    (Complex.continuous_im.comp continuous_subtype_val).abs.measurable
  unfold H
  exact ENNReal.measurable_ofReal.comp ((h1.pow_const 2).mul (measurable_const.add (h2.pow_const _)))

def B (y : ℝ) : ℝ≥0∞ :=
  if 0 < y then ENNReal.ofReal (16 * y ^ 2 / ((1 + y) ^ 2) * (1 + y ^ (-(1 / 2 : ℝ)))) * (ENNReal.ofReal y⁻¹ * A) else 0

theorem inner_le (y : ℝ) (hy : y ≠ 0) :
    ∫⁻ x : ℝ, H (pt x y hy) ≤ B y := by
  rcases lt_or_gt_of_ne hy with hn | hp
  · have : ∀ x, H (pt x y hy) = 0 := by
      intro x
      rw [H, kap_neg _ (by simp [pt, hn])]
      simp
    simp [this]
  · rw [B, if_pos hp, ← x_int hp, ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_mono fun x => ?_
    rw [H, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have him : |(pt x y hy).1.im| = y := by simp [pt, abs_of_pos hp]
    rw [him]
    have h := kap_sq_le (x := x) hp
    have hp0 : 0 ≤ y ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp.le _
    calc kap iP (pt x y hy) ^ 2 * (1 + y ^ (-(1 / 2 : ℝ)))
        ≤ 16 * y ^ 2 / ((1 + y) ^ 2) * (1 + (y * x) ^ 2)⁻¹ * (1 + y ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring

theorem H_lt (h5 : UpperHalfPlaneMeasureCoordinates) (hc : Continuous fun p : P × P => kap p.1 p.2) : ∫⁻ w, H w < ∞ := by
  obtain ⟨hmp, -, hcont⟩ := h5
  have hHm := H_meas hc
  have hBm : Measurable B := by
    unfold B
    refine Measurable.ite measurableSet_Ioi ?_ measurable_const
    fun_prop
  have hs : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have : SigmaFinite (Measure.comap Subtype.val (volume : Measure ℝ) : Measure {y : ℝ // y ≠ 0}) := by
    refine SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable ?_
    convert (inferInstance : SigmaFinite ((volume : Measure ℝ).restrict {y : ℝ | y ≠ 0})) using 1
    all_goals first | rfl | exact map_comap_subtype_coe hs _
  have e := lintegral_prod_symm (μ := volume)
    (ν := (Measure.comap Subtype.val volume).withDensity fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|))
    (fun p : ℝ × {y : ℝ // y ≠ 0} => H (pt p.1 p.2.1 p.2.2)) (hHm.comp hcont.measurable).aemeasurable
  rw [← hmp.lintegral_comp hHm]
  refine lt_of_eq_of_lt e ?_
  calc ∫⁻ y : {y : ℝ // y ≠ 0}, ∫⁻ x : ℝ, H (pt x y.1 y.2) ∂volume
        ∂((Measure.comap Subtype.val volume).withDensity fun y => ENNReal.ofReal (1 / |y.1|))
      ≤ ∫⁻ y : {y : ℝ // y ≠ 0}, B y.1
        ∂((Measure.comap Subtype.val volume).withDensity fun y => ENNReal.ofReal (1 / |y.1|)) :=
        lintegral_mono fun y => inner_le y.1 y.2
    _ = ∫⁻ y : {y : ℝ // y ≠ 0}, ENNReal.ofReal (1 / |y.1|) * B y.1 ∂(Measure.comap Subtype.val volume) := by
        refine (lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (hBm.comp measurable_subtype_coe)).trans ?_
        rfl
    _ = ∫⁻ y in {y : ℝ | y ≠ 0}, ENNReal.ofReal (1 / |y|) * B y :=
        lintegral_subtype_comap hs (fun y => ENNReal.ofReal (1 / |y|) * B y)
    _ ≤ ∫⁻ y, (Ioi (0 : ℝ)).indicator (fun y => ENNReal.ofReal (16 * F y) * A) y := by
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
        by_cases hy : 0 < y
        · rw [indicator_of_mem (show y ∈ Ioi 0 from hy), B, if_pos hy, abs_of_pos hy, ← mul_assoc, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          refine le_of_eq (congrArg (· * A) (congrArg ENNReal.ofReal ?_))
          unfold F
          field_simp
        · simp [B, hy]
    _ = ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (16 * F y) * A := lintegral_indicator measurableSet_Ioi _
    _ = (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (16 * F y)) * A :=
        lintegral_mul_const _ (by unfold F; fun_prop)
    _ < ∞ := ENNReal.mul_lt_top (F_int.const_mul 16).lintegral_lt_top A_lt

theorem rp_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) {k : ℕ} (hk : 4 ≤ k) : t ^ ((k : ℝ) / 2) ≤ t ^ 2 := by
  have hk2 : (2 : ℝ) ≤ (k : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rcases h0.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by linarith)]
    positivity
  · have := Real.rpow_le_rpow_of_exponent_ge h h1 hk2
    simpa using this

end UpperTheory.Esk.HyperbolicBallVolume

open UpperTheory.Esk UpperTheory.Esk.HyperbolicBallVolume in
theorem UpperTheory.Esk.hyperbolic_ball_volume_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.B6 := by
  intro h1a h1b h1c h5 k hk
  have hc := h1c.2.2.2.2.1
  have hfin := H_lt h5 hc
  refine ⟨(∫⁻ w, H w).toNNReal, fun z => ?_⟩
  rw [ENNReal.coe_toNNReal hfin.ne]
  obtain ⟨g, hg0, hg1, hgz⟩ := h1c.2.2.2.2.2 z
  subst hgz
  have hmp := (h1a.2.2 g).2
  have him : ∀ w : P, (g • w).1.im = g.val.det * w.1.im := by
    intro w
    have hden : den g w.1 = 1 := by simp [den, hg0, hg1]
    rw [coe_smul, im_div, hden, Complex.normSq_one, div_one]
  have hdet : g.val.det ≠ 0 := g.det_ne_zero
  have hkc : ∀ z : P, Continuous fun w : P => kap z w := fun z =>
    hc.comp (continuous_const.prodMk continuous_id)
  have hima : Measurable fun w : P => |w.1.im| :=
    (Complex.continuous_im.comp continuous_subtype_val).abs.measurable
  have hb := h1c.1
  have hkinv := h1b.2.2.2.1 g iP
  constructor
  · calc ∫⁻ w, ENNReal.ofReal (kap (g • iP) w ^ ((k : ℝ) / 2))
        = ∫⁻ w, ENNReal.ofReal (kap (g • iP) (g • w) ^ ((k : ℝ) / 2)) :=
          (hmp.lintegral_comp (ENNReal.measurable_ofReal.comp ((hkc _).measurable.pow_const _))).symm
      _ ≤ ∫⁻ w, H w := by
          refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
          rw [hkinv w]
          obtain ⟨h0, h1, -⟩ := hb iP w
          have hp0 : 0 ≤ |w.1.im| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
          calc kap iP w ^ ((k : ℝ) / 2) ≤ kap iP w ^ 2 := rp_le h0 h1 hk
            _ ≤ kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))) :=
              le_mul_of_one_le_right (by positivity) (by linarith)
  · calc ∫⁻ w, ENNReal.ofReal (kap (g • iP) w ^ ((k : ℝ) / 2) * (|(g • iP).1.im| / |w.1.im|) ^ ((1 : ℝ) / 2))
        = ∫⁻ w, ENNReal.ofReal (kap (g • iP) (g • w) ^ ((k : ℝ) / 2) *
            (|(g • iP).1.im| / |(g • w).1.im|) ^ ((1 : ℝ) / 2)) :=
          (hmp.lintegral_comp (ENNReal.measurable_ofReal.comp (((hkc _).measurable.pow_const _).mul
            ((measurable_const.div hima).pow_const _)))).symm
      _ ≤ ∫⁻ w, H w := by
          refine lintegral_mono fun w => ENNReal.ofReal_le_ofReal ?_
          rw [hkinv w, him, him]
          obtain ⟨h0, h1, -⟩ := hb iP w
          have e : |g.val.det * iP.1.im| / |g.val.det * w.1.im| = |w.1.im|⁻¹ := by
            rw [show iP.1.im = 1 by simp [iP], mul_one, abs_mul, div_mul_eq_div_div, div_self (abs_ne_zero.2 hdet),
              one_div]
          rw [e, Real.inv_rpow (abs_nonneg _), ← Real.rpow_neg (abs_nonneg _)]
          have hp0 : 0 ≤ |w.1.im| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
          have hk' := rp_le h0 h1 hk
          have : (-((1 : ℝ) / 2)) = -(1 / 2 : ℝ) := rfl
          calc kap iP w ^ ((k : ℝ) / 2) * |w.1.im| ^ (-((1 : ℝ) / 2))
              ≤ kap iP w ^ 2 * |w.1.im| ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hk' hp0
            _ ≤ kap iP w ^ 2 * (1 + |w.1.im| ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
end
end
