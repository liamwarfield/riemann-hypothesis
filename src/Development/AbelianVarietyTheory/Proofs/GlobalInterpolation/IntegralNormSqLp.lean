module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralNormSqLp
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped FourierTransform SchwartzMap Real

namespace GlobalTheory.GallagherLemma

theorem continuous_fourier {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf

theorem fourier_ae_eq {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    𝓕 f =ᵐ[volume] (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) := by
  refine ae_eq_of_integral_contDiff_smul_eq (continuous_fourier hf).locallyIntegrable
    ((Lp.memLp _).locallyIntegrable (by norm_num)) ?_
  intro g hg hc
  have hc' : HasCompactSupport (fun x => (g x : ℂ)) := hc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  have hg' := Complex.ofRealCLM.contDiff.comp hg
  set φ : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hg' with hφ
  have hφx : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 := congrArg (fun D => D φ) (Lp.fourier_toTemperedDistribution_eq (h2.toLp f))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
  have h3 : ∫ x, (𝓕 φ) x • f x = ∫ x, φ x • 𝓕 f x := by
    simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner φ.integrable hf
  have h4 : ∫ x, (𝓕 φ) x • (h2.toLp f) x = ∫ x, (𝓕 φ) x • f x := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [h4, h3] at h1
  simpa [hφx] using h1

theorem integral_norm_sq_Lp (F : Lp ℂ 2 (volume : Measure ℝ)) : ∫ x, ‖F x‖ ^ 2 = ‖F‖ ^ 2 := by
  have := L2.inner_def (𝕜 := ℂ) F F
  rw [inner_self_eq_norm_sq_to_K] at this
  simp only [inner_self_eq_norm_sq_to_K] at this
  have h : ((∫ x, ‖F x‖ ^ 2 : ℝ) : ℂ) = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    push_cast
    exact this.symm
  exact_mod_cast h

theorem plancherel {f : ℝ → ℂ} (hf : Integrable f) (h2 : MemLp f 2) :
    Integrable (fun x => ‖𝓕 f x‖ ^ 2) ∧ ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := fourier_ae_eq hf h2
  constructor
  · have h3 : MemLp (𝓕 f) 2 volume :=
      (memLp_congr_ae h).2 (Lp.memLp (𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)))
    exact (memLp_two_iff_integrable_sq_norm h3.aestronglyMeasurable).1 h3
  · calc ∫ x, ‖𝓕 f x‖ ^ 2 = ∫ x, ‖(𝓕 (h2.toLp f) : Lp ℂ 2 (volume : Measure ℝ)) x‖ ^ 2 := by
          refine integral_congr_ae ?_
          filter_upwards [h] with x hx
          rw [hx]
      _ = ∫ x, ‖(h2.toLp f) x‖ ^ 2 := by
          rw [integral_norm_sq_Lp, integral_norm_sq_Lp, Lp.norm_fourier_eq]
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [h2.coeFn_toLp] with x hx
          rw [hx]

theorem fourier_indicator (l δ : ℝ) (hδ : 0 ≤ δ) (c : ℂ) (w : ℝ) :
    𝓕 ((Set.Ico (l - δ) l).indicator (fun _ => c)) w =
      c * cexp (-(2 * π * w * l : ℝ) * I) * ∫ u in (0 : ℝ)..δ, cexp ((2 * π * w * u : ℝ) * I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have : ∀ v : ℝ, cexp (↑(-2 * π * v * w) * I) • (Set.Ico (l - δ) l).indicator (fun _ => c) v =
      (Set.Ico (l - δ) l).indicator (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) v := by
    intro v
    by_cases hv : v ∈ Set.Ico (l - δ) l <;> simp [hv]
  simp_rw [this]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  have h2 := intervalIntegral.integral_comp_sub_left (a := 0) (b := δ)
    (fun v : ℝ => cexp (↑(-2 * π * v * w) * I) * c) l
  rw [sub_zero] at h2
  rw [← h2, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [mul_comm _ c, mul_assoc c, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem kernel_lower (δ s : ℝ) (hδ : 0 ≤ δ) (hs : |s| * δ ≤ 1) :
    δ / 2 ≤ ‖∫ u in (0 : ℝ)..δ, cexp ((s * u : ℝ) * I)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  have hc : Continuous fun u : ℝ => cexp ((s * u : ℝ) * I) := by fun_prop
  have := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (hc.intervalIntegrable (μ := volume) 0 δ)
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  calc δ / 2 = ∫ u in (0 : ℝ)..δ, (1 / 2 : ℝ) := by simp; ring
    _ ≤ _ := by
      refine intervalIntegral.integral_mono_on hδ (by simp)
        ((Complex.continuous_re.comp hc).intervalIntegrable _ _) fun u hu => ?_
      rw [exp_ofReal_mul_I_re]
      have h1 : |s * u| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg hu.1]
        exact le_trans (mul_le_mul_of_nonneg_left hu.2 (abs_nonneg _)) hs
      have h2 := Real.one_sub_sq_div_two_le_cos (x := s * u)
      have h3 : (s * u) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (s * u)]
      linarith

theorem exp_sum (S : Finset ℕ) (a : ℕ → ℂ) (l : ℕ → ℝ) (T : ℝ) (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2) ≤
      8 * π * T ^ 2 *
        ∫ v : ℝ, ‖∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v‖ ^ 2 := by
  set f : ℝ → ℂ := fun v => ∑ n ∈ S, (Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n) v
    with hf
  have hmem : ∀ (p : ENNReal) (n : ℕ),
      MemLp ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) p volume := fun p n =>
    memLp_indicator_const p measurableSet_Ico.nullMeasurableSet _ (Or.inr (by simp))
  have hint : ∀ n, Integrable ((Set.Ico (l n - 1 / T) (l n)).indicator (fun _ => a n)) volume :=
    fun n => memLp_one_iff_integrable.1 (hmem 1 n)
  have hf1 : Integrable f := integrable_finsetSum _ fun n _ => hint n
  have hf2 : MemLp f 2 := memLp_finsetSum _ fun n _ => hmem 2 n
  obtain ⟨hI, hP⟩ := plancherel hf1 hf2
  have hδ : 0 ≤ 1 / T := by positivity
  have hF : ∀ w : ℝ, 𝓕 f w = (∑ n ∈ S, a n * cexp (-(2 * π * w * l n : ℝ) * I)) *
      ∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I) := by
    intro w
    rw [Finset.sum_mul]
    simp_rw [← fourier_indicator _ _ hδ]
    simp_rw [Real.fourier_real_eq, hf, Finset.smul_sum]
    refine integral_finsetSum _ fun n _ => ?_
    simpa [mul_comm] using (Real.fourierIntegral_convergent_iff w).2 (hint n)
  have hpi : (0 : ℝ) < 2 * π := by positivity
  set D : ℝ → ℝ := fun t => ‖∑ n ∈ S, a n * cexp (-(t * l n : ℝ) * I)‖ ^ 2 with hD
  have hDc : Continuous D := by fun_prop
  have h1 : ∫ t in (-T)..T, D t = (2 * π) * ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) := by
    have := intervalIntegral.mul_integral_comp_mul_left (f := D) (a := -T / (2 * π))
      (b := T / (2 * π)) (2 * π)
    rw [this, mul_div_cancel₀ _ hpi.ne', mul_div_cancel₀ _ hpi.ne']
  have hle : -T / (2 * π) ≤ T / (2 * π) := by gcongr; linarith
  have h2 : ∫ w in (-T / (2 * π))..(T / (2 * π)), D (2 * π * w) ≤
      ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on hle
      ((hDc.comp (by fun_prop : Continuous fun w : ℝ => 2 * π * w)).intervalIntegrable _ _)
      ((hI.const_mul _).intervalIntegrable) fun w hw => ?_
    have hw' : |2 * π * w| ≤ T := by
      rw [abs_le]
      constructor
      · have := (div_le_iff₀ hpi).1 hw.1
        linarith
      · have := (le_div_iff₀ hpi).1 hw.2
        linarith
    have hk := kernel_lower (1 / T) (2 * π * w) hδ (by rw [mul_one_div, div_le_one hT]; exact hw')
    rw [hF, norm_mul, mul_pow]
    set k := ‖∫ u in (0 : ℝ)..(1 / T), cexp ((2 * π * w * u : ℝ) * I)‖
    have hk1 : 1 ≤ 2 * T * k := by
      have : 2 * T * (1 / T / 2) = 1 := by field_simp
      rw [← this]; gcongr
    have hk2 : 1 ≤ 4 * T ^ 2 * k ^ 2 := by nlinarith
    have hD0 : 0 ≤ D (2 * π * w) := by positivity
    change D (2 * π * w) ≤ 4 * T ^ 2 * (D (2 * π * w) * k ^ 2)
    nlinarith
  have h3 : ∫ w in (-T / (2 * π))..(T / (2 * π)), 4 * T ^ 2 * ‖𝓕 f w‖ ^ 2 ≤
      4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2 := by
    rw [intervalIntegral.integral_const_mul, ← hP, intervalIntegral.integral_of_le hle]
    exact mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hI (Filter.Eventually.of_forall fun w => by positivity))
      (by positivity)
  rw [h1]
  calc _ ≤ (2 * π) * (4 * T ^ 2 * ∫ v, ‖f v‖ ^ 2) := by
        gcongr; exact h2.trans h3
    _ = _ := by ring

theorem gallagher : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a : ℕ → ℂ) (T : ℝ), 1 ≤ T →
    (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * T ^ 2 * ∫ x in Set.Ioi (0 : ℝ), ‖∑ n ∈ (Finset.Icc 1 N).filter
        (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x * Real.exp (1 / T)), a n‖ ^ 2 / x := by
  refine ⟨8 * π, by positivity, fun N a T hT => ?_⟩
  have h := exp_sum (Finset.Icc 1 N) a (fun n => Real.log n) T (by linarith)
  convert h using 2
  · funext t
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : n ≠ 0)
    rw [cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    congr 2
    push_cast
    ring
  · rw [← Real.range_exp, ← Set.image_univ,
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
        (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
      Measure.restrict_univ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [abs_of_pos (Real.exp_pos v), mul_div_cancel₀ _ (Real.exp_pos v).ne', Finset.sum_filter]
    congr 2
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : (0 : ℝ) < n := by
      have := (Finset.mem_Icc.1 hn).1
      exact_mod_cast (by omega : 0 < n)
    rw [Set.indicator_apply, ← Real.exp_add]
    refine if_congr ?_ rfl rfl
    rw [Set.mem_Ico, ← Real.lt_log_iff_exp_lt hn0, ← Real.log_le_iff_le_exp hn0]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

end GlobalTheory.GallagherLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormSubOneMulRiemannZetaLe
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology

namespace GlobalTheory.ZetaLeft

noncomputable def emT (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ (1 - s) - (1 - s) * (x : ℂ) ^ (1 - s - 1) / 2
    + (1 - s) * (1 - s - 1) * (x : ℂ) ^ (1 - s - 1 - 1) / 12

noncomputable def emE (x : ℝ) (s : ℂ) : ℂ :=
  emT (x + 1) s - emT x s - (1 - s) * (x : ℂ) ^ (1 - s - 1)

lemma hasDerivAt_shift_cpow {a t : ℝ} (h : 0 < a + t) (c : ℂ) :
    HasDerivAt (fun z : ℂ => ((a : ℂ) + z) ^ c) (c * ((a : ℂ) + t) ^ (c - 1)) (t : ℂ) := by
  have h1 : HasDerivAt (fun z : ℂ => (a : ℂ) + z) 1 (t : ℂ) := (hasDerivAt_id _).const_add _
  have h2 : ((a : ℂ) + t) ∈ slitPlane := by
    left; simpa using h
  simpa using h1.cpow_const (c := c) h2

lemma norm_emE_le {a : ℝ} (ha : 1 ≤ a) {s : ℂ} (hs : -(15/8 : ℝ) ≤ s.re) :
    ‖emE a s‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
  set w : ℂ := 1 - s with hw
  let G : ℂ → ℂ := fun z => ((a : ℂ) + z) ^ w - (z - 1/2) * (w * ((a : ℂ) + z) ^ (w - 1))
    + (z ^ 2 - z + 1/6) / 2 * (w * (w - 1) * ((a : ℂ) + z) ^ (w - 1 - 1))
    - (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6 * (w * (w - 1) * (w - 1 - 1) * ((a : ℂ) + z) ^ (w - 1 - 1 - 1))
  let G' : ℝ → ℂ := fun t => - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) *
    (w * (w - 1) * (w - 1 - 1) * (w - 1 - 1 - 1) * ((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1))
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun y : ℝ => G y) (G' t) t := by
    intro t ht
    have h : 0 < a + t := by linarith
    have p1 : HasDerivAt (fun z : ℂ => z - 1/2) 1 (t : ℂ) := (hasDerivAt_id _).sub_const _
    have p2 : HasDerivAt (fun z : ℂ => (z ^ 2 - z + 1/6) / 2) ((t : ℂ) - 1/2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 2).sub (hasDerivAt_id _)).add_const (1/6)).div_const 2
      exact this.congr_deriv (by simp; ring)
    have p3 : HasDerivAt (fun z : ℂ => (z ^ 3 - 3/2 * z ^ 2 + z / 2) / 6)
        (((t : ℂ) ^ 2 - t + 1/6) / 2) (t : ℂ) := by
      have := ((((hasDerivAt_id (t : ℂ)).pow 3).sub
        (((hasDerivAt_id (t : ℂ)).pow 2).const_mul (3/2))).add
        ((hasDerivAt_id (t : ℂ)).div_const 2)).div_const 6
      exact this.congr_deriv (by simp; ring)
    have hG : HasDerivAt G (G' t) (t : ℂ) := by
      have := (((hasDerivAt_shift_cpow h w).sub
        (p1.mul ((hasDerivAt_shift_cpow h (w - 1)).const_mul w))).add
        (p2.mul ((hasDerivAt_shift_cpow h (w - 1 - 1)).const_mul (w * (w - 1))))).sub
        (p3.mul ((hasDerivAt_shift_cpow h (w - 1 - 1 - 1)).const_mul (w * (w - 1) * (w - 1 - 1))))
      exact this.congr_deriv (by simp only [G']; ring)
    exact hG.comp_ofReal
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖G' t‖ ≤ (‖s‖ + 2) ^ 4 * a ^ (-(9/8 : ℝ)) := by
    intro t ht
    have h : 0 < a + t := by linarith [ht.1]
    have b1 : ‖- (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)‖ ≤ 1 := by
      have : - (((t : ℂ) ^ 3 - 3/2 * t ^ 2 + t / 2) / 6)
          = ((- ((t ^ 3 - 3/2 * t ^ 2 + t / 2) / 6) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have h2 : t ^ 2 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht.1 ht.2.le
      have h4 : 0 ≤ t ^ 2 := by positivity
      have h5 : 0 ≤ t ^ 3 := pow_nonneg ht.1 _
      constructor <;> linarith [ht.1, ht.2]
    have key : ∀ c : ℝ, |c| ≤ 2 → ‖(c : ℂ) - s‖ ≤ ‖s‖ + 2 := by
      intro c hc
      have := norm_sub_le (c : ℂ) s
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have c0 : ‖w‖ ≤ ‖s‖ + 2 := by simpa using key 1 (by norm_num)
    have c1 : ‖w - 1‖ ≤ ‖s‖ + 2 := by
      convert key 0 (by norm_num) using 2; rw [hw]; push_cast; ring
    have c2 : ‖w - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-1) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c3 : ‖w - 1 - 1 - 1‖ ≤ ‖s‖ + 2 := by
      convert key (-2) (by norm_num) using 2; rw [hw]; push_cast; ring
    have c4 : ‖((a : ℂ) + t) ^ (w - 1 - 1 - 1 - 1)‖ ≤ a ^ (-(9/8 : ℝ)) := by
      rw [← Complex.ofReal_add, Complex.norm_cpow_eq_rpow_re_of_pos h]
      have e : (w - 1 - 1 - 1 - 1).re ≤ -(9/8 : ℝ) := by
        simp [hw]; linarith
      calc _ ≤ (a + t) ^ (-(9/8 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith [ht.1]) e
        _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [ht.1]) (by norm_num)
    simp only [G', norm_mul]
    calc _ ≤ 1 * ((‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * (‖s‖ + 2) * a ^ (-(9/8 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun y : ℝ => G y) (f' := G')
    (fun t ht => (hd t ht.1).hasDerivWithinAt) hb
  refine le_of_eq_of_le (congrArg _ ?_) this
  simp only [G, emE, emT, ← hw]
  push_cast
  simp only [add_zero]
  ring

lemma summable_nine_pow_mul_inv_sq_succ : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(9/8 : ℝ))) := by
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by norm_num : -(9/8 : ℝ) < -1))
  simpa using this

lemma differentiable_emT {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emT x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  unfold emT
  fun_prop

lemma differentiable_emE {x : ℝ} (hx : 0 < x) : Differentiable ℂ (emE x) := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have : NeZero (x : ℂ) := ⟨hx'⟩
  have h1 := differentiable_emT hx
  have h2 := differentiable_emT (x := x + 1) (by linarith)
  unfold emE
  fun_prop

lemma differentiableOn_tsum_emE :
    DifferentiableOn ℂ (fun s => ∑' n : ℕ, emE ((n : ℝ) + 1) s) {s : ℂ | -(15/8 : ℝ) < s.re} := by
  intro s hs
  have ho : IsOpen ({z : ℂ | -(15/8 : ℝ) < z.re} ∩ Metric.ball 0 (‖s‖ + 1)) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun (n : ℕ) (z : ℂ) => emE ((n : ℝ) + 1) z)
    (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 3) ^ 4))
    (fun n => (differentiable_emE (by positivity)).differentiableOn) ho (by
      intro n z hz
      have h1 : ‖z‖ < ‖s‖ + 1 := by simpa using hz.2
      refine (norm_emE_le (by simp) (le_of_lt hz.1)).trans ?_
      have h2 : ‖z‖ + 2 ≤ ‖s‖ + 3 := by linarith
      gcongr)
  exact (this.differentiableAt (ho.mem_nhds ⟨hs, by simp⟩)).differentiableWithinAt

lemma tendsto_cpow_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1 : ℝ) : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have := (tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp h1
  refine this.congr fun n => ?_
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

lemma eq_of_one_lt {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have hsum : Summable (fun n : ℕ => emE ((n : ℝ) + 1) s) :=
    Summable.of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 2) ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have hT : Tendsto (fun n : ℕ => emT ((n : ℝ) + 1) s) atTop (𝓝 0) := by
    have := ((tendsto_cpow_zero (c := 1 - s) (by simp; linarith)).sub
      (((tendsto_cpow_zero (c := 1 - s - 1) (by simp; linarith)).const_mul (1 - s)).div_const 2)).add
      (((tendsto_cpow_zero (c := 1 - s - 1 - 1) (by simp; linarith)).const_mul
        ((1 - s) * (1 - s - 1))).div_const 12)
    simpa [emT] using this
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
    exact (by simpa using this : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s)).hasSum
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, emE ((n : ℝ) + 1) s =
      emT ((N : ℝ) + 1) s - emT 1 s + (s - 1) * ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ s := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, emE]
      have : (1 - s - 1) = -s := by ring
      rw [this, Complex.cpow_neg]
      push_cast
      ring
  have h1 := (hT.sub_const (emT 1 s)).add (hz.tendsto_sum_nat.const_mul (s - 1))
  have h2 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h2
  rw [tendsto_nhds_unique h2 h1]
  ring

lemma eq_of_lt {s : ℂ} (hs : -(15/8 : ℝ) < s.re) (h1 : s ≠ 1) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have ho : IsOpen {z : ℂ | -(15/8 : ℝ) < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : ∀ z : ℂ, z ≠ 1 → LFunctionTrivChar₁ 1 z = (z - 1) * riemannZeta z := by
    intro z hz
    rw [LFunctionTrivChar₁, Function.update_of_ne hz, LFunctionTrivChar, LFunction_modOne_eq]
  have hA : AnalyticOnNhd ℂ (LFunctionTrivChar₁ 1) {z : ℂ | -(15/8 : ℝ) < z.re} :=
    (differentiable_LFunctionTrivChar₁ 1).differentiableOn.analyticOnNhd ho
  have hB : AnalyticOnNhd ℂ (fun s => emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s)
      {z : ℂ | -(15/8 : ℝ) < z.re} :=
    ((differentiable_emT one_pos).differentiableOn.add differentiableOn_tsum_emE).analyticOnNhd ho
  have := hA.eqOn_of_preconnected_of_eventuallyEq hB
    (convex_halfSpace_re_gt _).isPreconnected (z₀ := 2) (by simp; norm_num) (by
      have : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
        (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
      filter_upwards [this] with z hz
      rw [hf z (by rintro rfl; simp at hz), eq_of_one_lt hz])
  rw [← hf s h1]
  exact this hs

theorem norm_sub_one_mul_riemannZeta_le :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(7/4 : ℝ) ≤ s.re → s ≠ 1 →
      ‖(s - 1) * riemannZeta s‖ ≤ C * (‖s‖ + 2) ^ 5 := by
  set K : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(9/8 : ℝ)) with hK
  have hK0 : 0 ≤ K := tsum_nonneg fun n => by positivity
  refine ⟨3 + K, by linarith, fun s hs h1 => ?_⟩
  rw [eq_of_lt (by linarith) h1]
  set R := ‖s‖ + 2 with hR
  have hR1 : 1 ≤ R := by have := norm_nonneg s; linarith
  have h2 : ‖∑' n : ℕ, emE ((n : ℝ) + 1) s‖ ≤ R ^ 4 * K :=
    tsum_of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.hasSum.mul_left (R ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have c0 : ‖1 - s‖ ≤ R := by
    have := norm_sub_le 1 s
    rw [norm_one] at this; linarith
  have c1 : ‖1 - s - 1‖ ≤ R := by simp [hR]
  have h3 : ‖emT 1 s‖ ≤ 1 + R / 2 + R * R / 12 := by
    simp only [emT, Complex.ofReal_one, Complex.one_cpow, mul_one]
    refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans ?_) ?_)
    · simp only [norm_one, norm_div, Complex.norm_ofNat]; gcongr
    · simp only [norm_mul, norm_div, Complex.norm_ofNat]; gcongr
  have p0 : 1 ≤ R ^ 5 := one_le_pow₀ hR1
  have p1 : R ^ 1 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p2 : R ^ 2 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p4 : R ^ 4 ≤ R ^ 5 := pow_le_pow_right₀ hR1 (by norm_num)
  have p5 : R ^ 4 * K ≤ R ^ 5 * K := by gcongr
  refine (norm_add_le _ _).trans ?_
  nlinarith

end GlobalTheory.ZetaLeft
end
