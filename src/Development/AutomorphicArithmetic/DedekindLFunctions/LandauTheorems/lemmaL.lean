module

public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData
section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiModOne
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem mellin_Gchi_modOne_sum {μ : Measure ℝ} (T : ℕ → ℝ → ℂ) (E : ℝ → ℂ)
    (hT : ∀ n, Integrable (T n) μ) (hE : Integrable E μ)
    (hs : Summable fun n => ∫ a, ‖T n a‖ ∂μ) (hp : ∀ a, Summable fun n => T n a) :
    ∫ a, (E a + ∑' n, T n a) ∂μ = ∫ a, E a ∂μ + ∑' n, ∫ a, T n a ∂μ := by
  let F : ℕ → ℝ → ℂ := fun n => Nat.casesOn n E T
  have hF : ∀ n, Integrable (F n) μ := fun n => by
    cases n with
    | zero => exact hE
    | succ n => exact hT n
  have hFs : Summable fun n => ∫ a, ‖F n a‖ ∂μ := (summable_nat_add_iff 1).mp hs
  have h := hasSum_integral_of_summable_integral_norm hF hFs
  have h2 : ∀ a, ∑' n, F n a = E a + ∑' n, T n a := fun a =>
    ((summable_nat_add_iff (f := fun n => F n a) 1).mp (hp a)).tsum_eq_zero_add
  simp_rw [h2] at h
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  rfl

theorem mellin_Gchi_modOne_int (n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have ha : (-s).re < -1 := by simp; linarith
  have hb : (-s - 1).re < -1 := by simp; linarith
  refine Integrable.mono' (integrableOn_Ioi_norm_cpow_of_lt ha zero_lt_one) ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ (integrableOn_Ioi_cpow_of_lt hb zero_lt_one).1
    exact Continuous.aestronglyMeasurable (by fun_prop)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
    have hy1 : (1 : ℝ) < y := hy
    have hy0 : (0 : ℝ) < y := by linarith
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have h1 : y / n ≤ y := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simpa using hy0.le
      · exact div_le_self hy0.le (by exact_mod_cast hn)
    have h2 : max (y / n - 1) 0 ≤ y := max_le (by linarith) hy0.le
    rw [norm_mul, cpow_sub _ _ hyC, cpow_one, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (le_max_right _ _), Real.norm_of_nonneg hy0.le]
    calc _ ≤ y * (‖(y : ℂ) ^ (-s)‖ / y) := by gcongr
      _ = _ := by field_simp

theorem mellin_Gchi_modOne_term (n : ℕ) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1)) =
      LSeries.term (fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s n / (s * (s - 1)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [integral_const_mul, mellin_ramp n hn s hs, LSeries.term_of_ne_zero hn.ne', cpow_neg]
  ring

theorem mellin_Gchi_modOne_log_int (s : ℂ) (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) (Ioi 1) ∧
    Tendsto (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1)) atTop (𝓝 0) := by
  have ha : (-s).re < -1 := by simp; linarith
  set e : ℝ := (s.re - 1) / 2 with he
  have he0 : 0 < e := by linarith
  have key : ∀ (c : ℂ) (y : ℝ), 1 < y →
      ‖((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ c‖ ≤ y ^ (e + c.re) / e := by
    intro c y hy
    have hy0 : (0 : ℝ) < y := by linarith
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hy.le),
      Complex.norm_cpow_eq_rpow_re_of_pos hy0, Real.rpow_add hy0]
    calc _ ≤ y ^ e / e * y ^ c.re := by
          gcongr
          exact Real.log_le_rpow_div hy0.le he0
      _ = _ := by ring
  constructor
  · have hc : e + (-s).re < -1 := by simp; linarith
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt hc zero_lt_one).div_const e) ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).1
      exact (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable
    · exact ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => key _ y hy
  · have hc : 0 < -(e + (-s + 1).re) := by simp; linarith
    have h := (tendsto_rpow_neg_atTop hc).div_const e
    rw [neg_neg, zero_div] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [eventually_gt_atTop 1] with y hy using key _ y hy

theorem mellin_Gchi_modOne_log (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s) = 1 / (s - 1) ^ 2 := by
  have ha : (-s).re < -1 := by simp; linarith
  have hs1 : -s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨hi, ht⟩ := mellin_Gchi_modOne_log_int s hs
  have hd : ∀ y ∈ Ici (1 : ℝ), HasDerivAt (fun y : ℝ => ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s + 1))
      ((-s + 1) * (((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)) + (y : ℂ) ^ (-s)) y := by
    intro y hy
    have hy0 : y ≠ 0 := (zero_lt_one.trans_le hy).ne'
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
    refine ((Real.hasDerivAt_log hy0).ofReal_comp.mul
      (hasDerivAt_ofReal_cpow_const hy0 hs1)).congr_deriv ?_
    rw [add_sub_cancel_right, cpow_add _ _ hyC, cpow_one]
    push_cast
    field_simp
    ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd
    ((hi.const_mul _).add (integrableOn_Ioi_cpow_of_lt ha zero_lt_one)) ht
  rw [integral_add (hi.const_mul _) (integrableOn_Ioi_cpow_of_lt ha zero_lt_one),
    integral_const_mul, integral_Ioi_cpow_of_lt ha zero_lt_one] at h
  simp only [ofReal_one, one_cpow, Real.log_one, ofReal_zero, zero_mul, sub_zero] at h
  have e2 : (s - 1) ^ 2 = (-s + 1) ^ 2 := by ring
  rw [e2]
  field_simp at h ⊢
  linear_combination h

theorem mellin_Gchi_modOne (χ : DirichletCharacter ℂ 1) (s : ℂ) (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), Gchi χ y * (y : ℂ) ^ (-s - 1) =
      -(deriv riemannZeta s / riemannZeta s + 1 / (s - 1) + 1 - (1 + Real.eulerMascheroniConstant) * s) /
        (s * (s - 1)) := by
  have h1 : χ = 1 := DirichletCharacter.level_one χ
  have h2 : ∀ n : ℕ, χ n = 1 := fun n => by
    rw [h1]; exact MulChar.one_apply (isUnit_of_subsingleton _)
  have ha : (-s).re < -1 := by simp; linarith
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  let T : ℕ → ℝ → ℂ := fun n y => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      (((max (y / n - 1) 0 : ℝ) : ℂ) * (y : ℂ) ^ (-s - 1))
  let E : ℝ → ℂ := fun y => (1 + Real.eulerMascheroniConstant) * (y : ℂ) ^ (-s) -
    ((Real.log y : ℝ) : ℂ) * (y : ℂ) ^ (-s)
  have hz : ∀ y : ℝ, ∀ n ∉ Finset.range (⌊y⌋₊ + 1), T n y = 0 := by
    intro y n hn
    have hn' : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
    have hpos : (0 : ℝ) < n := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hlt : y < n := by
      have h1 := Nat.lt_floor_add_one y
      have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
      push_cast at h2
      linarith
    have : max (y / n - 1) 0 = 0 := by
      apply max_eq_right
      have := (div_lt_one hpos).mpr hlt
      linarith
    simp [T, this]
  have hc : EqOn (fun y : ℝ => Gchi χ y * (y : ℂ) ^ (-s - 1))
      (fun y => E y + ∑' n, T n y) (Ioi 1) := by
    intro y hy
    have hy1 : (1 : ℝ) < y := hy
    have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hy1).ne'
    have h3 : (y : ℂ) ^ (-s) = y * (y : ℂ) ^ (-s - 1) := by
      rw [cpow_sub _ _ hyC, cpow_one]
      field_simp
    beta_reduce
    rw [tsum_eq_sum (hz y)]
    simp only [Gchi, if_pos h1, h2, ramp, T, E, h3, mul_one, ← mul_assoc,
      ← Finset.sum_mul]
    push_cast
    ring
  have hi := (mellin_Gchi_modOne_log_int s hs).1
  have hi2 := integrableOn_Ioi_cpow_of_lt ha zero_lt_one
  have hsum : Summable fun n => ∫ y in Ioi (1 : ℝ), ‖T n y‖ := by
    have hσ : 1 < ((s.re : ℝ) : ℂ).re := by simpa using hs
    rw [← Complex.summable_ofReal]
    refine ((ArithmeticFunction.LSeriesSummable_vonMangoldt hσ).div_const
      ((s.re : ℂ) * (s.re - 1))).congr fun n => ?_
    rw [← mellin_Gchi_modOne_term n _ hσ, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := zero_lt_one.trans hy
    simp only [T]
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Real.norm_of_nonneg (le_max_right _ _), Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have : (y : ℂ) ^ (-(s.re : ℂ) - 1) = ((y ^ (-s - 1).re : ℝ) : ℂ) := by
      rw [ofReal_cpow hy0.le]
      simp
    rw [this]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi hc,
    mellin_Gchi_modOne_sum T E (fun n => (mellin_Gchi_modOne_int n s hs).const_mul _)
      ((hi2.const_mul _).sub hi) hsum (fun y => summable_of_ne_finset_zero (hz y))]
  simp only [T, E, mellin_Gchi_modOne_term _ s hs]
  rw [tsum_div_const, integral_sub (hi2.const_mul _) hi, integral_const_mul,
    integral_Ioi_cpow_of_lt ha zero_lt_one, mellin_Gchi_modOne_log s hs]
  have h4 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [LSeries] at h4
  rw [h4, neg_div (riemannZeta s)]
  have e2 : -s + 1 = -(s - 1) := by ring
  rw [e2]
  generalize deriv riemannZeta s / riemannZeta s = D
  simp only [ofReal_one, one_cpow]
  field_simp
  ring

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiConj
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem Gchi_conj_ramp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (starRingEnd ℂ) (ramp (fun n => χ n) y) = ramp (fun n => χ⁻¹ n) y := by
  unfold ramp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
  congr 2
  exact MulChar.star_apply' χ (n : ZMod N)

theorem Gchi_conj_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.LFunction χ⁻¹ =
      (starRingEnd ℂ) ∘ DirichletCharacter.LFunction χ ∘ (starRingEnd ℂ) := by
  funext s
  have h := LFunction_conj χ ((starRingEnd ℂ) s)
  rw [Complex.conj_conj] at h
  simp only [Function.comp_apply]
  exact h

private theorem deriv_conj_comp_conj (f : ℂ → ℂ) (x : ℂ) :
    deriv ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x) =
      (starRingEnd ℂ) (deriv f x) := by
  by_cases hf : DifferentiableAt ℂ f x
  · exact hf.hasDerivAt.conj_conj.deriv
  · have hg : ¬ DifferentiableAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x) := by
      rw [differentiableAt_conj_conj_iff, Complex.conj_conj]
      exact hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hg, map_zero]

theorem Gchi_conj {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (starRingEnd ℂ) (Gchi χ y) = Gchi χ⁻¹ y := by
  by_cases h1 : χ = 1
  · subst h1
    simp only [Gchi, inv_one, if_true]
    rw [map_add (f := _), map_sub, Gchi_conj_ramp, inv_one, Complex.conj_ofReal, Complex.conj_ofReal]
  · have h2 : χ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.mp h)
    simp only [Gchi, h1, h2, if_false]
    have hL := Gchi_conj_LFunction χ
    have h1c : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
    rw [map_add (f := _), map_mul, map_div₀, Gchi_conj_ramp, Complex.conj_ofReal, hL]
    congr 2
    rw [← h1c, deriv_conj_comp_conj, h1c]
    simp only [Function.comp_apply, h1c]

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.measurableGchi
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem measurable_Gchi_floor (g : ℕ → ℝ → ℂ) (hg : ∀ k, Measurable (g k)) :
    Measurable (fun y : ℝ => g ⌊y⌋₊ y) := by
  have h : Measurable fun p : ℝ × ℕ => g p.2 p.1 :=
    measurable_from_prod_countable_left fun k => hg k
  exact h.comp (measurable_id.prodMk Nat.measurable_floor)

theorem measurable_Gchi_ramp (f : ℕ → ℂ) : Measurable (ramp f) := by
  unfold ramp
  refine measurable_Gchi_floor
    (fun k y => ∑ n ∈ Finset.range (k + 1),
      (ArithmeticFunction.vonMangoldt n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)) ?_
  intro k
  refine Finset.measurable_sum _ fun n _ => ?_
  fun_prop

theorem measurable_Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Measurable (Gchi χ) := by
  unfold Gchi
  split_ifs
  · exact ((measurable_Gchi_ramp _).sub (by fun_prop)).add (by fun_prop)
  · exact (measurable_Gchi_ramp _).add (by fun_prop)

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LogDerivLocal
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem logDeriv_local {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) (hne : ¬ ∀ᶠ s in 𝓝 ρ, f s = 0) :
    ∃ m : ℕ, (m = 0 ↔ f ρ ≠ 0) ∧ (m : ℕ∞) = analyticOrderAt f ρ ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
      ∀ᶠ s in 𝓝[≠] ρ, deriv f s / f s = (m : ℂ) / (s - ρ) + h s := by
  have htop : analyticOrderAt f ρ ≠ ⊤ := fun h => hne (analyticOrderAt_eq_top.mp h)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp htop
  set m := analyticOrderNatAt f ρ with hm
  refine ⟨m, ?_, Nat.cast_analyticOrderNatAt htop, fun s => deriv g s / g s,
    hg.deriv.div hg hg0, ?_⟩
  · rw [← hf.analyticOrderAt_eq_zero, ← Nat.cast_analyticOrderNatAt htop]
    exact Nat.cast_eq_zero.symm
  · have hev : ∀ᶠ s in 𝓝 ρ, (∀ᶠ z in 𝓝 s, f z = (z - ρ) ^ m • g z) ∧ g s ≠ 0 ∧ AnalyticAt ℂ g s :=
      (Filter.Eventually.eventually_nhds hfg).and
        ((hg.continuousAt.eventually_ne hg0).and hg.eventually_analyticAt)
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with s hs hsne
    obtain ⟨hs1, hs2, hs3⟩ := hs
    have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hsne
    have hd : HasDerivAt (fun z => (z - ρ) ^ m * g z)
        (↑m * (s - ρ) ^ (m - 1) * 1 * g s + (s - ρ) ^ m * deriv g s) s :=
      (((hasDerivAt_id' s).sub_const ρ).pow m).mul hs3.differentiableAt.hasDerivAt
    have e1 : deriv f s = deriv (fun z => (z - ρ) ^ m * g z) s := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [hs1] with z hz
      rw [hz, smul_eq_mul]
    have e2 : f s = (s - ρ) ^ m * g s := by simpa only [smul_eq_mul] using hs1.self_of_nhds
    rw [e1, hd.deriv, e2]
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]
      simp
    · obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]
      field_simp

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiGrowth
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem Gchi_growth_ramp (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {y : ℝ} (hy : 1 ≤ y) :
    ‖ramp f y‖ ≤ 2 * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have key : ∀ n ∈ Finset.range (⌊y⌋₊ + 1),
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)‖ ≤ y := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using hy0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_self hn'.le)
    have h0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : max (y / n - 1) 0 ≤ y / n := max_le (by linarith) (by positivity)
    have h3 : 0 ≤ max (y / n - 1) 0 := le_max_right _ _
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h0,
      Real.norm_of_nonneg h3]
    calc _ ≤ (n : ℝ) * 1 * (y / n) := by
          gcongr
          exact hf n
      _ = y := by field_simp
  have h := (norm_sum_le _ _).trans (Finset.sum_le_card_nsmul _ _ _ key)
  rw [Finset.card_range, nsmul_eq_mul] at h
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0
  unfold ramp
  refine h.trans ?_
  push_cast
  nlinarith

theorem Gchi_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y → ‖Gchi χ y‖ ≤ C * y ^ 2 := by
  by_cases h : χ = 1
  · refine ⟨2 + 1 + |1 + Real.eulerMascheroniConstant|, fun y hy => ?_⟩
    have hr := Gchi_growth_ramp (fun n => χ n) (fun n => χ.norm_le_one _) hy
    have hy0 : 0 ≤ y := by linarith
    have hl0 : 0 ≤ Real.log y := Real.log_nonneg hy
    have hl : Real.log y ≤ y := Real.log_le_self hy0
    have hyy : y ≤ y ^ 2 := by nlinarith
    unfold Gchi
    rw [if_pos h]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hy0 hl0),
      Real.norm_eq_abs, abs_mul, abs_of_nonneg hy0]
    have h1 : y * Real.log y ≤ y ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left hyy (abs_nonneg (1 + Real.eulerMascheroniConstant))
    linarith
  · refine ⟨2 + ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖,
      fun y hy => ?_⟩
    have hr := Gchi_growth_ramp (fun n => χ n) (fun n => χ.norm_le_one _) hy
    have hy0 : 0 ≤ y := by linarith
    have hyy : y ≤ y ^ 2 := by nlinarith
    unfold Gchi
    rw [if_neg h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0]
    have h2 := mul_le_mul_of_nonneg_left hyy
      (norm_nonneg (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1))
    linarith

end Deduction

end
end

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem poleData_dslope {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) :
    AnalyticAt ℂ (dslope f a) a := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

theorem poleData_abstract (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h1 : g 1 ≠ 0) (k : ℂ) :
    ∃ Φ : ℂ → ℂ,
      (∀ s, s ≠ 1 → Φ s =
        -(deriv g s / g s - s * (deriv g 1 / g 1) + k * (1 - s)) / (s * (s - 1))) ∧
      (∀ ρ, ρ ≠ 0 → g ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
      (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ g ρ ≠ 0) ∧ ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h s) ∧
      (∀ z, ∀ᶠ w in 𝓝[≠] z, g w ≠ 0) := by
  have hA : ∀ z, AnalyticAt ℂ g z := fun z => hg.analyticAt z
  have hnz : ∀ z, ¬ ∀ᶠ w in 𝓝 z, g w = 0 := by
    intro z hz
    have hon : AnalyticOnNhd ℂ g Set.univ := fun w _ => hA w
    have hzero := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (Set.mem_univ z) hz
    exact h1 (hzero (Set.mem_univ 1))
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = deriv g 1 / g 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ → ℂ, N = fun s => deriv g s / g s - s * c + k * (1 - s) := ⟨_, rfl⟩
  have hNs : ∀ s, N s = deriv g s / g s - s * c + k * (1 - s) := fun s => by rw [hN]
  have hN1 : N 1 = 0 := by rw [hNs, hc]; ring
  have hUo : IsOpen {s | g s ≠ 0} := isOpen_ne_fun hg.continuous continuous_const
  have hNd : DifferentiableOn ℂ N {s | g s ≠ 0} := by
    intro s hs
    have hd : DifferentiableAt ℂ (deriv g) s := (hA s).deriv.differentiableAt
    have hd2 : DifferentiableAt ℂ (fun s => deriv g s / g s - s * c + k * (1 - s)) s :=
      ((hd.div (hA s).differentiableAt hs).sub (differentiableAt_id.mul (differentiableAt_const c))).add
        ((differentiableAt_const k).mul ((differentiableAt_const 1).sub differentiableAt_id))
    rw [hN]
    exact hd2.differentiableWithinAt
  have hDd : DifferentiableOn ℂ (dslope N 1) {s | g s ≠ 0} :=
    (differentiableOn_dslope (hUo.mem_nhds h1)).mpr hNd
  have hPhi : ∀ s, s ≠ 1 → -(dslope N 1 s) / s =
      -(deriv g s / g s - s * (deriv g 1 / g 1) + k * (1 - s)) / (s * (s - 1)) := by
    intro s hs
    rw [dslope_of_ne _ hs, slope_def_field, hN1, hNs, ← hc]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hPan : ∀ ρ, ρ ≠ 0 → g ρ ≠ 0 → AnalyticAt ℂ (fun s => -(dslope N 1 s) / s) ρ := by
    intro ρ hρ hgρ
    exact (hDd.analyticAt (hUo.mem_nhds hgρ)).neg.div analyticAt_id hρ
  refine ⟨fun s => -(dslope N 1 s) / s, hPhi, hPan, ?_, ?_⟩
  · intro ρ hρ
    by_cases hgρ : g ρ = 0
    · have hρ1 : ρ ≠ 1 := fun h => h1 (h ▸ hgρ)
      obtain ⟨m, hm0, -, h0, hh0, hev⟩ := logDeriv_local (hA ρ) (hnz ρ)
      have hr : AnalyticAt ℂ (fun s : ℂ => 1 / (s * (s - 1))) ρ :=
        analyticAt_const.div (analyticAt_id.mul (analyticAt_id.sub analyticAt_const))
          (mul_ne_zero hρ (sub_ne_zero.mpr hρ1))
      have hq := poleData_dslope hr
      refine ⟨m, hm0, fun s => -((m : ℂ) * dslope (fun s : ℂ => 1 / (s * (s - 1))) ρ s)
          - (h0 s - s * c + k * (1 - s)) * (1 / (s * (s - 1))), ?_, ?_⟩
      · exact ((analyticAt_const.mul hq).neg).sub
          (((hh0.sub (analyticAt_id.mul analyticAt_const)).add
            (analyticAt_const.mul (analyticAt_const.sub analyticAt_id))).mul hr)
      · have hne0 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 0 :=
          nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ)
        have hne1 : ∀ᶠ s in 𝓝[≠] ρ, s ≠ 1 :=
          nhdsWithin_le_nhds (isOpen_ne.mem_nhds hρ1)
        have hneρ : ∀ᶠ s in 𝓝[≠] ρ, s ≠ ρ := self_mem_nhdsWithin
        filter_upwards [hev, hne0, hne1, hneρ] with s hs hs0 hs1 hsρ
        rw [hPhi s hs1, hs, dslope_of_ne _ hsρ, slope_def_field, ← hc]
        simp only [div_eq_mul_inv, mul_inv]
        ring
    · refine ⟨0, by simp [hgρ], fun s => -(dslope N 1 s) / s, hPan ρ hρ hgρ, ?_⟩
      exact Filter.Eventually.of_forall (fun s => by simp)
  · intro z
    rcases (hA z).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h (hnz z)
    · exact h

theorem poleData_integrable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : 2 < s.re) :
    IntegrableOn (fun u : ℝ => Gchi χ (Real.exp u) * cexp (-s * u)) (Ioi 0) := by
  obtain ⟨C, hC⟩ := Gchi_growth χ
  have hb : 0 < s.re - 2 := by linarith
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hb).const_mul (max C 0)) ?_ ?_
  · exact (((measurable_Gchi χ).comp Real.measurable_exp).mul
      (by fun_prop : Measurable fun u : ℝ => cexp (-s * u))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0:ℝ) < u := hu
    have he : ‖cexp (-s * u)‖ = Real.exp (-s.re * u) := by
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, he]
    have hg := hC (Real.exp u) (Real.one_le_exp hu0.le)
    calc ‖Gchi χ (Real.exp u)‖ * Real.exp (-s.re * u)
        ≤ (max C 0 * Real.exp u ^ 2) * Real.exp (-s.re * u) := by
          gcongr
          exact hg.trans (by gcongr; exact le_max_left _ _)
      _ = max C 0 * Real.exp (-(s.re - 2) * u) := by
          rw [mul_assoc, sq, ← Real.exp_add, ← Real.exp_add]
          congr 2
          ring

theorem poleData_change (G : ℝ → ℂ) (s : ℂ) :
    ∫ u in Ioi (0 : ℝ), G (Real.exp u) * cexp (-s * u) =
      ∫ y in Ioi (1 : ℝ), G y * (y : ℂ) ^ (-s - 1) := by
  have himg : Real.exp '' Ioi 0 = Ioi 1 := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      show (1:ℝ) < Real.exp u
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.2 hu
    · intro hy
      have hy1 : (1:ℝ) < y := hy
      exact ⟨Real.log y, Real.log_pos hy1, Real.exp_log (by linarith)⟩
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [abs_of_pos (Real.exp_pos u), Complex.real_smul,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos u).ne'),
    ← Complex.ofReal_log (Real.exp_pos u).le, Real.log_exp, Complex.ofReal_exp,
    mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem poleData_char {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (adm : N = 1 ∨ χ ≠ 1) :
    ∃ Φ : ℂ → ℂ,
      (∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), Gchi χ (Real.exp u) * cexp (-s * u)) ∧
      (∀ ρ, ρ ≠ 0 → DirichletCharacter.LFunction χ ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
      (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ DirichletCharacter.LFunction χ ρ ≠ 0) ∧
        ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
        ∀ᶠ s in 𝓝[≠] ρ, Φ s = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h s) ∧
      (∀ z, ∀ᶠ w in 𝓝[≠] z, DirichletCharacter.LFunction χ w ≠ 0) := by
  by_cases hχ : χ = 1
  · have hN : N = 1 := adm.resolve_right (fun h => h hχ)
    subst hN
    simp only [DirichletCharacter.LFunction_modOne_eq]
    set g : ℂ → ℂ := Function.update (fun s => (s - 1) * riemannZeta s) 1 1 with hg_def
    have hg_ne : ∀ w : ℂ, w ≠ 1 → g w = (w - 1) * riemannZeta w := by
      intro w hw
      simp [g, Function.update_apply, hw]
    have hg1 : g 1 = 1 := by simp [g]
    have hg : Differentiable ℂ g := by
      rw [← differentiableOn_univ,
        ← differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem]
      refine ⟨?_, ?_⟩
      · intro z hz
        have hz1 : z ≠ 1 := by simpa using hz
        apply DifferentiableAt.differentiableWithinAt
        have hev : g =ᶠ[𝓝 z] fun s => (s - 1) * riemannZeta s := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hz1] with w hw
          exact hg_ne w hw
        have hd : DifferentiableAt ℂ (fun s => (s - 1) * riemannZeta s) z :=
          DifferentiableAt.mul (by fun_prop) (differentiableAt_riemannZeta hz1)
        exact hd.congr_of_eventuallyEq hev
      · simpa only [g, continuousAt_update_same] using riemannZeta_residue_one
    have hderiv1 : deriv g 1 = Real.eulerMascheroniConstant := by
      have hd : HasDerivAt g (deriv g 1) 1 := (hg 1).hasDerivAt
      rw [hasDerivAt_iff_tendsto_slope] at hd
      refine tendsto_nhds_unique hd (tendsto_riemannZeta_sub_one_div.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : s ≠ 1 := hs
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [slope_def_field, hg_ne s hs1, hg1]
      field_simp
    have hderiv : ∀ s : ℂ, s ≠ 1 →
        deriv g s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
      intro s hs1
      have hev : g =ᶠ[𝓝 s] fun s => (s - 1) * riemannZeta s := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with w hw
        exact hg_ne w hw
      rw [hev.deriv_eq]
      have h1 : HasDerivAt (fun s : ℂ => s - 1) 1 s := (hasDerivAt_id s).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
        (differentiableAt_riemannZeta hs1).hasDerivAt
      have h3 : HasDerivAt (fun s : ℂ => (s - 1) * riemannZeta s)
          (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s := h1.mul h2
      rw [h3.deriv]
      ring
    have hgz : ∀ w : ℂ, g w ≠ 0 ↔ riemannZeta w ≠ 0 := by
      intro w
      by_cases hw : w = 1
      · subst hw
        rw [hg1]
        exact ⟨fun _ => riemannZeta_one_ne_zero, fun _ => one_ne_zero⟩
      · rw [hg_ne w hw]
        have hw' : w - 1 ≠ 0 := sub_ne_zero.mpr hw
        constructor
        · intro h hz
          exact h (by rw [hz, mul_zero])
        · intro h
          exact mul_ne_zero hw' h
    obtain ⟨Φ, h1, h2, h3, h4⟩ := poleData_abstract g hg (by rw [hg1]; exact one_ne_zero) 1
    refine ⟨Φ, ?_, ?_, ?_, ?_⟩
    · intro s hs
      have hs1 : s ≠ 1 := by
        intro h
        rw [h] at hs
        norm_num at hs
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hs0 : s ≠ 0 := by
        intro h
        rw [h] at hs
        norm_num at hs
      have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
      rw [h1 s hs1, poleData_change, mellin_Gchi_modOne χ s (by linarith), hderiv s hs1,
        hg_ne s hs1, hderiv1, hg1]
      congr 1
      field_simp
      ring
    · intro ρ hρ hL
      exact h2 ρ hρ ((hgz ρ).mpr hL)
    · intro ρ hρ
      obtain ⟨m, hm, rest⟩ := h3 ρ hρ
      exact ⟨m, hm.trans (hgz ρ), rest⟩
    · intro z
      filter_upwards [h4 z] with w hw
      exact (hgz w).mp hw
  · obtain ⟨Φ, h1, h2, h3, h4⟩ := poleData_abstract (DirichletCharacter.LFunction χ)
      (DirichletCharacter.differentiable_LFunction hχ)
      (DirichletCharacter.LFunction_apply_one_ne_zero hχ) 0
    refine ⟨Φ, ?_, h2, h3, h4⟩
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hs
      norm_num at hs
    rw [h1 s hs1, poleData_change, mellin_Gchi_of_ne_one χ hχ s (by linarith), zero_mul, add_zero]

theorem poleData_inv_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) :
    DirichletCharacter.LFunction χ⁻¹ ρ = 0 ↔
      DirichletCharacter.LFunction χ ((starRingEnd ℂ) ρ) = 0 := by
  have := LFunction_conj χ ((starRingEnd ℂ) ρ)
  rw [Complex.conj_conj] at this
  rw [this, map_eq_zero]

theorem poleData (F : CharFamily) : ∃ Φ : ℂ → ℂ, PoleData (gm F) Φ (zeroSet F) := by
  classical
  have adm' : ∀ i, F.N i = 1 ∨ (F.χ i)⁻¹ ≠ 1 := fun i => (F.adm i).imp id (fun h => inv_ne_one.mpr h)
  choose Φ1 hΦ1int hΦ1an hΦ1pol hΦ1iso using fun i => poleData_char (F.χ i) (F.adm i)
  choose Φ2 hΦ2int hΦ2an hΦ2pol hΦ2iso using fun i => poleData_char (F.χ i)⁻¹ (adm' i)
  choose C hC using fun i => Gchi_growth (F.χ i)
  have hZ : ∀ ρ, ρ ∈ zeroSet F ↔ 0 < ρ.re ∧ ∃ i, DirichletCharacter.LFunction (F.χ i) ρ = 0 ∨
      DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) ρ) = 0 := by
    intro ρ
    rw [zeroSet.eq_1]
    rfl
  have hconj : ∀ i (w : ℂ), DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) w) = 0 ↔
      DirichletCharacter.LFunction (F.χ i)⁻¹ w = 0 := fun i w => (poleData_inv_zero (F.χ i) w).symm
  refine ⟨fun s => ∑ i, (F.a i : ℂ) / 2 * (Φ1 i s + Φ2 i s), ?_⟩
  refine PoleData.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have hg : gm F = fun u => ∑ i, F.a i * (Gchi (F.χ i) (Real.exp u)).re := by
      funext u
      rw [gm.eq_1, Gm.eq_1]
    rw [hg]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Complex.measurable_re.comp ((measurable_Gchi (F.χ i)).comp Real.measurable_exp))
  · refine ⟨∑ i, F.a i * C i, fun u hu => ?_⟩
    rw [gm.eq_1, Gm.eq_1]
    have hy : 1 ≤ Real.exp u := Real.one_le_exp hu
    have he : Real.exp u ^ 2 = Real.exp (2 * u) := by
      rw [sq, ← Real.exp_add, two_mul]
    calc |∑ i, F.a i * (Gchi (F.χ i) (Real.exp u)).re|
        ≤ ∑ i, |F.a i * (Gchi (F.χ i) (Real.exp u)).re| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, F.a i * (C i * Real.exp (2 * u)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_pos (F.a_pos i)]
        apply mul_le_mul_of_nonneg_left _ (F.a_pos i).le
        calc |(Gchi (F.χ i) (Real.exp u)).re| ≤ ‖Gchi (F.χ i) (Real.exp u)‖ := Complex.abs_re_le_norm _
          _ ≤ C i * Real.exp u ^ 2 := hC i _ hy
          _ = C i * Real.exp (2 * u) := by rw [he]
      _ = (∑ i, F.a i * C i) * Real.exp (2 * u) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
  · intro s hs
    have hpt : ∀ u : ℝ, ((gm F u : ℝ) : ℂ) * cexp (-s * u) = ∑ i, (F.a i : ℂ) / 2 *
        (Gchi (F.χ i) (Real.exp u) * cexp (-s * u) + Gchi (F.χ i)⁻¹ (Real.exp u) * cexp (-s * u)) := by
      intro u
      rw [gm.eq_1, Gm.eq_1]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_eq_add_conj, Gchi_conj]
      ring
    simp_rw [hpt]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_const_mul, integral_add (poleData_integrable _ s hs) (poleData_integrable _ s hs),
        hΦ1int i s hs, hΦ2int i s hs]
    · intro i _
      exact ((poleData_integrable _ s hs).add (poleData_integrable _ s hs)).const_mul _
  · intro ρ hρ
    exact ((hZ ρ).1 hρ).1
  · intro s hs
    obtain ⟨hsre, hsZ⟩ := hs
    have hsre' : 0 < s.re := hsre
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre'; simp at hsre'
    have hL : ∀ i, DirichletCharacter.LFunction (F.χ i) s ≠ 0 ∧
        DirichletCharacter.LFunction (F.χ i)⁻¹ s ≠ 0 := by
      intro i
      constructor
      · intro h
        exact hsZ ((hZ s).2 ⟨hsre', i, Or.inl h⟩)
      · intro h
        exact hsZ ((hZ s).2 ⟨hsre', i, Or.inr ((hconj i s).2 h)⟩)
    apply DifferentiableAt.differentiableWithinAt
    have han : AnalyticAt ℂ (fun s => ∑ i, (F.a i : ℂ) / 2 * (Φ1 i s + Φ2 i s)) s := by
      apply Finset.analyticAt_fun_sum
      intro i _
      exact analyticAt_const.mul ((hΦ1an i s hs0 (hL i).1).add (hΦ2an i s hs0 (hL i).2))
    exact han.differentiableAt
  · intro z _
    have hall : ∀ᶠ w in 𝓝[≠] z, ∀ i, DirichletCharacter.LFunction (F.χ i) w ≠ 0 ∧
        DirichletCharacter.LFunction (F.χ i)⁻¹ w ≠ 0 := by
      rw [Filter.eventually_all]
      intro i
      exact (hΦ1iso i z).and (hΦ2iso i z)
    filter_upwards [hall] with w hw hwZ
    obtain ⟨_, i, hi⟩ := (hZ w).1 hwZ
    rcases hi with hi | hi
    · exact (hw i).1 hi
    · exact (hw i).2 ((hconj i w).1 hi)
  · intro ρ hρ
    obtain ⟨hρre, i0, hi0⟩ := (hZ ρ).1 hρ
    have hρ0 : ρ ≠ 0 := fun h => by rw [h] at hρre; simp at hρre
    have hρ1 : ρ ≠ 1 := by
      intro h
      rcases hi0 with h' | h'
      · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 ρ (by rw [h]; simp) h'
      · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 _ (by rw [h]; simp) h'
    choose m1 hm1 h1 hh1an hh1ev using fun i => hΦ1pol i ρ hρ0
    choose m2 hm2 h2 hh2an hh2ev using fun i => hΦ2pol i ρ hρ0
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ i, F.a i / 2 * ((m1 i : ℝ) + m2 i) := ⟨_, rfl⟩
    have hS0 : 0 < S := by
      have hpos : 0 < F.a i0 / 2 * ((m1 i0 : ℝ) + m2 i0) := by
        apply mul_pos (by linarith [F.a_pos i0])
        have hm1n : (0:ℝ) ≤ m1 i0 := Nat.cast_nonneg _
        have hm2n : (0:ℝ) ≤ m2 i0 := Nat.cast_nonneg _
        rcases hi0 with h | h
        · have hne : m1 i0 ≠ 0 := fun hm => ((hm1 i0).1 hm) h
          have : (1:ℝ) ≤ m1 i0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          linarith
        · have hne : m2 i0 ≠ 0 := fun hm => ((hm2 i0).1 hm) ((hconj i0 ρ).1 h)
          have : (1:ℝ) ≤ m2 i0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
          linarith
      rw [hS]
      calc 0 < F.a i0 / 2 * ((m1 i0 : ℝ) + m2 i0) := hpos
        _ ≤ ∑ i, F.a i / 2 * ((m1 i : ℝ) + m2 i) :=
          Finset.single_le_sum (f := fun i => F.a i / 2 * ((m1 i : ℝ) + m2 i))
            (fun i _ => by have := F.a_pos i; positivity) (Finset.mem_univ i0)
    refine ⟨(S : ℂ) * (-1 / (ρ * (ρ - 1))), ?_, ?_, ?_⟩
    · have hr0 : (-1 / (ρ * (ρ - 1)) : ℂ) ≠ 0 :=
        div_ne_zero (by norm_num) (mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1))
      exact mul_ne_zero (by exact_mod_cast hS0.ne') hr0
    · intro him
      have hρx : ρ = (ρ.re : ℂ) := by
        apply Complex.ext <;> simp [him]
      have hlt : ρ.re < 1 := by
        by_contra hge
        push_neg at hge
        rcases hi0 with h' | h'
        · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 ρ hge h'
        · exact charFamily_LFunction_ne_zero_of_one_le_re F i0 _ (by simpa using hge) h'
      have hc : (S : ℂ) * (-1 / (ρ * (ρ - 1))) = ((S * (-1 / (ρ.re * (ρ.re - 1))) : ℝ) : ℂ) := by
        push_cast
        rw [← hρx]
      rw [hc, Complex.ofReal_re, Complex.ofReal_im]
      refine ⟨?_, rfl⟩
      have hneg : ρ.re * (ρ.re - 1) < 0 := mul_neg_of_pos_of_neg hρre (by linarith)
      exact mul_pos hS0 (div_pos_of_neg_of_neg (by norm_num) hneg)
    · refine ⟨fun s => ∑ i, (F.a i : ℂ) / 2 * (h1 i s + h2 i s), ?_, ?_⟩
      · apply Finset.analyticAt_fun_sum
        intro i _
        exact analyticAt_const.mul ((hh1an i).add (hh2an i))
      · have hev : ∀ᶠ s in 𝓝[≠] ρ, ∀ i,
            Φ1 i s = (m1 i : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h1 i s ∧
            Φ2 i s = (m2 i : ℂ) * (-1 / (ρ * (ρ - 1))) / (s - ρ) + h2 i s := by
          rw [Filter.eventually_all]
          intro i
          exact (hh1ev i).and (hh2ev i)
        filter_upwards [hev] with s hs
        rw [hS]
        push_cast
        rw [Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [(hs i).1, (hs i).2]
        ring

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.WindowHypUOfWindowHyp
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem windowHypU_of_windowHyp_image (a b : ℝ) :
    Real.exp '' Icc a b = Icc (Real.exp a) (Real.exp b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨Real.exp_le_exp.2 h1, Real.exp_le_exp.2 h2⟩
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := lt_of_lt_of_le (Real.exp_pos a) h1
    refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy⟩
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h1
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h2

theorem windowHypU_of_windowHyp_fun (R : ℝ → ℝ) (θ : ℝ) :
    (fun u : ℝ => |Real.exp u| • (R (Real.exp u) * Real.exp u ^ (-θ - 1))) =
      fun u => R (Real.exp u) * Real.exp (-θ * u) := by
  funext u
  rw [abs_of_pos (Real.exp_pos u), smul_eq_mul, ← Real.exp_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

theorem windowHypU_of_windowHyp (F : CharFamily) {θ δ : ℝ} (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    WindowHypU (gm F) θ δ := by
  intro η hη U₀
  obtain ⟨Y, hY, R, hint, hR, hbound⟩ := h η hη (Real.exp U₀)
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hS : Real.exp '' Icc (Real.log Y) ((1 + δ) * Real.log Y) = Icc Y (Y ^ (1 + δ)) := by
    rw [windowHypU_of_windowHyp_image, Real.exp_log hYpos, Real.rpow_def_of_pos hYpos, mul_comm]
  have hd : ∀ x ∈ Icc (Real.log Y) ((1 + δ) * Real.log Y),
      HasDerivWithinAt Real.exp (Real.exp x) (Icc (Real.log Y) ((1 + δ) * Real.log Y)) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp (Icc (Real.log Y) ((1 + δ) * Real.log Y)) :=
    Real.exp_injective.injOn
  refine ⟨Real.log Y, ?_, fun u => R (Real.exp u), ?_, ?_, ?_⟩
  · rw [← Real.exp_le_exp, Real.exp_log hYpos]; exact hY
  · have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hd hinj
      (fun y => R y * y ^ (-θ - 1))).1 (by rw [hS]; exact hint)
    rw [windowHypU_of_windowHyp_fun] at this
    exact this
  · intro u hu
    have hmem : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) := by
      rw [← hS]; exact ⟨u, hu, rfl⟩
    exact hR _ hmem
  · have e := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd hinj
      (fun y => R y * y ^ (-θ - 1))
    rw [hS, windowHypU_of_windowHyp_fun] at e
    rw [← e]
    calc ∫ y in Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η := hbound
      _ = Real.exp (η * Real.log Y) := by rw [Real.rpow_def_of_pos hYpos, mul_comm]

end Deduction

end
end

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem lemmaL (F : CharFamily) {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    ZeroFree F θ := by
  intro i s hs hzero
  obtain ⟨Φ, hP⟩ := poleData F
  have hZ := landau_window hP hθ hθ1 hδ (windowHypU_of_windowHyp F hδ h)
  by_cases h1 : 1 ≤ s.re
  · exact charFamily_LFunction_ne_zero_of_one_le_re F i s h1 hzero
  · have hmem : s ∈ zeroSet F := ⟨by linarith, i, Or.inl hzero⟩
    have := hZ s hmem
    linarith

end Deduction

end
