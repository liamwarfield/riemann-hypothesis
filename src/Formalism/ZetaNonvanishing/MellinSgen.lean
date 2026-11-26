module

public import Formalism.StatementU

@[expose] public section

section -- merged from Formalism.ZetaNonvanishing.MellinSAux
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def mxS (n : ℕ) (x : ℝ) : ℝ := max (x / n - 1) 0

lemma mxS_nonneg (n : ℕ) (x : ℝ) : 0 ≤ mxS n x := by
  show 0 ≤ max (x / n - 1) 0
  exact le_max_right _ _

lemma mxS_eq_indicator {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    mxS n x = (Ioi (n : ℝ)).indicator (fun x => x / n - 1) x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  show max (x / n - 1) 0 = _
  by_cases hx : x ∈ Ioi (n : ℝ)
  · rw [Set.indicator_of_mem hx]
    have h1 : 1 ≤ x / n := by
      rw [le_div_iff₀ hn0]
      have := Set.mem_Ioi.mp hx
      linarith
    exact max_eq_left (sub_nonneg.mpr h1)
  · rw [Set.indicator_of_notMem hx]
    have h1 : x / n ≤ 1 := (div_le_one hn0).mpr (le_of_not_gt (fun h => hx (Set.mem_Ioi.mpr h)))
    exact max_eq_right (sub_nonpos.mpr h1)

lemma mxS_mellin {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1) = (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : (-s).re < -1 := by
    simp only [Complex.neg_re]
    linarith
  have hb : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  have hs2 : -s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at h'
    linarith

  have hfun : (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
  have heq : EqOn (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans hn0 (Set.mem_Ioi.mp hx)).ne'
    have hpow : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
      calc (x : ℂ) ^ (-s) = (x : ℂ) ^ ((-s - 1) + 1) := by rw [sub_add_cancel]
        _ = (x : ℂ) ^ (-s - 1) * x := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
    show ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)
    rw [hpow]
    push_cast
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_cpow_of_lt ha hn0) (1 / (n : ℂ))
  have hB : Integrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_cpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_cpow_of_lt ha hn0, integral_Ioi_cpow_of_lt hb hn0, sub_add_cancel,
    Complex.ofReal_natCast, Complex.cpow_add _ _ hnC, Complex.cpow_one]
  field_simp
  ring

lemma mxS_mellin_real {n : ℕ} (hn : 1 ≤ n) {σ : ℝ} (hσ : 1 < σ) :
    IntegrableOn (fun x : ℝ => mxS n x * x ^ (-σ - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), mxS n x * x ^ (-σ - 1) = (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : -σ < -1 := by linarith
  have hb : -σ - 1 < -1 := by linarith
  have hσ0 : σ ≠ 0 := (by linarith : (0 : ℝ) < σ).ne'
  have hσ1 : σ - 1 ≠ 0 := (by linarith : (0 : ℝ) < σ - 1).ne'
  have hσ2 : -σ + 1 ≠ 0 := (by linarith : -σ + 1 < 0).ne
  have hnR : (n : ℝ) ≠ 0 := hn0.ne'

  have hfun : (fun x : ℝ => mxS n x * x ^ (-σ - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have heq : EqOn (fun x : ℝ => (x / n - 1) * x ^ (-σ - 1))
      (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hn0 (Set.mem_Ioi.mp hx)
    have hpow : x ^ (-σ) = x ^ (-σ - 1) * x := by
      calc x ^ (-σ) = x ^ ((-σ - 1) + 1) := by rw [sub_add_cancel]
        _ = x ^ (-σ - 1) * x := by rw [Real.rpow_add hx0, Real.rpow_one]
    show (x / n - 1) * x ^ (-σ - 1) = 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1)
    rw [hpow]
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_rpow_of_lt ha hn0) (1 / (n : ℝ))
  have hB : Integrable (fun x : ℝ => x ^ (-σ - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_rpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℝ) * x ^ (-σ) - x ^ (-σ - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_rpow_of_lt ha hn0, integral_Ioi_rpow_of_lt hb hn0, sub_add_cancel,
    Real.rpow_add hn0, Real.rpow_one]
  field_simp
  ring

lemma integrable_tsum_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : ℕ → α → ℝ} (hφ : ∀ n, Integrable (φ n) μ) (h0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ φ n x)
    (hsx : ∀ x, Summable (fun n => φ n x)) (hs : Summable fun n => ∫ x, φ n x ∂μ) :
    Integrable (fun x => ∑' n, φ n x) μ := by
  have hall : ∀ᵐ x ∂μ, ∀ n, 0 ≤ φ n x := ae_all_iff.mpr h0
  have hm : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (φ n x)) μ :=
    fun n => (hφ n).aemeasurable.ennreal_ofReal
  have hmeas : AEMeasurable (fun x => ∑' n, ENNReal.ofReal (φ n x)) μ :=
    AEMeasurable.tsum hm
  have hlin : ∫⁻ x, ∑' n, ENNReal.ofReal (φ n x) ∂μ = ENNReal.ofReal (∑' n, ∫ x, φ n x ∂μ) := by
    rw [lintegral_tsum hm,
      ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg_of_ae (h0 n)) hs]
    exact tsum_congr fun n => (ofReal_integral_eq_lintegral_ofReal (hφ n) (h0 n)).symm
  have hint := integrable_toReal_of_lintegral_ne_top hmeas (by rw [hlin]; exact ENNReal.ofReal_ne_top)
  refine hint.congr ?_
  filter_upwards [hall] with x hx
  rw [← ENNReal.ofReal_tsum_of_nonneg hx (hsx x), ENNReal.toReal_ofReal (tsum_nonneg hx)]

end Formalism
end
end

open Complex MeasureTheory Set Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism

section
variable (a : ℕ → ℝ)

lemma Sa_measurable : Measurable (Sa a) := by
  have hk : ∀ k : ℕ, Measurable fun x : ℝ => ∑ n ∈ Finset.Icc 1 k, a n * (x / n - 1) :=
    fun k => Finset.measurable_sum _ fun n _ => by fun_prop
  unfold Sa
  first
    | (have hg : Measurable (fun p : ℝ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, a n * (p.1 / n - 1)) := by
        first
          | exact measurable_from_prod_countable_right hk
          | exact measurable_from_prod_countable_left hk
          | exact measurable_from_prod_countable hk
       exact hg.comp (measurable_id.prodMk Nat.measurable_floor))
    | (have hg : Measurable (fun p : ℕ × ℝ => ∑ n ∈ Finset.Icc 1 p.1, a n * (p.2 / n - 1)) := by
        first
          | exact measurable_from_prod_countable_left hk
          | exact measurable_from_prod_countable_right hk
       exact hg.comp (Nat.measurable_floor.prodMk measurable_id))

lemma a_mxS_eq_zero (ha0 : a 0 = 0) (x : ℝ) (n : ℕ) (hn : n ∉ Finset.Icc 1 ⌊x⌋₊) :
    a n * mxS n x = 0 := by
  unfold mxS
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · have h0 : n = 0 := by omega
    subst h0
    simp [ha0]
  · have hx : x < n := Nat.lt_of_floor_lt hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hle : x / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn0]
      exact hx.le
    rw [max_eq_right hle, mul_zero]

lemma Sa_eq_tsum (ha0 : a 0 = 0) (x : ℝ) : Sa a x = ∑' n, a n * mxS n x := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn)]
  unfold Sa
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx : (n : ℝ) ≤ x := by
    have hx0 : 0 ≤ x := by
      by_contra hneg
      push_neg at hneg
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hn
      omega
    exact (Nat.le_floor_iff hx0).mp hn.2
  have hnn : 0 ≤ x / n - 1 := by
    rw [sub_nonneg, le_div_iff₀ hn0]
    linarith
  unfold mxS
  rw [max_eq_left hnn]

lemma summable_a_mxS (ha0 : a 0 = 0) (x : ℝ) : Summable (fun n => a n * mxS n x) :=
  summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn)

lemma abs_Sa_le (ha0 : a 0 = 0) (x : ℝ) : |Sa a x| ≤ ∑' n, |a n| * mxS n x := by
  have hm : ∀ n, 0 ≤ mxS n x := fun n => by
    unfold mxS
    exact le_max_right _ _
  rw [Sa_eq_tsum a ha0 x, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn),
    tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => by
      have h := a_mxS_eq_zero a ha0 x n hn
      rcases mul_eq_zero.mp h with h | h <;> simp [h])]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  rw [abs_mul, abs_of_nonneg (hm n)]

lemma summable_abs_a (K : ℝ) (hK : ∀ n : ℕ, |a n| ≤ K * vonMangoldt n) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => |a n| * (n : ℝ) ^ (-σ)) := by
  have hs : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n => ?_) (hs.norm.mul_left |K|)
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  · have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.norm_term_eq, if_neg hn.ne']
    simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg hΛ]
    rw [div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
    have hK' : |a n| ≤ |K| * ArithmeticFunction.vonMangoldt n :=
      (hK n).trans (mul_le_mul_of_nonneg_right (le_abs_self K) hΛ)
    calc |a n| * (n : ℝ) ^ (-σ) ≤ |K| * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hK' (Real.rpow_nonneg hnpos.le _)
      _ = |K| * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) := by ring

end

theorem mellinSgen : MellinSgen := by
  intro a K hK
  have ha0 : a 0 = 0 := by
    have h := hK 0
    rw [ArithmeticFunction.map_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  refine ⟨Sa_measurable a, fun σ hσ => ?_, fun s hs => ?_⟩
  · have key := integrable_tsum_of_nonneg (μ := volume.restrict (Ioi (1 : ℝ)))
      (φ := fun n x => |a n| * (mxS n x * x ^ (-σ - 1))) (fun n => ?_) (fun n => ?_)
      (fun x => ?_) ?_
    · have hmeas : Measurable (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) := by
        have := Sa_measurable a
        fun_prop
      refine key.mono' hmeas.aestronglyMeasurable ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      have hxp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hxp)]
      calc |Sa a x| * x ^ (-σ - 1) ≤ (∑' n, |a n| * mxS n x) * x ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right (abs_Sa_le a ha0 x) hxp
        _ = ∑' n, |a n| * (mxS n x * x ^ (-σ - 1)) := by
            rw [← tsum_mul_right]; congr 1; funext n; ring
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [ha0]
      · exact ((mxS_mellin_real hn hσ).1).const_mul _
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (mxS_nonneg n x)
        (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _))
    · have ha0' : |a 0| = 0 := by simp [ha0]
      simpa only [mul_assoc] using
        (summable_a_mxS (fun n => |a n|) ha0' x).mul_right (x ^ (-σ - 1))
    · have : (fun n => ∫ x in Ioi (1 : ℝ), |a n| * (mxS n x * x ^ (-σ - 1))) =
          fun n : ℕ => |a n| * (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
        funext n
        rw [integral_const_mul]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [ha0]
        · rw [(mxS_mellin_real hn hσ).2]; ring
      rw [this]; exact (summable_abs_a a K hK hσ).div_const _
  · set F : ℕ → ℝ → ℂ := fun n x => (a n : ℂ) * ((mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) with hFdef
    have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (1 : ℝ))) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [F, ha0]
      · exact ((mxS_mellin hn hs).1).const_mul _
    have hnorm : ∀ n, ∫ x in Ioi (1 : ℝ), ‖F n x‖ =
        |a n| * (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
      intro n
      rw [setIntegral_congr_fun measurableSet_Ioi
        (g := fun x => |a n| * (mxS n x * x ^ (-s.re - 1))) (fun x hx => ?_)]
      · rw [integral_const_mul]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [ha0]
        · rw [(mxS_mellin_real hn hs).2]; ring
      · have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
        simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mxS_nonneg n x), norm_cpow_eq_rpow_re_of_pos hx0]
        congr 3
    have hsum : Summable (fun n => ∫ x in Ioi (1 : ℝ), ‖F n x‖) := by
      simp_rw [hnorm]; exact (summable_abs_a a K hK hs).div_const _
    have hpt : ∀ x ∈ Ioi (1 : ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) = ∑' n, F n x := by
      intro x hx
      rw [Sa_eq_tsum a ha0, ofReal_tsum, ← tsum_mul_right]
      congr 1; funext n; simp only [F]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      ← integral_tsum_of_summable_integral_norm hint hsum, LSeries, ← tsum_div_const]
    congr 1; funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, ha0]
    · simp only [F]
      rw [integral_const_mul, (mxS_mellin hn hs).2, LSeries.term_of_ne_zero (by omega), cpow_neg]
      ring

end Formalism
