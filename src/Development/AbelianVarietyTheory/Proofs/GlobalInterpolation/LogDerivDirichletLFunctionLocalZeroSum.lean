module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionEqTsumOfOneLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivDirichletLFunctionLocalZeroSum
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableAtMellinSummatory
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LGrowth

open Filter Topology Asymptotics

theorem norm_partialSum_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)‖ ≤ q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hper : ∀ m : ℕ, ∑ k ∈ Finset.range q, χ ((m + k : ℕ) : ZMod q) = 0 := by
    intro m
    have h0 : ∑ a : ZMod q, χ a = 0 := χ.sum_eq_zero_of_ne_one hχ
    rw [← h0, ← Equiv.sum_comp (Equiv.addLeft (m : ZMod q))]
    refine Finset.sum_bij (fun k _ => (k : ZMod q)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
    · intro a ha b hb hab
      have := (ZMod.natCast_eq_natCast_iff' a b q).1 hab
      rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 ha), Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
        at this
    · intro b _
      exact ⟨b.val, Finset.mem_range.2 (ZMod.val_lt b), ZMod.natCast_zmod_val b⟩
    · intro a _
      simp
  have hI : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q)
      = ∑ k ∈ Finset.range n, χ ((1 + k : ℕ) : ZMod q) := by
    intro n
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp
  rw [hI]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n q with h | h
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun k _ => χ.norm_le_one _).trans ?_
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      exact_mod_cast h.le
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      rw [Finset.sum_range_add]
      have := hper (1 + m)
      simp only [← add_assoc]
      rw [this, add_zero]
      exact ih m (by omega)

section General

variable {f : ℕ → ℂ} {C : ℝ}

noncomputable def summatory (f : ℕ → ℂ) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

theorem measurable_summatory (f : ℕ → ℂ) : Measurable (summatory f) :=
  (measurable_from_top (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

theorem summatory_eq_zero {t : ℝ} (ht : t < 1) : summatory f t = 0 := by
  simp [summatory, Nat.floor_eq_zero.2 ht]

theorem mellin_summatory (s : ℂ) :
    mellin (summatory f) (-s) =
      ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k) * (t : ℂ) ^ (-(s + 1)) := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi
    (s := Set.Ici (1 : ℝ)) (fun t ht => Set.mem_Ioi.2 (zero_lt_one.trans_le (Set.mem_Ici.1 ht))), integral_Ici_eq_integral_Ioi]
  · refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [summatory, smul_eq_mul]
    rw [mul_comm]
    congr 2
    ring
  · intro t ht
    rw [summatory_eq_zero (not_le.1 ht.2), smul_zero]

theorem differentiableAt_mellin_summatory (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (summatory f) (-z)) s := by
  have h : DifferentiableAt ℂ (mellin (summatory f)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1) ?_ ?_ ?_ ?_ ?_
    · refine LocallyIntegrable.locallyIntegrableOn ?_ _
      refine (locallyIntegrable_const C).mono (measurable_summatory f).aestronglyMeasurable ?_
      exact Eventually.of_forall fun t => (hC _).trans (Real.le_norm_self C)
    · refine IsBigO.of_bound C (Eventually.of_forall fun t => ?_)
      simpa [summatory] using hC ⌊t⌋₊
    · simpa using hs
    · refine IsBigO.of_bound 0 ?_
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
      simp [summatory_eq_zero ht]
    · simp
  exact h.comp s differentiableAt_id.neg

theorem norm_mellin_summatory_le (hC : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    ‖mellin (summatory f) (-s)‖ ≤ C / s.re := by
  rw [mellin_summatory]
  have hlt : -(s.re + 1) < -1 := by linarith
  refine (norm_integral_le_of_norm_le (g := fun t : ℝ => C * t ^ (-(s.re + 1)))
    ((integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul C) ?_).trans ?_
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [neg_re, add_re, one_re]
    exact mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg ht0.le _)
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt zero_lt_one, Real.one_rpow]
    refine le_of_eq ?_
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this]
    field_simp

end General

theorem LFunction_eq_mul_mellin (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * mellin (summatory fun n => χ (n : ZMod q)) (-s) := by
  have hC := norm_partialSum_le q χ hχ
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have h1 : AnalyticOnNhd ℂ (LFunction χ) {z : ℂ | 0 < z.re} :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hU
  have h2 : AnalyticOnNhd ℂ (fun z => z * mellin (summatory fun n => χ (n : ZMod q)) (-z))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hU
    exact (differentiableAt_id.mul
      (differentiableAt_mellin_summatory hC hz)).differentiableWithinAt
  refine h1.eqOn_of_preconnected_of_eventuallyEq h2 (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := 2) (by simp) ?_ hs
  have hV : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
  filter_upwards [hV.mem_nhds (show (2 : ℂ) ∈ {z : ℂ | 1 < z.re} by simp)] with z hz
  rw [LFunction_eq_LSeries χ hz, mellin_summatory]
  refine LSeries_eq_mul_integral _ le_rfl (zero_lt_one.trans hz)
    (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hz) ?_
  refine IsBigO.of_bound q (Eventually.of_forall fun n => ?_)
  simpa using hC n

theorem norm_LFunction_le : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ s : ℂ, 0 < s.re → ‖LFunction χ s‖ ≤ q * ‖s‖ / s.re := by
  intro q _ χ hχ s hs
  rw [LFunction_eq_mul_mellin q χ hχ hs, norm_mul]
  refine (mul_le_mul_of_nonneg_left
    (norm_mellin_summatory_le (norm_partialSum_le q χ hχ) hs) (norm_nonneg s)).trans ?_
  exact le_of_eq (by ring)

end GlobalTheory.LGrowth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivDirichletLFunctionLocalZeroSum
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LLocal

theorem analyticOrderNatAt_comp_const_add (g : ℂ → ℂ) (c w : ℂ) :
    analyticOrderNatAt (fun z => g (c + z)) w = analyticOrderNatAt g (c + w) := by
  unfold analyticOrderNatAt
  congr 1
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := g) (g := fun z : ℂ => c + z) (z₀ := w)
    (by fun_prop) (by simp)
  exact h

theorem logDeriv_LFunction_local : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (2/3) (5/6) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨6 * C, by positivity, ?_⟩
  intro q _ χ hχ t s hs hLs
  set c : ℂ := 3/2 + t * I with hc
  have hcre : c.re = 3/2 := by simp [hc]
  have hcn : ‖c‖ ≤ 3/2 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
  have ht : 0 ≤ |t| := abs_nonneg t
  have hd : Differentiable ℂ (LFunction χ) := differentiable_LFunction hχ
  have hf : AnalyticOnNhd ℂ (fun z => LFunction χ (c + z)) (Metric.closedBall 0 1) := by
    intro z _
    have : Differentiable ℂ (fun z => LFunction χ (c + z)) := hd.comp (by fun_prop)
    exact this.analyticAt z
  have hlow : 1/3 ≤ ‖LFunction χ (c + 0)‖ := by
    have := GlobalTheory.LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)
    rw [hcre] at this
    rw [add_zero]
    linarith
  have hf0 : LFunction χ (c + 0) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hM : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖LFunction χ (c + z)‖ ≤ q * (2 * |t| + 5) := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have hre : 1/2 ≤ (c + z).re := by
      have := (abs_le.1 ((Complex.abs_re_le_norm z).trans hz1)).1
      rw [add_re, hcre]; linarith
    have hn : ‖c + z‖ ≤ |t| + 5/2 := by
      have := norm_add_le c z
      linarith
    refine (GlobalTheory.LGrowth.norm_LFunction_le q χ hχ (c + z) (by linarith)).trans ?_
    rw [div_le_iff₀ (by linarith)]
    calc (q : ℝ) * ‖c + z‖ ≤ q * (|t| + 5/2) := by gcongr
      _ = q * (2 * |t| + 5) * (1/2) := by ring
      _ ≤ _ := by gcongr
  obtain ⟨⟨hfin, -⟩, hb⟩ := H _ _ hf hf0 hM
  have hb' := hb (s - c) hs (by simpa using hLs)
  have hset : {w : ℂ | ‖w - c‖ ≤ 5/6 ∧ LFunction χ w = 0} =
      (fun z => c + z) '' {w : ℂ | ‖w‖ ≤ 5/6 ∧ LFunction χ (c + w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨w - c, ⟨h1, by simpa using h2⟩, by simp⟩
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      exact ⟨by simpa using h1, h2⟩
  rw [hset]
  refine ⟨hfin.image _, ?_⟩
  rw [finsum_mem_image (fun a _ b _ h => add_left_cancel h)]
  rw [deriv_comp_const_add] at hb'
  simp only [analyticOrderNatAt_comp_const_add, add_sub_cancel, sub_sub] at hb'
  refine hb'.trans ?_
  set X : ℝ := q * (|t| + 2) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hl2 : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX2
  have hl : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hp : 0 < ‖LFunction χ (c + 0)‖ := by linarith
  have h8 : q * (2 * |t| + 5) / ‖LFunction χ (c + 0)‖ ≤ 2 ^ 3 * X := by
    rw [div_le_iff₀ hp]
    calc (q : ℝ) * (2 * |t| + 5) ≤ 2 ^ 3 * X * (1/3) := by rw [hX]; nlinarith
      _ ≤ _ := by gcongr
  have h9 := Real.log_le_log (by positivity) h8
  rw [Real.log_mul (by norm_num) (by linarith), Real.log_pow] at h9
  push_cast at h9
  have : 1 + Real.log (q * (2 * |t| + 5) / ‖LFunction χ (c + 0)‖) ≤ 6 * Real.log X := by
    linarith
  calc _ ≤ C * (6 * Real.log X) := by gcongr
    _ = _ := by ring

end GlobalTheory.LLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivDirichletLFunctionLocalZeroSumStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDeriv_dirichletLFunction_local_zero_sum : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (t : ℝ) (s : ℂ), ‖s - (3/2 + t * I)‖ ≤ 2/3 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}.Finite ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (3/2 + t * I)‖ ≤ 5/6 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|t| + 2)) := by
  first | exact @GlobalTheory.LLocal.logDeriv_LFunction_local | exact GlobalTheory.LLocal.logDeriv_LFunction_local | (intros; apply GlobalTheory.LLocal.logDeriv_LFunction_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumTruncConv
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.ZeroDetect

theorem _root_.GlobalTheory.ZeroDetect.sum_trunc_conv (a f : ℕ → ℂ)
    (hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n)
    (D X : ℕ) :
    ∑ n ∈ Finset.Ioc 0 X, (∑ d ∈ n.divisors.filter (fun d => d ≤ D), a d) * f n
      = ∑ d ∈ Finset.Icc 1 D, a d * f d * ∑ m ∈ Finset.Icc 1 (X / d), f m := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 D)
    (s' := fun d => (Finset.Ioc 0 X).filter (fun n => d ∣ n))]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 0 < d := (Finset.mem_Icc.1 hd).1
    rw [Finset.mul_sum]
    refine Finset.sum_bij' (fun n _ => n / d) (fun m _ => d * m) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h0, hX⟩, k, rfl⟩ := hn
      have hk : 0 < k := Nat.pos_of_mul_pos_left h0
      rw [Nat.mul_div_cancel_left k hd1, Finset.mem_Icc]
      exact ⟨hk, (Nat.le_div_iff_mul_le hd1).2 (by rw [mul_comm]; exact hX)⟩
    · intro m hm
      rw [Finset.mem_Icc] at hm
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, dvd_mul_right d m⟩
      have := (Nat.le_div_iff_mul_le hd1).1 hm.2
      rw [mul_comm]; exact this
    · intro n hn
      simp only [Finset.mem_filter] at hn
      exact Nat.mul_div_cancel' hn.2
    · intro m _
      exact Nat.mul_div_cancel_left m hd1
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
      obtain ⟨⟨h0, _⟩, k, rfl⟩ := hn
      have hk : 0 < k := Nat.pos_of_mul_pos_left h0
      rw [Nat.mul_div_cancel_left k hd1, hf d k hd1 hk]
      ring
  · intro n d
    simp only [Finset.mem_Ioc, Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h0, hX⟩, ⟨hdn, -⟩, hdD⟩
      exact ⟨⟨⟨h0, hX⟩, hdn⟩, Nat.pos_of_dvd_of_pos hdn h0, hdD⟩
    · rintro ⟨⟨⟨h0, hX⟩, hdn⟩, -, hdD⟩
      exact ⟨⟨h0, hX⟩, ⟨hdn, h0.ne'⟩, hdD⟩

theorem _root_.GlobalTheory.ZeroDetect.sum_initial (f : ℕ → ℂ) (D : ℕ) (hD : 1 ≤ D) :
    ∑ n ∈ Finset.Ioc 0 D,
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ D), (moebius d : ℤ) : ℤ) : ℂ) * f n = f 1 := by
  have hsum : ∀ n, ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
    intro n
    rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  rw [Finset.sum_eq_single 1]
  · simp [Finset.filter_singleton, hD]
  · intro n hn hn1
    have hfil : n.divisors.filter (fun d => d ≤ D) = n.divisors := by
      apply Finset.filter_true_of_mem
      intro d hd
      exact (Nat.divisor_le hd).trans (Finset.mem_Ioc.1 hn).2
    rw [hfil, hsum, if_neg hn1]
    simp
  · intro h
    exact absurd (Finset.mem_Ioc.2 ⟨zero_lt_one, hD⟩) h

theorem _root_.GlobalTheory.ZeroDetect.rpow_bound {Q y σ : ℝ} (hQ : 1024 ≤ Q) (hy : Q ^ 6 ≤ 2 * y)
    (hσ : 11 / 12 ≤ σ) :
    y ^ (-σ) ≤ (16 * Q ^ 5)⁻¹ := by
  have hQ0 : 0 < Q := by linarith
  have hQ6 : (2:ℝ) ^ 60 ≤ Q ^ 6 := by
    calc (2:ℝ) ^ 60 = 1024 ^ 6 := by norm_num
      _ ≤ Q ^ 6 := pow_le_pow_left₀ (by norm_num) hQ 6
  have hy1 : 1 ≤ y := by nlinarith
  have hy0 : 0 < y := by linarith
  have h5 : 0 < 16 * Q ^ 5 := by positivity
  have key : 16 * Q ^ 5 ≤ y ^ ((11:ℝ) / 12) := by
    have hpow : (y ^ ((11:ℝ) / 12)) ^ 12 = y ^ 11 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy0.le]
      norm_num
    have h12 : (16 * Q ^ 5) ^ 12 ≤ (y ^ ((11:ℝ) / 12)) ^ 12 := by
      rw [hpow]
      have hyQ : Q ^ 6 / 2 ≤ y := by linarith
      calc (16 * Q ^ 5) ^ 12 = 2 ^ 48 * Q ^ 60 := by ring
        _ ≤ (Q ^ 6) ^ 11 / 2 ^ 11 := by
          have : (Q ^ 6) ^ 11 = Q ^ 6 * Q ^ 60 := by ring
          rw [this]
          have hQ60 : 0 < Q ^ 60 := by positivity
          rw [le_div_iff₀ (by positivity)]
          nlinarith
        _ = (Q ^ 6 / 2) ^ 11 := by ring
        _ ≤ y ^ 11 := pow_le_pow_left₀ (by positivity) hyQ 11
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h12
  rw [Real.rpow_neg hy0.le]
  apply inv_anti₀ h5
  calc 16 * Q ^ 5 ≤ y ^ ((11:ℝ) / 12) := key
    _ ≤ y ^ σ := Real.rpow_le_rpow_of_exponent_le hy1 hσ

theorem _root_.GlobalTheory.ZeroDetect.zero_detect : ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → q ≤ Q → ∀ ρ : ℂ,
    1 - 1 / 400 ≤ ρ.re → |ρ.im| ≤ Q → LFunction χ ρ = 0 →
    (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ)‖ := by
  refine ⟨1024, fun Q hQ q _ χ hχ hqQ ρ hre him hL => ?_⟩
  have hσ : (11 / 12 : ℝ) ≤ ρ.re := by norm_num at hre; linarith
  have hσ0 : 0 < ρ.re := by linarith
  have hQR : (1024 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hD : Q ^ 3 ≤ Q ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hQ3 : 2 ≤ Q ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) Q)
  have hD2 : 2 * Q ^ 3 ≤ Q ^ 6 := by
    calc 2 * Q ^ 3 ≤ Q ^ 3 * Q ^ 3 := Nat.mul_le_mul_right _ hQ3
      _ = Q ^ 6 := by ring
  set f : ℕ → ℂ := fun n => χ (n : ZMod q) * (n : ℂ) ^ (-ρ) with hfdef
  set a : ℕ → ℂ := fun d => ((moebius d : ℤ) : ℂ) with hadef
  have hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n := by
    intro m n _ _
    simp only [f, Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hS : ∀ Y : ℕ, ∑ n ∈ Finset.Ioc 0 Y,
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      ∑ n ∈ Finset.Ioc 0 Y, (∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), a d) * f n := by
    intro Y
    apply Finset.sum_congr rfl
    intro n _
    simp only [a, f]
    push_cast
    ring
  have hsplit := Finset.sum_Ioc_consecutive (fun n =>
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ)) (Nat.zero_le (Q ^ 3)) hD
  have hinit : ∑ n ∈ Finset.Ioc 0 (Q ^ 3),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) = 1 := by
    calc _ = ∑ n ∈ Finset.Ioc 0 (Q ^ 3),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * f n :=
          Finset.sum_congr rfl (fun n _ => mul_assoc _ _ _)
      _ = f 1 := _root_.GlobalTheory.ZeroDetect.sum_initial f (Q ^ 3) (by omega)
      _ = 1 := by simp [f]
  have hmain : ∑ n ∈ Finset.Ioc 0 (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      ∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m := by
    rw [hS]
    exact _root_.GlobalTheory.ZeroDetect.sum_trunc_conv a f hf _ _
  have hnorm : ‖ρ‖ / ρ.re ≤ 1 + 2 * Q := by
    have h1 := Complex.norm_le_abs_re_add_abs_im ρ
    rw [abs_of_pos hσ0] at h1
    rw [div_le_iff₀ hσ0]
    nlinarith
  set C : ℝ := 2 * (q : ℝ) * (1 + ‖ρ‖ / ρ.re) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hCle : C ≤ 8 * (Q : ℝ) ^ 2 := by
    have h4 : 1 + ‖ρ‖ / ρ.re ≤ 4 * Q := by linarith
    calc C ≤ 2 * (Q : ℝ) * (4 * Q) := by
          apply mul_le_mul (by linarith) h4 (by positivity) (by positivity)
      _ = 8 * (Q : ℝ) ^ 2 := by ring
  have hterm : ∀ d ∈ Finset.Icc 1 (Q ^ 3),
      ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ ≤ C * (16 * (Q : ℝ) ^ 5)⁻¹ := by
    intro d hd
    obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.1 hd
    have hN : 1 ≤ Q ^ 6 / d := (Nat.le_div_iff_mul_le hd1).2 (by omega)
    have hP : ‖∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ ≤ C * ((Q ^ 6 / d : ℕ) : ℝ) ^ (-ρ.re) := by
      have := _root_.GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le q χ hχ ρ hσ0 (Q ^ 6 / d) hN
      rw [hL, zero_sub, norm_neg] at this
      exact this
    have ha : ‖a d‖ ≤ 1 := by
      simp only [a]
      rw [Complex.norm_intCast]
      exact_mod_cast abs_moebius_le_one
    have hfd : ‖f d‖ ≤ (d : ℝ) ^ (-ρ.re) := by
      simp only [f]
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hd1, Complex.neg_re]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
    have hyN : Q ^ 6 ≤ 2 * (d * (Q ^ 6 / d)) := by
      have h1 := Nat.div_add_mod (Q ^ 6) d
      have h2 := Nat.mod_lt (Q ^ 6) hd1
      omega
    have hy : (Q : ℝ) ^ 6 ≤ 2 * ((d : ℝ) * ((Q ^ 6 / d : ℕ) : ℝ)) := by exact_mod_cast hyN
    have hrp := _root_.GlobalTheory.ZeroDetect.rpow_bound hQR hy hσ
    calc ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖
        = ‖a d‖ * ‖f d‖ * ‖∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * (d : ℝ) ^ (-ρ.re) * (C * ((Q ^ 6 / d : ℕ) : ℝ) ^ (-ρ.re)) := by gcongr
      _ = C * ((d : ℝ) * ((Q ^ 6 / d : ℕ) : ℝ)) ^ (-ρ.re) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]; ring
      _ ≤ C * (16 * (Q : ℝ) ^ 5)⁻¹ := by gcongr
  have hsum : ‖∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖
      ≤ 1 / 2 := by
    calc _ ≤ ∑ d ∈ Finset.Icc 1 (Q ^ 3), ‖a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ :=
          norm_sum_le _ _
      _ ≤ ∑ d ∈ Finset.Icc 1 (Q ^ 3), C * (16 * (Q : ℝ) ^ 5)⁻¹ := Finset.sum_le_sum hterm
      _ = (Q : ℝ) ^ 3 * (C * (16 * (Q : ℝ) ^ 5)⁻¹) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          push_cast
          simp
      _ = C / (16 * (Q : ℝ) ^ 2) := by field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]
          linarith
  have hT : ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
      ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
        χ (n : ZMod q) * (n : ℂ) ^ (-ρ) =
      (∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m) - 1 := by
    rw [← hmain, ← hsplit, hinit]
    ring
  rw [hT, norm_sub_rev]
  have h1 := norm_sub_norm_le (1 : ℂ)
    (∑ d ∈ Finset.Icc 1 (Q ^ 3), a d * f d * ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m)
  rw [norm_one] at h1
  linarith

end GlobalTheory.ZeroDetect
end
