module

public import Development.AutomorphicArithmetic.CharacterBoxes.PairGood
public import Development.AutomorphicArithmetic.MeanSquareBounds.PairExists
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mertensUpper
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

theorem mertens_upper_sum_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ N * Real.log N - N + 1 + Real.log N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le _)]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : Real.log ((N : ℝ) / (N + 1)) ≤ (N : ℝ) / (N + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hN'.ne' (by positivity)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ N + 1 by positivity)
    have h3 : ((N : ℝ) + 1) * ((N : ℝ) / (N + 1) - 1) = -1 := by field_simp; ring
    rw [h3] at h2
    push_cast
    nlinarith

theorem mertens_upper_log_le (x c : ℝ) (hx : 0 < x) (hc : 0 < c) :
    Real.log x ≤ Real.log c + x / c - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / c by positivity)
  rw [Real.log_div hx.ne' hc.ne'] at h
  linarith

theorem mertens_upper_psi_bound (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n + 1 + Real.log N ≤ 3 * N := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  by_cases h25 : 25 ≤ N
  · have hp := Chebyshev.psi_le hN'
    rw [Chebyshev.psi, Nat.floor_natCast] at hp
    have h25' : (25 : ℝ) ≤ N := by exact_mod_cast h25
    have hs : 5 ≤ Real.sqrt N := Real.le_sqrt_of_sq_le (by linarith)
    have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
    have hL : Real.log N = 2 * Real.log (Real.sqrt N) := by
      rw [Real.log_sqrt (by linarith)]; ring
    have hl := mertens_upper_log_le (Real.sqrt N) 4 (by linarith) (by norm_num)
    set s := Real.sqrt N
    have hl' : Real.log N ≤ 0.78 + s / 2 := by linarith
    have h5 : 2 * s * Real.log N ≤ 2 * s * (0.78 + s / 2) :=
      mul_le_mul_of_nonneg_left hl' (by linarith)
    have h6 : Real.log 4 * N ≤ 1.39 * N := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  · have h1 : ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n
        ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log n :=
      Finset.sum_le_sum fun n _ => ArithmeticFunction.vonMangoldt_le_log
    have h2 := mertens_upper_sum_log N hN
    have h24 : (N : ℝ) ≤ 24 := by exact_mod_cast (by omega : N ≤ 24)
    by_cases h3 : 3 ≤ N
    · have h3' : (3 : ℝ) ≤ N := by exact_mod_cast h3
      have hl := mertens_upper_log_le N 16 (by linarith) (by norm_num)
      have hl' : Real.log N ≤ 1.78 + N / 16 := by linarith
      have h5 : ((N : ℝ) + 2) * Real.log N ≤ (N + 2) * (1.78 + N / 16) :=
        mul_le_mul_of_nonneg_left hl' (by linarith)
      nlinarith
    · have h2' : (N : ℝ) ≤ 2 := by exact_mod_cast (by omega : N ≤ 2)
      have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N by linarith)
      have h5 : ((N : ℝ) + 2) * Real.log N ≤ (N + 2) * (N - 1) :=
        mul_le_mul_of_nonneg_left hl (by linarith)
      nlinarith

theorem mertens_upper_nat (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ Real.log N + 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hid := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum ArithmeticFunction.vonMangoldt N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at hid
  simp only [ArithmeticFunction.log_apply] at hid
  have h1 := mertens_upper_sum_log N hN
  have h2 := mertens_upper_psi_bound N hN
  have h3 : N * ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n * ((N / n : ℕ) : ℝ) +
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlt : (N : ℝ) / n ≤ ((N / n : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hn']
      have : N ≤ (N / n + 1) * n := by
        have := Nat.lt_div_mul_add (a := N) hn0
        nlinarith
      exact_mod_cast this
    have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    calc (N : ℝ) * (ArithmeticFunction.vonMangoldt n / n)
        = ArithmeticFunction.vonMangoldt n * ((N : ℝ) / n) := by ring
      _ ≤ ArithmeticFunction.vonMangoldt n * (((N / n : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hlt hΛ
      _ = _ := by ring
  rw [← hid] at h3
  refine le_of_mul_le_mul_left ?_ hN'
  nlinarith

theorem mertens_upper (y : ℝ) (hy : 1 ≤ y) :
    ∑ n ∈ Finset.range (⌊y⌋₊ + 1), ArithmeticFunction.vonMangoldt n / (n : ℝ) ≤ Real.log y + 2 := by
  have hN : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have h := mertens_upper_nat ⌊y⌋₊ hN
  have hN' : (0 : ℝ) < (⌊y⌋₊ : ℕ) := by exact_mod_cast hN
  have hl : Real.log (⌊y⌋₊ : ℕ) ≤ Real.log y :=
    Real.log_le_log hN' (Nat.floor_le (by linarith))
  rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le _)]
  simp only [Nat.cast_zero, div_zero, zero_add]
  linarith

end Deduction

end
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.Kappa4Loglog
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem kappa4_num (K : ℝ) (hK : 0 ≤ K) (s Q : ℝ) (hs : 3 ≤ s) (hQ : 0 < Q)
    (hQs : (s ^ 4) ^ 1006 ≤ Q) (x : ℝ) (hx : x = s ^ 10) :
    ((K * s ^ 4 * (s ^ 4 * (1 / x ^ 2) * (x ^ 400) ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2))) ≤ 2 * K + 802 := by
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs.trans (le_self_pow₀ hs1 (by norm_num))
  have hx0 : 0 < x := by linarith
  have hxa : x ^ ((2 / 5) / 4 : ℝ) = s := by
    rw [hx, ← Real.rpow_natCast s 10, ← Real.rpow_mul hs0.le]
    norm_num
  apply le_of_mul_le_mul_left _ hx0
  rw [Formalism.HermitianLattices.Ext.BoxTail.tail_num_rpow x (2 / 5) hx0, hxa,
    Formalism.HermitianLattices.Ext.BoxTail.tail_num_alg x Q K _ _ _ hx0 hQ]
  have t3 := Formalism.HermitianLattices.Ext.BoxTail.tail_num_third x hx3
  have t1 : (s ^ 4) ^ 2 * s ≤ x := by
    rw [hx]
    calc (s ^ 4) ^ 2 * s = s ^ 9 := by ring
      _ ≤ s ^ 10 := pow_le_pow_right₀ hs1 (by norm_num)
  have t2 : s ^ 4 * x ^ 403 / Q ≤ x := by
    rw [div_le_iff₀ hQ]
    have e : s ^ 4 * x ^ 403 = x * (s ^ 4) ^ 1006 := by
      rw [hx, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    rw [e]
    exact mul_le_mul_of_nonneg_left hQs hx0.le
  have u1 := mul_le_mul_of_nonneg_left t1 hK
  have u2 := mul_le_mul_of_nonneg_left t2 hK
  have u3 : (802 : ℝ) ≤ x * 802 := by linarith
  have e1 : K * (s ^ 4) ^ 2 * s = K * ((s ^ 4) ^ 2 * s) := mul_assoc _ _ _
  have e2 : x * (2 * K + 802) = K * x + K * x + x * 802 := by ring
  rw [e1, e2]
  exact add_le_add (add_le_add u1 u2) (t3.trans u3)

set_option maxRecDepth 4096 in
private theorem kappa4_loglog : ∃ C l₀ : ℝ, 1 ≤ l₀ ∧ ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    l₀ ≤ Real.log Q → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 1000 * Real.log (Real.log Q) + C := by
  obtain ⟨K, hK0, hK⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_contour ((2 / 5) / 1600) (by positivity) (by norm_num)
  have hev : ∀ᶠ l : ℝ in Filter.atTop, l ^ 1006 ≤ Real.exp l := by
    have h := (Real.tendsto_exp_div_pow_atTop 1006).eventually_ge_atTop 1
    filter_upwards [h, Filter.eventually_gt_atTop 0] with l hl hl0
    rwa [le_div_iff₀ (by positivity), one_mul] at hl
  obtain ⟨l₀, hl₀⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_ge_atTop 81))
  refine ⟨2 * K + 802 + 2, l₀, by linarith [(hl₀ l₀ le_rfl).2], ?_⟩
  intro Q N _ χ hQlo hgood
  obtain ⟨hχ, hNQ, hbox⟩ := hgood
  obtain ⟨hexp, h81⟩ := hl₀ _ hQlo
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hQ0 : 0 < Q := by linarith
  rw [Real.exp_log hQ0] at hexp
  have hQ2 : 2 ≤ Q := by
    have := Real.log_le_self hQ0.le
    linarith
  obtain ⟨s, hs0, hs4⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 4 = Real.log Q :=
    ⟨Real.log Q ^ ((4 : ℕ) : ℝ)⁻¹, Real.rpow_nonneg (by linarith) _,
      Real.rpow_inv_natCast_pow (by linarith) (by norm_num)⟩
  have hs3 : 3 ≤ s := by
    apply le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hs0
    rw [hs4]; linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = s ^ 10 := ⟨_, rfl⟩
  have hnum := kappa4_num K hK0 s Q hs3 hQ0 (by rw [hs4]; exact hexp) x hx
  rw [hs4] at hnum
  have hx3 : 3 ≤ x := by
    rw [hx]; exact hs3.trans (le_self_pow₀ (by linarith) (by norm_num))
  have hx0 : 0 < x := by linarith
  have hlogz : Real.log (x ^ 400) = 1000 * Real.log (Real.log Q) := by
    rw [← hs4, hx, Real.log_pow, Real.log_pow, Real.log_pow]; push_cast; ring
  set z : ℝ := x ^ 400 with hz
  set η : ℝ := 1 / x ^ 2 with hη
  have hz1 : 1 ≤ z := one_le_pow₀ (by linarith)
  have hη0 : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    rw [hη, div_le_one (by positivity)]; nlinarith
  have hzη : 0 < z * η := by positivity
  have hC := hK N χ Q z η hχ hQ2 hNQ hbox hz1 hη0 hη1
  have hD := Formalism.HermitianLattices.Ext.BoxTail.tail_diff_schi χ z (z * η) hz1 hzη
  set P : ℂ := ∑ n ∈ Icc 1 ⌊z⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod N) / (n : ℂ) with hP
  have hkey : ((z * η : ℝ) : ℂ) * (Formalism.ZeroFreeDirichlet.negLD χ 1 - P) =
      -(Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * Formalism.ZeroFreeDirichlet.negLD χ 1) +
      (Formalism.ZeroFreeDirichlet.Schi χ (z + z * η) - Formalism.ZeroFreeDirichlet.Schi χ z - ((z * η : ℝ) : ℂ) * P) := by ring
  have hnorm : ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ ≤
      (K * Real.log Q * (Real.log Q * η * z ^ (1 - 1 / 400 + (2 / 5) / 1600 : ℝ) + z ^ 2 / Q)
        + z * η * (z * η + 1) * Real.log (z + z * η) / z) / (z * η) := by
    rw [le_div_iff₀ hzη]
    have h1 := congrArg norm hkey
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hzη.le] at h1
    calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ * (z * η) = z * η * ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := mul_comm _ _
      _ = _ := h1
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        exact add_le_add hC hD
  have htail := hnorm.trans hnum
  have hPle : ‖P‖ ≤ Real.log z + 2 := by
    have hM : ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ≤ Real.log z + 2 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (Deduction.mertens_upper z hz1)
      · intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
      · intro n _ _
        exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
    refine le_trans (norm_sum_le _ _) (le_trans ?_ hM)
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_natCast,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχn : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛ : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    gcongr
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ (n : ZMod N)‖ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 := by gcongr
      _ = ArithmeticFunction.vonMangoldt n := mul_one _
  have hLD : logDerivLAtOne χ = -(Formalism.ZeroFreeDirichlet.negLD χ 1) := by
    simp only [logDerivLAtOne, Formalism.ZeroFreeDirichlet.negLD, neg_neg]
  rw [hLD, norm_neg]
  calc ‖Formalism.ZeroFreeDirichlet.negLD χ 1‖ = ‖P + (Formalism.ZeroFreeDirichlet.negLD χ 1 - P)‖ := by rw [add_sub_cancel]
    _ ≤ ‖P‖ + ‖Formalism.ZeroFreeDirichlet.negLD χ 1 - P‖ := norm_add_le _ _
    _ ≤ _ := by rw [← hlogz]; linarith

theorem kappa4 :
    ∀ ε A : ℝ, 0 < ε → ε < 1 / 52 → 0 < A → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ A * Y ^ (ε / 5) * Real.log Y ^ 2 → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ 4 * Real.log Y := by
  intro ε A hε hε1 hA
  obtain ⟨C, l₀, hl₀, hC⟩ := kappa4_loglog
  have e1 : ∀ᶠ Y : ℝ in Filter.atTop, l₀ ≤ Y ^ (ε / 6) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 6)).eventually_ge_atTop _
  have e2 : ∀ᶠ u : ℝ in Filter.atTop, ‖Real.log u‖ ≤ (1 / 26000) * ‖u‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num)
  have e3 : ∀ᶠ u : ℝ in Filter.atTop, 13 * (1000 * Real.log A + C) ≤ u := Filter.eventually_ge_atTop _
  have e4 := Real.tendsto_log_atTop.eventually (e2.and (e3.and (Filter.eventually_ge_atTop 1)))
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 (e1.and (e4.and (Filter.eventually_gt_atTop 0)))
  refine ⟨Y₀, ?_⟩
  intro Y hY Q N _ χ hlo hhi hgood
  obtain ⟨h1, ⟨h2, h3, h4⟩, hY0⟩ := hY₀ Y hY
  have hb := hC Q N χ (h1.trans hlo) hgood
  have hu0 : 0 < Real.log Y := by linarith
  have hp : 0 < Y ^ (ε / 5) := Real.rpow_pos_of_pos hY0 _
  have hl : Real.log (Real.log Q) ≤ Real.log A + ε / 5 * Real.log Y + 2 * Real.log (Real.log Y) := by
    refine (Real.log_le_log (by linarith) hhi).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hA.ne' hp.ne', Real.log_rpow hY0,
      Real.log_pow]
    push_cast; ring
  rw [Real.norm_of_nonneg hu0.le, Real.norm_of_nonneg (Real.log_nonneg h4)] at h2
  have h5 : ε * Real.log Y ≤ 1 / 52 * Real.log Y := mul_le_mul_of_nonneg_right hε1.le hu0.le
  have h6 : ε / 5 * Real.log Y = ε * Real.log Y / 5 := by ring
  rw [h6] at hl
  linarith

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.IndDrop
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem ind_drop :
    ∀ (N₀ q M : ℕ) (ξ : DirichletCharacter ℂ N₀) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), 0 < N₀ → q.Prime → q ≠ 2 → ¬ q ∣ N₀ → M ≠ 0 →
      Ind χ (fun n => ξ n * J q n) M → Ind χ (fun n => ξ n * J q n) (N₀ * q) := by
  intro N₀ q M ξ N _ χ hN₀ hq hq2 hqN₀ hM hχ
  obtain ⟨hχp, hind⟩ := hχ
  haveI : NeZero N₀ := ⟨hN₀.ne'⟩
  haveI : NeZero ξ.conductor := ⟨ξ.conductor_ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  have hqf : ¬ q ∣ ξ.conductor := fun h => hqN₀ (h.trans ξ.conductor_dvd_level)
  obtain ⟨ψ, hψ, -, hψeq⟩ :=
    twist_prim ξ.conductor q ξ.primitiveCharacter ξ.primitiveCharacter_isPrimitive hq hq2 hqf
  have hprim : ∀ n : ℕ, n.Coprime N₀ → ξ n = ξ.primitiveCharacter n := by
    intro n hn
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ.primitiveCharacter
      ξ.conductor_dvd_level (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn)
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    rw [Int.cast_natCast, Int.cast_natCast] at h
    exact h
  have heq := ind_unique N (ξ.conductor * q) (M * N₀ * q) χ ψ
    (mul_ne_zero (mul_ne_zero hM hN₀.ne') hq.ne_zero) hχp hψ (fun n hn => by
      rw [hind n (Nat.Coprime.coprime_dvd_right (Dvd.intro (N₀ * q) (by ring)) hn), hψeq]
      dsimp only
      rw [hprim n (Nat.Coprime.coprime_dvd_right (Dvd.intro (M * q) (by ring)) hn)])
  obtain ⟨hN, hχψ⟩ := Sigma.mk.inj_iff.1 heq
  subst hN
  have hc : χ = ψ := eq_of_heq hχψ
  subst hc
  refine ⟨hχp, fun n hn => ?_⟩
  rw [hψeq]
  dsimp only
  rw [hprim n (Nat.Coprime.coprime_dvd_right (dvd_mul_right N₀ q) hn)]

end QH
end

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem pairEx_lift {N L : ℕ} [NeZero L] (h : N ∣ L) (ξ : DirichletCharacter ℂ N) (n : ℕ) (hn : n.Coprime L) :
    DirichletCharacter.changeLevel h ξ (n : ZMod L) = ξ (n : ZMod N) := by
  have ha : IsCoprime (n : ℤ) (L : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  have key := DirichletCharacter.changeLevel_eq_cast_of_dvd' ξ h ha
  simpa using key

private theorem pairEx_box (M : ℕ) (hM : 0 < M) (C τ Y X z z' : ℝ) (q d : ℕ) (hR : Rows z z' q d) (hq : 8 * M < q)
    (hQ : GoodQ (8 * M) C τ Y X z q) (hD : GoodD (8 * M) C τ Y X z z' q d)
    (f : ℕ → ℂ) (ξ : DirichletCharacter ℂ (8 * M)) (hf : ∀ n : ℕ, n.Coprime (8 * M) → ξ (n : ZMod (8 * M)) = f n)
    (i j : Fin 2) (hij : i ≠ 0 ∨ j ≠ 0) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (hI : Formalism.HC.An.Induces χ (UpperTheory.Top.tw f q d i j) (2 * M * q * d)) :
    Box (8 * M * Real.exp z * Real.exp z' ^ (j : ℕ)) C τ Y X χ := by
  have hq2 : q ≠ 2 := by
    intro h2
    have hm := hR.q_mod
    rw [h2] at hm
    norm_num at hm
  have hqN : ¬ q ∣ 8 * M := by
    intro hd
    have hle := Nat.le_of_dvd (by omega) hd
    omega
  have h8 : ∀ n : ℕ, n.Coprime (2 * M * q * d) → n.Coprime (8 * M) := by
    intro n hn
    have h2 : n.Coprime 2 := Nat.Coprime.coprime_dvd_right ⟨M * q * d, by ring⟩ hn
    have hM' : n.Coprime M := Nat.Coprime.coprime_dvd_right ⟨2 * q * d, by ring⟩ hn
    have h8' : n.Coprime 8 := by simpa using Nat.Coprime.pow_right 3 h2
    exact Nat.Coprime.mul_right h8' hM'
  have hlev : 2 * M * q * d ≠ 0 :=
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hM) hR.q_prime.pos) hR.d_prime.pos).ne'
  obtain ⟨hprim, hval⟩ := hI
  fin_cases j
  · fin_cases i
    · simp at hij
    · have hInd : Ind χ (fun n ↦ ξ n * J q n) (2 * M * q * d) := by
        refine ⟨hprim, fun n hn => ?_⟩
        rw [hval n hn]
        simp [UpperTheory.Top.tw, J, hf n (h8 n hn)]
      have hInd' := ind_drop (8 * M) q (2 * M * q * d) ξ N χ (by omega) hR.q_prime hq2 hqN hlev hInd
      have hB := hQ ξ N χ hInd'
      refine (congrArg (fun Q => Box Q C τ Y X χ) ?_).mpr hB
      simp
  · have hInd : Ind χ (fun n ↦ ξ n * J q n ^ (i : ℕ) * J d n) (8 * M * q * d) := by
      refine ⟨hprim, fun n hn => ?_⟩
      have hn' : n.Coprime (2 * M * q * d) := Nat.Coprime.coprime_dvd_right ⟨4, by ring⟩ hn
      rw [hval n hn']
      simp [UpperTheory.Top.tw, J, hf n (h8 n hn')]
    have hB := hD ξ (i : ℕ) (Nat.lt_succ_iff.mp i.isLt) N χ hInd
    refine (congrArg (fun Q => Box Q C τ Y X χ) ?_).mpr hB
    simp [Real.exp_add, mul_assoc]

private theorem pairEx_g {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (h : χ ≠ 1) (y : ℝ) :
    Formalism.HC.An.gChi χ y = Gchi χ y := by
  unfold Formalism.HC.An.gChi
  rw [if_neg h]
  unfold Formalism.HC.An.sumLamChi Gchi
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
  have hfl : 0 < ⌊y⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)
  have hy1 : 1 ≤ y := Nat.floor_pos.mp hfl
  have hny : (n : ℝ) ≤ y := le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))
  have hnn : 0 ≤ y / n - 1 := by
    rw [sub_nonneg, le_div_iff₀ (by linarith)]
    linarith
  rw [max_eq_left hnn]

private theorem log_exp_product_bounds (M : ℕ) (hM : 0 < M) (ε Y : ℝ) (hε : 0 < ε)
    (hY : Real.exp (1 + Real.log (8 * M)) ≤ Y) (j : ℕ) (hj : j ≤ 1) :
    Y ^ (ε / 6) ≤ Real.log (8 * M * Real.exp (Y ^ (ε / 5)) * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2) ^ j) ∧
    Real.log (8 * M * Real.exp (Y ^ (ε / 5)) * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2) ^ j)
      ≤ 3 * Y ^ (ε / 5) * Real.log Y ^ 2 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM8 : (1 : ℝ) ≤ 8 * M := by linarith
  have hlog8 : 0 ≤ Real.log (8 * M) := Real.log_nonneg hM8
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_exp (by linarith)) hY
  have hYpos : 0 < Y := by linarith
  have hL : 1 + Real.log (8 * M) ≤ Real.log Y := (Real.le_log_iff_exp_le hYpos).mpr hY
  have hw1 : 1 ≤ Y ^ (ε / 5) := Real.one_le_rpow hY1 (by linarith)
  have h65 : Y ^ (ε / 6) ≤ Y ^ (ε / 5) := Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
  set w := Y ^ (ε / 5) with hw
  set L := Real.log Y with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hwL : L ^ 2 ≤ w * L ^ 2 := by nlinarith
  have hlogQ : Real.log (8 * M * Real.exp w * Real.exp (w * L ^ 2) ^ j)
      = Real.log (8 * M) + w + j * (w * L ^ 2) := by
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
      Real.log_mul (ne_of_gt (by linarith)) (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hj' : (j : ℝ) ≤ 1 := by exact_mod_cast hj
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hz0 : 0 ≤ w * L ^ 2 := by positivity
  rw [hlogQ]
  constructor
  · nlinarith
  · have a1 : w ≤ w * L ^ 2 := by nlinarith
    have a2 : (j : ℝ) * (w * L ^ 2) ≤ w * L ^ 2 := by nlinarith
    linarith

theorem pairEx :
    UpperTheory.Top.PairEx := by
  intro M hM eps A heps heps' hA
  obtain ⟨C, hC, hpair⟩ := pair_exists
  obtain ⟨Y₀, hY₀⟩ := hpair eps (eps / 2) A (8 * M) heps heps' (by linarith) hA (by omega)
  obtain ⟨Y₁, hY₁⟩ := kappa4 eps 3 heps heps' (by norm_num)
  refine ⟨max (max Y₀ Y₁) (Real.exp (1 + Real.log (8 * M))), fun Y hY => ?_⟩
  have hYa : Y₀ ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hYb : Y₁ ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYc : Real.exp (1 + Real.log (8 * M)) ≤ Y := le_trans (le_max_right _ _) hY
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog8 : 0 ≤ Real.log (8 * M) := Real.log_nonneg (by linarith)
  have hY1 : 1 ≤ Y := le_trans (Real.one_le_exp (by linarith)) hYc
  have hz0 : 0 ≤ Y ^ (eps / 5) * Real.log Y ^ 2 := by
    have := Real.log_nonneg hY1
    positivity
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  obtain ⟨q, d, hR, hq, hQ, hD⟩ := hY₀ Y hYa (Y ^ A) (Y ^ (eps / 5) * Real.log Y ^ 2) le_rfl le_rfl
    (le_mul_of_one_le_left hz0 hA2)
  have hq2 : q ≠ 2 := by
    intro h2
    have hm := hR.q_mod
    rw [h2] at hm
    norm_num at hm
  haveI : NeZero (8 * M) := ⟨by omega⟩
  have hM8 : M ∣ 8 * M := Dvd.intro_left 8 rfl
  refine ⟨q, d, ?_, ?_, ?_, ?_⟩
  · refine ⟨hR.q_prime, hR.q_mod, hR.q_gt, hR.q_le, hR.d_prime, hR.d_mod, hR.d_gt, hR.d_le, ?_, ?_⟩
    · exact Nat.dvd_of_mod_eq_zero (hR.d_class q hR.q_prime hq2 (Or.inr rfl))
    · intro p hp hp2 hpl
      exact Nat.dvd_of_mod_eq_zero (hR.d_class p hp hp2 (Or.inl hpl))
  · have hqM : ¬ q ∣ M := fun h => by
      have := Nat.le_of_dvd hM h
      omega
    have hdM : ¬ d ∣ M := fun h => by
      have := Nat.le_of_dvd hM h
      have := hR.q_lt_d
      omega
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hR.q_prime).mpr hqM).symm
      ((Nat.Prime.coprime_iff_not_dvd hR.d_prime).mpr hdM).symm
  · intro ξ i j hij N _ χ hI y hy1 hy2
    have hB := pairEx_box M hM C (eps / 2) Y (Y ^ A) (Y ^ (eps / 5)) (Y ^ (eps / 5) * Real.log Y ^ 2) q d
      hR hq hQ hD (fun a ↦ ξ a) (DirichletCharacter.changeLevel hM8 ξ)
      (fun n hn => pairEx_lift hM8 ξ n hn) i j hij N χ hI
    obtain ⟨hgood, _, hG⟩ := hB
    have hne : χ ≠ 1 := hgood.1
    constructor
    · rw [pairEx_g χ hne]
      exact hG y ⟨hy1, hy2⟩
    · obtain ⟨hk1, hk2⟩ := log_exp_product_bounds M hM eps Y heps hYc (j : ℕ) (Nat.lt_succ_iff.mp j.isLt)
      have hk := hY₁ Y hYb _ N χ hk1 hk2 hgood
      have hlog : Real.log Y ≤ Real.log y := Real.log_le_log (by linarith) hy1
      exact le_trans hk (by linarith)
  · intro ρ hρ hρN i j hij N _ χ hI
    have hB := pairEx_box M hM C (eps / 2) Y (Y ^ A) (Y ^ (eps / 5)) (Y ^ (eps / 5) * Real.log Y ^ 2) q d
      hR hq hQ hD ρ.val (DirichletCharacter.changeLevel hρN ρ.χ)
      (fun n hn => pairEx_lift hρN ρ.χ n hn) i j hij N χ hI
    exact hB.1.2.2

end QH
