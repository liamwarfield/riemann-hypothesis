module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensBlock
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.OneSubTwoCpowLower

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.SecondBlockCount
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DyadicSizeLePowTwelveSecond
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem log_pow_five_le_sqrt (c : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 5 ≤ Real.sqrt q := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := 10)).bound
    (c := 1 / (c ^ 2 + 1)) (by positivity)
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 h
  refine ⟨⌈x₀⌉₊, fun q hq => ?_⟩
  have hqx : x₀ ≤ (q : ℝ) := (Nat.le_ceil x₀).trans (by exact_mod_cast hq)
  have h1 := hx₀ q hqx
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hq0] at h1
  have h2 : Real.log q ^ 10 ≤ 1 / (c ^ 2 + 1) * q := (le_abs_self _).trans h1
  have h3 : (c ^ 2 + 1) * Real.log q ^ 10 ≤ q := by
    have hp : (0 : ℝ) < c ^ 2 + 1 := by positivity
    calc (c ^ 2 + 1) * Real.log q ^ 10 ≤ (c ^ 2 + 1) * (1 / (c ^ 2 + 1) * q) := by gcongr
      _ = (q : ℝ) := by field_simp
  have h4 : (c * Real.log q ^ 5) ^ 2 ≤ q := by
    have : (0 : ℝ) ≤ Real.log q ^ 10 := by positivity
    nlinarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h4)

theorem one_le_log_of_three_le_second {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem dyadic_index_le_log_second (q : ℕ) (hq : 3 ≤ q) : ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) ≤ 24 * Real.log q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 q ≤ q := by exact_mod_cast h1
  have h3 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h2
  have h4 := Real.log_two_gt_d9
  have h5 := one_le_log_of_three_le_second hq'
  have h6 : (0 : ℝ) ≤ (Nat.log 2 q : ℝ) := Nat.cast_nonneg _
  push_cast
  nlinarith

theorem dyadic_size_le_pow_twelve_second (q : ℕ) (hq : 256 ≤ q) : q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1)) ≤ q ^ 12 := by
  have h1 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ (8 * (Nat.log 2 q + 1)) = 256 * (2 ^ Nat.log 2 q) ^ 8 := by
    rw [← pow_mul]; rw [show 8 * (Nat.log 2 q + 1) = 8 + Nat.log 2 q * 8 by ring, pow_add]; norm_num
  rw [h2]
  calc q ^ 3 * (256 * (2 ^ Nat.log 2 q) ^ 8) ≤ q ^ 3 * (q * q ^ 8) := by gcongr
    _ = q ^ 12 := by ring

theorem second_small_condition (u l K J q s Lq : ℝ) (hq : 0 < q) (hs : 0 < s) (hu : u ≤ 1 / (q * s))
    (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 48 * q) (hJ0 : 0 < J) (hJ : J ≤ 24 * Lq)
    (hc : 971882496 * Lq ^ 5 ≤ s) : 2 * u * l ^ 3 * K ≤ (1 / (2 * J)) ^ 2 / 2 := by
  have hL : 0 < Lq := by nlinarith
  have h1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by
    have : 0 ≤ 1 / (q * s) := by positivity
    calc 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by gcongr
      _ ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) := by gcongr
  have h2 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (48 * q) = 210912 * Lq ^ 3 / s := by
    field_simp; ring
  have h3 : 1 / (4608 * Lq ^ 2) ≤ (1 / (2 * J)) ^ 2 / 2 := by
    have : (1 / (2 * J)) ^ 2 / 2 = 1 / (8 * J ^ 2) := by field_simp; ring
    rw [this]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h4 : 210912 * Lq ^ 3 / s ≤ 1 / (4608 * Lq ^ 2) := by
    rw [div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith

theorem rpow_neg_exponent_bound_second (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq'
  have hU' : (q : ℝ) ^ 3 ≤ U := by exact_mod_cast hU
  have h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)
  have h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  linarith

theorem rpow_pos_exponent_bound_second (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have hU' : (U : ℝ) ≤ (2 * x) ^ 12 := by
    calc (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
      _ ≤ (2 * x) ^ 12 := by gcongr
  have h1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hU' (by linarith)
  have h2 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 * x) ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  have h3 : (2 * x) ^ (24 * (1 - σ)) = 2 ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) :=
    Real.mul_rpow (by norm_num) hx.le
  have h4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    have : (2 : ℝ) ^ (6 : ℝ) = 64 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [← this]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h5 : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  rw [h2, h3] at h1
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ZeroDetectionSecond
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

attribute [local irreducible] qd pYd pJd pNd in
theorem zero_detection_second : Detect1 := by
  intro M _ χ hχ1 T hT hM ρ hρ hρim hL
  obtain ⟨X, hX⟩ : ∃ X : ℕ, qd M T = X := ⟨_, rfl⟩
  have hMT : (M : ℝ) * T ≤ X := by rw [← hX]; unfold qd; exact Nat.le_ceil _
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX6 : (6 : ℝ) ≤ X := by nlinarith
  have hX1 : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
  have hre0 : 0 < ρ.re := by linarith
  have hNX : X ^ 8 ≤ pNd M T := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    unfold pNd pJd
    rw [hX, mul_comm 8, pow_mul]
    exact Nat.pow_le_pow_left h.le 8
  have hY : pYd M T = X ^ 3 := by unfold pYd; rw [hX]
  have hYN : pYd M T ≤ pNd M T := by
    rw [hY]; exact le_trans (Nat.pow_le_pow_right hX1 (by norm_num)) hNX
  have hY1 : 1 ≤ pYd M T := by rw [hY]; exact Nat.one_le_pow _ _ (by omega)
  have hN1 : 1 ≤ pNd M T := le_trans hY1 hYN
  have hB := Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ1
  have hP := Formalism.FX.l_function_partial_sum M χ hχ1 _ hB ρ hre0 (pNd M T) hN1
  rw [hL, zero_sub, norm_neg] at hP
  have hMI := mollifier_identity M χ ρ (pYd M T) (pNd M T) (pYd M T * pNd M T) hY1 hYN le_rfl
  have hMo := mollM_norm_le χ ρ hre0.le (pYd M T)
  set P := ∑ n ∈ Icc 1 (pNd M T), χ (n : ZMod M) * (n : ℂ) ^ (-ρ) with hPdef
  set Mo := ∑ d ∈ Icc 1 (pYd M T), (((ArithmeticFunction.moebius d : ℤ)) : ℂ) * χ (d : ZMod M) * (d : ℂ) ^ (-ρ)
    with hMdef
  set D := ∑ n ∈ Ioc (pYd M T) (pYd M T * pNd M T), mco (pYd M T) (pNd M T) n * χ (n : ZMod M) * (n : ℂ) ^ (-ρ)
    with hD
  have hnum : ‖P‖ * (pYd M T : ℝ) ≤ 1 / 2 := by
    have hXpos : (0 : ℝ) < X := by linarith
    have hNpos : (0 : ℝ) < pNd M T := by exact_mod_cast hN1
    have hrho : 1 + ‖ρ‖ / ρ.re ≤ 3 * T := by
      have h1 : ‖ρ‖ ≤ ρ.re + T := by
        refine (Complex.norm_le_abs_re_add_abs_im ρ).trans ?_
        rw [abs_of_pos hre0]; linarith
      have h2 : ‖ρ‖ / ρ.re ≤ 1 + T / ρ.re := by
        rw [div_le_iff₀ hre0, add_mul, one_mul, div_mul_cancel₀ _ hre0.ne']; linarith
      have h3 : T / ρ.re ≤ 4 / 3 * T := by
        rw [div_le_iff₀ hre0]; nlinarith
      linarith
    have hpow : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by linarith)
    have hN8 : (X : ℝ) ^ (8 : ℕ) ≤ (pNd M T : ℝ) := by exact_mod_cast hNX
    have hpow2 : (X : ℝ) ^ (6 : ℕ) ≤ ((pNd M T : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by
      have e : ((X : ℝ) ^ (8 : ℕ)) ^ (3 / 4 : ℝ) = (X : ℝ) ^ (6 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le, ← Real.rpow_natCast]
        norm_num
      rw [← e]
      exact Real.rpow_le_rpow (by positivity) hN8 (by norm_num)
    have hinv : ((pNd M T : ℕ) : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := by
      rw [Real.rpow_neg hNpos.le, one_div]
      exact inv_anti₀ (by positivity) hpow2
    have hYr : (pYd M T : ℝ) = (X : ℝ) ^ (3 : ℕ) := by rw [hY, Nat.cast_pow]
    have hc : 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 8 * X := by
      have hpos : (0 : ℝ) ≤ 1 + ‖ρ‖ / ρ.re := by positivity
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) ≤ 2 * ((M : ℝ) + 1) * (3 * T) :=
            mul_le_mul_of_nonneg_left hrho (by positivity)
        _ ≤ 8 * X := by nlinarith
    have hPle : ‖P‖ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := by
      refine hP.trans ?_
      have a3 : ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) ≤ 1 / (X : ℝ) ^ (6 : ℕ) := hpow.trans hinv
      calc 2 * ((M : ℝ) + 1) * (1 + ‖ρ‖ / ρ.re) * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re)
          ≤ 8 * X * ((pNd M T : ℕ) : ℝ) ^ (-ρ.re) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) := mul_le_mul_of_nonneg_left a3 (by positivity)
    rw [hYr]
    calc ‖P‖ * (X : ℝ) ^ (3 : ℕ) ≤ 8 * X * (1 / (X : ℝ) ^ (6 : ℕ)) * (X : ℝ) ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_right hPle (by positivity)
      _ = 8 / X ^ 2 := by
          have hX0 : (X : ℝ) ≠ 0 := hXpos.ne'
          field_simp
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
  have h1D : ‖1 + D‖ ≤ 1 / 2 := by
    rw [← hMI, norm_mul]
    calc ‖P‖ * ‖Mo‖ ≤ ‖P‖ * (pYd M T : ℝ) := mul_le_mul_of_nonneg_left hMo (norm_nonneg _)
      _ ≤ 1 / 2 := hnum
  have hDge : 1 / 2 ≤ ‖D‖ := by
    have := norm_sub_le (1 + D) D
    simp only [add_sub_cancel_right, norm_one] at this
    linarith
  have hsplit : D = ∑ j ∈ range (pJd M T),
      blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ := by
    rw [hD, show pNd M T = 2 ^ pJd M T by unfold pNd; rfl, sum_blocks]
    rfl
  by_contra hcon
  push Not at hcon
  have hJ8 : 8 ≤ pJd M T := by unfold pJd; omega
  have hJpos : (0 : ℝ) < pJd M T := by exact_mod_cast (by omega : 0 < pJd M T)
  have hlt : ‖D‖ < 1 / 2 := by
    rw [hsplit]
    refine (norm_sum_le _ _).trans_lt ?_
    have hne : (range (pJd M T)).Nonempty := nonempty_range_iff.mpr (by omega)
    calc ∑ j ∈ range (pJd M T), ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ‖
        < ∑ j ∈ range (pJd M T), 1 / (2 * (pJd M T : ℝ)) := sum_lt_sum_of_nonempty hne hcon
      _ = 1 / 2 := by rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem second_block_count (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)) (U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 256 ≤ qd M T)
    (hc : 971882496 * Real.log (qd M T) ^ 5 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) U (fun n => p.1 (n : ZMod M)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) := by
  set q := qd M T with hqdef
  set x : ℝ := (M : ℝ) * T with hx
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ x := by rw [hx]; nlinarith
  have hxq : x ≤ q := Nat.le_ceil x
  have hqx1 : (q : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqx : (q : ℝ) ≤ 2 * x := by linarith
  have hq' : (256 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le_second (by linarith)
  have hLq1 : 1 ≤ Real.log q := one_le_log_of_three_le_second (by linarith)
  have hLq : Real.log q ≤ 2 * Real.log x := by
    have h1 : Real.log q ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hU : 1 ≤ U := le_trans (Nat.one_le_pow _ _ (by omega)) hU1
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log q := dyadic_index_le_log_second q (by omega)
  have hJ0 : (0 : ℝ) < (pJd M T : ℝ) := by
    have : 0 < pJd M T := by unfold pJd; omega
    exact_mod_cast this
  have hl0 : 0 ≤ Real.log (2 * (U : ℝ)) := Real.log_nonneg (by linarith)
  have hl : 1 + Real.log (2 * (U : ℝ)) ≤ 13 * Real.log q := by
    have h1 : (2 * (U : ℝ)) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU2
    have h2 : Real.log (2 * (U : ℝ)) ≤ Real.log ((q : ℝ) ^ 12) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hG : 9 + 8 * Real.log (2 * T + 1) ≤ 17 * Real.log x := by
    have h1 : Real.log (2 * T + 1) ≤ Real.log x :=
      Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
    linarith
  have hG0 : 0 ≤ 9 + 8 * Real.log (2 * T + 1) := by
    have : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
    linarith
  have hK0 : 0 ≤ 8 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hK : 8 * ((M : ℝ) + 1) * (2 + 2 * T) ≤ 48 * q := by
    have : 8 * ((M : ℝ) + 1) * (2 + 2 * T) ≤ 48 * x := by rw [hx]; nlinarith
    linarith
  have hθ : (0 : ℝ) < 1 / (2 * (pJd M T : ℝ)) := by positivity
  have hsmall := second_small_condition ((U : ℝ) ^ (1 - 2 * σ)) (1 + Real.log (2 * (U : ℝ)))
    (8 * ((M : ℝ) + 1) * (2 + 2 * T)) (pJd M T : ℝ) q (Real.sqrt q) (Real.log q) (by linarith)
    (Real.sqrt_pos.2 (by linarith)) (rpow_neg_exponent_bound_second q U σ (by omega) hσ hU1) (by linarith) hl hK0 hK
    hJ0 hJ hc
  have hmain := dyadic_block_count S (fun p n => p.1 (n : ZMod M)) (fun p => p.2) (pYd M T) (pNd M T) U σ
    (1 / (2 * (pJd M T : ℝ))) (9 + 8 * Real.log (2 * T + 1)) (8 * ((M : ℝ) + 1) * (2 + 2 * T))
    hU hθ (by linarith) hG0 hK0 (fun p _ n => DirichletCharacter.norm_le_one _ _)
    (fun p hp => (hS p hp).1)
    (off_diagonal_bound M S σ T U hU hT (by linarith) hS hsp) hbig hsmall
  refine hmain.trans ?_
  have hu2 := rpow_pos_exponent_bound_second q U x σ (by linarith) hqx hσ hσ1 (by omega)
  have hu0 : 0 ≤ (U : ℝ) ^ (2 - 2 * σ) := by positivity
  have he : 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) / (1 / (2 * (pJd M T : ℝ))) ^ 2 =
      4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) * (4 * (pJd M T : ℝ) ^ 2) := by
    field_simp
    ring
  rw [he]
  have hl' : 1 + Real.log (2 * (U : ℝ)) ≤ 26 * Real.log x := by linarith
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log x := by linarith
  have hl00 : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by linarith
  gcongr

theorem zero_count_second : Count1 := by
  obtain ⟨q₁, hq₁⟩ := log_pow_five_le_sqrt 971882496
  refine ⟨48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)), max q₁ 256, ?_⟩
  intro M _ T σ S hM hT hσ hq hS hsp
  have hq256 : 256 ≤ qd M T := le_trans (le_max_right _ _) hq
  have hc := hq₁ (qd M T) (le_trans (le_max_left _ _) hq)
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ (M : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ Real.log ((M : ℝ) * T) := one_le_log_of_three_le_second (by linarith)
  have hX0 : 0 ≤ ((M : ℝ) * T) ^ (24 * (1 - σ)) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [card_empty, Nat.cast_zero]; positivity
  have hσ1 : σ ≤ 1 := by
    obtain ⟨-, h1, h2, -⟩ := hS p₀ hp₀
    linarith
  set B : ℝ := 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) * (4 * (48 * Real.log ((M : ℝ) * T)) ^ 2) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  classical
  let Sj : ℕ → Finset (DirichletCharacter ℂ M × ℂ) := fun j =>
    S.filter (fun p => 1 / (2 * (pJd M T : ℝ)) ≤
      ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => p.1 (n : ZMod M)) p.2‖)
  have hsub : S ⊆ (range (pJd M T)).biUnion Sj := by
    intro p hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS p hp
    obtain ⟨j, hj, hjb⟩ := zero_detection_second M p.1 h1 T hT hM p.2 (by linarith) h4 h5
    exact mem_biUnion.2 ⟨j, hj, mem_filter.2 ⟨hp, hjb⟩⟩
  have hj : ∀ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ B := by
    intro j hj
    have hjJ : j < pJd M T := mem_range.1 hj
    have hYN : qd M T ^ 3 * 2 ^ pJd M T ≤ qd M T ^ 12 := dyadic_size_le_pow_twelve_second (qd M T) hq256
    apply second_block_count M T σ (Sj j) (pYd M T * 2 ^ j) hM hT hσ hσ1 hq256 hc
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc 2 * (pYd M T * 2 ^ j) = qd M T ^ 3 * 2 ^ (j + 1) := by unfold pYd; ring
        _ ≤ qd M T ^ 3 * 2 ^ pJd M T := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ _ := hYN
    · intro p hp
      obtain ⟨-, h2, h3, h4, -⟩ := hS p (mem_filter.1 hp).1
      exact ⟨h2, h3.le, h4⟩
    · intro p hp p' hp'
      exact hsp p (mem_filter.1 hp).1 p' (mem_filter.1 hp').1
    · intro p hp
      exact (mem_filter.1 hp).2
  have h1 : (S.card : ℝ) ≤ ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    exact_mod_cast this
  have h2 : ∑ j ∈ range (pJd M T), ((Sj j).card : ℝ) ≤ (pJd M T : ℝ) * B := by
    have := sum_le_card_nsmul (range (pJd M T)) (fun j => ((Sj j).card : ℝ)) B hj
    simpa using this
  have hJ' : (pJd M T : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) := by
    have hJ : ((pJd M T : ℕ) : ℝ) ≤ 24 * Real.log (qd M T) := dyadic_index_le_log_second (qd M T) (by omega)
    have hqx1 : ((qd M T : ℕ) : ℝ) < (M : ℝ) * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hq' : (256 : ℝ) ≤ (qd M T : ℝ) := by exact_mod_cast hq256
    have h3 : Real.log (qd M T) ≤ Real.log (2 * ((M : ℝ) * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have h4 : Real.log 2 ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : (pJd M T : ℝ) * B ≤ 48 * Real.log ((M : ℝ) * T) * B := by gcongr
  have h4 : 48 * Real.log ((M : ℝ) * T) * B =
      48 * (4 * 64 * 26 ^ 3 * 17 * (4 * 48 ^ 2)) * ((M : ℝ) * T) ^ (24 * (1 - σ)) *
        Real.log ((M : ℝ) * T) ^ 7 := by
    rw [hB]; ring
  have h5 : Real.log ((M : ℝ) * T) ^ 7 ≤ Real.log ((M : ℝ) * T) ^ 10 :=
    pow_le_pow_right₀ hl1 (by norm_num)
  calc (S.card : ℝ) ≤ 48 * Real.log ((M : ℝ) * T) * B := h1.trans (h2.trans h3)
    _ = _ := h4
    _ ≤ _ := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ZeroCountFirst
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.OneLeLogOfThreeLe
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

theorem log_pow_seven_le_sqrt (c : ℝ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → c * Real.log q ^ 7 ≤ Real.sqrt q := by
  have h := isLittleO_log_rpow_rpow_atTop (7 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
  have hb := h.bound (show (0 : ℝ) < 1 / (|c| + 1) by positivity)
  have hn := tendsto_natCast_atTop_atTop.eventually hb
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp (hn.and (Filter.eventually_ge_atTop 1))
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨h1, h2⟩ := hq₀ q hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast h2
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at h1
  have e7 : Real.log q ^ (7 : ℝ) = Real.log q ^ 7 := by
    exact_mod_cast Real.rpow_natCast (Real.log q) 7
  rw [e7, ← Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  calc c * Real.log q ^ 7 ≤ |c| * Real.log q ^ 7 :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
    _ ≤ |c| * (1 / (|c| + 1) * Real.sqrt q) := by gcongr
    _ ≤ Real.sqrt q := by
        rw [← mul_assoc]
        apply mul_le_of_le_one_left hs
        rw [mul_one_div, div_le_one (by positivity)]
        linarith

theorem one_le_log_of_three_le' {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem dyadic_index_le_log (q : ℕ) (hq : 3 ≤ q) :
    ((8 * (Nat.log 2 q + 1) : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  have h1 : ((2 : ℝ) ^ Nat.log 2 q) ≤ q := by exact_mod_cast hpow
  have h2 : (Nat.log 2 q : ℝ) * Real.log 2 ≤ Real.log q := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have hl2 := Real.log_two_gt_d9
  have hlq : 1 ≤ Real.log q := one_le_log_of_three_le' (by exact_mod_cast hq)
  have hn0 : (0 : ℝ) ≤ Nat.log 2 q := Nat.cast_nonneg _
  have h3 : 0.6931471803 * (Nat.log 2 q : ℝ) ≤ Real.log q := by nlinarith
  push_cast
  linarith

theorem dyadic_size_le_pow_twelve (q : ℕ) (hq : 512 ≤ q) :
    2 * (q ^ 3 * 2 ^ (8 * (Nat.log 2 q + 1))) ≤ q ^ 12 := by
  have hpow : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 (by omega)
  generalize Nat.log 2 q = n at hpow ⊢
  have h8 : 2 ^ (8 * (n + 1)) = 256 * (2 ^ n) ^ 8 := by
    rw [show 8 * (n + 1) = n * 8 + 8 by ring, pow_add, pow_mul]
    ring
  have h9 : (2 ^ n) ^ 8 ≤ q ^ 8 := Nat.pow_le_pow_left hpow 8
  rw [h8]
  calc 2 * (q ^ 3 * (256 * (2 ^ n) ^ 8)) ≤ 2 * (q ^ 3 * (256 * q ^ 8)) := by gcongr
    _ = 512 * q ^ 11 := by ring
    _ ≤ q * q ^ 11 := by gcongr
    _ = q ^ 12 := by ring

theorem first_small_condition (u l K J q s Lq c : ℝ) (hq : 0 < q) (hs : 0 < s) (hc0 : 0 < c)
    (hu : u ≤ 1 / (q * s)) (hl0 : 0 ≤ l) (hl : l ≤ 13 * Lq) (hK0 : 0 ≤ K) (hK : K ≤ 16 * q)
    (hJ0 : 0 < J) (hJ : J ≤ 25 * Lq) (hc : 87880000 / c ^ 2 * Lq ^ 7 ≤ s) :
    2 * u * l ^ 3 * K ≤ (c / (J * Lq)) ^ 2 / 2 := by
  have hL : 0 < Lq := by linarith
  have hlK : 0 ≤ l ^ 3 * K := by positivity
  have step1 : 2 * u * l ^ 3 * K ≤ 2 * (1 / (q * s)) * l ^ 3 * K := by
    have := mul_le_mul_of_nonneg_right hu hlK
    nlinarith
  have step2 : 2 * (1 / (q * s)) * l ^ 3 * K ≤ 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) := by
    gcongr
  have step3 : 2 * (1 / (q * s)) * (13 * Lq) ^ 3 * (16 * q) = 70304 * Lq ^ 3 / s := by
    field_simp
    ring
  have hJL : (c / (25 * Lq * Lq)) ^ 2 / 2 ≤ (c / (J * Lq)) ^ 2 / 2 := by
    gcongr
  have hc' : 87880000 * Lq ^ 7 ≤ s * c ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hc
    exact hc
  have step4 : 70304 * Lq ^ 3 / s ≤ (c / (25 * Lq * Lq)) ^ 2 / 2 := by
    have e : (c / (25 * Lq * Lq)) ^ 2 / 2 = c ^ 2 / (1250 * Lq ^ 4) := by
      field_simp
      ring
    rw [e, div_le_div_iff₀ hs (by positivity)]
    nlinarith
  linarith

theorem rpow_neg_exponent_bound (q U : ℕ) (σ : ℝ) (hq : 1 ≤ q) (hσ : 3 / 4 ≤ σ) (hU : q ^ 3 ≤ U) :
    (U : ℝ) ^ (1 - 2 * σ) ≤ 1 / ((q : ℝ) * Real.sqrt q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq3 : (1 : ℝ) ≤ (q : ℝ) ^ 3 := one_le_pow₀ hq'
  have hU' : (q : ℝ) ^ 3 ≤ U := by exact_mod_cast hU
  have h1 : (U : ℝ) ^ (1 - 2 * σ) ≤ (U : ℝ) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : (U : ℝ) ^ (-(1 / 2) : ℝ) ≤ ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hU' (by norm_num)
  have h3 : ((q : ℝ) ^ 3) ^ (-(1 / 2) : ℝ) = 1 / ((q : ℝ) * Real.sqrt q) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, one_div]
    congr 1
    rw [show (q : ℝ) ^ 3 = (q : ℝ) ^ 2 * q by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  linarith

theorem rpow_pos_exponent_bound (q U : ℕ) (x σ : ℝ) (hx : 0 < x) (hqx : (q : ℝ) ≤ 2 * x) (hσ : 3 / 4 ≤ σ)
    (hσ1 : σ ≤ 1) (hU : U ≤ q ^ 12) : (U : ℝ) ^ (2 - 2 * σ) ≤ 64 * x ^ (24 * (1 - σ)) := by
  have he : 0 ≤ 2 - 2 * σ := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hUq : (U : ℝ) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU
  have s1 : (U : ℝ) ^ (2 - 2 * σ) ≤ ((q : ℝ) ^ 12) ^ (2 - 2 * σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hUq he
  have s2 : ((q : ℝ) ^ 12) ^ (2 - 2 * σ) ≤ ((2 * x) ^ 12) ^ (2 - 2 * σ) := by
    apply Real.rpow_le_rpow (by positivity) _ he
    gcongr
  have s3 : ((2 * x) ^ 12) ^ (2 - 2 * σ) = (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx.le]
    rw [show ((12 : ℕ) : ℝ) * (2 - 2 * σ) = 24 * (1 - σ) by push_cast; ring]
  have s4 : (2 : ℝ) ^ (24 * (1 - σ)) ≤ 64 := by
    calc (2 : ℝ) ^ (24 * (1 - σ)) ≤ (2 : ℝ) ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 64 := by rw [Real.rpow_natCast]; norm_num
  have hx' : 0 ≤ x ^ (24 * (1 - σ)) := by positivity
  calc (U : ℝ) ^ (2 - 2 * σ) ≤ (2 : ℝ) ^ (24 * (1 - σ)) * x ^ (24 * (1 - σ)) := by
        rw [← s3]; exact s1.trans s2
    _ ≤ 64 * x ^ (24 * (1 - σ)) := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem count_block0 (M : ℕ) (T σ c : ℝ) (S : Finset (DirichletCharacter ℂ 1 × ℂ)) (N U : ℕ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hσ : 3 / 4 ≤ σ) (hσ1 : σ ≤ 1) (hq : 512 ≤ qd M T) (hc0 : 0 < c)
    (hc : 87880000 / c ^ 2 * Real.log (qd M T) ^ 7 ≤ Real.sqrt (qd M T))
    (hU1 : qd M T ^ 3 ≤ U) (hU2 : 2 * U ≤ qd M T ^ 12)
    (hS : ∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T)
    (hsp : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → 1 ≤ |p.2.im - p'.2.im|)
    (hbig : ∀ p ∈ S, c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
      ‖blkD (pYd M T) N U (fun n => p.1 (n : ZMod 1)) p.2‖) :
    (S.card : ℝ) ≤ 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) *
      ((50 * Real.log ((M : ℝ) * T) * (2 * Real.log ((M : ℝ) * T))) ^ 2 / c ^ 2) := by
  set q := qd M T with hqdef
  set x : ℝ := (M : ℝ) * T with hx
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ x := by rw [hx]; nlinarith
  have hxq : x ≤ q := Nat.le_ceil x
  have hqx1 : (q : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hqx : (q : ℝ) ≤ 2 * x := by linarith
  have hq' : (512 : ℝ) ≤ q := by exact_mod_cast hq
  have hl1 : 1 ≤ Real.log x := one_le_log_of_three_le' (by linarith)
  have hLq1 : 1 ≤ Real.log q := one_le_log_of_three_le' (by linarith)
  have hLq : Real.log q ≤ 2 * Real.log x := by
    have h1 : Real.log q ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hqx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hU : 1 ≤ U := le_trans (Nat.one_le_pow _ _ (by omega)) hU1
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hJ : ((pJd M T : ℕ) : ℝ) + 1 ≤ 25 * Real.log q := dyadic_index_le_log q (by omega)
  have hJ0 : (0 : ℝ) < (pJd M T : ℝ) + 1 := by positivity
  have hl0 : 0 ≤ Real.log (2 * (U : ℝ)) := Real.log_nonneg (by linarith)
  have hl : 1 + Real.log (2 * (U : ℝ)) ≤ 13 * Real.log q := by
    have h1 : (2 * (U : ℝ)) ≤ (q : ℝ) ^ 12 := by exact_mod_cast hU2
    have h2 : Real.log (2 * (U : ℝ)) ≤ Real.log ((q : ℝ) ^ 12) := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at h2
    push_cast at h2
    linarith
  have hG : 9 + 8 * Real.log (2 * T + 1) ≤ 17 * Real.log x := by
    have h1 : Real.log (2 * T + 1) ≤ Real.log x :=
      Real.log_le_log (by linarith) (by rw [hx]; nlinarith)
    linarith
  have hG0 : 0 ≤ 9 + 8 * Real.log (2 * T + 1) := by
    have : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
    linarith
  have hK0 : 0 ≤ 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hK : 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) ≤ 16 * q := by
    have : 8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T) ≤ 16 * x := by
      rw [hx]; push_cast; nlinarith
    linarith
  have hθ : (0 : ℝ) < c / (((pJd M T : ℝ) + 1) * Real.log q) := by positivity
  have hsmall := first_small_condition ((U : ℝ) ^ (1 - 2 * σ)) (1 + Real.log (2 * (U : ℝ)))
    (8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T)) ((pJd M T : ℝ) + 1) q (Real.sqrt q) (Real.log q) c
    (by linarith) (Real.sqrt_pos.2 (by linarith)) hc0 (rpow_neg_exponent_bound q U σ (by omega) hσ hU1)
    (by linarith) hl hK0 hK hJ0 hJ hc
  have hmain := dyadic_block_count S (fun p n => p.1 (n : ZMod 1)) (fun p => p.2) (pYd M T) N U σ
    (c / (((pJd M T : ℝ) + 1) * Real.log q)) (9 + 8 * Real.log (2 * T + 1))
    (8 * (((1 : ℕ) : ℝ) + 1) * (2 + 2 * T))
    hU hθ (by linarith) hG0 hK0 (fun p _ n => DirichletCharacter.norm_le_one _ _)
    (fun p hp => (hS p hp).1)
    (off_diagonal_bound 1 S σ T U hU hT (by linarith) hS (fun p hp p' hp' hne _ => hsp p hp p' hp' hne))
    hbig hsmall
  refine hmain.trans ?_
  have hu2 := rpow_pos_exponent_bound q U x σ (by linarith) hqx hσ hσ1 (by omega)
  have hu0 : 0 ≤ (U : ℝ) ^ (2 - 2 * σ) := by positivity
  have he : 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) / (c / (((pJd M T : ℝ) + 1) * Real.log q)) ^ 2 =
      4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * (U : ℝ))) ^ 3 *
      (9 + 8 * Real.log (2 * T + 1)) * ((((pJd M T : ℝ) + 1) * Real.log q) ^ 2 / c ^ 2) := by
    have hLq0 : Real.log q ≠ 0 := by linarith
    field_simp
  rw [he]
  have hl' : 1 + Real.log (2 * (U : ℝ)) ≤ 26 * Real.log x := by linarith
  have hJ' : (pJd M T : ℝ) + 1 ≤ 50 * Real.log x := by linarith
  have hl00 : 0 ≤ 1 + Real.log (2 * (U : ℝ)) := by linarith
  have hLq00 : 0 ≤ Real.log q := by linarith
  gcongr

theorem zero_count_first : Count0 := by
  obtain ⟨c, hc0, q₂, hdet⟩ := zero_detection_first
  obtain ⟨q₁, hq₁⟩ := log_pow_seven_le_sqrt (87880000 / c ^ 2)
  refine ⟨100 * (4 * 64 * 26 ^ 3 * 17 * (100 ^ 2 / c ^ 2)), max (max q₁ q₂) 512, ?_⟩
  intro M _ T σ S hM hT hσ hq hS hsp
  have hq512 : 512 ≤ qd M T := le_trans (le_max_right _ _) hq
  have hc := hq₁ (qd M T) (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq)
  have hq2 : q₂ ≤ qd M T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hx6 : 6 ≤ (M : ℝ) * T := by nlinarith
  have hl1 : 1 ≤ Real.log ((M : ℝ) * T) := one_le_log_of_three_le' (by linarith)
  have hX0 : 0 ≤ ((M : ℝ) * T) ^ (24 * (1 - σ)) := by positivity
  rcases S.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · simp only [card_empty, Nat.cast_zero]; positivity
  have hσ1 : σ ≤ 1 := by
    obtain ⟨-, h1, h2, -⟩ := hS p₀ hp₀
    linarith
  set B : ℝ := 4 * (64 * ((M : ℝ) * T) ^ (24 * (1 - σ))) * (26 * Real.log ((M : ℝ) * T)) ^ 3 *
      (17 * Real.log ((M : ℝ) * T)) *
      ((50 * Real.log ((M : ℝ) * T) * (2 * Real.log ((M : ℝ) * T))) ^ 2 / c ^ 2) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  classical
  let e : DirichletCharacter ℂ M × ℂ → DirichletCharacter ℂ 1 × ℂ := fun p => (1, p.2)
  have hinj : Set.InjOn e (S : Set (DirichletCharacter ℂ M × ℂ)) := by
    intro p hp p' hp' h
    have h2 : (e p).2 = (e p').2 := congrArg Prod.snd h
    exact Prod.ext ((hS p hp).1.trans (hS p' hp').1.symm) h2
  set S' : Finset (DirichletCharacter ℂ 1 × ℂ) := S.image e with hS'
  have hcard : S'.card = S.card := card_image_of_injOn hinj
  let Sij : ℕ × ℕ → Finset (DirichletCharacter ℂ 1 × ℂ) := fun ij =>
    S'.filter (fun p => c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
      ‖blkD (pYd M T) (2 ^ ij.1 * pNd M T) (pYd M T * 2 ^ ij.2) (fun n => p.1 (n : ZMod 1)) p.2‖)
  have hsub : S' ⊆ (range 2 ×ˢ range (pJd M T + 1)).biUnion Sij := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hS a ha
    rw [h1] at h5
    obtain ⟨i, hi, j, hj, hjb⟩ := hdet M T hT hM hq2 a.2 (by linarith) h4 h5
    exact mem_biUnion.2 ⟨(i, j), mem_product.2 ⟨hi, hj⟩, mem_filter.2 ⟨hp, hjb⟩⟩
  have hj : ∀ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) ≤ B := by
    intro ij hij
    have hjJ : ij.2 < pJd M T + 1 := mem_range.1 (mem_product.1 hij).2
    have hYN : 2 * (qd M T ^ 3 * 2 ^ pJd M T) ≤ qd M T ^ 12 := dyadic_size_le_pow_twelve (qd M T) hq512
    apply count_block0 M T σ c (Sij ij) (2 ^ ij.1 * pNd M T) (pYd M T * 2 ^ ij.2) hM hT hσ hσ1 hq512
      hc0 hc
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · calc 2 * (pYd M T * 2 ^ ij.2) ≤ 2 * (qd M T ^ 3 * 2 ^ pJd M T) := by
            unfold pYd
            gcongr
            omega
        _ ≤ _ := hYN
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_filter.1 hp).1
      obtain ⟨-, h2, h3, h4, -⟩ := hS a ha
      exact ⟨h2, h3.le, h4⟩
    · intro p hp p' hp' hne
      obtain ⟨a, ha, rfl⟩ := mem_image.1 (mem_filter.1 hp).1
      obtain ⟨a', ha', rfl⟩ := mem_image.1 (mem_filter.1 hp').1
      exact hsp a ha a' ha' (fun h => hne (by rw [h]))
    · intro p hp
      exact (mem_filter.1 hp).2
  have h1 : (S.card : ℝ) ≤ ∑ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) := by
    have := (card_le_card hsub).trans card_biUnion_le
    rw [hcard] at this
    exact_mod_cast this
  have h2 : ∑ ij ∈ range 2 ×ˢ range (pJd M T + 1), ((Sij ij).card : ℝ) ≤
      2 * ((pJd M T : ℝ) + 1) * B := by
    have := sum_le_card_nsmul (range 2 ×ˢ range (pJd M T + 1)) (fun ij => ((Sij ij).card : ℝ)) B hj
    simpa using this
  have hJ' : (pJd M T : ℝ) + 1 ≤ 50 * Real.log ((M : ℝ) * T) := by
    have hJ : ((pJd M T : ℕ) : ℝ) + 1 ≤ 25 * Real.log (qd M T) := dyadic_index_le_log (qd M T) (by omega)
    have hqx1 : ((qd M T : ℕ) : ℝ) < (M : ℝ) * T + 1 := Nat.ceil_lt_add_one (by linarith)
    have hq' : (512 : ℝ) ≤ (qd M T : ℝ) := by exact_mod_cast hq512
    have h3 : Real.log (qd M T) ≤ Real.log (2 * ((M : ℝ) * T)) :=
      Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h3
    have h4 : Real.log 2 ≤ Real.log ((M : ℝ) * T) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have h3 : 2 * ((pJd M T : ℝ) + 1) * B ≤ 2 * (50 * Real.log ((M : ℝ) * T)) * B := by gcongr
  have h4 : 2 * (50 * Real.log ((M : ℝ) * T)) * B =
      100 * (4 * 64 * 26 ^ 3 * 17 * (100 ^ 2 / c ^ 2)) * ((M : ℝ) * T) ^ (24 * (1 - σ)) *
        Real.log ((M : ℝ) * T) ^ 9 := by
    rw [hB]; ring
  have h5 : Real.log ((M : ℝ) * T) ^ 9 ≤ Real.log ((M : ℝ) * T) ^ 10 :=
    pow_le_pow_right₀ hl1 (by norm_num)
  calc (S.card : ℝ) ≤ 2 * (50 * Real.log ((M : ℝ) * T)) * B := h1.trans (h2.trans h3)
    _ = _ := h4
    _ ≤ _ := by gcongr

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

theorem re_lt_one_of_isLZero {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M} {s : ℂ}
    (h : IsLZero χ s) : s.re < 1 := by
  by_contra hc
  push Not at hc
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h.1 hc h.2

theorem log_density_bound : Formalism.HermitianLattices.Ext.PrimesInProgressions.LogDensityM := by
  classical
  obtain ⟨C0, q0, h0⟩ := zero_count_first
  obtain ⟨C1, q1, h1⟩ := zero_count_second
  refine ⟨24, 10, |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ), ?_⟩
  intro M _ T σ S hM hT hσ hS hsp
  suffices key : (S.card : ℝ) ≤ (|C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ)) *
      ((M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ (10 : ℕ)) by
    have hpow : Real.log (M * T) ^ (10 : ℝ) = Real.log (M * T) ^ (10 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [hpow, mul_assoc]
    exact key
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX : (6 : ℝ) ≤ M * T := by nlinarith
  have hX0 : (0 : ℝ) < M * T := by linarith
  have hL : (1 : ℝ) ≤ Real.log (M * T) := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hL10 : (1 : ℝ) ≤ Real.log (M * T) ^ 10 := one_le_pow₀ hL
  have hq0 : (0 : ℝ) ≤ ((max q0 q1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hCnn : 0 ≤ |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ) := by positivity
  have htriv : (S.card : ℝ) ≤ 3 * (M * T) := by
    have h := trivial_bound M T S (by linarith) (fun p hp => (hS p hp).2.1) hsp
    have hMnn : (0 : ℝ) ≤ M := by linarith
    nlinarith
  rcases S.eq_empty_or_nonempty with hE | ⟨p0, hp0⟩
  · rw [hE]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hCnn (mul_nonneg (Real.rpow_nonneg hX0.le _) (by positivity))
  have hσ1 : σ ≤ 1 := by
    have h1' := re_lt_one_of_isLZero (hS p0 hp0).2.2
    linarith [(hS p0 hp0).1]
  have hR1 : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) := Real.one_le_rpow (by linarith) (by linarith)
  have hP : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 := by nlinarith
  have hXP : σ < 3 / 4 → (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 := by
    intro hs
    have hXe : (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) := by
      calc (M * T : ℝ) = (M * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    nlinarith
  have h0' := fun S hσ' hq => h0 M T σ S hM hT hσ' hq
  have h1' := fun S hσ' hq => h1 M T σ S hM hT hσ' hq
  simp only [mul_assoc] at h0' h1'
  set P := (M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 with hPdef
  have hP0 : (0 : ℝ) ≤ P := by linarith
  set q : ℝ := ((max q0 q1 : ℕ) : ℝ) with hqdef
  have hexp : (|C0| + |C1| + 3 + 3 * q) * P = |C0| * P + |C1| * P + 3 * P + 3 * q * P := by ring
  rw [hexp]
  have eC0 := mul_le_mul_of_nonneg_right (le_abs_self C0) hP0
  have eC1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hP0
  have a0 : 0 ≤ |C0| * P := mul_nonneg (abs_nonneg _) hP0
  have a1 : 0 ≤ |C1| * P := mul_nonneg (abs_nonneg _) hP0
  have aq : q ≤ q * P := by nlinarith
  by_cases hq : max q0 q1 ≤ qd M T
  · by_cases hσ34 : 3 / 4 ≤ σ
    · have hA0 := h0' (S.filter (fun p => p.1 = 1)) hσ34 (le_trans (le_max_left _ _) hq)
        (by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hs := hS p hp.1
          exact ⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2⟩)
        (by
          intro p hp p' hp' hne
          rw [Finset.mem_filter] at hp hp'
          exact hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm))
      have hA1 := h1' (S.filter (fun p => ¬ p.1 = 1)) hσ34 (le_trans (le_max_right _ _) hq)
        (by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hs := hS p hp.1
          exact ⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2.2⟩)
        (by
          intro p hp p' hp' hne heq
          rw [Finset.mem_filter] at hp hp'
          exact hsp p hp.1 p' hp'.1 hne heq)
      have hcast : (S.card : ℝ) = ((S.filter (fun p => p.1 = 1)).card : ℝ) +
          ((S.filter (fun p => ¬ p.1 = 1)).card : ℝ) := by
        rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
      linarith
    · push_neg at hσ34
      have := hXP hσ34
      linarith
  · push_neg at hq
    have hXq : (M * T : ℝ) < q := by
      refine lt_of_le_of_lt (Nat.le_ceil _) ?_
      rw [hqdef]
      unfold qd at hq
      exact_mod_cast hq
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
