module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensPair
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma norm_cpow_neg_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(b : ℂ) ^ (-w) - (a : ℂ) ^ (-w)‖ ≤ ‖w‖ * ((b - a) / a) := by
  by_cases hw0 : w = 0
  · subst hw0; simp
  have ha0 : 0 < a := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]; intro h; linarith [h.1]
  have hr : -w - 1 ≠ -1 := by
    intro h; apply hw0; linear_combination -h
  have hint := integral_cpow (a := a) (b := b) (r := -w - 1) (Or.inr ⟨hr, h0⟩)
  have e : -w - 1 + 1 = -w := by ring
  rw [e] at hint
  have hEq : (b : ℂ) ^ (-w) - (a : ℂ) ^ (-w) = -w * ∫ x : ℝ in a..b, (x : ℂ) ^ (-w - 1) := by
    rw [hint]; field_simp
  rw [hEq, norm_mul, norm_neg]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hb : ∀ x ∈ Set.uIoc a b, ‖(x : ℂ) ^ (-w - 1)‖ ≤ 1 / a := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have hx0 : 0 < x := by linarith
    rw [norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-w - 1).re = -w.re - 1 := by simp
    rw [hre]
    calc x ^ (-w.re - 1) ≤ x ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x⁻¹ := Real.rpow_neg_one x
      _ ≤ 1 / a := by rw [one_div]; exact inv_anti₀ ha0 hx.1.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [abs_of_nonneg (by linarith)] at this
  calc _ ≤ 1 / a * (b - a) := this
    _ = (b - a) / a := by ring

lemma norm_natCast_cpow_neg_le_one {n : ℕ} (hn : 1 ≤ n) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(n : ℂ) ^ (-w)‖ ≤ 1 := by
  rw [norm_natCast_cpow_of_pos (by omega), neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

lemma norm_cpow_step_le' {i U : ℕ} (hU : 1 ≤ U) (hi : U ≤ i) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖(((i + 1 : ℕ) : ℂ) ^ (-w) - (i : ℂ) ^ (-w))‖ ≤ ‖w‖ / U := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (by omega : 1 ≤ i)
  have h := norm_cpow_neg_sub_le (a := i) (b := (i : ℝ) + 1) hi1 (by linarith) hw
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e1, e2] at h
  refine h.trans ?_
  have hUi : (U : ℝ) ≤ i := by exact_mod_cast hi
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have : ((i : ℝ) + 1 - i) / i ≤ 1 / U := by
    rw [add_sub_cancel_left]
    exact one_div_le_one_div_of_le hU0 hUi
  calc ‖w‖ * (((i : ℝ) + 1 - i) / i) ≤ ‖w‖ * (1 / U) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ‖w‖ / U := by ring

lemma norm_sum_twist_le (g : ℕ → ℂ) {m : ℝ} (hGs : ∀ k, ‖∑ i ∈ range k, g i‖ ≤ m) {w : ℂ}
    (hw : 0 ≤ w.re) {U : ℕ} (hU : 1 ≤ U) :
    ‖∑ n ∈ Ioc U (2 * U), g n * (n : ℂ) ^ (-w)‖ ≤ 2 * m * (1 + ‖w‖) := by
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-w) with hf
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hGs 0)
  have hrw : ∑ n ∈ Ioc U (2 * U), g n * (n : ℂ) ^ (-w) = ∑ n ∈ Ioc U (2 * U), f n • g n := by
    refine sum_congr rfl (fun n _ => ?_); simp only [hf, smul_eq_mul]; ring
  rw [hrw, Finset.sum_Ioc_by_parts f g (by omega : U < 2 * U)]
  have hb1 : ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (2 * U)‖ * ‖∑ i ∈ range (2 * U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_natCast_cpow_neg_le_one (by omega) hw) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb2 : ‖f (U + 1) • ∑ i ∈ range (U + 1), g i‖ ≤ m := by
    rw [smul_eq_mul, norm_mul]
    calc ‖f (U + 1)‖ * ‖∑ i ∈ range (U + 1), g i‖ ≤ 1 * m :=
          mul_le_mul (norm_natCast_cpow_neg_le_one (by omega) hw) (hGs _) (norm_nonneg _) zero_le_one
      _ = m := one_mul m
  have hb3 : ‖∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ m * ‖w‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ i ∈ Ioc U (2 * U - 1),
        ‖(f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖ ≤ ‖w‖ / U * m := by
      intro i hi
      rw [smul_eq_mul, norm_mul]
      have hi' : U ≤ i := by have := (mem_Ioc.1 hi).1; omega
      exact mul_le_mul (norm_cpow_step_le' hU hi' hw) (hGs _) (norm_nonneg _) (by positivity)
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    have hcnt : ((2 * U - 1 - U : ℕ) : ℝ) ≤ U := by exact_mod_cast (by omega : 2 * U - 1 - U ≤ U)
    calc ((2 * U - 1 - U : ℕ) : ℝ) * (‖w‖ / U * m) ≤ U * (‖w‖ / U * m) :=
          mul_le_mul_of_nonneg_right hcnt (by positivity)
      _ = m * ‖w‖ := by field_simp
  calc ‖f (2 * U) • ∑ i ∈ range (2 * U + 1), g i - f (U + 1) • ∑ i ∈ range (U + 1), g i -
        ∑ i ∈ Ioc U (2 * U - 1), (f (i + 1) - f i) • ∑ k ∈ range (i + 1), g k‖
      ≤ m + m + m * ‖w‖ := by
        refine (norm_sub_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add hb1 hb2)) hb3
    _ ≤ 2 * m * (1 + ‖w‖) := by nlinarith [norm_nonneg w]

theorem pair_cross_bound : PairCross := by
  intro M _ ψ hψ w hw U hU
  have h := norm_sum_twist_le (fun n => ψ (n : ZMod M)) (m := (M : ℝ))
    (fun k => norm_character_sum_range_le ψ hψ k) hw hU
  refine h.trans ?_
  have : (0 : ℝ) ≤ M := by positivity
  nlinarith [norm_nonneg w]

lemma norm_sum_range_periodic_le {M : ℕ} [NeZero M] (h : ZMod M → ℂ) {K : ℝ} (hK : ∀ a, ‖h a‖ ≤ K)
    (h0 : ∑ a : ZMod M, h a = 0) (k : ℕ) : ‖∑ n ∈ range k, h (n : ZMod M)‖ ≤ K * M := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hq : ∑ n ∈ range M, h (n : ZMod M) = 0 := by
    rw [← h0]
    refine Finset.sum_bij' (fun n _ => (n : ZMod M)) (fun a _ => a.val) ?_ ?_ ?_ ?_ ?_
    · intro n _; exact Finset.mem_univ _
    · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
    · intro n hn; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hn)
    · intro a _; exact ZMod.natCast_zmod_val a
    · intro n _; rfl
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hM : M ≤ k
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hM
      have : ∑ n ∈ range (M + j), h (n : ZMod M) = ∑ n ∈ range j, h (n : ZMod M) := by
        rw [Finset.sum_range_add, hq, zero_add]
        refine Finset.sum_congr rfl ?_
        intro x _
        congr 1
        push_cast
        simp
      rw [this]
      exact ih j (by have := NeZero.pos M; omega)
    · push Not at hM
      calc ‖∑ n ∈ range k, h (n : ZMod M)‖ ≤ ∑ n ∈ range k, ‖h (n : ZMod M)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ range k, K := Finset.sum_le_sum (fun n _ => hK _)
        _ = K * k := by simp [mul_comm]
        _ ≤ K * M := mul_le_mul_of_nonneg_left (by exact_mod_cast hM.le) hK0

lemma norm_cpow_sub_prim_le {i : ℕ} (hi : 1 ≤ i) {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 - w ≠ 0) :
    ‖((i + 1 : ℕ) : ℂ) ^ (-w) - (((i + 1 : ℕ) : ℂ) ^ (1 - w) - (i : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      ‖w‖ / i := by
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hi0 : (0 : ℝ) < i := by linarith
  have hle : (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (i : ℝ) ((i : ℝ) + 1) := by
    rw [Set.uIcc_of_le hle]; intro h; linarith [h.1]
  have hr : -w ≠ -1 := by
    intro h; apply hw1; linear_combination h
  have hint := integral_cpow (a := (i : ℝ)) (b := (i : ℝ) + 1) (r := -w) (Or.inr ⟨hr, h0⟩)
  have e : -w + 1 = 1 - w := by ring
  have e1 : (((i : ℝ) : ℂ)) = (i : ℂ) := by push_cast; rfl
  have e2 : ((((i : ℝ) + 1 : ℝ)) : ℂ) = ((i + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [e, e1, e2] at hint
  set c : ℂ := ((i + 1 : ℕ) : ℂ) ^ (-w) with hc
  have hconst : ∫ _x : ℝ in (i : ℝ)..((i : ℝ) + 1), c = c := by
    rw [intervalIntegral.integral_const]; simp
  have hsub : c - (((i + 1 : ℕ) : ℂ) ^ (1 - w) - (i : ℂ) ^ (1 - w)) / (1 - w) =
      ∫ x : ℝ in (i : ℝ)..((i : ℝ) + 1), (c - (x : ℂ) ^ (-w)) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)), hconst, hint]
  rw [hsub]
  have hb : ∀ x ∈ Set.uIoc (i : ℝ) ((i : ℝ) + 1), ‖c - (x : ℂ) ^ (-w)‖ ≤ ‖w‖ / i := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have hx1 : 1 ≤ x := by linarith [hx.1]
    have hx0 : 0 < x := by linarith
    have h := norm_cpow_neg_sub_le (a := x) (b := (i : ℝ) + 1) hx1 hx.2 hw
    rw [e2] at h
    refine h.trans ?_
    have : ((i : ℝ) + 1 - x) / x ≤ 1 / i :=
      div_le_div₀ zero_le_one (by linarith [hx.1]) hi0 hx.1.le
    calc ‖w‖ * (((i : ℝ) + 1 - x) / x) ≤ ‖w‖ * (1 / i) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = ‖w‖ / i := by ring
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

lemma norm_sum_cpow_sub_prim_le {U : ℕ} (hU : 1 ≤ U) {w : ℂ} (hw : 0 ≤ w.re) (hw1 : 1 - w ≠ 0)
    (V : ℕ) (hV : U ≤ V) :
    ‖∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) - ((V : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      ((V : ℝ) - U) * (‖w‖ / U) := by
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ V hV ih =>
    have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
    rw [Finset.sum_Ioc_succ_top (by omega : U ≤ V)]
    have hstep := norm_cpow_sub_prim_le (i := V) (by omega) hw hw1
    have hstep' : ‖((V + 1 : ℕ) : ℂ) ^ (-w) -
        (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (V : ℂ) ^ (1 - w)) / (1 - w)‖ ≤ ‖w‖ / U := by
      refine hstep.trans ?_
      exact div_le_div_of_nonneg_left (norm_nonneg _) hU0 (by exact_mod_cast hV)
    have hsplit : ∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) + ((V + 1 : ℕ) : ℂ) ^ (-w) -
        (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w) =
        (∑ n ∈ Ioc U V, (n : ℂ) ^ (-w) - ((V : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)) +
        (((V + 1 : ℕ) : ℂ) ^ (-w) -
          (((V + 1 : ℕ) : ℂ) ^ (1 - w) - (V : ℂ) ^ (1 - w)) / (1 - w)) := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ((add_le_add ih hstep').trans (le_of_eq ?_))
    push_cast; ring

lemma norm_prim_dyadic_le {U : ℕ} (hU : 1 ≤ U) {w : ℂ} (hw : 0 ≤ w.re) (ht : w.im ≠ 0) :
    ‖(((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hre : (1 - w).re = 1 - w.re := by simp
  have hP : 0 < (U : ℝ) ^ (1 - w.re) := Real.rpow_pos_of_pos hU0 _
  have h1 : ‖(U : ℂ) ^ (1 - w)‖ = (U : ℝ) ^ (1 - w.re) := by
    rw [norm_natCast_cpow_of_pos (by omega), hre]
  have h2 : ‖((2 * U : ℕ) : ℂ) ^ (1 - w)‖ ≤ 2 * (U : ℝ) ^ (1 - w.re) := by
    rw [norm_natCast_cpow_of_pos (by omega), hre]
    push_cast
    rw [Real.mul_rpow (by norm_num) hU0.le]
    refine mul_le_mul_of_nonneg_right ?_ hP.le
    calc (2 : ℝ) ^ (1 - w.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h3 : |w.im| ≤ ‖1 - w‖ := by
    have := Complex.abs_im_le_norm (1 - w)
    simpa using this
  have ht0 : 0 < |w.im| := abs_pos.mpr ht
  rw [norm_div]
  refine div_le_div₀ (by positivity) ?_ ht0 h3
  refine (norm_sub_le _ _).trans ?_
  rw [h1]; linarith

theorem pair_same_bound : PairSame := by
  intro M _ w hw hw1 ht U hU
  have hM0 : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have h1w : 1 - w ≠ 0 := by
    intro h; apply ht
    have := congrArg Complex.im h
    simpa using this
  set c : ℂ := (Fintype.card (ZMod M)ˣ : ℂ) / (M : ℂ) with hc
  have hcn : ‖c‖ ≤ 1 := by
    rw [hc, norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one hM0,
      ZMod.card_units_eq_totient]
    exact_mod_cast Nat.totient_le M
  set h : ZMod M → ℂ := fun a => (1 : DirichletCharacter ℂ M) a - c with hh
  have hK : ∀ a, ‖h a‖ ≤ 2 := by
    intro a
    refine (norm_sub_le _ _).trans ?_
    have := DirichletCharacter.norm_le_one (1 : DirichletCharacter ℂ M) a
    linarith
  have hsum0 : ∑ a : ZMod M, h a = 0 := by
    simp only [hh]
    rw [Finset.sum_sub_distrib, MulChar.sum_one_eq_card_units, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, hc]
    have : (M : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    field_simp
    ring
  have hA := norm_sum_twist_le (fun n => h (n : ZMod M)) (m := 2 * (M : ℝ))
    (fun k => norm_sum_range_periodic_le h hK hsum0 k) hw hU
  have hB := norm_sum_cpow_sub_prim_le hU hw h1w (2 * U) (by omega)
  have hC := norm_prim_dyadic_le hU hw ht
  have hB' : ((((2 * U : ℕ) : ℝ)) - U) * (‖w‖ / U) = ‖w‖ := by
    push_cast; field_simp; ring
  rw [hB'] at hB
  have hS : ‖∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖ ≤ ‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
    have := norm_add_le (∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w) -
      (((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w))
      ((((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w))
    rw [sub_add_cancel] at this
    linarith
  have hsplit : ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w) =
      ∑ n ∈ Ioc U (2 * U), h (n : ZMod M) * (n : ℂ) ^ (-w) +
        c * ∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hh]; ring
  rw [hsplit]
  have hQ : 0 ≤ (U : ℝ) ^ (1 - w.re) / |w.im| := by positivity
  have hcS : ‖c * ∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖ ≤
      ‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
    rw [norm_mul]
    calc ‖c‖ * ‖∑ n ∈ Ioc U (2 * U), (n : ℂ) ^ (-w)‖
        ≤ 1 * (‖w‖ + 3 * (U : ℝ) ^ (1 - w.re) / |w.im|) :=
          mul_le_mul hcn hS (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  refine (norm_add_le _ _).trans ((add_le_add hA hcS).trans ?_)
  have e3 : 3 * (U : ℝ) ^ (1 - w.re) / |w.im| = 3 * ((U : ℝ) ^ (1 - w.re) / |w.im|) := by ring
  have e4 : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| = 4 * ((U : ℝ) ^ (1 - w.re) / |w.im|) := by ring
  rw [e3, e4]
  nlinarith [norm_nonneg w]

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensDiv
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma divSq_harm (x : ℕ) : ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ ≤ 1 + Real.log x := by
  have h := harmonic_le_one_add_log x
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  exact h

lemma divSq_count (x : ℕ) : ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 =
      ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, if Nat.lcm p.1 p.2 ∣ n then (1 : ℝ) else 0 := by
    intro n hn
    rw [mem_Icc] at hn
    have hd : n.divisors = (Icc 1 x).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨h, h0⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h (by omega), (Nat.le_of_dvd (by omega) h).trans hn.2⟩, h⟩
      · rintro ⟨_, h⟩
        exact ⟨h, by omega⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, sq, ← Nat.cast_mul,
      ← card_product, hd, ← filter_product]
    congr 2
    ext p
    simp [Nat.lcm_dvd_iff]
  rw [sum_congr rfl h1, sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, ← Nat.Ioc_filter_dvd_card_eq_div]
  rfl

lemma divSq_lcm {a b : ℕ} (ha : 1 ≤ a) :
    Nat.lcm a b = Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
  have h1 : Nat.gcd a b * (a / Nat.gcd a b) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have h2 : Nat.gcd a b * (b / Nat.gcd a b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  apply Nat.eq_of_mul_eq_mul_left hg
  calc Nat.gcd a b * Nat.lcm a b = a * b := Nat.gcd_mul_lcm a b
    _ = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [h1, h2]
    _ = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by ring

lemma divSq_cube (x : ℕ) :
    ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ ≤ (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
    with hφ
  set F : ℕ × ℕ × ℕ → ℝ := fun t => ((t.1 : ℝ))⁻¹ * (((t.2.1 : ℝ))⁻¹ * ((t.2.2 : ℝ))⁻¹) with hF
  have hinj : Set.InjOn φ (Icc 1 x ×ˢ Icc 1 x : Finset (ℕ × ℕ)) := by
    intro p _ q _ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨hg, h1, h2⟩ := h
    have e1 : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e2 : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    have e3 : Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) = q.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have e4 : Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) = q.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    ext
    · calc p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) := e1.symm
        _ = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := by rw [h1, hg]
        _ = q.1 := e3
    · calc p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) := e2.symm
        _ = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := by rw [h2, hg]
        _ = q.2 := e4
  have hsub : (Icc 1 x ×ˢ Icc 1 x).image φ ⊆ Icc 1 x ×ˢ (Icc 1 x ×ˢ Icc 1 x) := by
    intro t ht
    rw [mem_image] at ht
    obtain ⟨p, hp, rfl⟩ := ht
    simp only [mem_product, mem_Icc] at hp
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hp
    have hg : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left _ a1
    simp only [hφ, mem_product, mem_Icc]
    refine ⟨⟨hg, (Nat.le_of_dvd a1 (Nat.gcd_dvd_left _ _)).trans a2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd a1 (Nat.gcd_dvd_left _ _)) hg, (Nat.div_le_self _ _).trans a2⟩,
      ⟨Nat.div_pos (Nat.le_of_dvd b1 (Nat.gcd_dvd_right _ _)) hg, (Nat.div_le_self _ _).trans b2⟩⟩
  calc ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹
      = ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, F (φ p) := by
        refine sum_congr rfl fun p hp => ?_
        simp only [mem_product, mem_Icc] at hp
        rw [divSq_lcm hp.1.1]
        simp only [hF, hφ]
        push_cast
        rw [mul_inv, mul_inv, mul_assoc]
    _ = ∑ t ∈ (Icc 1 x ×ˢ Icc 1 x).image φ, F t := (sum_image hinj).symm
    _ ≤ ∑ t ∈ Icc 1 x ×ˢ (Icc 1 x ×ˢ Icc 1 x), F t := by
        refine sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => ?_
        simp only [hF]
        positivity
    _ = (∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹) ^ 3 := by
        simp only [hF]
        rw [sum_product]
        simp only [sum_product, ← mul_sum, ← sum_mul]
        ring

theorem divisor_square_bound : DivSq := by
  intro x hx
  have hlog : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  have hH0 : 0 ≤ ∑ k ∈ Icc 1 x, ((k : ℝ))⁻¹ := sum_nonneg fun k _ => by positivity
  calc ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2
      = ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((x / Nat.lcm p.1 p.2 : ℕ) : ℝ) := divSq_count x
    _ ≤ ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, (x : ℝ) * ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ := by
        refine sum_le_sum fun p _ => ?_
        rw [← div_eq_mul_inv]
        exact Nat.cast_div_le
    _ = (x : ℝ) * ∑ p ∈ Icc 1 x ×ˢ Icc 1 x, ((Nat.lcm p.1 p.2 : ℕ) : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ (x : ℝ) * (1 + Real.log x) ^ 3 := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg x)
        exact (divSq_cube x).trans (pow_le_pow_left₀ hH0 (divSq_harm x) 3)

theorem coefficient_block_bound : CoefficientBlockBound := by
  intro Y N U σ hU hσ
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hterm : ∀ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤
      (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hUn : (U : ℝ) ≤ n := by exact_mod_cast hn.1.le
    have h1 : ‖mco Y N n‖ ≤ (n.divisors.card : ℝ) := mco_norm_le Y N hn1
    have h2 : (n : ℝ) ^ (-σ) ≤ (U : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hU0 hUn (by linarith)
    have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h4 : ((U : ℝ) ^ (-σ)) ^ 2 = (U : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
      congr 1
      push_cast
      ring
    calc (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
        ≤ ((n.divisors.card : ℝ) * (U : ℝ) ^ (-σ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) h3)
            (mul_le_mul h1 h2 h3 (Nat.cast_nonneg _)) 2
      _ = (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
          rw [mul_pow, h4, mul_comm]
  have hsub : Ioc U (2 * U) ⊆ Icc 1 (2 * U) := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [mem_Icc]
    omega
  have hD := divisor_square_bound (2 * U) (by omega)
  have hpow : (U : ℝ) ^ (1 - 2 * σ) = (U : ℝ) ^ (-(2 * σ)) * U := by
    rw [show (1 - 2 * σ) = -(2 * σ) + 1 by ring, Real.rpow_add hU0, Real.rpow_one]
  calc ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2
      ≤ ∑ n ∈ Ioc U (2 * U), (U : ℝ) ^ (-(2 * σ)) * ((n.divisors.card : ℕ) : ℝ) ^ 2 := sum_le_sum hterm
    _ = (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Ioc U (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * ∑ n ∈ Icc 1 (2 * U), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hU0.le _)
        exact sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ (U : ℝ) ^ (-(2 * σ)) * (((2 * U : ℕ) : ℝ) * (1 + Real.log ((2 * U : ℕ) : ℝ)) ^ 3) :=
        mul_le_mul_of_nonneg_left hD (Real.rpow_nonneg hU0.le _)
    _ = 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
        rw [hpow]
        push_cast
        ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

lemma char_mul_conj_self {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (a : ZMod M) :
    χ a * (starRingEnd ℂ) (χ a) = (1 : DirichletCharacter ℂ M) a := by
  have h : (starRingEnd ℂ) (χ a) = χ⁻¹ a := MulChar.star_apply' χ a
  rw [h, ← MulChar.mul_apply, mul_inv_cancel]

lemma char_mul_conj {M : ℕ} [NeZero M] (χ χ' : DirichletCharacter ℂ M) (a : ZMod M) :
    χ a * (starRingEnd ℂ) (χ' a) = (χ * χ'⁻¹) a := by
  have h : (starRingEnd ℂ) (χ' a) = χ'⁻¹ a := MulChar.star_apply' χ' a
  rw [h, ← MulChar.mul_apply]

lemma offdiag_term {M : ℕ} [NeZero M] (σ T : ℝ) (U : ℕ) (hU : 1 ≤ U) (hT : 2 ≤ T) (hσ : 1 / 2 ≤ σ)
    (p p' : DirichletCharacter ℂ M × ℂ)
    (hp : σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) (hp' : σ ≤ p'.2.re ∧ p'.2.re ≤ 1 ∧ |p'.2.im| ≤ T)
    (hsp : p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) :
    ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (if p' = p then (U : ℝ) else 0) +
        (if p'.1 = p.1 then 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) else 0) +
        4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
  obtain ⟨hl, hu, hi⟩ := hp
  obtain ⟨hl', hu', hi'⟩ := hp'
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  set w : ℂ := (p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ)) with hw
  have hwre : w.re = p.2.re + p'.2.re - 2 * σ := by
    simp only [hw, add_re, sub_re, ofReal_re, conj_re]; ring
  have hwim : w.im = p.2.im - p'.2.im := by
    simp only [hw, add_im, sub_im, ofReal_im, conj_im]; ring
  have hw0 : 0 ≤ w.re := by rw [hwre]; linarith
  have hw1 : w.re ≤ 1 := by rw [hwre]; linarith
  have hwn : ‖w‖ ≤ 1 + 2 * T := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_nonneg hw0, hwim]
    have : |p.2.im - p'.2.im| ≤ |p.2.im| + |p'.2.im| := abs_sub _ _
    linarith
  have hB : 4 * ((M : ℝ) + 1) * (1 + ‖w‖) ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by
    have : 1 + ‖w‖ ≤ 2 + 2 * T := by linarith
    gcongr
  have hB0 : 0 ≤ 4 * ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have hq0 : 0 ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by positivity
  by_cases h1 : p' = p
  · rw [if_pos h1, if_pos (by rw [h1])]
    have hdiag : ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-w)‖ ≤ U := by
      refine (norm_sum_le _ _).trans ?_
      have : ∀ n ∈ Ioc U (2 * U), ‖p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w)‖ ≤ 1 := by
        intro n hn
        have hn1 : 1 ≤ n := by have := (mem_Ioc.1 hn).1; omega
        rw [norm_mul, norm_mul, Complex.norm_conj]
        have a1 : ‖p.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a2 : ‖p'.1 (n : ZMod M)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
        have a3 : ‖(n : ℂ) ^ (-w)‖ ≤ 1 := norm_natCast_cpow_neg_le_one hn1 hw0
        calc ‖p.1 (n : ZMod M)‖ * ‖p'.1 (n : ZMod M)‖ * ‖(n : ℂ) ^ (-w)‖ ≤ 1 * 1 * 1 := by
              gcongr
          _ = 1 := by norm_num
      refine (sum_le_sum this).trans ?_
      rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
      exact_mod_cast (by omega : 2 * U - U ≤ U)
    linarith
  · rw [if_neg h1]
    by_cases h2 : p'.1 = p.1
    · rw [if_pos h2]
      have hgap : 1 ≤ |p.2.im - p'.2.im| := hsp (fun h => h1 h.symm) h2.symm
      have him : w.im ≠ 0 := by
        rw [hwim]; intro h0; rw [h0, abs_zero] at hgap; linarith
      have hsame := pair_same_bound M w hw0 hw1 him U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [h2, char_mul_conj_self]
      rw [heq]
      have hUp : (U : ℝ) ^ (1 - w.re) ≤ U := by
        calc (U : ℝ) ^ (1 - w.re) ≤ (U : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
          _ = U := Real.rpow_one _
      have hdiv : 4 * (U : ℝ) ^ (1 - w.re) / |w.im| ≤ 4 * (U : ℝ) * (1 / |p.2.im - p'.2.im|) := by
        rw [hwim, mul_one_div]
        gcongr
      linarith
    · rw [if_neg h2]
      have hne : p.1 * p'.1⁻¹ ≠ 1 := by
        intro h; exact h2 (mul_inv_eq_one.1 h).symm
      have hcross := pair_cross_bound M (p.1 * p'.1⁻¹) hne w hw0 U hU
      have heq : ∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
          (n : ℂ) ^ (-w) =
          ∑ n ∈ Ioc U (2 * U), (p.1 * p'.1⁻¹) (n : ZMod M) * (n : ℂ) ^ (-w) := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [char_mul_conj]
      rw [heq]
      linarith

theorem off_diagonal_bound : Offdiag := by
  intro M _ S σ T U hU hT hσ hS hsp p hp
  classical
  have hU0 : (0 : ℝ) ≤ U := by positivity
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
  have hterm := fun p' (hp' : p' ∈ S) =>
    offdiag_term σ T U hU hT hσ p p' (hS p hp) (hS p' hp') (hsp p hp p' hp')
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq' S p, if_pos hp,
    ← sum_filter, ← mul_sum]
  set Fib : Finset (DirichletCharacter ℂ M × ℂ) := S.filter (fun p' => p'.1 = p.1) with hFib
  set P : Finset ℝ := Fib.image (fun p' => p'.2.im) with hP
  have hinj : Set.InjOn (fun p' : DirichletCharacter ℂ M × ℂ => p'.2.im) (Fib : Set _) := by
    intro a ha b hb hab
    have ha' := mem_filter.1 (mem_coe.1 ha)
    have hb' := mem_filter.1 (mem_coe.1 hb)
    by_contra hne
    have := hsp a ha'.1 b hb'.1 hne (ha'.2.trans hb'.2.symm)
    simp only at hab
    rw [hab, sub_self, abs_zero] at this
    linarith
  have hpF : p ∈ Fib := mem_filter.2 ⟨hp, rfl⟩
  have htP : p.2.im ∈ P := mem_image_of_mem _ hpF
  have hsp' := (zero_spacing P T (by linarith)
    (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      exact (hS a (mem_filter.1 ha).1).2.2)
    (by
      intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hy
      have ha' := mem_filter.1 ha
      have hb' := mem_filter.1 hb
      exact hsp a ha'.1 b hb'.1 (fun h => hxy (by rw [h])) (ha'.2.trans hb'.2.symm))).2 _ htP
  have hsumeq : ∑ p' ∈ Fib, 1 / |p.2.im - p'.2.im| = ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| := by
    rw [← add_zero (∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x|)]
    have h0 : (0 : ℝ) = 1 / |p.2.im - p.2.im| := by simp
    rw [h0, sum_erase_add P _ htP, hP, sum_image hinj]
  rw [hsumeq]
  have hc0 : (0 : ℝ) ≤ S.card := by positivity
  have hB0 : 0 ≤ ((M : ℝ) + 1) * (2 + 2 * T) := by positivity
  have h1 : 4 * (U : ℝ) * ∑ x ∈ P.erase p.2.im, 1 / |p.2.im - x| ≤
      4 * (U : ℝ) * (2 * (1 + Real.log (2 * T + 1))) := by gcongr
  have h2 : (S.card : ℝ) * (4 * ((M : ℝ) + 1) * (2 + 2 * T)) ≤
      (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    nlinarith
  linarith

lemma conj_natCast_cpow_neg' (n : ℕ) (z : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-z)) = (n : ℂ) ^ (-(starRingEnd ℂ) z) := by
  have h := Complex.cpow_conj (n : ℂ) (-z) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [map_neg] at h
  rw [h, Complex.conj_natCast]

theorem dyadic_block_count : BlockCnt := by
  intro α S f ρ Y N U σ θ G K hU hθ hσ hG hK hf hρ hoff hlarge hsmall
  set b : ℕ → ℂ := fun n => mco Y N n * (n : ℂ) ^ (-(σ : ℂ)) with hb
  set v : α → ℕ → ℂ := fun p n => f p n * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) with hv
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hbv : ∀ p, ∀ n ∈ Ioc U (2 * U), b n * v p n = mco Y N n * f p n * (n : ℂ) ^ (-ρ p) := by
    intro p n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    have : (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(ρ p - (σ : ℂ))) = (n : ℂ) ^ (-ρ p) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    simp only [hb, hv]
    rw [← this]; ring
  have hsum : ∀ p, ∑ n ∈ Ioc U (2 * U), b n * v p n = blkD Y N U (f p) (ρ p) := by
    intro p; unfold blkD; exact sum_congr rfl (hbv p)
  have heq : ∀ p p', ∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n) =
      ∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) *
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
    intro p p'
    refine sum_congr rfl (fun n hn => ?_)
    have hn0 : (n : ℂ) ≠ 0 := by
      have := (mem_Ioc.1 hn).1; exact_mod_cast (by omega : n ≠ 0)
    simp only [hv]
    rw [map_mul, conj_natCast_cpow_neg']
    have : (n : ℂ) ^ (-(ρ p - (σ : ℂ))) * (n : ℂ) ^ (-(starRingEnd ℂ) (ρ p' - (σ : ℂ))) =
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ)))) := by
      rw [← Complex.cpow_add _ _ hn0]; congr 1; ring
    rw [← this]; ring
  have hΔ : ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), v p n * (starRingEnd ℂ) (v p' n)‖ ≤
      (U : ℝ) * G + (S.card : ℝ) * K := by
    intro p hp
    simp only [heq]
    exact hoff p hp
  have hΔ0 : (0 : ℝ) ≤ (U : ℝ) * G + (S.card : ℝ) * K := by positivity
  have hmain := duality_inequality α ℕ S (Ioc U (2 * U)) b v _ hΔ0 hΔ
  simp only [hsum] at hmain
  set a : ℝ := 2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 with ha
  have hbn : ∑ n ∈ Ioc U (2 * U), ‖b n‖ ^ 2 ≤ a := by
    refine le_trans (le_of_eq ?_) (coefficient_block_bound Y N U σ hU hσ)
    refine sum_congr rfl (fun n hn => ?_)
    have hn1 : 0 < n := by have := (mem_Ioc.1 hn).1; omega
    simp only [hb, norm_mul, norm_natCast_cpow_of_pos hn1, neg_re, ofReal_re]
  have hlow : (S.card : ℝ) * θ ^ 2 ≤ ∑ p ∈ S, ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
    have : ∀ p ∈ S, θ ^ 2 ≤ ‖blkD Y N U (f p) (ρ p)‖ ^ 2 := by
      intro p hp
      exact pow_le_pow_left₀ hθ.le (hlarge p hp) 2
    have h := sum_le_sum this
    rw [sum_const, nsmul_eq_mul] at h
    exact h
  have haU : a * U = 2 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 := by
    have : (U : ℝ) ^ (2 - 2 * σ) = (U : ℝ) ^ (1 - 2 * σ) * (U : ℝ) ^ (1 : ℝ) := by
      rw [← Real.rpow_add hU0]; congr 1; ring
    rw [this, Real.rpow_one, ha]; ring
  have h1 : (S.card : ℝ) * θ ^ 2 ≤ a * ((U : ℝ) * G + (S.card : ℝ) * K) :=
    hlow.trans (hmain.trans (mul_le_mul_of_nonneg_right hbn hΔ0))
  have hS0 : (0 : ℝ) ≤ S.card := by positivity
  have h2 : (S.card : ℝ) * θ ^ 2 ≤ 2 * (a * U) * G := by
    have := mul_le_mul_of_nonneg_left hsmall hS0
    nlinarith
  have hθ2 : 0 < θ ^ 2 := by positivity
  rw [le_div_iff₀ hθ2]
  rw [haU] at h2
  linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
