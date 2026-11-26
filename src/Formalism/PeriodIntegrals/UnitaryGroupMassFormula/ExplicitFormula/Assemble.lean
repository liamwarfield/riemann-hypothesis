module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronKernelB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronLOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructC

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronSumBound
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronSum
noncomputable section

namespace PI.EF

open Finset

theorem sum_rpow_le {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) ≤ 1 / ε := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(1 + ε))) (Set.Icc 1 (1 + (K : ℝ))) := by
    intro x hx y _ hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  beta_reduce at h1
  have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + (K : ℝ)) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨fun h => by linarith, h0⟩)] at h1
  have hexp : -(1 + ε) + 1 = -ε := by ring
  rw [hexp, Real.one_rpow] at h1
  have hpos : 0 ≤ (1 + (K : ℝ)) ^ (-ε) := Real.rpow_nonneg (by linarith) _
  have hrhs : ((1 + (K : ℝ)) ^ (-ε) - 1) / (-ε) ≤ 1 / ε := by
    rw [div_neg, ← neg_div, neg_sub]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  calc ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε))
      = ∑ i ∈ range K, (1 + ((i + 1 : ℕ) : ℝ)) ^ (-(1 + ε)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        push_cast
        ring
    _ ≤ _ := h1
    _ ≤ 1 / ε := hrhs

def logTerm (c : ℝ) (n : ℕ) : ℝ := Real.log n * (n : ℝ) ^ (-c)

theorem logTerm_nonneg (c : ℝ) (n : ℕ) : 0 ≤ logTerm c n := by
  exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem sum_logTerm_le {ε : ℝ} (hε : 0 < ε) (K : ℕ) :
    ∑ n ∈ range K, logTerm (1 + 2 * ε) n ≤ 1 / ε ^ 2 := by
  have e0 : logTerm (1 + 2 * ε) 0 = 0 := by simp [logTerm]
  have e1 : logTerm (1 + 2 * ε) 1 = 0 := by simp [logTerm]
  have hb : ∀ i : ℕ, logTerm (1 + 2 * ε) (i + 2) ≤ ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := by
    intro i
    unfold logTerm
    push_cast
    have hx : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hl := Real.log_le_rpow_div hx.le hε
    have hp : 0 ≤ ((i : ℝ) + 2) ^ (-(1 + 2 * ε)) := Real.rpow_nonneg hx.le _
    calc Real.log ((i : ℝ) + 2) * ((i : ℝ) + 2) ^ (-(1 + 2 * ε))
        ≤ ((i : ℝ) + 2) ^ ε / ε * ((i : ℝ) + 2) ^ (-(1 + 2 * ε)) := mul_le_mul_of_nonneg_right hl hp
      _ = ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hx]
        congr 2
        ring
  calc ∑ n ∈ range K, logTerm (1 + 2 * ε) n
      ≤ ∑ n ∈ range (K + 2), logTerm (1 + 2 * ε) n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => logTerm_nonneg _ n)
    _ = ∑ i ∈ range K, logTerm (1 + 2 * ε) (i + 2) := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [zero_add, e0, e1, add_zero]
    _ ≤ ∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε)) / ε := Finset.sum_le_sum fun i _ => hb i
    _ = (∑ i ∈ range K, ((i : ℝ) + 2) ^ (-(1 + ε))) / ε := (Finset.sum_div _ _ _).symm
    _ ≤ (1 / ε) / ε := div_le_div_of_nonneg_right (sum_rpow_le hε K) hε.le
    _ = 1 / ε ^ 2 := by ring

theorem kb_nonneg {T : ℝ} (hT : 0 < T) (y : ℝ) : 0 ≤ kb T y := by
  unfold kb
  split_ifs
  · norm_num
  · exact div_nonneg zero_le_one (mul_nonneg hT.le (abs_nonneg _))

theorem kb_le_two {T : ℝ} (_hT : 0 < T) (y : ℝ) : kb T y ≤ 2 := by
  unfold kb
  split_ifs with h
  · exact le_rfl
  · have h' := not_le.mp h
    rw [div_le_iff₀ (by linarith)]
    linarith

theorem kb_le_of_le {T d y : ℝ} (hT : 0 < T) (hd : 0 < d) (h : d ≤ |Real.log y|) :
    kb T y ≤ 2 / (T * d) := by
  have hTd : 0 < T * d := mul_pos hT hd
  have hle : T * d ≤ T * |Real.log y| := mul_le_mul_of_nonneg_left h hT.le
  unfold kb
  split_ifs with h1
  · rw [le_div_iff₀ hTd]
    linarith
  · calc 1 / (T * |Real.log y|) ≤ 1 / (T * d) := one_div_le_one_div_of_le hTd hle
      _ ≤ 2 / (T * d) := div_le_div_of_nonneg_right (by norm_num) hTd.le

theorem abs_log_div_ge_far {u x : ℝ} (hu : 0 < u) (hx : 0 < x) (h : x ≤ u / 2 ∨ 2 * u ≤ x) :
    Real.log 2 ≤ |Real.log (u / x)| := by
  rcases h with h | h
  · have h2 : 2 ≤ u / x := by
      rw [le_div_iff₀ hx]
      linarith
    exact (Real.log_le_log (by norm_num) h2).trans (le_abs_self _)
  · have h2 : 2 ≤ x / u := by
      rw [le_div_iff₀ hu]
      linarith
    have hflip : Real.log (u / x) = -Real.log (x / u) := by
      rw [← Real.log_inv, inv_div]
    rw [hflip, abs_neg]
    exact (Real.log_le_log (by norm_num) h2).trans (le_abs_self _)

theorem log_ge_half {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h2 := Real.log_le_log (by norm_num) hu
  have h3 := Real.log_two_gt_d9
  linarith

theorem cLine_le_three {u : ℝ} (hu : 2 ≤ u) : cLine u ≤ 3 := by
  have hl := log_ge_half hu
  have h : 1 / Real.log u ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  unfold cLine
  linarith

theorem cLine_pos {u : ℝ} (hu : 2 ≤ u) : 0 < cLine u := by
  have hl := log_ge_half hu
  have h : 0 < 1 / Real.log u := one_div_pos.mpr (by linarith)
  unfold cLine
  linarith

theorem rpow_cLine {u : ℝ} (hu : 2 ≤ u) : u ^ cLine u = Real.exp 1 * u := by
  have hu0 : 0 < u := by linarith
  have hl : Real.log u ≠ 0 := by linarith [log_ge_half hu]
  unfold cLine
  rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, mul_one_div_cancel hl, mul_comm]

end PI.EF
end
end

noncomputable section

namespace PI.EF

open Finset

def nearB (u T : ℝ) (n : ℕ) : ℝ :=
  if n < ⌊u⌋₊ then (4 * u / T) / ((⌊u⌋₊ : ℝ) - n)
  else if n ≤ ⌊u⌋₊ + 1 then 2 else (4 * u / T) / ((n : ℝ) - ⌊u⌋₊ - 1)

theorem nearB_nonneg {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (n : ℕ) : 0 ≤ nearB u T n := by
  unfold nearB
  have h4 : 0 ≤ 4 * u / T := by positivity
  split_ifs with h1 h2
  · apply div_nonneg h4
    have h5 : (n : ℝ) < ⌊u⌋₊ := by exact_mod_cast h1
    linarith
  · norm_num
  · apply div_nonneg h4
    have h5 : (⌊u⌋₊ : ℝ) + 1 < n := by exact_mod_cast (by omega : ⌊u⌋₊ + 1 < n)
    linarith

theorem sum_inv_le (n : ℕ) : ∑ j ∈ range n, 1 / ((j : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ j ∈ range n, 1 / ((j : ℝ) + 1) := by
    rw [harmonic]
    push_cast
    simp [one_div]
  rw [← e]
  exact h

theorem sum_nearB (u T : ℝ) :
    ∑ n ∈ range (⌊u⌋₊ + (⌊u⌋₊ + 2)), nearB u T n =
      4 + 2 * ((4 * u / T) * ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1)) := by
  set n0 := ⌊u⌋₊ with hn0
  rw [Finset.sum_range_add, Finset.sum_range_succ', Finset.sum_range_succ']
  have e1 : ∑ n ∈ range n0, nearB u T n = (4 * u / T) * ∑ j ∈ range n0, 1 / ((j : ℝ) + 1) := by
    rw [← Finset.sum_range_reflect (fun j => 1 / ((j : ℝ) + 1)) n0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : n < n0 := Finset.mem_range.mp hn
    have hc : ((n0 - 1 - n : ℕ) : ℝ) + 1 = (n0 : ℝ) - n := by
      have : n0 - 1 - n + 1 = n0 - n := by omega
      have h2 : ((n0 - 1 - n + 1 : ℕ) : ℝ) = ((n0 - n : ℕ) : ℝ) := by rw [this]
      rw [Nat.cast_sub hn'.le] at h2
      rw [← h2]
      push_cast
      ring
    unfold nearB
    rw [if_pos (by rw [← hn0]; exact hn'), hc, ← hn0]
    ring
  have e2 : ∑ i ∈ range n0, nearB u T (n0 + (i + 1 + 1)) =
      (4 * u / T) * ∑ j ∈ range n0, 1 / ((j : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold nearB
    rw [← hn0, if_neg (by omega), if_neg (by omega)]
    have : ((n0 + (i + 1 + 1) : ℕ) : ℝ) - n0 - 1 = (i : ℝ) + 1 := by push_cast; ring
    rw [this]
    ring
  have e3 : nearB u T (n0 + (0 + 1)) = 2 := by
    unfold nearB
    rw [← hn0, if_neg (by omega), if_pos (by omega)]
  have e4 : nearB u T (n0 + 0) = 2 := by
    unfold nearB
    rw [← hn0, if_neg (by omega), if_pos (by omega)]
  rw [e1, e2, e3, e4]
  ring

theorem kb_le_div {u T x g : ℝ} (hu : 0 < u) (hT : 0 < T) (hx : 0 < x) (hx2 : x < 2 * u)
    (hg : 0 < g) (h : g ≤ |u - x|) : kb T (u / x) ≤ (4 * u / T) / g := by
  have hlog : g / (2 * u) ≤ |Real.log (u / x)| := by
    rcases le_or_gt x u with hxu | hxu
    · have h1 : 1 - x / u ≤ Real.log (u / x) := by
        have h0 := Real.one_sub_inv_le_log_of_pos (div_pos hu hx)
        rwa [inv_div] at h0
      have h2 : |u - x| = u - x := abs_of_nonneg (by linarith)
      rw [h2] at h
      have h3 : g / (2 * u) ≤ 1 - x / u := by
        rw [div_le_iff₀ (by positivity), sub_mul, div_mul_eq_mul_div, mul_div_assoc]
        have h4 : x * (2 * u) / u = 2 * x := by field_simp
        rw [mul_div_assoc] at h4
        nlinarith
      exact h3.trans (h1.trans (le_abs_self _))
    · have h1 : 1 - u / x ≤ Real.log (x / u) := by
        have h0 := Real.one_sub_inv_le_log_of_pos (div_pos hx hu)
        rwa [inv_div] at h0
      have e : |Real.log (u / x)| = Real.log (x / u) := by
        rw [Real.log_div hu.ne' hx.ne', Real.log_div hx.ne' hu.ne', abs_sub_comm,
          abs_of_nonneg (by linarith [Real.log_le_log hu hxu.le])]
      rw [e]
      have h2 : |u - x| = x - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      rw [h2] at h
      have h3 : g / (2 * u) ≤ 1 - u / x := by
        rw [div_le_iff₀ (by positivity)]
        have h4 : (1 - u / x) * (2 * u) = 2 * u - 2 * u * u / x := by ring
        rw [h4]
        have h5 : u * u / x ≤ u * u / u := div_le_div_of_nonneg_left (by positivity) hu hxu.le
        have h6 : u * u / u = u := by field_simp
        have h7 : 2 * u * u / x = 2 * (u * u / x) := by ring
        rw [h7]
        have h8 : (x - u) ≤ 2 * u - 2 * (u * u / x) := by
          have h9 : u * u / x ≤ u - (x - u) / 2 := by
            rw [div_le_iff₀ hx]
            nlinarith
          linarith
        linarith
      exact h3.trans h1
  unfold kb
  split_ifs with hk
  · rw [div_div, le_div_iff₀ (by positivity)]
    have hTg : T * (g / (2 * u)) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hlog hT.le) hk
    rw [mul_div_assoc'] at hTg
    rw [div_le_one (by positivity)] at hTg
    nlinarith
  · push_neg at hk
    rw [div_div, one_div_le (by positivity) (by positivity), one_div_div]
    have hTg : T * (g / (2 * u)) ≤ T * |Real.log (u / x)| := mul_le_mul_of_nonneg_left hlog hT.le
    have e : T * g / (4 * u) ≤ T * (g / (2 * u)) := by
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hT.le
      exact div_le_div_of_nonneg_left hg.le (by positivity) (by linarith)
    linarith

theorem kb_le_nearB {u T : ℝ} (hu : 0 < u) (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    (hn2 : (n : ℝ) < 2 * u) : kb T (u / n) ≤ nearB u T n := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have f1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu.le
  have f2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  unfold nearB
  split_ifs with h1 h2
  · have h3 : (n : ℝ) < ⌊u⌋₊ := by exact_mod_cast h1
    apply kb_le_div hu hT hx hn2 (by linarith)
    refine le_trans ?_ (le_abs_self _)
    linarith
  · exact kb_le_two hT _
  · have h3 : ((⌊u⌋₊ : ℝ) + 1) < n := by exact_mod_cast not_le.mp h2
    apply kb_le_div hu hT hx hn2 (by linarith)
    refine le_trans ?_ (neg_le_abs _)
    linarith

def pTerm (u T : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)

theorem pTerm_nonneg {u T : ℝ} (hu : 0 < u) (hT : 0 < T) (n : ℕ) : 0 ≤ pTerm u T n := by
  unfold pTerm
  have hk : 0 ≤ kb T (u / n) := by
    unfold kb
    split_ifs with h
    · norm_num
    · push_neg at h
      exact (one_div_pos.mpr (by linarith)).le
  exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)) hk

theorem pTerm_le_far {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    (h : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n) :
    pTerm u T n ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n := by
  have hu0 : 0 < u := by linarith
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : kb T (u / n) ≤ 4 / T := by
    have := kb_le_of_le hT (by norm_num : (0 : ℝ) < 1 / 2)
      (le_trans (by linarith [Real.log_two_gt_d9]) (abs_log_div_ge_far hu0 hx h))
    refine this.trans (le_of_eq ?_)
    field_simp
    norm_num
  have h2 : (u / n) ^ cLine u = Real.exp 1 * u * (n : ℝ) ^ (-cLine u) := by
    rw [Real.div_rpow hu0.le hx.le, Real.rpow_neg hx.le, rpow_cLine hu]
    rfl
  have h3 : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have h4 : 0 ≤ (u / n) ^ cLine u := Real.rpow_nonneg (by positivity) _
  have h5 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  unfold pTerm logTerm
  calc ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)
      ≤ Real.log n * (u / n) ^ cLine u * (4 / T) :=
        mul_le_mul (mul_le_mul_of_nonneg_right h3 h4) h1 (kb_nonneg hT _) (mul_nonneg h5 h4)
    _ = (4 * Real.exp 1 * u / T) * (Real.log n * (n : ℝ) ^ (-cLine u)) := by
        rw [h2]; ring

theorem pTerm_le_near {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) {n : ℕ}
    (h1 : u / 2 < (n : ℝ)) (h2 : (n : ℝ) < 2 * u) :
    pTerm u T n ≤ 16 * Real.log u * nearB u T n := by
  have hu0 : 0 < u := by linarith
  have hx : (0 : ℝ) < n := by linarith
  have hn : 0 < n := by exact_mod_cast hx
  have hL := log_ge_half hu
  have a1 : ArithmeticFunction.vonMangoldt n ≤ 2 * Real.log u := by
    refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
    have : Real.log n ≤ Real.log (2 * u) := Real.log_le_log hx h2.le
    rw [Real.log_mul (by norm_num) hu0.ne'] at this
    have h3 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
    linarith
  have a2 : (u / n) ^ cLine u ≤ 8 := by
    have hle : u / n ≤ 2 := by rw [div_le_iff₀ hx]; linarith
    calc (u / n) ^ cLine u ≤ (2 : ℝ) ^ cLine u :=
          Real.rpow_le_rpow (by positivity) hle (cLine_pos hu).le
      _ ≤ (2 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (cLine_le_three hu)
      _ = 8 := by
          rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have a3 := kb_le_nearB hu0 hT hn h2
  have b1 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have b2 : 0 ≤ (u / n) ^ cLine u := Real.rpow_nonneg (by positivity) _
  unfold pTerm
  calc ArithmeticFunction.vonMangoldt n * (u / n) ^ cLine u * kb T (u / n)
      ≤ (2 * Real.log u * 8) * nearB u T n :=
        mul_le_mul (mul_le_mul a1 a2 b2 (by linarith)) a3 (kb_nonneg hT _) (by positivity)
    _ = 16 * Real.log u * nearB u T n := by ring

theorem pTerm_le {u T : ℝ} (hu : 2 ≤ u) (hT : 0 < T) (n : ℕ) :
    pTerm u T n ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n +
      16 * Real.log u * (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
  have hu0 : 0 < u := by linarith
  have hL := log_ge_half hu
  have hA : 0 ≤ (4 * Real.exp 1 * u / T) * logTerm (cLine u) n :=
    mul_nonneg (by positivity) (logTerm_nonneg _ n)
  have hB : 0 ≤ 16 * Real.log u * (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
    apply mul_nonneg (by linarith)
    split_ifs
    · exact nearB_nonneg hu0 hT n
    · exact le_refl _
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · have : pTerm u T n = 0 := by simp [pTerm, h0]
    rw [this]
    linarith
  by_cases hfar : (n : ℝ) ≤ u / 2 ∨ 2 * u ≤ n
  · have := pTerm_le_far hu hT hn hfar
    linarith
  · rw [not_or, not_le, not_le] at hfar
    have h := pTerm_le_near hu hT hfar.1 hfar.2
    have f2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    have hlt : n < ⌊u⌋₊ + (⌊u⌋₊ + 2) := by
      have : (n : ℝ) < ((⌊u⌋₊ + (⌊u⌋₊ + 2) : ℕ) : ℝ) := by push_cast; linarith [hfar.2]
      exact_mod_cast this
    rw [if_pos hlt]
    linarith

theorem sum_pTerm_le {u T : ℝ} (hu : 2 ≤ u) (hT : 2 ≤ T) (K : ℕ) :
    ∑ n ∈ range K, pTerm u T n ≤ 500 * (u * Real.log u ^ 2 / T + Real.log u) := by
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  have hL := log_ge_half hu
  set L := Real.log u with hLdef
  have h1 : ∑ n ∈ range K, pTerm u T n ≤ (4 * Real.exp 1 * u / T) * ∑ n ∈ range K, logTerm (cLine u) n +
      16 * L * ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun n _ => pTerm_le hu hT0 n)
  have hc : cLine u = 1 + 2 * (1 / (2 * L)) := by
    unfold cLine
    rw [← hLdef]
    field_simp
  have h2 : ∑ n ∈ range K, logTerm (cLine u) n ≤ 4 * L ^ 2 := by
    rw [hc]
    refine (sum_logTerm_le (by positivity) K).trans (le_of_eq ?_)
    field_simp
    norm_num
  have h3 : ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) ≤
      4 + 2 * ((4 * u / T) * (3 * L)) := by
    rw [← Finset.sum_filter]
    have hsub : (range K).filter (fun n => n < ⌊u⌋₊ + (⌊u⌋₊ + 2)) ⊆ range (⌊u⌋₊ + (⌊u⌋₊ + 2)) := by
      intro n hn
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => nearB_nonneg hu0 hT0 n)).trans ?_
    rw [sum_nearB]
    have h4 := sum_inv_le ⌊u⌋₊
    have h5 : Real.log (⌊u⌋₊ : ℝ) ≤ L := by
      apply Real.log_le_log
      · exact_mod_cast Nat.floor_pos.mpr (by linarith : (1 : ℝ) ≤ u)
      · exact Nat.floor_le hu0.le
    have h6 : ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1) ≤ 3 * L := by linarith
    have h7 : (4 * u / T) * ∑ j ∈ range ⌊u⌋₊, 1 / ((j : ℝ) + 1) ≤ (4 * u / T) * (3 * L) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    linarith
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have huT : 0 < u / T := by positivity
  have k1 : (4 * Real.exp 1 * u / T) * ∑ n ∈ range K, logTerm (cLine u) n ≤
      (4 * 3 * (u / T)) * (4 * L ^ 2) := by
    have q1 : 4 * Real.exp 1 * u / T ≤ 4 * 3 * (u / T) := by
      have : 4 * Real.exp 1 * u / T = 4 * Real.exp 1 * (u / T) := by ring
      rw [this]
      nlinarith
    exact mul_le_mul q1 h2 (Finset.sum_nonneg (fun n _ => logTerm_nonneg _ n)) (by positivity)
  have k2 : 16 * L * ∑ n ∈ range K, (if n < ⌊u⌋₊ + (⌊u⌋₊ + 2) then nearB u T n else 0) ≤
      16 * L * (4 + 2 * ((4 * u / T) * (3 * L))) := mul_le_mul_of_nonneg_left h3 (by linarith)
  have k3 : u * L ^ 2 / T = (u / T) * L ^ 2 := by ring
  have k4 : 4 * u / T = 4 * (u / T) := by ring
  rw [k3]
  rw [k4] at k2
  have k5 : 0 ≤ (u / T) * L ^ 2 := by positivity
  nlinarith

theorem perronSumBound : PerronSumBound 500 := by
  intro u T hu hT
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  exact ⟨summable_of_sum_range_le (fun n => pTerm_nonneg hu0 hT0 n) (sum_pTerm_le hu hT),
    Real.tsum_le_of_sum_range_le (fun n => pTerm_nonneg hu0 hT0 n) (sum_pTerm_le hu hT)⟩

end PI.EF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectProofs
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.RectIntEqZeroOfDifferentiableOn
noncomputable section

namespace PI.EF.Rect

open Complex MeasureTheory intervalIntegral Set Filter Topology Real

def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I)

lemma continuousOn_hseg {f : ℂ → ℂ} {a₁ a₂ b : ℝ}
    (hc : ∀ x ∈ uIcc a₁ a₂, ContinuousAt f (x + b * I)) :
    ContinuousOn (fun x : ℝ => f (x + b * I)) (uIcc a₁ a₂) := by
  intro x hx
  exact (ContinuousAt.comp (f := fun t : ℝ => (t : ℂ) + b * I) (x := x) (hc x hx)
    (by fun_prop)).continuousWithinAt

lemma continuousOn_vseg {f : ℂ → ℂ} {a b₁ b₂ : ℝ}
    (hc : ∀ y ∈ uIcc b₁ b₂, ContinuousAt f (a + y * I)) :
    ContinuousOn (fun y : ℝ => f (a + y * I)) (uIcc b₁ b₂) := by
  intro y hy
  exact (ContinuousAt.comp (f := fun t : ℝ => (a : ℂ) + t * I) (x := y) (hc y hy)
    (by fun_prop)).continuousWithinAt

lemma hint_of_hasDerivAt {F f : ℂ → ℂ} {a₁ a₂ b : ℝ}
    (h : ∀ x ∈ uIcc a₁ a₂, HasDerivAt F (f (x + b * I)) (x + b * I))
    (hc : ∀ x ∈ uIcc a₁ a₂, ContinuousAt f (x + b * I)) :
    ∫ x : ℝ in a₁..a₂, f (x + b * I) = F (a₂ + b * I) - F (a₁ + b * I) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x + b * I))
    (fun x hx => ?_) (continuousOn_hseg hc).intervalIntegrable
  have hg : HasDerivAt (fun t : ℝ => (t : ℂ) + b * I) 1 x := by
    simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((b : ℂ) * I)
  have hd := (h x hx).comp x hg
  rw [mul_one] at hd
  exact hd

lemma vint_of_hasDerivAt {F f : ℂ → ℂ} {a b₁ b₂ : ℝ}
    (h : ∀ y ∈ uIcc b₁ b₂, HasDerivAt F (f (a + y * I)) (a + y * I))
    (hc : ∀ y ∈ uIcc b₁ b₂, ContinuousAt f (a + y * I)) :
    I • ∫ y : ℝ in b₁..b₂, f (a + y * I) = F (a + b₂ * I) - F (a + b₁ * I) := by
  have hd : ∀ y ∈ uIcc b₁ b₂, HasDerivAt (fun t : ℝ => F (a + t * I)) (f (a + y * I) * I) y := by
    intro y hy
    have hg : HasDerivAt (fun t : ℝ => (a : ℂ) + t * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (a : ℂ)
    exact (h y hy).comp y hg
  rw [← intervalIntegral.integral_smul]
  have e : (fun y : ℝ => I • f (a + y * I)) = fun y : ℝ => f (a + y * I) * I := by
    funext y
    rw [smul_eq_mul, mul_comm]
  rw [e]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_vseg hc).mul continuousOn_const).intervalIntegrable

def rectBdry (z w : ℂ) : Set ℂ :=
  {s | (s.re ∈ uIcc z.re w.re ∧ (s.im = z.im ∨ s.im = w.im)) ∨
       (s.im ∈ uIcc z.im w.im ∧ (s.re = z.re ∨ s.re = w.re))}

lemma hseg_mem_bdry_bot {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + z.im * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inl ⟨by simpa using hx, Or.inl (by simp)⟩

lemma hseg_mem_bdry_top {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    ((x : ℂ) + w.im * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inl ⟨by simpa using hx, Or.inr (by simp)⟩

lemma vseg_mem_bdry_left {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((z.re : ℂ) + y * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inr ⟨by simpa using hy, Or.inl (by simp)⟩

lemma vseg_mem_bdry_right {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    ((w.re : ℂ) + y * I) ∈ rectBdry z w := by
  simp only [rectBdry, Set.mem_ofPred_eq]
  exact Or.inr ⟨by simpa using hy, Or.inr (by simp)⟩

theorem rectInt_eq_zero_of_primitive {F f : ℂ → ℂ} {z w : ℂ}
    (h : ∀ s ∈ rectBdry z w, HasDerivAt F (f s) s) (hc : ∀ s ∈ rectBdry z w, ContinuousAt f s) :
    rectInt f z w = 0 := by
  unfold rectInt
  rw [hint_of_hasDerivAt (fun x hx => h _ (hseg_mem_bdry_bot hx)) (fun x hx => hc _ (hseg_mem_bdry_bot hx)),
    hint_of_hasDerivAt (fun x hx => h _ (hseg_mem_bdry_top hx)) (fun x hx => hc _ (hseg_mem_bdry_top hx)),
    vint_of_hasDerivAt (fun y hy => h _ (vseg_mem_bdry_right hy)) (fun y hy => hc _ (vseg_mem_bdry_right hy)),
    vint_of_hasDerivAt (fun y hy => h _ (vseg_mem_bdry_left hy)) (fun y hy => hc _ (vseg_mem_bdry_left hy))]
  ring

def rectOpen (z w : ℂ) : Set ℂ := {s | z.re < s.re ∧ s.re < w.re ∧ z.im < s.im ∧ s.im < w.im}

def rectClosed (z w : ℂ) : Set ℂ := Icc z.re w.re ×ℂ Icc z.im w.im

lemma ne_of_mem_bdry_of_mem_open {z w s p : ℂ} (hs : s ∈ rectBdry z w) (hp : p ∈ rectOpen z w) :
    s ≠ p := by
  rintro rfl
  obtain ⟨h1, h2, h3, h4⟩ := hp
  rcases hs with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> linarith

theorem rectInt_inv_sub_sq {z w p : ℂ} (hp : p ∈ rectOpen z w) :
    rectInt (fun s => ((s - p) ^ 2)⁻¹) z w = 0 := by
  apply rectInt_eq_zero_of_primitive (F := fun s => -(s - p)⁻¹)
  · intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    have hd := ((hasDerivAt_inv hne).comp_sub_const s p).neg
    rw [neg_neg] at hd
    exact hd
  · intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    exact ContinuousAt.fun_inv₀ (by fun_prop) (pow_ne_zero 2 hne)

lemma log_sub_log_neg_of_im_pos {a : ℂ} (ha : 0 < a.im) : Complex.log a - Complex.log (-a) = π * I := by
  have h := Complex.arg_neg_eq_arg_sub_pi_of_im_pos ha
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, h]

lemma log_neg_sub_log_of_im_neg {b : ℂ} (hb : b.im < 0) : Complex.log (-b) - Complex.log b = π * I := by
  have h := Complex.arg_neg_eq_arg_add_pi_of_im_neg hb
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, h]

theorem rectInt_inv_sub {z w p : ℂ} (hp : p ∈ rectOpen z w) :
    rectInt (fun s => (s - p)⁻¹) z w = 2 * π * I := by
  obtain ⟨h1, h2, h3, h4⟩ := id hp
  have hcont : ∀ s ∈ rectBdry z w, ContinuousAt (fun s => (s - p)⁻¹) s := fun s hs =>
    ContinuousAt.fun_inv₀ (by fun_prop) (sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp))
  have hL : ∀ s, s - p ∈ slitPlane → HasDerivAt (fun s => Complex.log (s - p)) ((s - p)⁻¹) s := by
    intro s hs
    simpa using ((hasDerivAt_id s).sub_const p).clog hs
  have hM : ∀ s, p - s ∈ slitPlane → HasDerivAt (fun s => Complex.log (p - s)) ((s - p)⁻¹) s := by
    intro s hs
    convert ((hasDerivAt_id s).const_sub p).clog hs using 1
    simp only [id_eq]
    rw [neg_div, ← div_neg, neg_sub, one_div]
    rfl
  unfold rectInt
  rw [hint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a₁ := z.re) (a₂ := w.re) (b := z.im)
      (fun x _ => hL _ (mem_slitPlane_iff.2 (Or.inr (by intro h; simp at h; linarith))))
      (fun x hx => hcont _ (hseg_mem_bdry_bot hx)),
    hint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a₁ := z.re) (a₂ := w.re) (b := w.im)
      (fun x _ => hL _ (mem_slitPlane_iff.2 (Or.inr (by intro h; simp at h; linarith))))
      (fun x hx => hcont _ (hseg_mem_bdry_top hx)),
    vint_of_hasDerivAt (F := fun s => Complex.log (s - p)) (f := fun s => (s - p)⁻¹)
      (a := w.re) (b₁ := z.im) (b₂ := w.im)
      (fun y _ => hL _ (mem_slitPlane_iff.2 (Or.inl (by simp; linarith))))
      (fun y hy => hcont _ (vseg_mem_bdry_right hy)),
    vint_of_hasDerivAt (F := fun s => Complex.log (p - s)) (f := fun s => (s - p)⁻¹)
      (a := z.re) (b₁ := z.im) (b₂ := w.im)
      (fun y _ => hM _ (mem_slitPlane_iff.2 (Or.inl (by simp; linarith))))
      (fun y hy => hcont _ (vseg_mem_bdry_left hy))]
  have e1 := log_sub_log_neg_of_im_pos (a := (z.re : ℂ) + w.im * I - p) (by simp; linarith)
  have e2 := log_neg_sub_log_of_im_neg (b := (z.re : ℂ) + z.im * I - p) (by simp; linarith)
  rw [neg_sub] at e1 e2
  beta_reduce
  linear_combination e1 + e2

lemma sides_integrable {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectBdry z w)) :
    IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + z.im * I).continuousOn
      fun x hx => hseg_mem_bdry_bot hx).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + w.im * I).continuousOn
      fun x hx => hseg_mem_bdry_top hx).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + y * I).continuousOn
      fun y hy => vseg_mem_bdry_right hy).intervalIntegrable
  · exact (hf.comp (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + y * I).continuousOn
      fun y hy => vseg_mem_bdry_left hy).intervalIntegrable

lemma rectInt_congr {f g : ℂ → ℂ} {z w : ℂ} (h : EqOn f g (rectBdry z w)) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  rw [intervalIntegral.integral_congr (fun x hx => h (hseg_mem_bdry_bot hx)),
    intervalIntegral.integral_congr (fun x hx => h (hseg_mem_bdry_top hx)),
    intervalIntegral.integral_congr (fun y hy => h (vseg_mem_bdry_right hy)),
    intervalIntegral.integral_congr (fun y hy => h (vseg_mem_bdry_left hy))]

lemma rectInt_add {f g : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectBdry z w))
    (hg : ContinuousOn g (rectBdry z w)) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  obtain ⟨f1, f2, f3, f4⟩ := sides_integrable hf
  obtain ⟨g1, g2, g3, g4⟩ := sides_integrable hg
  unfold rectInt
  beta_reduce
  rw [intervalIntegral.integral_add f1 g1, intervalIntegral.integral_add f2 g2,
    intervalIntegral.integral_add f3 g3, intervalIntegral.integral_add f4 g4]
  simp only [smul_eq_mul]
  ring

lemma rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectInt (fun s => c * f s) z w = c * rectInt f z w := by
  unfold rectInt
  beta_reduce
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

lemma rectInt_zero (z w : ℂ) : rectInt (fun _ => 0) z w = 0 := by
  unfold rectInt
  simp

lemma rectInt_finset_sum {ι : Type*} (S : Finset ι) (F : ι → ℂ → ℂ) {z w : ℂ}
    (hF : ∀ i ∈ S, ContinuousOn (F i) (rectBdry z w)) :
    rectInt (fun s => ∑ i ∈ S, F i s) z w = ∑ i ∈ S, rectInt (F i) z w := by
  classical
  revert hF
  refine Finset.induction_on S ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact rectInt_zero z w
  · intro a S ha ih hF
    simp only [Finset.sum_insert ha]
    rw [rectInt_add (hF a (Finset.mem_insert_self a S))
      (continuousOn_finsetSum _ fun i hi => hF i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

lemma mem_rectClosed {z w s : ℂ} :
    s ∈ rectClosed z w ↔ (z.re ≤ s.re ∧ s.re ≤ w.re) ∧ (z.im ≤ s.im ∧ s.im ≤ w.im) := by
  simp [rectClosed, Complex.mem_reProdIm]

lemma rectOpen_eq (z w : ℂ) : rectOpen z w = Ioo z.re w.re ×ℂ Ioo z.im w.im := by
  ext s
  simp [rectOpen, Complex.mem_reProdIm, and_assoc]

lemma rectClosed_mem_nhds {z w p : ℂ} (hp : p ∈ rectOpen z w) : rectClosed z w ∈ 𝓝 p := by
  have ho : IsOpen (rectOpen z w) := by
    rw [rectOpen_eq]
    exact isOpen_Ioo.reProdIm isOpen_Ioo
  refine Filter.mem_of_superset (ho.mem_nhds hp) fun s hs => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hs
  exact mem_rectClosed.2 ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩

lemma rectBdry_subset {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    rectBdry z w ⊆ rectClosed z w := by
  intro s hs
  rw [mem_rectClosed]
  rcases hs with ⟨hr, hi⟩ | ⟨hi, hr⟩
  · rw [uIcc_of_le hre, Set.mem_Icc] at hr
    rcases hi with hi | hi <;> exact ⟨hr, by constructor <;> linarith⟩
  · rw [uIcc_of_le him, Set.mem_Icc] at hi
    rcases hr with hr | hr <;> exact ⟨by constructor <;> linarith, hi⟩

lemma le_of_mem_rectOpen {z w p : ℂ} (hp : p ∈ rectOpen z w) : z.re ≤ w.re ∧ z.im ≤ w.im := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact ⟨by linarith, by linarith⟩

lemma continuousOn_div_sub {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : ContinuousOn h (rectBdry z w)) : ContinuousOn (fun s => h s / (s - p)) (rectBdry z w) :=
  hh.div (continuousOn_id.sub continuousOn_const) fun s hs =>
    sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)

lemma continuousOn_div_sub_sq {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : ContinuousOn h (rectBdry z w)) :
    ContinuousOn (fun s => h s / (s - p) ^ 2) (rectBdry z w) :=
  hh.div ((continuousOn_id.sub continuousOn_const).pow 2) fun s hs =>
    pow_ne_zero 2 (sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp))

theorem rectInt_div_sub {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : DifferentiableOn ℂ h (rectClosed z w)) :
    rectInt (fun s => h s / (s - p)) z w = 2 * π * I * h p := by
  obtain ⟨hre, him⟩ := le_of_mem_rectOpen hp
  have hN := rectClosed_mem_nhds hp
  have hsub := rectBdry_subset hre him
  have hdc : ContinuousOn (dslope h p) (rectClosed z w) :=
    (continuousOn_dslope hN).2 ⟨hh.continuousOn, hh.differentiableAt hN⟩
  have hz : rectInt (dslope h p) z w = 0 := by
    have e : rectClosed z w = uIcc z.re w.re ×ℂ uIcc z.im w.im := by
      rw [rectClosed, uIcc_of_le hre, uIcc_of_le him]
    unfold rectInt
    refine Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ z w {p}
      (Set.countable_singleton p) (e ▸ hdc) ?_
    intro x hx
    rw [min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hxo : x ∈ rectOpen z w := by
      rw [rectOpen_eq]
      exact hx1
    exact (differentiableAt_dslope_of_ne hx2).2 (hh.differentiableAt (rectClosed_mem_nhds hxo))
  have hinv : ContinuousOn (fun s => h p * (s - p)⁻¹) (rectBdry z w) :=
    continuousOn_const.mul (ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun s hs =>
      sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp))
  have hcong : EqOn (fun s => h s / (s - p)) (fun s => dslope h p s + h p * (s - p)⁻¹)
      (rectBdry z w) := by
    intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    simp only
    rw [dslope_of_ne _ (sub_ne_zero.1 hne), slope_def_field, div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [rectInt_congr hcong, rectInt_add (hdc.mono hsub) hinv, hz, rectInt_const_mul,
    rectInt_inv_sub hp]
  ring

theorem rectInt_div_sub_sq {h : ℂ → ℂ} {z w p : ℂ} (hp : p ∈ rectOpen z w)
    (hh : DifferentiableOn ℂ h (rectClosed z w)) :
    rectInt (fun s => h s / (s - p) ^ 2) z w = 2 * π * I * deriv h p := by
  obtain ⟨hre, him⟩ := le_of_mem_rectOpen hp
  have hN := rectClosed_mem_nhds hp
  have hsub := rectBdry_subset hre him
  have hd : DifferentiableOn ℂ (dslope h p) (rectClosed z w) :=
    (Complex.differentiableOn_dslope hN).2 hh
  have hinv : ContinuousOn (fun s => h p * ((s - p) ^ 2)⁻¹) (rectBdry z w) :=
    continuousOn_const.mul (ContinuousOn.inv₀ ((continuousOn_id.sub continuousOn_const).pow 2)
      fun s hs => pow_ne_zero 2 (sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)))
  have hcong : EqOn (fun s => h s / (s - p) ^ 2)
      (fun s => dslope h p s / (s - p) + h p * ((s - p) ^ 2)⁻¹) (rectBdry z w) := by
    intro s hs
    have hne : s - p ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs hp)
    simp only
    rw [dslope_of_ne _ (sub_ne_zero.1 hne), slope_def_field, div_div, ← sq, div_eq_mul_inv,
      div_eq_mul_inv]
    ring
  rw [rectInt_congr hcong, rectInt_add (continuousOn_div_sub hp (hd.continuousOn.mono hsub)) hinv,
    rectInt_div_sub hp hd, rectInt_const_mul, rectInt_inv_sub_sq hp, dslope_same]
  ring

theorem rect_residue_gen {z w : ℂ} {H E : ℂ → ℂ} (Z : Finset ℂ) (wt : ℂ → ℂ) (e : ℂ)
    (h0 : (0 : ℂ) ∈ rectOpen z w) (hH : DifferentiableOn ℂ H (rectClosed z w))
    (hE : DifferentiableOn ℂ E (rectClosed z w)) (hZ : ∀ ρ ∈ Z, ρ ≠ 0 ∧ ρ ∈ rectOpen z w) :
    rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * (E s / s)) z w =
      2 * π * I * (H 0 * E 0 + (∑ ρ ∈ Z, wt ρ * ((E ρ - E 0) / ρ)) + e * deriv E 0) := by
  obtain ⟨hre, him⟩ := le_of_mem_rectOpen h0
  have hsub := rectBdry_subset hre him
  have hEb : ContinuousOn E (rectBdry z w) := hE.continuousOn.mono hsub
  have hA : ContinuousOn (fun s => H s * E s / (s - 0)) (rectBdry z w) :=
    continuousOn_div_sub h0 ((hH.mul hE).continuousOn.mono hsub)
  have hT : ∀ ρ ∈ Z, ContinuousOn
      (fun s => wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0))) (rectBdry z w) :=
    fun ρ hρ => (continuousOn_const.mul (continuousOn_div_sub (hZ ρ hρ).2 hEb)).add
      (continuousOn_const.mul (continuousOn_div_sub h0 hEb))
  have hB : ContinuousOn
      (fun s => ∑ ρ ∈ Z, (wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0))))
      (rectBdry z w) := continuousOn_finsetSum _ hT
  have hC : ContinuousOn (fun s => e * (E s / (s - 0) ^ 2)) (rectBdry z w) :=
    continuousOn_const.mul (continuousOn_div_sub_sq h0 hEb)
  have hcong : EqOn (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * (E s / s))
      (fun s => H s * E s / (s - 0) +
        (∑ ρ ∈ Z, (wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0)))) +
        e * (E s / (s - 0) ^ 2)) (rectBdry z w) := by
    intro s hs
    have hs0 : s ≠ 0 := ne_of_mem_bdry_of_mem_open hs h0
    simp only [sub_zero]
    rw [add_mul, add_mul, Finset.sum_mul]
    have hterm : ∀ ρ ∈ Z, wt ρ / (s - ρ) * (E s / s) =
        wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / s) := by
      intro ρ hρ
      have hρ0 := (hZ ρ hρ).1
      have hsρ : s - ρ ≠ 0 := sub_ne_zero.2 (ne_of_mem_bdry_of_mem_open hs (hZ ρ hρ).2)
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm]
    congr 1
    · rw [mul_div_assoc]
    · rw [div_mul_div_comm, ← sq, mul_div_assoc]
  have hsum : ∀ ρ ∈ Z, rectInt (fun s => wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0))) z w =
      2 * π * I * (wt ρ * ((E ρ - E 0) / ρ)) := by
    intro ρ hρ
    rw [rectInt_add (f := fun s => wt ρ / ρ * (E s / (s - ρ))) (g := fun s => -(wt ρ / ρ) * (E s / (s - 0)))
      (continuousOn_const.mul (continuousOn_div_sub (hZ ρ hρ).2 hEb))
      (continuousOn_const.mul (continuousOn_div_sub h0 hEb)), rectInt_const_mul, rectInt_const_mul,
      rectInt_div_sub (hZ ρ hρ).2 hE, rectInt_div_sub h0 hE]
    ring
  rw [rectInt_congr hcong,
    rectInt_add (f := fun s => H s * E s / (s - 0) +
        ∑ ρ ∈ Z, (wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0))))
      (g := fun s => e * (E s / (s - 0) ^ 2)) (hA.add hB) hC,
    rectInt_add (f := fun s => H s * E s / (s - 0))
      (g := fun s => ∑ ρ ∈ Z, (wt ρ / ρ * (E s / (s - ρ)) + -(wt ρ / ρ) * (E s / (s - 0)))) hA hB, rectInt_finset_sum Z _ hT,
    rectInt_div_sub (h := fun s => H s * E s) h0 (hH.mul hE), rectInt_const_mul, rectInt_div_sub_sq h0 hE,
    Finset.sum_congr rfl hsum, ← Finset.mul_sum]
  ring

theorem rect_residue {z w : ℂ} {H : ℂ → ℂ} (Z : Finset ℂ) (wt : ℂ → ℂ) (e : ℂ) {u : ℝ} (hu : 0 < u)
    (h0 : (0 : ℂ) ∈ rectOpen z w) (hH : DifferentiableOn ℂ H (rectClosed z w))
    (hZ : ∀ ρ ∈ Z, ρ ≠ 0 ∧ ρ ∈ rectOpen z w) :
    rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + e / s) * ((u : ℂ) ^ s / s)) z w =
      2 * π * I * (H 0 + (∑ ρ ∈ Z, wt ρ * (((u : ℂ) ^ ρ - 1) / ρ)) + e * Real.log u) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
  have hd : ∀ s : ℂ, HasDerivAt (fun s : ℂ => (u : ℂ) ^ s) ((u : ℂ) ^ s * Complex.log u) s :=
    fun s => (hasStrictDerivAt_const_cpow (Or.inl hu0)).hasDerivAt
  have hE : DifferentiableOn ℂ (fun s : ℂ => (u : ℂ) ^ s) (rectClosed z w) :=
    fun s _ => (hd s).differentiableAt.differentiableWithinAt
  rw [rect_residue_gen Z wt e h0 hH hE hZ]
  beta_reduce
  rw [(hd 0).deriv, ofReal_log hu.le]
  simp only [cpow_zero, mul_one, one_mul]

end PI.EF.Rect
end
end

namespace PI.EF

open Complex

theorem rectResidue : RectResidue := by
  intro x₀ x₁ y₀ y₁ H Z wt e u hu h1 h2 h3 h4 hH hZ
  exact Rect.rect_residue (z := ⟨x₀, y₀⟩) (w := ⟨x₁, y₁⟩) Z wt e hu
    ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4⟩ hH
    (fun ρ hρ => ⟨(hZ ρ hρ).1, (hZ ρ hρ).2⟩)

end PI.EF
end

noncomputable section

namespace PI.EF

theorem explicitFormula_of_local (hZW : PI.ZerosWindow) (hLL : ∃ C, 0 < C ∧ LocalLemma C)
    (hSides : GlueSides) : PI.ExplicitFormula := by
  obtain ⟨Cw, hCw, hW⟩ := hZW
  obtain ⟨Cl, hCl, hL⟩ := hLL
  have hκ0 : (0 : ℝ) < 12 * Cw + 4 := by linarith
  have hCI : ContourIdentity := glueContour rectResidue zeroLocus zerosFinite
  have hH : ∃ C, 0 < C ∧ LogDerivHoriz (12 * Cw + 4) C :=
    ⟨_, by have := mul_pos hCw hκ0; linarith, logDerivHoriz_of hCw.le hCl.le hκ0 hW hL zeroLocus⟩
  have hLf : ∃ C, 0 < C ∧ LogDerivLeft C := ⟨_, by linarith, logDerivLeft_of hCw.le hCl.le hW hL zeroLocus⟩
  obtain ⟨Cs, hCs, hS⟩ := hSides (12 * Cw + 4) hκ0 hH hLf
  exact explicitFormula_of_perron_shift (12 * Cw + 4)
    ⟨500, by norm_num, PK.perronL_of (by norm_num) (PK.perronTrunc_of PK.perron_kernel_single_term perronSumBound)⟩
    ⟨Cs + (Cw + Cl) + 3, by linarith,
      shiftBound_of hκ0 hCs.le (by linarith) regularPart hCI hS (regAtZero_of hW hL)⟩
    (goodHeightExists_of hCw.le hW)
    ⟨4 * Cw, by linarith, truncChange_of hCw.le hW⟩ zerosFinite

end PI.EF
