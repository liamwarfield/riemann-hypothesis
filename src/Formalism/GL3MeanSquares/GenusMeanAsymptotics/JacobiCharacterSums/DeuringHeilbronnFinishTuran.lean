module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.NormUSum
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.UbTerms
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TwentyFiveMulSmallConstant
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExistsPowerSumLowerBound
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem exists_power_sum_lower_bound (C : ℝ) (a : ℕ) (hC : 0 < C)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (ε : ℝ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 2)
    (N : ℕ) (u : Fin N → ℂ) (hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re) (hi : ∃ i, 1 / 2 ≤ ‖u i‖)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ j n : ℕ, m + 1 ≤ j ∧ j ≤ m + a * n ∧ 1 ≤ n ∧ (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re ∧
      (1 / 2) ^ j * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤
        ‖∑ i, u i ^ j‖ + ε ^ (j - 2) * ∑ i, (u i).re := by
  classical
  have hre0 : ∀ i, 0 ≤ (u i).re := fun i => le_trans (sq_nonneg _) (hu i)
  have hle1 : ∀ i, ‖u i‖ ≤ 1 := by
    intro i
    have h1 := hu i
    have h2 : (u i).re ≤ ‖u i‖ := by
      first
        | exact Complex.re_le_norm (u i)
        | exact Complex.re_le_abs (u i)
    nlinarith [norm_nonneg (u i)]
  obtain ⟨i0, hi0⟩ := hi

  set I := Finset.univ.filter (fun i => ε ≤ ‖u i‖) with hIdef
  have hi0I : i0 ∈ I := Finset.mem_filter.2 ⟨Finset.mem_univ _, by linarith⟩
  have hIne : I.Nonempty := ⟨i0, hi0I⟩
  obtain ⟨i1, hi1I, hi1⟩ := Finset.exists_mem_eq_sup' hIne (fun i => ‖u i‖)
  set r := I.sup' hIne (fun i => ‖u i‖) with hr
  have hr0 : 1 / 2 ≤ r := le_trans hi0 (Finset.le_sup' (fun i => ‖u i‖) hi0I)
  have hrpos : 0 < r := by linarith
  have hnr : ‖(r : ℂ)‖ = r := by
    first
      | rw [Complex.norm_real, Real.norm_of_nonneg hrpos.le]
      | simp [abs_of_pos hrpos]
  set n := I.card with hn
  have hn1 : 1 ≤ n := Finset.card_pos.2 hIne
  let e : Fin n ≃ I := I.equivFin.symm
  let z : Fin n → ℂ := fun k => u (e k) / r
  have hz1 : ∀ k, ‖z k‖ ≤ 1 := by
    intro k
    simp only [z]
    rw [norm_div, hnr, div_le_one hrpos]
    exact Finset.le_sup' (fun i => ‖u i‖) (e k).2
  have hz2 : ∃ k, ‖z k‖ = 1 := by
    refine ⟨e.symm ⟨i1, hi1I⟩, ?_⟩
    simp only [z, Equiv.apply_symm_apply]
    rw [norm_div, hnr, ← hi1]
    exact div_self hrpos.ne'
  obtain ⟨k, hk1, hk2, hkB⟩ := hT n m z hn1 hz1 hz2

  have hsumz : ∑ k', z k' ^ k = (∑ i ∈ I, u i ^ k) / (r : ℂ) ^ k := by
    simp only [z, div_pow]
    rw [← Finset.sum_div]
    congr 1
    rw [← Finset.sum_coe_sort I]
    exact e.sum_comp (fun i : I => u i ^ k)
  have hB0 : 0 ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
    pow_nonneg (div_nonneg (Nat.cast_nonneg _) (mul_nonneg hC.le (by positivity))) _
  have hmain : (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i ∈ I, u i ^ k‖ := by
    rw [hsumz, norm_div, norm_pow, hnr, le_div_iff₀ (pow_pos hrpos k)] at hkB
    calc (1 / 2) ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n)
        ≤ r ^ k * ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hr0 k) hB0
      _ ≤ ‖∑ i ∈ I, u i ^ k‖ := by linarith

  have hcompl : ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ε ^ (k - 2) * ∑ i, (u i).re := by
    calc ∑ i ∈ Iᶜ, ‖u i‖ ^ k ≤ ∑ i ∈ Iᶜ, ε ^ (k - 2) * (u i).re := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hlt : ‖u i‖ < ε := by
            rw [Finset.mem_compl, Finset.mem_filter] at hi
            push_neg at hi
            exact hi (Finset.mem_univ _)
          calc ‖u i‖ ^ k = ‖u i‖ ^ 2 * ‖u i‖ ^ (k - 2) := by
                rw [← pow_add]
                congr 1
                omega
            _ ≤ (u i).re * ε ^ (k - 2) :=
                mul_le_mul (hu i) (pow_le_pow_left₀ (norm_nonneg _) hlt.le _) (by positivity) (hre0 i)
            _ = ε ^ (k - 2) * (u i).re := by ring
      _ = ε ^ (k - 2) * ∑ i ∈ Iᶜ, (u i).re := by rw [Finset.mul_sum]
      _ ≤ ε ^ (k - 2) * ∑ i, (u i).re :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i)
            (by positivity)
  have hsplit : ‖∑ i ∈ I, u i ^ k‖ ≤ ‖∑ i, u i ^ k‖ + ∑ i ∈ Iᶜ, ‖u i‖ ^ k := by
    have h := Finset.sum_add_sum_compl I (fun i => u i ^ k)
    have h' : ∑ i ∈ I, u i ^ k = ∑ i, u i ^ k - ∑ i ∈ Iᶜ, u i ^ k := by
      rw [← h]
      ring
    rw [h']
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_pow _ _))
  have hnε : (n : ℝ) * ε ^ 2 ≤ ∑ i, (u i).re := by
    calc (n : ℝ) * ε ^ 2 = ∑ i ∈ I, ε ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, (u i).re := Finset.sum_le_sum fun i hi =>
          le_trans (pow_le_pow_left₀ hε0.le (Finset.mem_filter.1 hi).2 2) (hu i)
      _ ≤ ∑ i, (u i).re :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hre0 i
  refine ⟨k, n, hk1, hk2, hn1, hnε, ?_⟩
  linarith [hmain, hsplit, hcompl]

theorem turan_lb (C : ℝ) (hC : 0 < C) (a n m : ℕ) (hn : 1 ≤ n) :
    Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1)) ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hCm : 0 < max C 1 := lt_max_of_lt_right one_pos
  have h1 : Real.exp (-(m : ℝ) / n) * (m + n) ≤ n :=
    calc Real.exp (-(m : ℝ) / n) * (m + n) = n * (Real.exp (-(m : ℝ) / n) * ((m : ℝ) / n + 1)) := by
          field_simp
      _ ≤ n * (Real.exp (-(m : ℝ) / n) * Real.exp ((m : ℝ) / n)) := by
          gcongr
          exact Real.add_one_le_exp _
      _ = n := by
          rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one]
  have hb : Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ≤ (n : ℝ) / (C * (m + n)) := by
    rw [Real.exp_sub, Real.exp_log hCm]
    have h2 : Real.exp (-(m : ℝ) / n) ≤ n / (m + n) := by
      rw [le_div_iff₀ (by positivity)]
      exact h1
    calc Real.exp (-(m : ℝ) / n) / max C 1 ≤ ((n : ℝ) / (m + n)) / max C 1 := by gcongr
      _ ≤ ((n : ℝ) / (m + n)) / C := by
          gcongr
          exact le_max_left _ _
      _ = n / (C * (m + n)) := by rw [div_div, mul_comm]
  calc Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1))
      = Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ^ (a * n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
    _ ≤ ((n : ℝ) / (C * (m + n))) ^ (a * n) := pow_le_pow_left₀ (Real.exp_pos _).le hb _

theorem fact_bound (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (hj : 1 ≤ j) :
    x ^ j / ((j - 1).factorial : ℝ) ≤ j * (Real.exp 1 * x / j) ^ j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hF : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hF1 : ((j - 1).factorial : ℝ) ≠ 0 := by positivity
  have hP : (0 : ℝ) < (j : ℝ) ^ j := pow_pos hjpos j
  have hfact : ((j - 1).factorial : ℝ) * j = j.factorial := by
    have : j * (j - 1).factorial = j.factorial := by
      first
        | exact Nat.mul_factorial_pred (show j ≠ 0 by omega)
        | exact Nat.mul_factorial_pred (show 0 < j by omega)
    rw [← this]
    push_cast
    ring
  have hkey : (j : ℝ) ^ j / j.factorial ≤ Real.exp 1 ^ j :=
    calc (j : ℝ) ^ j / j.factorial ≤ Real.exp j := by
          first
            | exact Real.pow_div_factorial_le_exp _ hjpos.le j
            | exact Real.pow_div_factorial_le_exp hjpos.le j
      _ = Real.exp 1 ^ j := by rw [← Real.exp_nat_mul, mul_one]
  have h1 : 1 / (j.factorial : ℝ) ≤ Real.exp 1 ^ j / (j : ℝ) ^ j := by
    rw [div_le_div_iff₀ hF hP]
    rw [div_le_iff₀ hF] at hkey
    linarith
  have hx' : 0 ≤ (j : ℝ) * x ^ j := by positivity
  calc x ^ j / ((j - 1).factorial : ℝ) = ((j : ℝ) * x ^ j) * (1 / j.factorial) := by
        rw [← hfact]
        field_simp
    _ ≤ ((j : ℝ) * x ^ j) * (Real.exp 1 ^ j / (j : ℝ) ^ j) := mul_le_mul_of_nonneg_left h1 hx'
    _ = j * (Real.exp 1 * x / j) ^ j := by
        rw [div_pow, mul_pow]
        ring

theorem log_sq_bound (M : ℝ) (hM : 1 ≤ M) : Real.log (3 * M) ^ 2 ≤ 32 * Real.sqrt M := by
  have h3M : (1 : ℝ) ≤ 3 * M := by linarith
  have hL0 : 0 ≤ Real.log (3 * M) := Real.log_nonneg h3M
  have hL : Real.log (3 * M) ≤ (3 * M) ^ ((1 : ℝ) / 4) / (1 / 4) :=
    Real.log_le_rpow_div (by linarith) (by norm_num)
  have hq : ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt (3 * M) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : Real.sqrt (3 * M) ≤ 2 * Real.sqrt M := by
    rw [← h4, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  calc Real.log (3 * M) ^ 2 ≤ ((3 * M) ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 2 :=
        pow_le_pow_left₀ hL0 hL 2
    _ = 16 * ((3 * M) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
    _ = 16 * Real.sqrt (3 * M) := by rw [hq]
    _ ≤ 32 * Real.sqrt M := by linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

def rr (a : ℕ) : ℝ := 16 * Real.exp ((a : ℝ) + 1)
def eps (a : ℕ) : ℝ := 1 / rr a
def th (a : ℕ) : ℝ := 1 / (2 * Real.log (rr a))
def kap (a : ℕ) (D : ℝ) : ℝ := th a * eps a ^ 2 / (a * (D + 1))
def c0 (a : ℕ) : ℝ := 1 / (25 * rr a)
def E0 (a : ℕ) (D : ℝ) : ℝ := Real.exp (a * D / eps a ^ 2)
def j0 (a : ℕ) : ℝ := 1 + a / eps a ^ 2
def GG (a : ℕ) (CP cZ cS c₁ : ℝ) : ℝ :=
  (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * c₁ * Real.exp (j0 a * Real.log (rr a)) + 1 + rr a + rr a ^ 2
def K0 (a : ℕ) (D CP cZ cS c₁ : ℝ) : ℝ := E0 a D * GG a CP cZ cS c₁ / th a

theorem rr_gt (a : ℕ) : 16 < rr a := by
  unfold rr
  have h1 := Real.add_one_le_exp ((a : ℝ) + 1)
  have h2 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  linarith

theorem log_rr_pos (a : ℕ) : 0 < Real.log (rr a) :=
  Real.log_pos (by linarith [rr_gt a])

theorem th_pos (a : ℕ) : 0 < th a := by
  unfold th
  exact div_pos one_pos (mul_pos two_pos (log_rr_pos a))

theorem th_log (a : ℕ) : 2 * th a * Real.log (rr a) = 1 := by
  have hL := (log_rr_pos a).ne'
  unfold th
  have e : 2 * (1 / (2 * Real.log (rr a))) * Real.log (rr a)
      = Real.log (rr a) * (Real.log (rr a))⁻¹ := by ring
  rw [e, mul_inv_cancel₀ hL]

private theorem rr_pos' (a : ℕ) : 0 < rr a := by
  unfold rr
  positivity

theorem eps_pos (a : ℕ) : 0 < eps a := by
  unfold eps
  exact div_pos one_pos (rr_pos' a)

theorem eps_le (a : ℕ) : eps a ≤ 1 / 16 := by
  have h := (rr_gt a).le
  unfold eps
  exact one_div_le_one_div_of_le (by norm_num) h

theorem kap_pos (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : 0 < kap a D := by
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  unfold kap
  exact div_pos (mul_pos (th_pos a) (pow_pos (eps_pos a) 2))
    (mul_pos ha0 (by linarith))

private theorem mul_kap_div_eps_sq_eq_th_div_succ (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    (a : ℝ) * kap a D / eps a ^ 2 = th a / (D + 1) := by
  have ha0 : (a : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega)).ne'
  have hi : eps a ^ 2 ≠ 0 := (pow_pos (eps_pos a) 2).ne'
  calc (a : ℝ) * kap a D / eps a ^ 2
      = th a / (D + 1) * ((a : ℝ) * (a : ℝ)⁻¹)
          * (eps a ^ 2 * (eps a ^ 2)⁻¹) := by
        have e : ∀ x h i d : ℝ, x * (h * i ^ 2 / (x * d)) / i ^ 2
            = h / d * (x * x⁻¹) * (i ^ 2 * (i ^ 2)⁻¹) := by
          intro x h i d
          ring
        unfold kap
        exact e _ _ _ _
    _ = th a / (D + 1) := by
        rw [mul_inv_cancel₀ ha0, mul_inv_cancel₀ hi, mul_one, mul_one]

private theorem div_mul_cancel_of_ne_zero_real (q d : ℝ) (hd : d ≠ 0) : q / d * d = q := by
  have e : q / d * d = q * (d * d⁻¹) := by ring
  rw [e, mul_inv_cancel₀ hd, mul_one]

theorem akapD_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) :
    a * D * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  have e2 : (a : ℝ) * D * kap a D / eps a ^ 2
      = D * ((a : ℝ) * kap a D / eps a ^ 2) := by ring
  rw [e2, mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0]

theorem akap_le' (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : a * kap a D / eps a ^ 2 ≤ th a := by
  have hD1 : (0 : ℝ) < D + 1 := by linarith
  have hq0 : 0 ≤ th a / (D + 1) := (div_pos (th_pos a) hD1).le
  have hq : th a / (D + 1) * (D + 1) = th a :=
    div_mul_cancel_of_ne_zero_real _ _ hD1.ne'
  rw [mul_kap_div_eps_sq_eq_th_div_succ a ha D hD]
  nlinarith [hq, hq0, mul_nonneg hq0 hD]

theorem kap_le (a : ℕ) (ha : 1 ≤ a) (D : ℝ) (hD : 0 ≤ D) : kap a D ≤ th a := by
  have hh := th_pos a
  have hi := eps_pos a
  have hi16 := eps_le a
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hM : (1 : ℝ) ≤ a * (D + 1) := by nlinarith
  have hMne : (a : ℝ) * (D + 1) ≠ 0 := (lt_of_lt_of_le one_pos hM).ne'
  have hs : kap a D * ((a : ℝ) * (D + 1)) = th a * eps a ^ 2 := by
    unfold kap
    exact div_mul_cancel_of_ne_zero_real _ _ hMne
  have hs0 : 0 ≤ kap a D := (kap_pos a ha D hD).le
  have hi2 : eps a ^ 2 ≤ 1 := by
    nlinarith [mul_le_mul hi16 hi16 hi.le (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  have hhi := mul_le_mul_of_nonneg_left hi2 hh.le
  have hsM := mul_le_mul_of_nonneg_left hM hs0
  nlinarith [hs, hhi, hsM]

theorem twentyFive_mul_smallConstant (a : ℕ) : 25 * c0 a = 1 / rr a := by
  unfold c0
  ring

private theorem succ_cube_le_eight_pow (j : ℕ) : (j + 1) ^ 3 ≤ 8 ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    calc (n + 1 + 1) ^ 3 ≤ (2 * (n + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * (n + 1) ^ 3 := by ring
      _ ≤ 8 * 8 ^ n := by gcongr
      _ = 8 ^ (n + 1) := by ring

theorem final_step (a : ℕ) (E G : ℝ) (hE : 0 < E) (hG : 0 < G) (j : ℕ)
    (hj : E * G < j)
    (h : 1 / (E * (rr a / 8) ^ j) ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j) : False := by
  have hb := rr_pos' a
  have hP : 0 < (rr a / 8) ^ j := by positivity
  have hB : 0 < rr a ^ j := by positivity
  have hPB : (rr a / 8) ^ j * 8 ^ j = rr a ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  have h1 : 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) = 1 :=
    div_mul_cancel_of_ne_zero_real _ _ (mul_pos hE hP).ne'
  have h2 : G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j = G * ((j : ℝ) + 1) ^ 2 :=
    div_mul_cancel_of_ne_zero_real _ _ hB.ne'
  have h3 := mul_le_mul_of_nonneg_right h (mul_pos hE hB).le
  have h4 : (8 : ℝ) ^ j ≤ G * ((j : ℝ) + 1) ^ 2 * E := by
    calc (8 : ℝ) ^ j = 1 / (E * (rr a / 8) ^ j) * (E * (rr a / 8) ^ j) * 8 ^ j := by
          rw [h1, one_mul]
      _ = 1 / (E * (rr a / 8) ^ j) * (E * rr a ^ j) := by
          rw [← hPB]
          ring
      _ ≤ G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * (E * rr a ^ j) := h3
      _ = G * ((j : ℝ) + 1) ^ 2 / rr a ^ j * rr a ^ j * E := by ring
      _ = G * ((j : ℝ) + 1) ^ 2 * E := by rw [h2]
  have hc : ((j : ℝ) + 1) ^ 3 ≤ 8 ^ j := by exact_mod_cast succ_cube_le_eight_pow j
  have hm := mul_lt_mul_of_pos_right hj (by positivity : (0 : ℝ) < ((j : ℝ) + 1) ^ 2)
  nlinarith [hm, hc, h4, sq_nonneg ((j : ℝ) + 1)]

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem lb_part (a : ℕ) (D : ℝ) (m n j : ℕ) (T : ℝ) (hmj : m ≤ j)
    (hanD : (a : ℝ) * n * D ≤ a * D / eps a ^ 2 + j)
    (hT : Real.exp (-((a : ℝ) * m) - a * n * D) ≤ T) :
    1 / (E0 a D * (rr a / 8) ^ j) ≤ (1 / 2) ^ j * T := by
  have hR : rr a / 8 = 2 * Real.exp ((a : ℝ) + 1) := by unfold rr; ring
  have hm' : (m : ℝ) ≤ j := by exact_mod_cast hmj
  have ham : (a : ℝ) * m ≤ a * j := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg a)
  have key : Real.exp (-((a : ℝ) * D / eps a ^ 2) - ((a : ℝ) + 1) * j)
      ≤ Real.exp (-((a : ℝ) * m) - a * n * D) := by
    apply Real.exp_le_exp.mpr
    linarith
  have heq : 1 / (E0 a D * (rr a / 8) ^ j)
      = (1 / 2) ^ j * Real.exp (-((a : ℝ) * D / eps a ^ 2) - ((a : ℝ) + 1) * j) := by
    rw [hR, E0, mul_pow, Real.exp_sub, Real.exp_neg, mul_comm ((a : ℝ) + 1) (j : ℝ),
      Real.exp_nat_mul]
    rw [one_div (2 : ℝ)]
    first
    | ring1
    | (field_simp; done)
    | (field_simp; ring1)
    | (field_simp; rw [← mul_pow]; norm_num)
  rw [heq]
  exact (mul_le_mul_of_nonneg_left key (by positivity)).trans
    (mul_le_mul_of_nonneg_left hT (by positivity))

theorem x_part (a : ℕ) (c₁ K : ℝ) (hc₁ : 0 < c₁) (j : ℕ) (hj : (j : ℝ) ≤ 2 * th a * K + j0 a) :
    c₁ * Real.exp (-K) ≤ c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j := by
  have hlog := log_rr_pos a
  have hid := th_log a
  have hRpos : 0 < rr a := by linarith [rr_gt a]
  have hRj : rr a ^ j = Real.exp (j * Real.log (rr a)) := by
    rw [Real.exp_nat_mul, Real.exp_log hRpos]
  rw [hRj, mul_div_assoc, ← Real.exp_sub]
  refine mul_le_mul_of_nonneg_left ?_ hc₁.le
  rw [Real.exp_le_exp]
  have h1 : (j : ℝ) * Real.log (rr a)
      ≤ (2 * th a * K + j0 a) * Real.log (rr a) :=
    mul_le_mul_of_nonneg_right hj hlog.le
  have h2 : (2 * th a * K + j0 a) * Real.log (rr a)
      = K + j0 a * Real.log (rr a) := by
    linear_combination K * hid
  linarith

theorem far_part (a : ℕ) (S : ℝ) (j : ℕ) (hj2 : 2 ≤ j) (hS : S ≤ 1 + j) :
    eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
  have hRpos : 0 < rr a := by linarith [rr_gt a]
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  have hinv : eps a ^ k = 1 / rr a ^ k := by
    unfold eps; rw [one_div_pow]
  have hJ0 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hSX : S ≤ (((k + 2 : ℕ) : ℝ) + 1) ^ 2 := by linarith [sq_nonneg ((k + 2 : ℕ) : ℝ)]
  have e : rr a ^ 2 * (((k + 2 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ (k + 2)
      = (((k + 2 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ k := by
    rw [pow_add (rr a) k 2, mul_comm (rr a ^ k) (rr a ^ 2),
      mul_div_mul_left _ _ (pow_ne_zero 2 hRpos.ne')]
  rw [hinv, e, one_div_mul_eq_div]
  gcongr

private theorem pow_mul_div_pow_succ_eq_div (η X : ℝ) (hη : η ≠ 0) (j : ℕ) :
    η ^ j * (X / η ^ (j + 1)) = X / η := by
  first
  | rw [mul_div_assoc', pow_succ η j, mul_div_mul_left _ _ (pow_ne_zero j hη)]
  | (field_simp; done)
  | (field_simp; ring)

private theorem pow_mul_div_mul_pow_eq_div (η M X : ℝ) (hη : η ≠ 0) (j : ℕ) :
    η ^ j * (X / (M * η ^ j)) = X / M := by
  first
  | rw [mul_div_assoc', mul_comm M (η ^ j), mul_div_mul_left _ _ (pow_ne_zero j hη)]
  | (field_simp; done)
  | (field_simp; ring)


set_option maxHeartbeats 800000 in
theorem ub_terms (a : ℕ) (CP CF cZ cS c₂ κ L ℓ lam η Mr K : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hCP : 0 < CP) (hCF : 0 < CF) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₂ : 0 < c₂)
    (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam) (hη : 0 < η) (hMr : 0 < Mr) (hK : 0 < K)
    (hlη1 : lam / η ≤ 2 * (lam * L) / cZ) (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hηc : η ≤ c0 a)
    (hηL : η * L < c₂ * K) (h25c : 25 * CF * c₂ ≤ κ) (hκth : κ ≤ th a)
    (hc₂P : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a) (hjr : th a * K < j) :
    η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) ≤
      (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
  have hR16 := rr_gt a
  have hRpos : 0 < rr a := by linarith
  have hRne : rr a ≠ 0 := hRpos.ne'
  have hηne : η ≠ 0 := hη.ne'
  have hL0 : 0 < L := by linarith
  have hJ1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hJpos : (0 : ℝ) < j := by linarith
  have hJsq : (j : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by linarith [sq_nonneg (j : ℝ)]
  have hL2 : 1 ≤ L ^ 2 := by linarith [mul_le_mul hL hL zero_le_one hL0.le]
  have hLL3 : L ≤ L ^ 3 := by linarith [mul_le_mul_of_nonneg_left hL2 hL0.le]
  have hL3 : 1 ≤ L ^ 3 := by linarith
  have hJ1sq : (j : ℝ) + 1 ≤ ((j : ℝ) + 1) ^ 2 * L ^ 3 := by
    linarith [mul_le_mul_of_nonneg_left hL3 (sq_nonneg ((j : ℝ) + 1)), sq_nonneg (j : ℝ)]
  have hJL : (j : ℝ) * L ≤ ((j : ℝ) + 1) ^ 2 * L ^ 3 := mul_le_mul hJsq hLL3 hL0.le (by positivity)
  have hℓ2 : ℓ ^ 2 ≤ 4 * L ^ 2 := by
    linarith [mul_le_mul hℓ hℓ hℓ0 (by linarith : (0 : ℝ) ≤ 2 * L)]
  have b1 : η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1)) ≤ 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_pow_succ_eq_div η _ hηne j]
    calc CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η = CP * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 * (lam / η) := by ring
      _ ≤ CP * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 * (2 * (lam * L) / cZ) :=
          mul_le_mul_of_nonneg_left hlη1 (by positivity)
      _ = 2 * CP * lam * L / cZ * ((j : ℝ) + 1) ^ 2 * ℓ ^ 2 := by ring
      _ ≤ 2 * CP * lam * L / cZ * ((j : ℝ) + 1) ^ 2 * (4 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hℓ2 (by positivity)
      _ = 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have b3 : η ^ j * (CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j)) ≤ 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_mul_pow_eq_div η Mr _ hηne j]
    calc CP * ((j : ℝ) + 1) * ℓ ^ 2 / Mr = CP * ((j : ℝ) + 1) * (ℓ ^ 2 / Mr) := by ring
      _ ≤ CP * ((j : ℝ) + 1) * (32 * lam / cS) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = 32 * CP / cS * lam * ((j : ℝ) + 1) := by ring
      _ ≤ 32 * CP / cS * lam * (((j : ℝ) + 1) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_left hJ1sq (by positivity)
      _ = 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have b4 : η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1)) ≤ 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by
    rw [pow_mul_div_pow_succ_eq_div η _ hηne j]
    calc 2 * (j : ℝ) * lam / η = 2 * (j : ℝ) * (lam / η) := by ring
      _ ≤ 2 * (j : ℝ) * (2 * (lam * L) / cZ) := mul_le_mul_of_nonneg_left hlη1 (by positivity)
      _ = 4 / cZ * lam * ((j : ℝ) * L) := by ring
      _ ≤ 4 / cZ * lam * (((j : ℝ) + 1) ^ 2 * L ^ 3) := mul_le_mul_of_nonneg_left hJL (by positivity)
      _ = 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) := by ring
  have hx0 : 0 ≤ CP * ℓ * η := by positivity
  have hxK : CP * ℓ * η ≤ 2 * CP * c₂ * K := by
    have e1 : CP * η * ℓ ≤ CP * η * (2 * L) := mul_le_mul_of_nonneg_left hℓ (by positivity)
    have e2 : CP * (η * L) ≤ CP * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le hCP.le
    linarith
  have hexR : Real.exp 1 * (CP * ℓ * η) * rr a ≤ th a * K := by
    calc Real.exp 1 * (CP * ℓ * η) * rr a
        ≤ Real.exp 1 * (2 * CP * c₂ * K) * rr a :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxK (Real.exp_pos 1).le) hRpos.le
      _ = (2 * Real.exp 1 * CP * c₂ * rr a) * K := by ring
      _ ≤ th a * K := mul_le_mul_of_nonneg_right hc₂P hK.le
  have hy : Real.exp 1 * (CP * ℓ * η) / (j : ℝ) ≤ 1 / rr a := by
    first
    | (rw [div_le_div_iff₀ hJpos hRpos]; linarith)
    | (rw [div_le_div_iff hJpos hRpos]; linarith)
    | (rw [div_le_div_iff_of_pos hJpos hRpos]; linarith)
  have b2 : η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) ≤ ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    calc η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) = (CP * ℓ * η) ^ j / ((j - 1).factorial : ℝ) := by ring
      _ ≤ (j : ℝ) * (Real.exp 1 * (CP * ℓ * η) / j) ^ j := fact_bound _ hx0 j hj
      _ ≤ (j : ℝ) * (1 / rr a) ^ j := by
          first
          | exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hy j) hJpos.le
          | exact mul_le_mul_of_nonneg_left (pow_le_pow_left (by positivity) hy j) hJpos.le
          | gcongr (j : ℝ) * ?_ ^ j
      _ = (j : ℝ) / rr a ^ j := by rw [one_div_pow, mul_one_div]
      _ ≤ ((j : ℝ) + 1) ^ 2 / rr a ^ j := by gcongr
  have b5 : η ^ j * (CF * L * 25 ^ j) ≤ rr a * (((j : ℝ) + 1) ^ 2 / rr a ^ j) := by
    have h25 : 25 * η ≤ 1 / rr a := by
      have := twentyFive_mul_smallConstant a
      linarith
    have hcl : 25 * (CF * η * L) ≤ (j : ℝ) := by
      have e1 : CF * (η * L) ≤ CF * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le hCF.le
      have e2 : 25 * CF * c₂ * K ≤ th a * K :=
        mul_le_mul_of_nonneg_right (h25c.trans hκth) hK.le
      linarith
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    calc η ^ (k + 1) * (CF * L * 25 ^ (k + 1)) = 25 * (CF * η * L) * (25 * η) ^ k := by ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (1 / rr a) ^ k := by
          first
          | exact mul_le_mul hcl (pow_le_pow_left₀ (by positivity) h25 k) (by positivity) (by positivity)
          | exact mul_le_mul hcl (pow_le_pow_left (by positivity) h25 k) (by positivity) (by positivity)
      _ = ((k + 1 : ℕ) : ℝ) / rr a ^ k := by rw [one_div_pow, mul_one_div]
      _ ≤ (((k + 1 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ k := by gcongr
      _ = rr a * ((((k + 1 : ℕ) : ℝ) + 1) ^ 2 / rr a ^ (k + 1)) := by
          rw [pow_succ (rr a) k, mul_div_assoc', mul_comm (rr a ^ k) (rr a),
            mul_div_mul_left _ _ hRne]
  have hsplit : η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ) + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * (j : ℝ) * lam / η ^ (j + 1) + CF * L * 25 ^ j)
      = η ^ j * (CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1)) + η ^ j * ((CP * ℓ) ^ j / ((j - 1).factorial : ℝ)) + η ^ j * (CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j)) + η ^ j * (2 * (j : ℝ) * lam / η ^ (j + 1)) + η ^ j * (CF * L * 25 ^ j) := by
    ring
  have hfin : 8 * CP / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + ((j : ℝ) + 1) ^ 2 / rr a ^ j + 32 * CP / cS * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + 4 / cZ * (((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)) + rr a * (((j : ℝ) + 1) ^ 2 / rr a ^ j) = (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by ring
  rw [hsplit]
  exact (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5).trans_eq hfin

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds

theorem norm_u_sum (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) (hη : 0 ≤ η) :
    ‖∑ i, ((η : ℂ) / w i) ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖ := by
  have e : ∑ i, ((η : ℂ) / w i) ^ j = (η : ℂ) ^ j * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow, mul_one_div]
  rw [e, norm_mul, norm_pow]
  congr 2
  simpa using abs_of_nonneg hη

theorem core2 (CT : ℝ) (a : ℕ) (hCT : 0 < CT) (ha : 1 ≤ a)
    (hT : ∀ (n m : ℕ) (z : Fin n → ℂ), 1 ≤ n → (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) →
      ∃ k : ℕ, m + 1 ≤ k ∧ k ≤ m + a * n ∧ ((n : ℝ) / (CT * ((m : ℝ) + n))) ^ (a * n) ≤ ‖∑ i, z i ^ k‖)
    (CF CP cZ cS c₁ c₂ : ℝ) (hCF : 0 < CF) (hCP : 0 < CP) (hcZ : 0 < cZ) (hcS : 0 < cS) (hc₁ : 0 < c₁)
    (hc₁Z : c₁ ≤ cZ / 4) (hc₂ : 0 < c₂)
    (hc₂κ : c₂ ≤ kap a (Real.log (max CT 1)) / (25 * CF))
    (hc₂P : c₂ ≤ th a / (2 * Real.exp 1 * CP * rr a))
    (L ℓ lam η Mr K : ℝ) (hL : 1 ≤ L) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ 2 * L) (hlam : 0 < lam)
    (hηZ : cZ / (2 * L) ≤ η) (hηc : η ≤ c0 a) (hηL : η * L < c₂ * K) (hMr : 0 < Mr)
    (hM : ℓ ^ 2 / Mr ≤ 32 * lam / cS) (hX : lam * L ^ 3 = c₁ * Real.exp (-K))
    (hK : K0 a (Real.log (max CT 1)) CP cZ cS c₁ < K)
    (N : ℕ) (w : Fin N → ℂ) (hw : ∀ i, η ≤ (w i).re) (hi0 : ∃ i, w i = ((η + η : ℝ) : ℂ))
    (hS : (∑ i, 1 / w i).re ≤ 2 * lam / η ^ 2 + CF * L * 25)
    (hpow : ∀ j : ℕ, 1 ≤ j → ‖∑ i, 1 / (w i) ^ j‖ ≤
        CP * lam * ℓ ^ 2 * ((j : ℝ) + 1) ^ 2 / η ^ (j + 1) + (CP * ℓ) ^ j / ((j - 1).factorial : ℝ)
        + CP * ((j : ℝ) + 1) * ℓ ^ 2 / (Mr * η ^ j) + 2 * j * lam / η ^ (j + 1) + CF * L * 25 ^ j) :
    False := by
  set D := Real.log (max CT 1) with hD_def
  have hD : 0 ≤ D := Real.log_nonneg (le_max_right _ _)
  have hL0 : 0 < L := by linarith
  have hη : 0 < η := lt_of_lt_of_le (by positivity) hηZ
  have hr := rr_gt a
  have hr0 : 0 < rr a := by linarith
  have hε0 := eps_pos a
  have hε1 := eps_le a
  have hth := th_pos a
  have hκ := kap_pos a ha D hD
  have hκth := kap_le a ha D hD
  have hE0 : 0 < E0 a D := Real.exp_pos _
  have hG : 0 < GG a CP cZ cS c₁ := by unfold GG; positivity
  have hK0 : 0 < K0 a D CP cZ cS c₁ := by unfold K0; positivity
  have hKpos : 0 < K := lt_trans hK0 hK
  have hthK : E0 a D * GG a CP cZ cS c₁ < th a * K := by
    have h1 : K0 a D CP cZ cS c₁ * th a = E0 a D * GG a CP cZ cS c₁ := by unfold K0; field_simp
    have h2 : K0 a D CP cZ cS c₁ * th a < K * th a := mul_lt_mul_of_pos_right hK hth
    linarith only [h1, h2]
  have hexpK : Real.exp (-K) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hXc : lam * L ^ 3 ≤ c₁ := by
    rw [hX]; have := mul_le_mul_of_nonneg_left hexpK hc₁.le; linarith only [this]
  have hlη1 : lam / η ≤ 2 * (lam * L) / cZ := by
    rw [div_le_div_iff₀ hη hcZ]
    have h1 : cZ ≤ 2 * L * η := by rw [div_le_iff₀ (by positivity)] at hηZ; linarith only [hηZ]
    have := mul_le_mul_of_nonneg_left h1 hlam.le
    linarith only [this]
  have hlamL : lam * L ≤ lam * L ^ 3 := by
    have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
    have h3 : L ≤ L ^ 3 := by
      have : L ^ 3 = L * L ^ 2 := by ring
      rw [this]; have := mul_le_mul_of_nonneg_left h2 hL0.le; linarith only [this]
    exact mul_le_mul_of_nonneg_left h3 hlam.le
  have hlη2 : lam / η ≤ 1 / 2 := by
    have h1 : 2 * (lam * L) / cZ ≤ 1 / 2 := by
      rw [div_le_iff₀ hcZ]; linarith only [hlamL, hXc, hc₁Z]
    linarith only [h1, hlη1]

  set u : Fin N → ℂ := fun i => (η : ℂ) / w i with hu_def
  have hu : ∀ i, ‖u i‖ ^ 2 ≤ (u i).re := fun i => Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_disc η hη (w i) (hw i)
  have hi : ∃ i, 1 / 2 ≤ ‖u i‖ := by
    obtain ⟨i, hi⟩ := hi0
    refine ⟨i, ?_⟩
    simp only [hu_def, hi, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη,
      abs_of_pos (by linarith : (0 : ℝ) < η + η)]
    rw [le_div_iff₀ (by linarith)]; linarith
  set S : ℝ := ∑ i, (u i).re with hS_def
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => le_trans (by positivity) (hu i))
  have hS_eq : S = η * (∑ i, 1 / w i).re := by
    have := Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_sum_re η w 1
    simp only [pow_one] at this
    rw [hS_def, ← this, Complex.re_sum]
  have hSle : S ≤ 2 * (lam / η) + 25 * CF * (η * L) := by
    rw [hS_eq]
    have h2 := mul_le_mul_of_nonneg_left hS hη.le
    have h3 : η * (2 * lam / η ^ 2 + CF * L * 25) = 2 * (lam / η) + 25 * CF * (η * L) := by
      field_simp
    linarith only [h2, h3]
  have h25c : 25 * CF * c₂ ≤ kap a D := by
    rw [le_div_iff₀ (by positivity)] at hc₂κ; linarith only [hc₂κ]
  have hCFηL : 25 * CF * (η * L) ≤ kap a D * K := by
    have h1 : 25 * CF * (η * L) ≤ 25 * CF * (c₂ * K) := mul_le_mul_of_nonneg_left hηL.le (by positivity)
    have h2 := mul_le_mul_of_nonneg_right h25c hKpos.le
    linarith only [h1, h2]
  have hSK : S ≤ 1 + kap a D * K := by linarith only [hSle, hCFηL, hlη2]

  set m := ⌈th a * K⌉₊ with hm_def
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
    rw [hm_def]; exact (Nat.ceil_pos.mpr (by positivity)).ne')
  have hmle : (m : ℝ) < th a * K + 1 := Nat.ceil_lt_add_one (by positivity)
  have hmge : th a * K ≤ m := Nat.le_ceil _
  obtain ⟨j, n, hmj, hjan, hn1, hnS, hLB⟩ :=
    exists_power_sum_lower_bound CT a hCT hT (eps a) hε0 (by linarith) N u hu hi m hm1
  have hjr1 : (m : ℝ) + 1 ≤ j := by exact_mod_cast hmj
  have hjr : th a * K < j := by linarith only [hjr1, hmge]
  have hj1 : 1 ≤ j := by omega
  have hj2 : 2 ≤ j := by omega
  have hnε : (n : ℝ) * eps a ^ 2 ≤ 1 + kap a D * K := le_trans hnS hSK
  have hjan' : (j : ℝ) ≤ m + a * n := by exact_mod_cast hjan
  have hjup : (j : ℝ) ≤ 2 * th a * K + j0 a := by
    have h1 : (a : ℝ) * n ≤ a / eps a ^ 2 + a * kap a D / eps a ^ 2 * K := by
      have : (n : ℝ) ≤ (1 + kap a D * K) / eps a ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hnε
      calc (a : ℝ) * n ≤ a * ((1 + kap a D * K) / eps a ^ 2) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have h2 : a * kap a D / eps a ^ 2 * K ≤ th a * K :=
      mul_le_mul_of_nonneg_right (akap_le' a ha D hD) hKpos.le
    unfold j0; linarith only [h1, h2, hjan', hmle]
  have hanD : (a : ℝ) * n * D ≤ a * D / eps a ^ 2 + j := by
    have h1 : (a : ℝ) * n * D = (a * D / eps a ^ 2) * (n * eps a ^ 2) := by field_simp
    have h2 := akapD_le a ha D hD
    have h3 : (a * D / eps a ^ 2) * (n * eps a ^ 2) ≤ (a * D / eps a ^ 2) * (1 + kap a D * K) :=
      mul_le_mul_of_nonneg_left hnε (by positivity)
    have h4 : (a * D / eps a ^ 2) * (1 + kap a D * K) = a * D / eps a ^ 2 + (a * D * kap a D / eps a ^ 2) * K := by ring
    have h5 := mul_le_mul_of_nonneg_right h2 hKpos.le
    linarith only [h1, h3, h4, h5, hjr]
  have hLB2 : 1 / (E0 a D * (rr a / 8) ^ j) ≤ ‖∑ i, u i ^ j‖ + eps a ^ (j - 2) * S :=
    le_trans (lb_part a D m n j _ (by omega) hanD (turan_lb CT hCT a n m hn1)) hLB

  have hU : ‖∑ i, u i ^ j‖ ≤ (8 * CP / cZ + 4 / cZ + 32 * CP / cS) * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    have h1 : ‖∑ i, u i ^ j‖ = η ^ j * ‖∑ i, 1 / (w i) ^ j‖ := norm_u_sum η w j hη.le
    have h2 := mul_le_mul_of_nonneg_left (hpow j hj1) (pow_pos hη j).le
    have hc₂P' : 2 * Real.exp 1 * CP * c₂ * rr a ≤ th a := by
      rw [le_div_iff₀ (by positivity)] at hc₂P; linarith only [hc₂P]
    have h3 := ub_terms a CP CF cZ cS c₂ (kap a D) L ℓ lam η Mr K j hj1 hCP hCF hcZ hcS hc₂ hL hℓ0 hℓ hlam hη
      hMr hKpos hlη1 hM hηc hηL h25c hκth hc₂P' hjr
    rw [h1]; exact le_trans h2 h3
  have hF : eps a ^ (j - 2) * S ≤ rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j :=
    far_part a S j hj2 (by linarith only [hSK, hjr, mul_le_mul_of_nonneg_right hκth hKpos.le])
  have hXj := x_part a c₁ K hc₁ j hjup
  rw [← hX] at hXj
  set cA := 8 * CP / cZ + 4 / cZ + 32 * CP / cS with hcA
  have hcA0 : 0 ≤ cA := by positivity
  have hJ0 : 0 ≤ ((j : ℝ) + 1) ^ 2 := by positivity
  have hU2 : cA * ((j : ℝ) + 1) ^ 2 * (lam * L ^ 3) ≤
      cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j) :=
    mul_le_mul_of_nonneg_left hXj (by positivity)
  have htot : 1 / (E0 a D * (rr a / 8) ^ j) ≤ GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
    have : GG a CP cZ cS c₁ * ((j : ℝ) + 1) ^ 2 / rr a ^ j =
        cA * ((j : ℝ) + 1) ^ 2 * (c₁ * Real.exp (j0 a * Real.log (rr a)) / rr a ^ j)
        + (1 + rr a) * ((j : ℝ) + 1) ^ 2 / rr a ^ j + rr a ^ 2 * ((j : ℝ) + 1) ^ 2 / rr a ^ j := by
      unfold GG; rw [hcA]; ring
    rw [this]; linarith only [hLB2, hU, hF, hU2]
  exact final_step a (E0 a D) (GG a CP cZ cS c₁) hE0 hG j (by linarith only [hthK, hjr]) htot

end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

set_option maxHeartbeats 1000000 in
theorem deuring_heilbronn_finish_turan : DHFinish2Of := by
  intro hTur hIneq hPrime
  obtain ⟨CT, a, hCT, ha, hT2⟩ := hTur
  obtain ⟨CF, hCF, hF⟩ := hIneq
  obtain ⟨CP, hCP, hP⟩ := hPrime
  obtain ⟨cS, hcS, hE⟩ := excBound (1 / 2) (by norm_num)
  obtain ⟨cZ, hcZ, hG⟩ := DHF.region_gap
  have hD0 : 0 ≤ Real.log (max CT 1) := Real.log_nonneg (le_max_right _ _)
  obtain ⟨c₁, hc₁pos, hc₁Z, hc₁20⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ cZ / 4 ∧ c ≤ 1 / 20 :=
    ⟨min (cZ / 4) (1 / 20), lt_min (by linarith) (by norm_num), min_le_left _ _, min_le_right _ _⟩
  have hrr : 16 < TuranPowerSumBounds.rr a := TuranPowerSumBounds.rr_gt a
  obtain ⟨c₂, hc₂pos, hc₂k, hc₂t, hc₂K⟩ : ∃ c : ℝ, 0 < c ∧
      c ≤ TuranPowerSumBounds.kap a (Real.log (max CT 1)) / (25 * CF) ∧
      c ≤ TuranPowerSumBounds.th a / (2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a) ∧
      c * (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) ≤ cZ := by
    have hk := div_pos (TuranPowerSumBounds.kap_pos a ha _ hD0) (by positivity : (0 : ℝ) < 25 * CF)
    have ht := div_pos (TuranPowerSumBounds.th_pos a) (by positivity : (0 : ℝ) < 2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a)
    have hq : (0 : ℝ) < 2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) := by positivity
    refine ⟨min (min (TuranPowerSumBounds.kap a (Real.log (max CT 1)) / (25 * CF))
      (TuranPowerSumBounds.th a / (2 * Real.exp 1 * CP * TuranPowerSumBounds.rr a)))
      (cZ / (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1))),
      lt_min (lt_min hk ht) (div_pos hcZ hq),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _), ?_⟩
    rw [← le_div_iff₀ hq]
    exact min_le_right _ _
  have hc0pos : 0 < TuranPowerSumBounds.c0 a := by
    have := TuranPowerSumBounds.twentyFive_mul_smallConstant a
    have : 0 < 1 / TuranPowerSumBounds.rr a := by positivity
    linarith
  have hc0 : TuranPowerSumBounds.c0 a ≤ 1 / 25 := by
    have := TuranPowerSumBounds.twentyFive_mul_smallConstant a
    have h1 : 1 / TuranPowerSumBounds.rr a ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  refine ⟨TuranPowerSumBounds.c0 a, c₁, c₂, 3, hc0pos, hc₁pos, hc₂pos, ?_⟩
  intro M _ χ₁ χ β₁ T ρ hM hT hsq hne1 hL hβ hβ1 hρ hre hIm hne
  have hL1 : 1 ≤ Real.log ((M : ℝ) * T) := DHF.logMT_ge_one M T hM hT
  have hLpos : 0 < Real.log ((M : ℝ) * T) := by linarith
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hgap := hG M χ₁ χ β₁ T c₁ ρ hM hT hne1 hL hc₁pos (by linarith) hβ hρ hIm hne
  have hη : 0 < 1 - ρ.re := by
    by_contra h
    push_neg at h
    nlinarith
  have hηZ : cZ / (2 * Real.log ((M : ℝ) * T)) ≤ 1 - ρ.re := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hηc0 : 1 - ρ.re ≤ TuranPowerSumBounds.c0 a := by linarith
  have hlam : 0 < 1 - β₁ := by linarith
  have hEx := hE M χ₁ β₁ hsq hne1 hL
  have hs : 0 < √(M : ℝ) := Real.sqrt_pos.mpr hMpos
  have hmm : √(M : ℝ) * √(M : ℝ) = M := Real.mul_self_sqrt hMpos.le
  have hsqrt : (M : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / √(M : ℝ) := by
    rw [Real.rpow_neg hMpos.le, ← Real.sqrt_eq_rpow, one_div]
  have hcs : cS ≤ (1 - β₁) * √(M : ℝ) := by
    rw [hsqrt] at hEx
    have h1 : cS * (1 / √(M : ℝ)) ≤ 1 - β₁ := by linarith
    rw [mul_one_div, div_le_iff₀ hs] at h1
    exact h1
  have hℓ0 : 0 ≤ Real.log (3 * (M : ℝ)) := Real.log_nonneg (by linarith)
  have hℓpos : 0 < Real.log (3 * (M : ℝ)) := Real.log_pos (by linarith)
  have hℓL : Real.log (3 * (M : ℝ)) ≤ 2 * Real.log ((M : ℝ) * T) := by
    have hT4 : (4 : ℝ) ≤ T ^ 2 := by nlinarith
    have h3 : 3 * (M : ℝ) ≤ ((M : ℝ) * T) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hT4 (sq_nonneg (M : ℝ))]
    calc Real.log (3 * (M : ℝ)) ≤ Real.log (((M : ℝ) * T) ^ 2) :=
          Real.log_le_log (by linarith) h3
      _ = 2 * Real.log ((M : ℝ) * T) := by
          rw [Real.log_pow]
          push_cast
          ring
  have hℓM : Real.log (3 * (M : ℝ)) ^ 2 / (M : ℝ) ≤ 32 * (1 - β₁) / cS := by
    rw [div_le_div_iff₀ hMpos hcS]
    have hls := TuranPowerSumBounds.log_sq_bound (M : ℝ) (by linarith)
    calc Real.log (3 * (M : ℝ)) ^ 2 * cS ≤ 32 * √(M : ℝ) * cS :=
          mul_le_mul_of_nonneg_right hls hcS.le
      _ ≤ 32 * √(M : ℝ) * ((1 - β₁) * √(M : ℝ)) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = 32 * (1 - β₁) * (M : ℝ) := by linear_combination (32 * (1 - β₁)) * hmm
  rw [div_le_iff₀ hLpos]
  by_contra hcon
  push_neg at hcon
  have hKK0 : TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁ <
      Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)) := by
    by_contra h
    push_neg at h
    have h1 : c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)) ≤
        c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [le_abs_self (TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁)])
        hc₂pos.le
    have h3 : c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1) ≤ cZ / 2 := by
      have e : c₂ * (2 * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) =
          2 * (c₂ * (|TuranPowerSumBounds.K0 a (Real.log (max CT 1)) CP cZ cS c₁| + 1)) := by ring
      linarith
    linarith
  have hpos : 0 < c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3) := by positivity
  have hexp : (1 - β₁) * Real.log ((M : ℝ) * T) ^ 3 =
      c₁ * Real.exp (-Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3))) := by
    rw [Real.exp_neg, Real.exp_log hpos]
    field_simp
  have hρre : (22 / 25 : ℝ) ≤ ρ.re := by linarith
  have hβ20 : (19 / 20 : ℝ) ≤ β₁ := by
    have : c₁ / Real.log ((M : ℝ) * T) ≤ 1 / 20 := by
      rw [div_le_iff₀ hLpos]
      nlinarith
    linarith
  obtain ⟨N, w, hwre, hwex, hwsum, hwj⟩ := hF M χ₁ χ β₁ T (1 - ρ.re) ρ hM hT hsq hne1 hL hβ20 hβ1
    hρ hρre hIm hne hη (by linarith)
  have hβP : 1 - 1 / Real.log (3 * (M : ℝ)) ≤ β₁ := by
    have : c₁ / Real.log ((M : ℝ) * T) ≤ 1 / Real.log (3 * (M : ℝ)) := by
      rw [div_le_div_iff₀ hLpos hℓpos]
      nlinarith
    linarith
  refine TuranPowerSumBounds.core2 CT a hCT ha hT2 CF CP cZ cS c₁ c₂ hCF hCP hcZ hcS hc₁pos hc₁Z hc₂pos hc₂k hc₂t
    (Real.log ((M : ℝ) * T)) (Real.log (3 * (M : ℝ))) (1 - β₁) (1 - ρ.re) (M : ℝ)
    (Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ 3)))
    hL1 hℓ0 hℓL hlam hηZ hηc0 hcon hMpos hℓM hexp hKK0 N w hwre hwex hwsum ?_
  intro j hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 := hwj (i + 1) hj
  have h2 := hP M χ₁ β₁ (1 + (1 - ρ.re)) i hM hsq hne1 hL hβP hβ1 (by linarith) (by linarith)
  simp only [Nat.add_sub_cancel] at h1 ⊢
  have e1 : (1 + (1 - ρ.re)) - 1 = 1 - ρ.re := by ring
  rw [e1] at h2
  have hA : CP * (1 - β₁) * Real.log (3 * (M : ℝ)) ^ 2 * ((i : ℝ) + 2) ^ 2 / (1 - ρ.re) ^ (i + 2) =
      CP * (1 - β₁) * Real.log (3 * (M : ℝ)) ^ 2 * (((i + 1 : ℕ) : ℝ) + 1) ^ 2 /
        (1 - ρ.re) ^ (i + 1 + 1) := by
    push_cast
    ring_nf
  have hC : CP * ((i : ℝ) + 2) * Real.log (3 * (M : ℝ)) ^ 2 / ((M : ℝ) * (1 - ρ.re) ^ (i + 1)) =
      CP * (((i + 1 : ℕ) : ℝ) + 1) * Real.log (3 * (M : ℝ)) ^ 2 / ((M : ℝ) * (1 - ρ.re) ^ (i + 1)) := by
    push_cast
    ring_nf
  rw [hA, hC] at h2
  exact h1.trans (add_le_add (add_le_add h2 le_rfl) le_rfl)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
