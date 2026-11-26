module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.DHFinish2Of

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeD
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeC
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeA
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter
open scoped LSeries.notation ComplexOrder

def dhprC {M : ℕ} (χ₁ : DirichletCharacter ℂ M) (n : ℕ) : ℝ :=
  ((1 : DirichletCharacter ℂ M) (n : ZMod M)).re + (χ₁ (n : ZMod M)).re

lemma dhpr_hasSum {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (k : ℕ) {σ : ℝ}
    (hσ : 1 < σ) :
    HasSum (fun n : ℕ => (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n)
      ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h1 := dhPos_hasSum (1 : DirichletCharacter ℂ M) k hs
  have h2 := dhPos_hasSum χ₁ k hs
  have h3 := h1.add h2
  rw [show ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
      + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re =
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)).re +
      ((-1 : ℂ) ^ k * iteratedDeriv k (negLD χ₁) (σ : ℂ)).re by rw [mul_add, Complex.add_re]]
  convert h3 using 1
  funext n
  have hiter : ∀ (f : ℕ → ℂ) (j m : ℕ), (LSeries.logMul^[j] f) m = (Complex.log m) ^ j * f m := by
    intro f j
    induction j with
    | zero => intro m; simp
    | succ j ih =>
      intro m
      rw [Function.iterate_succ_apply', LSeries.logMul, ih]
      ring
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term]
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, hiter, hiter]
  simp only [Pi.mul_apply]
  have hn' : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [hn', ← Complex.ofReal_log (Nat.cast_nonneg _), ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_pow]
  simp only [Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.re_mul_ofReal]
  unfold dhprC
  ring

lemma dhpr_C_bounds {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (n : ℕ) : 0 ≤ dhprC χ₁ n ∧ dhprC χ₁ n ≤ 2 := by
  unfold dhprC
  by_cases hu : IsUnit (n : ZMod M)
  · have h2 : χ₁ (n : ZMod M) ^ 2 = 1 := by
      have e := congrArg (fun ψ : DirichletCharacter ℂ M => ψ hu.unit) h1
      simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at e
      simpa using e
    have h3 : χ₁ (n : ZMod M) = 1 ∨ χ₁ (n : ZMod M) = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
    rw [MulChar.one_apply hu]
    rcases h3 with h3 | h3 <;> rw [h3] <;> norm_num
  · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
    norm_num

lemma dhpr_r_nonneg {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (n : ℕ) : 0 ≤ (zetaMul χ₁ n).re := by
  exact (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg h1 n)).1

set_option backward.isDefEq.respectTransparency.types false in
lemma dhpr_zetaMul_eq_sum {M : ℕ} (χ : DirichletCharacter ℂ M) (n : ℕ) :
    zetaMul χ n = ∑ d ∈ n.divisors, χ (d : ZMod M) := by
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  first
    | exact if_neg hd0
    | simp only [LSeries.toArithmeticFunction, ArithmeticFunction.coe_mk, if_neg hd0]

lemma dhpr_zetaMul_prime_pow {M : ℕ} (χ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    (a : ℕ) : zetaMul χ (p ^ a) = ∑ i ∈ range (a + 1), χ (p : ZMod M) ^ i := by
  rw [dhpr_zetaMul_eq_sum, Nat.divisors_prime_pow hp, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  simp [Nat.cast_pow, map_pow]

lemma dhpr_coef_le {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (n : ℕ) : Λ n * dhprC χ₁ n ≤ 2 * Real.log n * (zetaMul χ₁ n).re := by
  have hr0 := dhpr_r_nonneg χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  by_cases hΛ : Λ n = 0
  · rw [hΛ, zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) hl) hr0
  obtain ⟨p, a, hp', ha, rfl⟩ := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  have hp : p.Prime := Nat.prime_iff.mpr hp'
  have ha0 : a ≠ 0 := Nat.pos_iff_ne_zero.mp ha
  have hΛp : Λ (p ^ a) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow ha0, ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log ((p ^ a : ℕ) : ℝ) = a * Real.log p := by
    rw [Nat.cast_pow, Real.log_pow]
  have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha

  have key : dhprC χ₁ (p ^ a) ≤ 2 * (zetaMul χ₁ (p ^ a)).re := by
    unfold dhprC
    rw [dhpr_zetaMul_prime_pow χ₁ hp a]
    by_cases hu : IsUnit (p : ZMod M)
    · have hua : IsUnit ((p ^ a : ℕ) : ZMod M) := by rw [Nat.cast_pow]; exact hu.pow a
      have h2 : χ₁ (p : ZMod M) ^ 2 = 1 := by
        have e := congrArg (fun ψ : DirichletCharacter ℂ M => ψ hu.unit) h1
        simp only [MulChar.pow_apply_coe, MulChar.one_apply_coe] at e
        simpa using e
      have h3 : χ₁ (p : ZMod M) = 1 ∨ χ₁ (p : ZMod M) = -1 := mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
      rw [MulChar.one_apply hua, Nat.cast_pow, map_pow]
      rcases h3 with h3 | h3
      · rw [h3]
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        simp
        linarith
      · rw [h3]
        have hsum : ∀ b : ℕ, 2 * ∑ i ∈ range (b + 1), ((-1 : ℂ)) ^ i = 1 + (-1) ^ b := by
          intro b
          induction b with
          | zero => norm_num
          | succ b ih =>
            rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
            ring
        have hre := congrArg Complex.re (hsum a)
        simp only [Complex.add_re, Complex.one_re] at hre
        have h2re : (2 * ∑ i ∈ range (a + 1), ((-1 : ℂ)) ^ i).re = 2 * (∑ i ∈ range (a + 1), ((-1 : ℂ)) ^ i).re := by
          simp [Complex.mul_re] <;> split_ifs <;> simp
        rw [h2re] at hre
        simp only [Complex.one_re]
        linarith
    · have hua : ¬ IsUnit ((p ^ a : ℕ) : ZMod M) := by
        rw [Nat.cast_pow]
        exact fun h => hu ((isUnit_pow_iff ha0).mp h)
      rw [MulChar.map_nonunit _ hua, MulChar.map_nonunit _ hua]
      have := (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg h1 (p ^ a))).1
      rw [dhpr_zetaMul_prime_pow χ₁ hp a] at this
      simp only [Complex.zero_re, add_zero]
      linarith
  rw [hΛp, hlog]
  calc Real.log p * dhprC χ₁ (p ^ a) ≤ Real.log p * (2 * (zetaMul χ₁ (p ^ a)).re) :=
        mul_le_mul_of_nonneg_left key hlp
    _ ≤ 2 * (a * Real.log p) * (zetaMul χ₁ (p ^ a)).re := by
        have hrr := dhpr_r_nonneg χ₁ h1 (p ^ a)
        nlinarith [mul_nonneg hlp hrr]

lemma dhpr_term_nonneg {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (k n : ℕ) (σ : ℝ) : 0 ≤ (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n := by
  have h1' := (dhpr_C_bounds χ₁ h1 n).1
  have hl := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have hn : 0 ≤ (n : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg n) σ
  exact mul_nonneg (mul_nonneg (pow_nonneg hl k) (div_nonneg hΛ hn)) h1'

lemma dhpr_term_le_r {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (k n : ℕ) (σ : ℝ) :
    (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤
      2 * (Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ := by
  have hc := dhpr_coef_le χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  have h0 : 0 ≤ Real.log n ^ k / (n : ℝ) ^ σ :=
    div_nonneg (pow_nonneg hl k) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  calc Real.log n ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n = (Real.log n ^ k / (n : ℝ) ^ σ) * (Λ n * dhprC χ₁ n) := by
        ring
    _ ≤ (Real.log n ^ k / (n : ℝ) ^ σ) * (2 * Real.log n * (zetaMul χ₁ n).re) := mul_le_mul_of_nonneg_left hc h0
    _ = 2 * Real.log n ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ := by ring

lemma dhpr_term_le_small {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1)
    (k n : ℕ) {σ : ℝ} (hσ : 1 ≤ σ) :
    (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤ 2 * (Real.log n) ^ k * (Λ n / n) := by
  have hC := dhpr_C_bounds χ₁ h1 n
  have hl := Real.log_natCast_nonneg n
  have hΛ : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  by_cases hn : n = 0
  · subst hn
    simp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ σ := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 hσ
    rwa [Real.rpow_one] at this
  have hd : Λ n / (n : ℝ) ^ σ ≤ Λ n / n := div_le_div_of_nonneg_left hΛ (by linarith) hpow
  have h0 : 0 ≤ Real.log n ^ k * (Λ n / n) := mul_nonneg (pow_nonneg hl k) (div_nonneg hΛ (Nat.cast_nonneg n))
  calc Real.log n ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n ≤ Real.log n ^ k * (Λ n / n) * 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (pow_nonneg hl k)) hC.2 hC.1 h0
    _ = 2 * Real.log n ^ k * (Λ n / n) := by ring

lemma lfunction_one_le_of_siegel_zero : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ),
    χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - 1 / Real.log (3 * M) ≤ β₁ → β₁ < 1 →
    ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ C * Real.log (3 * M) ^ 2 * (1 - β₁) := by
  obtain ⟨C, hC⟩ := lfunction_deriv_near_one
  refine ⟨max C 0, le_max_right _ _, fun M _ χ₁ β₁ hχ hz hβ hβ1 => ?_⟩
  have hd := DirichletCharacter.differentiable_LFunction hχ
  have hder : ∀ t ∈ Set.Icc β₁ 1,
      HasDerivWithinAt (fun t : ℝ => DirichletCharacter.LFunction χ₁ (t : ℂ))
        (deriv (DirichletCharacter.LFunction χ₁) (t : ℂ)) (Set.Icc β₁ 1) t :=
    fun t _ => ((hd (t : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbd : ∀ t ∈ Set.Ico β₁ 1,
      ‖deriv (DirichletCharacter.LFunction χ₁) (t : ℂ)‖ ≤ max C 0 * Real.log (3 * M) ^ 2 := by
    intro t ht
    exact (hC M χ₁ hχ t (le_trans hβ ht.1) ht.2.le).trans (by gcongr; exact le_max_left _ _)
  have := norm_image_sub_le_of_norm_deriv_le_segment' hder hbd 1 ⟨hβ1.le, le_rfl⟩
  simp only [hz, sub_zero, ofReal_one] at this
  exact this

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHPrimeB
open Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

lemma dhpr_pow_exp_le (m : ℕ) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    b ^ m * (t ^ m * Real.exp (-(b * t))) ≤ (m.factorial : ℝ) := by
  have hx : 0 ≤ b * t := mul_nonneg hb ht
  have hf : (0:ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h1 : (b * t) ^ m ≤ Real.exp (b * t) * (m.factorial : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (b * t) hx m
    rwa [div_le_iff₀ hf] at h
  calc b ^ m * (t ^ m * Real.exp (-(b * t))) = (b * t) ^ m * Real.exp (-(b * t)) := by
        rw [mul_pow]; ring
    _ ≤ (Real.exp (b * t) * (m.factorial : ℝ)) * Real.exp (-(b * t)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (m.factorial : ℝ) := by
        rw [mul_comm (Real.exp (b * t)), mul_assoc, ← Real.exp_add]; simp

lemma dhpr_one_sub_exp_neg {a : ℝ} (ha : 0 < a) : a / (1 + a) ≤ 1 - Real.exp (-a) := by
  have hpos : 0 < 1 + a := by linarith
  have h4 : Real.exp (-a) * (1 + a) ≤ 1 := by
    calc Real.exp (-a) * (1 + a) ≤ Real.exp (-a) * Real.exp a :=
          mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp a]) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  rw [div_le_iff₀ hpos]
  have e : (1 - Real.exp (-a)) * (1 + a) = (1 + a) - Real.exp (-a) * (1 + a) := by ring
  rw [e]; linarith

lemma dhpr_pow_ratio (m : ℕ) : ((m : ℝ) + 1) ^ m ≤ Real.exp 1 * (m : ℝ) ^ m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp only [pow_zero, mul_one]
    linarith [Real.add_one_le_exp (1:ℝ)]
  · have hm : (0:ℝ) < m := by exact_mod_cast h
    have hm' : (m:ℝ) ≠ 0 := hm.ne'
    have key : (m:ℝ) + 1 ≤ m * Real.exp (1 / m) := by
      have h1 := Real.add_one_le_exp (1 / (m:ℝ))
      have h2 : (m:ℝ) * (1 / m + 1) = m + 1 := by
        rw [mul_add, mul_one_div_cancel hm', mul_one, add_comm]
      calc (m:ℝ) + 1 = m * (1 / m + 1) := h2.symm
        _ ≤ m * Real.exp (1 / m) := mul_le_mul_of_nonneg_left h1 hm.le
    calc ((m:ℝ) + 1) ^ m ≤ ((m:ℝ) * Real.exp (1 / m)) ^ m := by gcongr
      _ = Real.exp 1 * (m:ℝ) ^ m := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_one_div_cancel hm', mul_comm]

lemma dhpr_wsup (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v : ℕ) :
    ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤ Real.exp 1 * m.factorial / η ^ m := by
  have hηm : 0 < η ^ m := pow_pos hη m
  have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
  have h1 := dhpr_pow_exp_le m hη.le ht
  have h2 : Real.exp (-(η * v)) ≤ Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : -(η * (v:ℝ)) = 1 + -(η * ((v:ℝ) + 1)) - (1 - η) := by ring
    rw [e]; linarith
  calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * v))
      ≤ ((v : ℝ) + 1) ^ m * (Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp 1 * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
    _ ≤ Real.exp 1 * ((m.factorial : ℝ) / η ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
        rw [le_div_iff₀ hηm]
        calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1))) * η ^ m
            = η ^ m * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
          _ ≤ (m.factorial : ℝ) := h1
    _ = Real.exp 1 * m.factorial / η ^ m := by ring

lemma dhpr_wsum (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) / η ^ (m + 1) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / ((m:ℝ) + 1) := ⟨_, rfl⟩
  have hm1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have hm1ne : (m:ℝ) + 1 ≠ 0 := hm1.ne'
  have hδη : ((m:ℝ) + 1) * δ = η := by rw [hδ]; field_simp
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos hη hm1
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  have hη'nn : 0 ≤ (m:ℝ) * δ := mul_nonneg hm0 hδpos.le
  have hsplit : (m:ℝ) * δ + δ = η := by rw [← hδη]; ring
  have hη'le : (m:ℝ) * δ ≤ 1 := by linarith
  have hpow : η ^ m ≤ Real.exp 1 * ((m:ℝ) * δ) ^ m := by
    rw [← hδη, mul_pow, mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (dhpr_pow_ratio m) (pow_nonneg hδpos.le m)
  have hterm : ∀ v : ℕ, η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) ≤
      Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
    intro v
    have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
    have h1 := dhpr_pow_exp_le m hη'nn ht
    have hexp : Real.exp (-(η * v)) ≤
        Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← hsplit]
      have e : -(((m:ℝ) * δ + δ) * (v:ℝ)) =
          1 + -((m:ℝ) * δ * ((v:ℝ) + 1)) + -(δ * v) - (1 - (m:ℝ) * δ) := by ring
      rw [e]; linarith
    calc η ^ m * (((v:ℝ) + 1) ^ m * Real.exp (-(η * v)))
        ≤ (Real.exp 1 * ((m:ℝ) * δ) ^ m) * (((v:ℝ) + 1) ^ m *
            (Real.exp 1 * Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))) * Real.exp (-(δ * v)))) := by
          refine mul_le_mul hpow ?_ (by positivity) (mul_nonneg (Real.exp_pos 1).le (pow_nonneg hη'nn m))
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Real.exp 1 * Real.exp 1 * (((m:ℝ) * δ) ^ m * (((v:ℝ) + 1) ^ m *
            Real.exp (-((m:ℝ) * δ * ((v:ℝ) + 1))))) * Real.exp (-(δ * v)) := by ring
      _ ≤ Real.exp 1 * Real.exp 1 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Real.exp 2 * (m.factorial : ℝ) * Real.exp (-(δ * v)) := by
          rw [← Real.exp_add]; norm_num
  have hsum : η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤
      Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun v _ => hterm v)
  have hG : (∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ ≤ 1 + δ := by
    have hrw : ∀ v : ℕ, Real.exp (-(δ * v)) = Real.exp (-δ) ^ v := by
      intro v; rw [← Real.exp_nat_mul]; congr 1; ring
    simp only [hrw]
    have hr0 : 0 < Real.exp (-δ) := Real.exp_pos _
    have hsub : ∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        rw [Finset.mem_Ico] at hx
        rw [Finset.mem_range]
        exact hx.2
      · intro i _ _
        exact pow_nonneg hr0.le i
    have hG0 : 0 ≤ ∑ v ∈ range V, Real.exp (-δ) ^ v :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have hgeo : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) ≤ 1 := by
      have h := geom_sum_mul (Real.exp (-δ)) V
      have hV : 0 ≤ Real.exp (-δ) ^ V := pow_nonneg hr0.le V
      have e : (∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ)) =
          -((∑ v ∈ range V, Real.exp (-δ) ^ v) * (Real.exp (-δ) - 1)) := by ring
      rw [e, h]; linarith
    have h2 := dhpr_one_sub_exp_neg hδpos
    have h2' : δ ≤ (1 - Real.exp (-δ)) * (1 + δ) := by
      rwa [div_le_iff₀ (by linarith)] at h2
    calc (∑ v ∈ Ico v0 V, Real.exp (-δ) ^ v) * δ
        ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * δ := mul_le_mul_of_nonneg_right hsub hδpos.le
      _ ≤ (∑ v ∈ range V, Real.exp (-δ) ^ v) * ((1 - Real.exp (-δ)) * (1 + δ)) :=
          mul_le_mul_of_nonneg_left h2' hG0
      _ = ((∑ v ∈ range V, Real.exp (-δ) ^ v) * (1 - Real.exp (-δ))) * (1 + δ) := by ring
      _ ≤ 1 * (1 + δ) := mul_le_mul_of_nonneg_right hgeo (by linarith)
      _ = 1 + δ := one_mul _
  rw [le_div_iff₀ (pow_pos hη (m + 1))]
  calc (∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η ^ (m + 1)
      = (η ^ m * ∑ v ∈ Ico v0 V, ((v:ℝ) + 1) ^ m * Real.exp (-(η * v))) * η := by ring
    _ ≤ (Real.exp 2 * (m.factorial : ℝ) * ∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * η :=
        mul_le_mul_of_nonneg_right hsum hη.le
    _ = Real.exp 2 * (m.factorial : ℝ) * ((∑ v ∈ Ico v0 V, Real.exp (-(δ * v))) * δ) *
          ((m:ℝ) + 1) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (1 + δ) * ((m:ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hm1.le
        exact mul_le_mul_of_nonneg_left hG (by positivity)
    _ = Real.exp 2 * (m.factorial : ℝ) * ((m:ℝ) + 1 + η) := by rw [← hδη]; ring
    _ ≤ Real.exp 2 * (m.factorial : ℝ) * (2 * ((m:ℝ) + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ = 2 * Real.exp 2 * ((m : ℝ) + 1) * (m.factorial : ℝ) := by ring

lemma dhpr_esum (v0 V : ℕ) :
    ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)) ≤
      20 * Real.exp (-((v0 : ℝ) / 4)) := by
  have hr0 : 0 < Real.exp (-(1/4:ℝ)) := Real.exp_pos _
  have hterm : ∀ v : ℕ, ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2)) ≤ 4 * Real.exp (-(1/4:ℝ)) ^ v := by
    intro v
    have h1 := Real.add_one_le_exp ((v:ℝ) / 4)
    have hv : (0:ℝ) ≤ v := Nat.cast_nonneg v
    calc ((v:ℝ) + 1) * Real.exp (-((v:ℝ) / 2))
        ≤ (4 * Real.exp ((v:ℝ) / 4)) * Real.exp (-((v:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ = 4 * (Real.exp ((v:ℝ) / 4) * Real.exp (-((v:ℝ) / 2))) := by ring
      _ = 4 * Real.exp (-(1/4:ℝ)) ^ v := by
          rw [← Real.exp_add, ← Real.exp_nat_mul]
          congr 2
          ring
  have h15 : (1:ℝ) / 5 ≤ 1 - Real.exp (-(1/4:ℝ)) := by
    have h := dhpr_one_sub_exp_neg (show (0:ℝ) < 1/4 by norm_num)
    have e : (1/4:ℝ) / (1 + 1/4) = 1 / 5 := by norm_num
    rw [e] at h
    exact h
  have hgeo : ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v ≤ 5 * Real.exp (-(1/4:ℝ)) ^ v0 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [pow_add]
    rw [← Finset.mul_sum, mul_comm (Real.exp (-(1/4:ℝ)) ^ v0)]
    have hG0 : 0 ≤ ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k :=
      Finset.sum_nonneg (fun i _ => pow_nonneg hr0.le i)
    have h := geom_sum_mul (Real.exp (-(1/4:ℝ))) (V - v0)
    have hV : 0 ≤ Real.exp (-(1/4:ℝ)) ^ (V - v0) := pow_nonneg hr0.le _
    have hmul := mul_le_mul_of_nonneg_left h15 hG0
    have hle : ∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k ≤ 5 := by
      have e : (∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (1 - Real.exp (-(1/4:ℝ))) =
          -((∑ k ∈ range (V - v0), Real.exp (-(1/4:ℝ)) ^ k) * (Real.exp (-(1/4:ℝ)) - 1)) := by ring
      rw [h] at e
      linarith
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg hr0.le _)
  calc ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))
      ≤ ∑ v ∈ Ico v0 V, 4 * Real.exp (-(1/4:ℝ)) ^ v := Finset.sum_le_sum (fun v _ => hterm v)
    _ = 4 * ∑ v ∈ Ico v0 V, Real.exp (-(1/4:ℝ)) ^ v := by rw [Finset.mul_sum]
    _ ≤ 4 * (5 * Real.exp (-(1/4:ℝ)) ^ v0) := mul_le_mul_of_nonneg_left hgeo (by norm_num)
    _ = 20 * Real.exp (-((v0 : ℝ) / 4)) := by
        rw [← Real.exp_nat_mul]
        have e : (v0:ℝ) * -(1/4) = -((v0:ℝ) / 4) := by ring
        rw [e]; ring

lemma dhpr_floor_mono {v w : ℕ} (h : v ≤ w) :
    ⌊Real.exp (v : ℝ)⌋₊ ≤ ⌊Real.exp (w : ℝ)⌋₊ :=
  Nat.floor_mono (Real.exp_le_exp.mpr (by exact_mod_cast h))

lemma dhpr_blocks (g : ℕ → ℝ) (v0 : ℕ) : ∀ V, v0 ≤ V →
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, g n =
      ∑ v ∈ Ico v0 V, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, g n := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ← ih]
    exact (Finset.sum_Ioc_consecutive g (dhpr_floor_mono hn)
      (dhpr_floor_mono (by omega : n ≤ n + 1))).symm

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter

def dhprF {M : ℕ} (χ₁ : DirichletCharacter ℂ M) (k : ℕ) (σ : ℝ) (n : ℕ) : ℝ :=
  (Real.log n) ^ k * (Λ n / (n : ℝ) ^ σ) * dhprC χ₁ n

lemma dhpr_rpow_le {σ : ℝ} (hσ : 1 ≤ σ) {n v : ℕ} (hn : 1 ≤ n) (hv : (v : ℝ) < Real.log n) :
    1 / (n : ℝ) ^ σ ≤ Real.exp (-((σ - 1) * v)) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : Real.exp ((σ - 1) * v) * n ≤ (n : ℝ) ^ σ := by
    have e1 : (n : ℝ) ^ σ = (n : ℝ) ^ (σ - 1) * n := by
      rw [← Real.rpow_add_one hn0.ne']
      ring_nf
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ hn0.le
    rw [Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.le) (sub_nonneg.mpr hσ)]
  have e2 : Real.exp (-((σ - 1) * v)) / n = 1 / (Real.exp ((σ - 1) * v) * n) := by
    rw [Real.exp_neg]
    field_simp
  rw [e2]
  exact one_div_le_one_div_of_le (by positivity) key

lemma dhpr_block {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ : ℝ} (hσ : 1 ≤ σ) (v : ℕ) (B : ℝ)
    (hH : ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤ B) :
    ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n ≤
      2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) * B := by
  have hterm : ∀ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
      dhprF χ₁ k σ n ≤ 2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
        ((∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hgt : Real.exp (v : ℝ) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hn.1
    have hle : (n : ℝ) ≤ Real.exp ((v + 1 : ℕ) : ℝ) := (Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2
    have hnpos : (0 : ℝ) < n := lt_trans (Real.exp_pos _) hgt
    have hn1 : 1 ≤ n := by
      by_contra hc
      push_neg at hc
      interval_cases n
      simp at hnpos
    have hlogv : (v : ℝ) < Real.log n := by
      rw [Real.lt_log_iff_exp_lt hnpos]
      exact hgt
    have hlog1 : Real.log n ≤ (v : ℝ) + 1 := by
      have h5 := Real.log_le_log hnpos hle
      rw [Real.log_exp] at h5
      push_cast at h5
      linarith
    have hlog0 : 0 ≤ Real.log n := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg v) hlogv)
    have hz := dhpr_r_nonneg χ₁ h1 n
    have hr := dhpr_rpow_le hσ hn1 hlogv
    have hp1 : (Real.log n) ^ (k + 1) ≤ ((v : ℝ) + 1) ^ (k + 1) := pow_le_pow_left₀ hlog0 hlog1 _
    have hq0 : 0 ≤ (Real.log n) ^ (k + 1) := pow_nonneg hlog0 _
    rw [← dhpr_zetaMul_eq_sum]
    calc dhprF χ₁ k σ n ≤ 2 * (Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re / (n : ℝ) ^ σ :=
          dhpr_term_le_r χ₁ h1 k n σ
      _ = 2 * ((Real.log n) ^ (k + 1) * (zetaMul χ₁ n).re) * (1 / (n : ℝ) ^ σ) := by ring
      _ ≤ 2 * (((v : ℝ) + 1) ^ (k + 1) * (zetaMul χ₁ n).re) * (Real.exp (-((σ - 1) * v)) / n) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp1 hz) (by norm_num)) hr
            (by positivity) (by positivity)
      _ = _ := by ring
  calc _ ≤ ∑ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
          ((∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n) := Finset.sum_le_sum hterm
    _ = 2 * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-((σ - 1) * v))) *
          ∑ n ∈ Finset.Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
            (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / n := by rw [Finset.mul_sum]
    _ ≤ _ := by gcongr

lemma dhpr_small {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ : ℝ} (hσ : 1 ≤ σ) (v0 : ℕ) (hv0 : 1 ≤ v0) {CT : ℝ} (hCT : 0 ≤ CT)
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y) :
    ∑ n ∈ Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n ≤ 2 * CT * (v0 : ℝ) ^ (k + 1) := by
  have hy : (2 : ℝ) ≤ Real.exp (v0 : ℝ) := by
    have hv1 : (1 : ℝ) ≤ v0 := by exact_mod_cast hv0
    calc (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      _ ≤ Real.exp v0 := Real.exp_le_exp.mpr hv1
  have hM := hMert _ hy
  rw [Real.log_exp] at hM
  have hIoc : Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊ = Finset.Icc 1 ⌊Real.exp (v0 : ℝ)⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n ≤ 2 * (v0 : ℝ) ^ k * (Λ n / n) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlog : Real.log n ≤ v0 := by
      have hnle : (n : ℝ) ≤ Real.exp v0 := (Nat.le_floor_iff (Real.exp_pos _).le).mp hn.2
      calc Real.log n ≤ Real.log (Real.exp v0) := Real.log_le_log (by linarith) hnle
        _ = v0 := Real.log_exp _
    have hΛ : 0 ≤ (Λ n : ℝ) / (n : ℝ) := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    calc dhprF χ₁ k σ n ≤ 2 * (Real.log n) ^ k * (Λ n / n) := dhpr_term_le_small χ₁ h1 k n hσ
      _ ≤ 2 * (v0 : ℝ) ^ k * (Λ n / n) := by gcongr
  calc ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, 2 * (v0 : ℝ) ^ k * (Λ n / n) := Finset.sum_le_sum hterm
    _ = 2 * (v0 : ℝ) ^ k * ∑ n ∈ Finset.Icc 1 ⌊Real.exp (v0 : ℝ)⌋₊, Λ n / n := by rw [← Finset.mul_sum, hIoc]
    _ ≤ 2 * (v0 : ℝ) ^ k * (CT * v0) := by gcongr
    _ = 2 * CT * (v0 : ℝ) ^ (k + 1) := by ring

lemma dhpr_hyper_simp (A CH x : ℝ) (v : ℕ) :
    A * Real.log (Real.exp ((v + 1 : ℕ) : ℝ) / Real.exp (v : ℝ))
      + CH * x * (Real.log (Real.exp (v : ℝ)) + 1) / Real.sqrt (Real.exp (v : ℝ)) =
      A + CH * x * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
  have h1 : Real.log (Real.exp ((v + 1 : ℕ) : ℝ) / Real.exp (v : ℝ)) = 1 := by
    rw [← Real.exp_sub, Real.log_exp]
    push_cast
    ring
  have h2 : Real.sqrt (Real.exp (v : ℝ)) = Real.exp ((v : ℝ) / 2) := by
    rw [show Real.exp (v : ℝ) = Real.exp ((v : ℝ) / 2) * Real.exp ((v : ℝ) / 2) by
      rw [← Real.exp_add]; ring_nf, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [h1, Real.log_exp, h2, Real.exp_neg]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter

lemma dhpr_large {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ η : ℝ} (hσ : 1 ≤ σ) (hση : σ - 1 = η) (hη : 0 < η) (hη1 : η ≤ 1) (v0 V : ℕ) (hV : v0 ≤ V)
    {A CH : ℝ} (hA : 0 ≤ A) (hCH : 0 ≤ CH)
    (hHyp : ∀ v : ℕ, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
        (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
          A + CH * M * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)))) :
    ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp (V : ℝ)⌋₊, dhprF χ₁ k σ n ≤
      2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) *
          (20 * Real.exp (-((v0 : ℝ) / 4)))) := by
  have hw : ∀ v : ℕ, ((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v)) ≤
      Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) := by
    intro v
    have h := dhpr_wsup (k + 1) hη hη1 v
    rw [Nat.factorial_succ] at h
    push_cast at h
    exact h
  have hS : ∑ v ∈ Ico v0 V, ((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v)) ≤
      2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 2) := by
    have h := dhpr_wsum (k + 1) hη hη1 v0 V
    rw [Nat.factorial_succ] at h
    push_cast at h
    refine h.trans (le_of_eq ?_)
    ring
  have hE := dhpr_esum v0 V
  have hA2 : 0 ≤ 2 * A := mul_nonneg (by norm_num) hA
  have hC2 : 0 ≤ 2 * CH * (M : ℝ) := mul_nonneg (mul_nonneg (by norm_num) hCH) (Nat.cast_nonneg _)
  have hK : 0 ≤ Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1) :=
    div_nonneg (by positivity) (pow_nonneg hη.le _)
  rw [dhpr_blocks _ v0 V hV]
  calc _ ≤ ∑ v ∈ Ico v0 V, (2 * A * (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) +
        2 * CH * M * ((((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) *
          (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))))) := by
        apply Finset.sum_le_sum
        intro v _
        have h := dhpr_block χ₁ h1 k hσ v _ (hHyp v)
        rw [hση] at h
        refine h.trans (le_of_eq ?_)
        ring
    _ = 2 * A * ∑ v ∈ Ico v0 V, (((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) +
        2 * CH * M * ∑ v ∈ Ico v0 V, ((((v : ℝ) + 1) ^ (k + 1) * Real.exp (-(η * v))) *
          (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2)))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hS hA2
        · apply mul_le_mul_of_nonneg_left _ hC2
          calc _ ≤ ∑ v ∈ Ico v0 V, (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1)) *
                (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
                apply Finset.sum_le_sum
                intro v _
                exact mul_le_mul_of_nonneg_right (hw v) (by positivity)
            _ = (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / η ^ (k + 1)) *
                ∑ v ∈ Ico v0 V, (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
                rw [← Finset.mul_sum]
            _ ≤ _ := mul_le_mul_of_nonneg_left hE hK

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
open LSeries ArithmeticFunction DirichletCharacter

lemma dhpr_partial {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (h1 : χ₁ ^ 2 = 1) (k : ℕ)
    {σ CT CH A : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hCT : 0 ≤ CT) (hCH : 0 ≤ CH) (hA0 : 0 ≤ A)
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y)
    (hHyp : ∀ y x : ℝ, 1 ≤ y → y ≤ x →
      ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        A * Real.log (x / y) + CH * M * (Real.log y + 1) / Real.sqrt y)
    (v0 : ℕ) (hv0pos : 0 < v0) (N : ℕ) :
    ∑ n ∈ range N, dhprF χ₁ k σ n ≤ 2 * CT * (v0 : ℝ) ^ (k + 1) +
      (2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) / (σ - 1) ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * k.factorial) / (σ - 1) ^ (k + 1) *
          (20 * Real.exp (-((v0 : ℝ) / 4))))) := by
  have hη : 0 < σ - 1 := by linarith
  have hvV : v0 ≤ v0 + N := Nat.le_add_right _ _
  have hNZ : N ≤ ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ := by
    apply Nat.le_floor
    have := Real.add_one_le_exp ((v0 + N : ℕ) : ℝ)
    push_cast at this ⊢
    have : (0 : ℝ) ≤ v0 := Nat.cast_nonneg _
    linarith
  have hYZ := dhpr_floor_mono hvV
  have hrange : range (⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ + 1) =
      insert 0 (Ioc 0 ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊) := by
    ext n; simp only [mem_range, mem_insert, mem_Ioc]; omega
  have hf0 : dhprF χ₁ k σ 0 = 0 := by simp [dhprF]
  have hHyp' : ∀ v : ℕ, ∑ n ∈ Ioc ⌊Real.exp (v : ℝ)⌋₊ ⌊Real.exp ((v + 1 : ℕ) : ℝ)⌋₊,
      (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        A + CH * M * (((v : ℝ) + 1) * Real.exp (-((v : ℝ) / 2))) := by
    intro v
    have h := hHyp (Real.exp (v : ℝ)) (Real.exp ((v + 1 : ℕ) : ℝ))
      (Real.one_le_exp (Nat.cast_nonneg v)) (Real.exp_le_exp.mpr (by push_cast; linarith))
    rwa [dhpr_hyper_simp] at h
  calc ∑ n ∈ range N, dhprF χ₁ k σ n
      ≤ ∑ n ∈ range (⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊ + 1), dhprF χ₁ k σ n :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
          (fun n _ _ => dhpr_term_nonneg χ₁ h1 k n σ)
    _ = ∑ n ∈ Ioc 0 ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n := by
        rw [hrange, sum_insert (by simp), hf0, zero_add]
    _ = ∑ n ∈ Ioc 0 ⌊Real.exp (v0 : ℝ)⌋₊, dhprF χ₁ k σ n +
          ∑ n ∈ Ioc ⌊Real.exp (v0 : ℝ)⌋₊ ⌊Real.exp ((v0 + N : ℕ) : ℝ)⌋₊, dhprF χ₁ k σ n :=
        (sum_Ioc_consecutive _ (Nat.zero_le _) hYZ).symm
    _ ≤ _ := add_le_add (dhpr_small χ₁ h1 k hσ.le v0 hv0pos hCT hMert)
        (dhpr_large χ₁ h1 k hσ.le rfl hη (by linarith) v0 (v0 + N) hvV hA0 hCH hHyp')

lemma dhpr_arith (k : ℕ) {CT CD CH C A ℓ lam η F E M v0 : ℝ}
    (hCT : 0 ≤ CT) (hCD : 0 ≤ CD) (hCH : 0 ≤ CH)
    (hC1 : 30 * CD ≤ C) (hC2 : 18 * CT + 9 ≤ C) (hC3 : 110 * CH ≤ C)
    (hM0 : 0 < M) (hℓ1 : 1 ≤ ℓ) (hv00 : 0 ≤ v0) (hv0ℓ : v0 ≤ 9 * ℓ) (hA0 : 0 ≤ A)
    (hA : A ≤ CD * ℓ ^ 2 * lam) (hlam : 0 < lam) (hη : 0 < η) (hF : 0 < F) (hE0 : 0 ≤ E)
    (hexp : E ≤ 1 / M ^ 2) :
    2 * CT * v0 ^ (k + 1) +
      (2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2))
      + 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E))) ≤
    (C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) + (C * ℓ) ^ (k + 1) / F
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1))) * F := by
  have hd9 := Real.exp_one_lt_d9
  have he1 : Real.exp 1 ≤ 2.72 := by norm_num at hd9 ⊢; linarith
  have he2 : Real.exp 2 ≤ 7.4 := by
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [h]; nlinarith [Real.exp_pos 1]
  have hC9 : 9 ≤ C := by linarith
  have hk : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
  have hi : 2 * CT * v0 ^ (k + 1) ≤ (C * ℓ) ^ (k + 1) := by
    calc 2 * CT * v0 ^ (k + 1) ≤ 2 * CT * (9 * ℓ) ^ (k + 1) := by gcongr
      _ = (18 * CT) * 9 ^ k * ℓ ^ (k + 1) := by ring
      _ ≤ C * C ^ k * ℓ ^ (k + 1) := by gcongr; linarith
      _ = (C * ℓ) ^ (k + 1) := by ring
  have hii : 2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2)) ≤
      C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) * F := by
    calc 2 * A * (2 * Real.exp 2 * ((k : ℝ) + 2) * (((k : ℝ) + 1) * F) / η ^ (k + 2))
        = (4 * A * Real.exp 2 * ((k : ℝ) + 2) * ((k : ℝ) + 1)) * (F / η ^ (k + 2)) := by ring
      _ ≤ (4 * (CD * ℓ ^ 2 * lam) * 7.4 * ((k : ℝ) + 2) * ((k : ℝ) + 2)) * (F / η ^ (k + 2)) := by
          gcongr
      _ = (29.6 * CD) * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 * (F / η ^ (k + 2)) := by ring
      _ ≤ C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 * (F / η ^ (k + 2)) := by gcongr; linarith
      _ = _ := by ring
  have hiii : 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E)) ≤
      C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1)) * F := by
    have hME : M * E ≤ 1 / M := by
      calc M * E ≤ M * (1 / M ^ 2) := by gcongr
        _ = 1 / M := by field_simp
    have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
    have hC' : 108.8 * CH ≤ C * ℓ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hℓ2 (by linarith : (0 : ℝ) ≤ C)]
    calc 2 * CH * M * (Real.exp 1 * (((k : ℝ) + 1) * F) / η ^ (k + 1) * (20 * E))
        = (40 * CH * Real.exp 1 * ((k : ℝ) + 1)) * (M * E) * (F / η ^ (k + 1)) := by ring
      _ ≤ (40 * CH * 2.72 * ((k : ℝ) + 2)) * (1 / M) * (F / η ^ (k + 1)) := by gcongr
      _ = (108.8 * CH) * ((k : ℝ) + 2) * (F / (M * η ^ (k + 1))) := by field_simp; ring
      _ ≤ (C * ℓ ^ 2) * ((k : ℝ) + 2) * (F / (M * η ^ (k + 1))) := by gcongr
      _ = _ := by ring
  have hexpand : (C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) + (C * ℓ) ^ (k + 1) / F
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1))) * F =
      C * lam * ℓ ^ 2 * ((k : ℝ) + 2) ^ 2 / η ^ (k + 2) * F + (C * ℓ) ^ (k + 1)
      + C * ((k : ℝ) + 2) * ℓ ^ 2 / (M * η ^ (k + 1)) * F := by
    rw [add_mul, add_mul, div_mul_cancel₀ _ hF.ne']
  rw [hexpand]
  linarith

lemma dhpr_main {M : ℕ} [NeZero M] (χ₁ : DirichletCharacter ℂ M) (k : ℕ) {β₁ σ CH CD CT C : ℝ}
    (hM : 3 ≤ M) (h1 : χ₁ ^ 2 = 1) (hβ1 : β₁ < 1) (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (hCH : 0 ≤ CH) (hCD : 0 ≤ CD) (hCT : 0 ≤ CT)
    (hC1 : 30 * CD ≤ C) (hC2 : 18 * CT + 9 ≤ C) (hC3 : 110 * CH ≤ C)
    (hA : ‖DirichletCharacter.LFunction χ₁ 1‖ ≤ CD * Real.log (3 * M) ^ 2 * (1 - β₁))
    (hMert : ∀ y : ℝ, 2 ≤ y → ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ CT * Real.log y)
    (hHyp : ∀ y x : ℝ, 1 ≤ y → y ≤ x →
      ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊x⌋₊, (∑ d ∈ n.divisors, χ₁ (d : ZMod M)).re / (n : ℝ) ≤
        ‖DirichletCharacter.LFunction χ₁ 1‖ * Real.log (x / y)
          + CH * M * (Real.log y + 1) / Real.sqrt y) :
    ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ))).re / (k.factorial : ℝ) ≤
      C * (1 - β₁) * Real.log (3 * M) ^ 2 * (k + 2) ^ 2 / (σ - 1) ^ (k + 2)
        + (C * Real.log (3 * M)) ^ (k + 1) / (k.factorial : ℝ)
        + C * (k + 2) * Real.log (3 * M) ^ 2 / (M * (σ - 1) ^ (k + 1)) := by
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hlogM : 0 < Real.log M := Real.log_pos (by linarith)
  have hlogM3 : Real.log M ≤ Real.log (3 * M) := Real.log_le_log hM0 (by linarith)
  have hd9 := Real.exp_one_lt_d9
  have hℓ1 : 1 ≤ Real.log (3 * M) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    norm_num at hd9
    linarith
  have hF : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hA0 : 0 ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ := norm_nonneg _
  have hS : HasSum (dhprF χ₁ k σ) _ := dhpr_hasSum χ₁ k hσ
  have hv0a : 8 * Real.log M ≤ (⌈8 * Real.log M⌉₊ : ℝ) := Nat.le_ceil _
  have hv0b : (⌈8 * Real.log M⌉₊ : ℝ) < 8 * Real.log M + 1 := Nat.ceil_lt_add_one (by positivity)
  have hv0pos : 0 < ⌈8 * Real.log M⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hexp : Real.exp (-((⌈8 * Real.log M⌉₊ : ℝ) / 4)) ≤ 1 / (M : ℝ) ^ 2 := by
    have h2 : Real.exp (-(2 * Real.log M)) = 1 / (M : ℝ) ^ 2 := by
      rw [Real.exp_neg, show 2 * Real.log M = Real.log ((M : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), one_div]
    rw [← h2]; exact Real.exp_le_exp.mpr (by linarith)
  have hle := le_of_tendsto' hS.tendsto_sum_nat
    (dhpr_partial χ₁ h1 k hσ hσ2 hCT hCH hA0 hMert hHyp _ hv0pos)
  rw [div_le_iff₀ hF]
  refine hle.trans ?_
  exact dhpr_arith k hCT hCD hCH hC1 hC2 hC3 hM0 hℓ1 (Nat.cast_nonneg _) (by linarith) hA0 hA
    (by linarith) (by linarith) hF (Real.exp_pos _).le hexp

theorem deuring_heilbronn_prime_sum : DHPrimeOf := by
  intro hH
  obtain ⟨CH, hCH, hHyp⟩ := hH
  obtain ⟨CD, hCD, hL1⟩ := lfunction_one_le_of_siegel_zero
  obtain ⟨CT, hCT, hMert⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨max (max (30 * CD) (18 * CT + 9)) (110 * CH),
    lt_of_lt_of_le (by linarith : (0 : ℝ) < 18 * CT + 9) (le_max_of_le_left (le_max_right _ _)), ?_⟩
  intro M _ χ₁ β₁ σ k hM h1 hne hz hβ hβ1 hσ hσ2
  exact dhpr_main χ₁ k hM h1 hβ1 hσ hσ2 hCH.le hCD hCT
    (le_max_of_le_left (le_max_left _ _)) (le_max_of_le_left (le_max_right _ _)) (le_max_right _ _)
    (hL1 M χ₁ β₁ hne hz hβ hβ1) hMert (fun y x hy hyx => hHyp M χ₁ y x hM h1 hne hy hyx)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
