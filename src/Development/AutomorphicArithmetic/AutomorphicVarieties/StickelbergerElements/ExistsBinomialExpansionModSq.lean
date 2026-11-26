module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Expand

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.ExistsBinomialExpansionModSq
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.exists_binomial_expansion_mod_sq :
    ∀ (b j M : ℤ) (e : ℕ),
      (∃ z : ℤ, (b + M * j) ^ (e + 1) = b ^ (e + 1) + ((e : ℤ) + 1) * b ^ e * (M * j) + M ^ 2 * z) ∧
      ∃ w : ℤ, (b + M * j) ^ e = b ^ e + M * w := by
  intro b j M e
  have h2 : ∀ n : ℕ, ∃ w : ℤ, (b + M * j) ^ n = b ^ n + M * w := by
    intro n
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (b + M * j) b n
    refine ⟨j * c, ?_⟩
    have hd : (b + M * j) - b = M * j := by ring
    rw [hd] at hc
    linear_combination hc
  refine ⟨?_, h2 e⟩
  induction e with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨b * z + ((n : ℤ) + 1) * b ^ n * j ^ 2 + M * j * z, ?_⟩
    push_cast
    linear_combination (b + M * j) * hz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerBernoulliCoeffExpansionModDenominat
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator :
    ∀ (M e b : ℕ), 0 < M → ∃ z : ℤ,
      bcoef M (e + 1) b / ((e + 1 : ℕ) : ℚ) =
        (b : ℚ) ^ (e + 1) / (((e + 1 : ℕ) : ℚ) * M) - (b : ℚ) ^ e / 2 + 2 * (M : ℚ) / (dk (e + 1) : ℚ) * z := by
  intro M e b hM
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : ((e + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
  have h : ∀ j : ℕ, ∃ z : ℤ, j ≤ e + 1 → (primorial (e + 1 + 1) : ℚ) * bernoulli j = z := by
    intro j
    by_cases hj : j ≤ e + 1
    · obtain ⟨z, hz⟩ := b_primden (e + 1) j hj
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose z hz using h
  refine ⟨∑ j ∈ range e, ((e + 1).choose (j + 1 + 1) : ℤ) * z (j + 1 + 1) * (M : ℤ) ^ j *
    (b : ℤ) ^ (e + 1 - (j + 1 + 1)), ?_⟩
  have hs : ∑ j ∈ range e, (((e + 1).choose (j + 1 + 1) : ℕ) : ℚ) * bernoulli (j + 1 + 1) *
      (M : ℚ) ^ (((j + 1 + 1 : ℕ) : ℤ) - 1) * (b : ℚ) ^ (e + 1 - (j + 1 + 1)) =
      (M : ℚ) / (primorial (e + 1 + 1) : ℚ) *
        ((∑ j ∈ range e, ((e + 1).choose (j + 1 + 1) : ℤ) * z (j + 1 + 1) * (M : ℤ) ^ j *
          (b : ℤ) ^ (e + 1 - (j + 1 + 1)) : ℤ) : ℚ) := by
    rw [Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 + 1 ≤ e + 1 := by have := mem_range.mp hj; omega
    have hp : (((j + 1 + 1 : ℕ) : ℤ) - 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hp, zpow_natCast, Int.cast_mul, Int.cast_mul, Int.cast_mul, ← hz _ hj', Int.cast_pow, Int.cast_pow,
      Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]
    field_simp
    ring
  rw [b_expand M (e + 1) b hM, Finset.sum_range_succ', Finset.sum_range_succ', hs]
  have hdk : (dk (e + 1) : ℚ) = 2 * ((e + 1 : ℕ) : ℚ) * (primorial (e + 1 + 1) : ℚ) := by
    rw [dk]; push_cast; ring
  rw [hdk]
  generalize ((∑ j ∈ range e, ((e + 1).choose (j + 1 + 1) : ℤ) * z (j + 1 + 1) * (M : ℤ) ^ j *
          (b : ℤ) ^ (e + 1 - (j + 1 + 1)) : ℤ) : ℚ) = S
  simp only [zero_add, Nat.choose_one_right, Nat.choose_zero_right, bernoulli_one, bernoulli_zero,
    Nat.add_sub_cancel, Nat.sub_zero, Nat.cast_one, Nat.cast_zero, sub_self, zpow_zero, zero_sub, zpow_neg, zpow_one]
  field_simp
  ring
end
