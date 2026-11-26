module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denint

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primmem
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Denchar
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_denchar :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (Φ : ZMod N → R) (A : Subring R), 0 < N → (∀ a, Φ a ∈ A) → (den N k : R) * genB k Φ ∈ A := by
  intro R _ _ N k Φ A hN hΦ
  unfold genB
  rw [Finset.mul_sum]
  refine A.sum_mem fun a _ => ?_
  obtain ⟨z, hz⟩ := b_denint N k a hN
  have h : (den N k : R) * algebraMap ℚ R (bcoef N k a) = (z : R) := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, hz, map_intCast]
  rw [mul_left_comm, h]
  exact A.mul_mem (hΦ _) (intCast_mem A z)
end

open Finset UpperTheory.V.Bern

private theorem dirichletCharacter_unit_isIntegral {R : Type} [CommRing R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (u : (ZMod N)ˣ) : IsIntegral ℤ (χ u) := by
  have hpos : 0 < orderOf u := orderOf_pos u
  refine IsIntegral.of_pow hpos ?_
  have h1 : χ (u : ZMod N) ^ orderOf u = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  rw [h1]
  exact isIntegral_one

theorem UpperTheory.V.Bern.b_primmem :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N), (∀ A : Subalgebra ℚ R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → Bprim k χ ∈ A) ∧ (∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A) ∧ IsIntegral ℤ ((den N k : R) * Bprim k χ) ∧ IsIntegral ℤ ((den N k : R) * genB k χ) := by
  intro R _ _ N _ k χ
  have hN : N ≠ 0 := NeZero.ne N
  have hc : 0 < χ.conductor :=
    Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))
  have hdvd : den χ.conductor k ∣ den N k := den_dvd χ.conductor_dvd_level k
  have hB : Bprim k χ = genB k (⇑χ.primitiveCharacter) := rfl
  have hint : ∀ a : ZMod N, IsIntegral ℤ (χ a) := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha
      exact dirichletCharacter_unit_isIntegral χ u
    · rw [MulChar.map_nonunit χ ha]
      exact isIntegral_zero
  have part2 : ∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A := by
    intro A hA
    obtain ⟨m, hm⟩ := hdvd
    have hmem : (den χ.conductor k : R) * genB k (⇑χ.primitiveCharacter) ∈ A := by
      refine b_denchar k _ A hc ?_
      intro x
      rcases b_primval χ x with h | ⟨u, h⟩
      · rw [h]; exact A.zero_mem
      · rw [h]; exact hA u
    rw [hB, hm, Nat.cast_mul, mul_comm ((den χ.conductor k : ℕ) : R) (m : R), mul_assoc]
    exact A.mul_mem (natCast_mem A m) hmem
  refine ⟨?_, part2, ?_, ?_⟩
  · intro A hA
    rw [hB]
    refine genB_mem k _ A ?_
    intro x
    rcases b_primval χ x with h | ⟨u, h⟩
    · rw [h]; exact A.zero_mem
    · rw [h]; exact hA u
  · have := part2 (integralClosure ℤ R).toSubring (fun u => dirichletCharacter_unit_isIntegral χ u)
    exact this
  · have := b_denchar k (⇑χ) (integralClosure ℤ R).toSubring (Nat.pos_of_ne_zero hN) (fun a => hint a)
    exact this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Primlevel
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primlevel :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (χ : DirichletCharacter R N), 0 < N → 1 ≤ k → genB k χ = Bprim k χ * ∏ p ∈ N.primeFactors, (1 - primVal χ p * (p : R) ^ (k - 1)) := by
  intro R _ _ N k χ hN hk
  have h := b_level χ.conductor_dvd_level k χ.primitiveCharacter hN hk
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  rw [h]
  rfl
end
