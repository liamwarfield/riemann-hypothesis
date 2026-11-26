module

public import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum
namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem integer_mean_log_bound : IntegerMeanLog := by
  intro K _ _ x hx
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hne : ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≠ 0 := fun φ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero φ).mpr hx'
  rw [← Real.log_prod (fun φ _ => hne φ)]
  apply Real.log_nonneg
  rw [← norm_prod]
  have key : (∏ φ : K →+* ℂ, φ (x : K)) = algebraMap ℚ ℂ (Algebra.norm ℚ (x : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun φ => rfl)
  rw [key, ← Algebra.coe_norm_int x]
  have hN0 : Algebra.norm ℤ x ≠ 0 := by
    intro h0
    have h5 : Algebra.norm ℚ (x : K) ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx'
    apply h5
    rw [← Algebra.coe_norm_int x, h0, Int.cast_zero]
  rw [eq_ratCast, Rat.cast_intCast, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hN0

theorem weber_function_root : WeberRoot := by
  intro x j s hs hj hx
  have hs0 : (s : ℂ) ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  refine ⟨?_, ?_⟩
  · let R := integralClosure ℤ ℂ
    let jR : R := ⟨j, hj⟩
    let q : Polynomial R := (Polynomial.X - Polynomial.C (s : R)) ^ 3 - Polynomial.C jR * Polynomial.X
    have hq : q.Monic := by
      apply Polynomial.Monic.sub_of_left ((Polynomial.monic_X_sub_C _).pow 3)
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _) ?_
      norm_num
    have hxR : IsIntegral R x := by
      refine ⟨q, hq, ?_⟩
      simp only [q, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, Polynomial.eval₂_mul]
      simp only [map_intCast]
      have hjR : algebraMap R ℂ jR = j := rfl
      rw [hjR]
      linear_combination hx
    exact isIntegral_trans x hxR
  · intro h
    rw [h] at hx
    apply hs0
    have h3 : (s : ℂ) ^ 3 = 0 := by linear_combination -hx
    exact (pow_eq_zero_iff (by norm_num)).mp h3

end Formalism.HermitianLattices.IntegralLatticeDensity
end

section -- merged from Formalism.GL3MeanSquares.HookFormulaTorsion.BimultiplicativeDivisibleTorsion
namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset

theorem no_form_of_bidegree_one_one : PowerCongruenceIffEqual := by
  unfold PowerCongruenceIffEqual
  intro l d s s' hl hs hs' hdiv
  have h1 : l ^ s < l ^ d := Nat.pow_lt_pow_right (by omega) hs
  have h2 : l ^ s' < l ^ d := Nat.pow_lt_pow_right (by omega) hs'
  have h3 : 1 ≤ l ^ s := Nat.one_le_pow _ _ (by omega)
  have h4 : 1 ≤ l ^ s' := Nat.one_le_pow _ _ (by omega)
  have h5 : 1 ≤ l ^ d := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h5, Nat.cast_pow, Nat.cast_one] at hdiv
  have h1' : (l : ℤ) ^ s < (l : ℤ) ^ d := by exact_mod_cast h1
  have h2' : (l : ℤ) ^ s' < (l : ℤ) ^ d := by exact_mod_cast h2
  have h3' : (1 : ℤ) ≤ (l : ℤ) ^ s := by exact_mod_cast h3
  have h4' : (1 : ℤ) ≤ (l : ℤ) ^ s' := by exact_mod_cast h4
  have hz := Int.eq_zero_of_abs_lt_dvd hdiv (by rw [abs_lt]; constructor <;> linarith)
  have h6 : (l : ℤ) ^ s = (l : ℤ) ^ s' := by linarith
  have h7 : l ^ s = l ^ s' := by exact_mod_cast h6
  exact Nat.pow_right_injective hl h7

end Formalism.HermitianLattices.IntegralLatticeDensity
end
