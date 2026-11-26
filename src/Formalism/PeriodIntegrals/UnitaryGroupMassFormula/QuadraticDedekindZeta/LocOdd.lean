module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticInvariants.QuadPolyIrreducible

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.ClassNumImQInt
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ClassNumberIntegrality.HalfIntegral
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDifference.QuadraticDifferenceForm
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuadraticDifference.QuadDiffOf
noncomputable section

namespace PI.QD

open NumberField

def Arith : Prop :=
  ∀ (d : ℕ) (x y : ℚ), Squarefree d → d % 4 = 3 → (∃ u : ℤ, 2 * x = u) →
    (∃ N : ℤ, x ^ 2 + d * y ^ 2 = N) → ∃ a v : ℤ, x = a + v / 2 ∧ y = v / 2

def IntCoeffs : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K) (x y : ℚ), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : K) → IsIntegral ℤ ((x : K) + (y : K) * θ) →
    (∃ u : ℤ, 2 * x = u) ∧ (∃ N : ℤ, x ^ 2 + d * y ^ 2 = N)

def Form : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K), θ ^ 2 = -(d : K) →
    Algebra.adjoin ℚ {θ} = ⊤ → ∀ z : K, ∃ x y : ℚ, z = x + y * θ

end PI.QD

end
end

noncomputable section

namespace PI.QD

open NumberField Polynomial

theorem quadraticDifferenceArith : Arith := by
  unfold Arith
  intro d x y hsq hd4 ⟨u, hu⟩ ⟨N, hN⟩
  obtain ⟨M, hM⟩ : ∃ M : ℤ, (d : ℚ) * (2 * y) ^ 2 = M := ⟨4 * N - u ^ 2, by
    push_cast
    linear_combination 4 * hN - (2 * x + (u : ℚ)) * hu⟩
  obtain ⟨w, hw⟩ : ∃ w : ℚ, w = 2 * y := ⟨_, rfl⟩
  rw [← hw] at hM
  have h2 : w * w.den = w.num := Rat.mul_den_eq_num w
  have h3 : ((d * w.num ^ 2 : ℤ) : ℚ) = ((M * (w.den : ℤ) ^ 2 : ℤ) : ℚ) := by
    push_cast
    rw [← h2]
    linear_combination (w.den : ℚ) ^ 2 * hM
  have key : (d : ℤ) * w.num ^ 2 = M * (w.den : ℤ) ^ 2 := by exact_mod_cast h3
  have hcop : IsCoprime ((w.den : ℤ) ^ 2) (w.num ^ 2) :=
    (Int.isCoprime_iff_gcd_eq_one.mpr (show Int.gcd w.num (w.den : ℤ) = 1 from w.reduced)).symm.pow
  have hdvd : (w.den : ℤ) ^ 2 ∣ (d : ℤ) := by
    apply hcop.dvd_of_dvd_mul_right
    exact ⟨M, by rw [key]; ring⟩
  have hdvd' : w.den * w.den ∣ d := by
    rw [← pow_two]
    exact_mod_cast hdvd
  have hden : w.den = 1 := Nat.isUnit_iff.mp (hsq _ hdvd')
  rw [hden, Nat.cast_one, mul_one] at h2
  obtain ⟨v, hv⟩ : ∃ v : ℤ, v = w.num := ⟨_, rfl⟩
  rw [← hv] at h2 key
  rw [hden] at key
  have hE : u ^ 2 + (d : ℤ) * v ^ 2 = 4 * N := by
    have h4 : ((u ^ 2 + (d : ℤ) * v ^ 2 : ℤ) : ℚ) = ((4 * N : ℤ) : ℚ) := by
      push_cast
      rw [← h2, hw]
      linear_combination 4 * hN - (2 * x + (u : ℚ)) * hu
    exact_mod_cast h4
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (d : ℤ) = 4 * t + 3 := ⟨((d / 4 : ℕ) : ℤ), by omega⟩
  rw [ht] at hE
  have hpar : ∃ a : ℤ, u - v = 2 * a := by
    rcases Int.even_or_odd' u with ⟨k, hk | hk⟩ <;> rcases Int.even_or_odd' v with ⟨m, hm | hm⟩ <;>
      subst hk <;> subst hm
    · exact ⟨k - m, by ring⟩
    · exfalso
      ring_nf at hE
      omega
    · exfalso
      ring_nf at hE
      omega
    · exact ⟨k - m, by ring⟩
  obtain ⟨a, ha⟩ := hpar
  refine ⟨a, v, ?_, ?_⟩
  · have ha' : ((u - v : ℤ) : ℚ) = ((2 * a : ℤ) : ℚ) := by rw [ha]
    push_cast at ha'
    linear_combination hu / 2 + ha' / 2
  · rw [← h2, hw]
    ring

theorem quadratic_difference_form : Form := by
  intro K _ _ d θ hθ htop z
  have hz : z ∈ Algebra.adjoin ℚ {θ} := by rw [htop]; trivial
  induction hz using Algebra.adjoin_induction with
  | mem w hw =>
    rw [Set.mem_singleton_iff] at hw
    exact ⟨0, 1, by rw [hw]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add w1 w2 _ _ h1 h2 =>
    obtain ⟨x1, y1, e1⟩ := h1
    obtain ⟨x2, y2, e2⟩ := h2
    exact ⟨x1 + x2, y1 + y2, by rw [e1, e2]; push_cast; ring⟩
  | mul w1 w2 _ _ h1 h2 =>
    obtain ⟨x1, y1, e1⟩ := h1
    obtain ⟨x2, y2, e2⟩ := h2
    refine ⟨x1 * x2 - d * y1 * y2, x1 * y2 + x2 * y1, ?_⟩
    rw [e1, e2]; push_cast
    linear_combination (y1 * y2 : K) * hθ

theorem quadratic_intCoeffs : IntCoeffs := by
  unfold IntCoeffs
  intro K _ _ d θ x y hsq hd4 hθ hint
  have hd : (0 : ℚ) < d := by
    have : 0 < d := by omega
    exact_mod_cast this
  by_cases hy : y = 0
  · subst hy
    have h1 : IsIntegral ℤ (algebraMap ℚ K x) := by
      rw [eq_ratCast]
      simpa using hint
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_algebraMap_iff ).mp h1)
    rw [eq_intCast] at hn
    subst hn
    exact ⟨⟨2 * n, by push_cast; ring⟩, ⟨n ^ 2, by push_cast; ring⟩⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial ℚ, p = X ^ 2 - C (2 * x) * X + C (x ^ 2 + d * y ^ 2) := ⟨_, rfl⟩
  have hmonic : p.Monic := by
    rw [hp]
    monicity!
  have hdeg : p.natDegree = 2 := by
    rw [hp]
    compute_degree!
  have haeval : aeval ((x : K) + (y : K) * θ) p = 0 := by
    rw [hp]
    simp only [map_add (f := _), map_sub, map_mul, aeval_X, aeval_C, map_pow, eq_ratCast]
    push_cast
    linear_combination ((y : K)) ^ 2 * hθ
  have hirr : Irreducible p := by
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
    rw [mem_roots hmonic.ne_zero, IsRoot, hp] at hr
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
    have hy2 : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (r - x), mul_pos hd hy2]
  have hmin : p = minpoly ℚ ((x : K) + (y : K) * θ) := minpoly.eq_of_irreducible_of_monic hirr haeval hmonic
  have hg := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hc : ∀ i, p.coeff i = ((minpoly ℤ ((x : K) + (y : K) * θ)).coeff i : ℚ) := by
    intro i
    rw [hmin, hg, Polynomial.coeff_map, eq_intCast]
  have h1 : p.coeff 1 = -(2 * x) := by
    rw [hp]
    simp
    rw [← C_pow, ← C_pow, coeff_C, coeff_C]
    simp
  have h0 : p.coeff 0 = x ^ 2 + d * y ^ 2 := by
    rw [hp]
    simp
    rw [← C_pow, ← C_pow, coeff_C, coeff_C]
    simp
  refine ⟨⟨-(minpoly ℤ ((x : K) + (y : K) * θ)).coeff 1, ?_⟩, ⟨(minpoly ℤ ((x : K) + (y : K) * θ)).coeff 0, ?_⟩⟩
  · push_cast
    rw [← hc, h1]
    ring
  · rw [← hc, h0]

end PI.QD
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.ClassNumImQInt

open NumberField Polynomial

theorem adjoin_top {K : Type} [Field K] [NumberField K] (b : K)
    (h : IntermediateField.adjoin ℚ {b} = ⊤) : Algebra.adjoin ℚ {b} = ⊤ := by
  rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic b), h]
  exact IntermediateField.top_toSubalgebra

theorem half_integral {K : Type} [Field K] [NumberField K] (d : ℕ) (b : K) (hd : d % 4 = 3)
    (hb : b ^ 2 = -(d : K)) : IsIntegral ℤ ((1 + b) / 2) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 4 * k := ⟨(d + 1) / 4, by omega⟩
  have hk' : (d : K) + 1 = 4 * (k : K) := by exact_mod_cast hk
  refine ⟨X ^ 2 - X + C (k : ℤ), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_natCast, map_natCast]
  linear_combination (1 / 4 : K) * hb - (1 / 4 : K) * hk'

theorem intBasis : PI.ClassNumImQ.IntBasis := by
  intro d K _ _ b ⟨hp, hd, _, hb, htop⟩
  have hsq : Squarefree d := hp.prime.squarefree
  have htop' := adjoin_top b htop
  refine ⟨half_integral d b hd hb, ?_⟩
  intro z
  obtain ⟨x, y, hxy⟩ := PI.QD.quadratic_difference_form K d b hb htop' (z : K)
  have hint : IsIntegral ℤ ((x : K) + (y : K) * b) := by rw [← hxy]; exact z.isIntegral_coe
  obtain ⟨h2x, hN⟩ := PI.QD.quadratic_intCoeffs K d b x y hsq hd hb hint
  obtain ⟨a, v, hx, hy⟩ := PI.QD.quadraticDifferenceArith d x y hsq hd h2x hN
  refine ⟨a, v, ?_⟩
  rw [hxy, hx, hy]
  push_cast
  ring

end PI.UnitaryGroupMassFormula.ClassNumImQInt
end
end

theorem imag_quadratic_integral_basis : PI.ClassNumImQ.IntBasis :=
  PI.UnitaryGroupMassFormula.ClassNumImQInt.intBasis
end

open NumberField

namespace PI.ClassNumImQ.ZetaNonvanishing₂.Loc

variable {d : ℕ} {K : Type} [Field K] [NumberField K] {b : K}

noncomputable def om (hq : QuadData d K b) : 𝓞 K :=
  ⟨(1 + b) / 2, (imag_quadratic_integral_basis d K b hq).1⟩

theorem om_coe (hq : QuadData d K b) : ((om hq : 𝓞 K) : K) = (1 + b) / 2 := rfl

theorem basis (hq : QuadData d K b) (x : 𝓞 K) : ∃ m n : ℤ, x = m + n * om hq := by
  obtain ⟨m, n, h⟩ := (imag_quadratic_integral_basis d K b hq).2 x
  refine ⟨m, n, RingOfIntegers.ext ?_⟩
  rw [h]
  push_cast [om_coe]
  rfl

theorem coeff_unique (hq : QuadData d K b) {m n m' n' : ℤ}
    (h : (m : 𝓞 K) + n * om hq = m' + n' * om hq) : m = m' ∧ n = n' := by
  have hK : (m : K) + n * ((1 + b) / 2) = m' + n' * ((1 + b) / 2) := by
    have h' := congrArg (fun x : 𝓞 K => (x : K)) h
    push_cast [om_coe] at h'
    exact h'
  by_cases hn : n = n'
  · subst hn
    refine ⟨?_, rfl⟩
    exact_mod_cast add_right_cancel hK
  · exfalso
    have hne : ((n : K) - n') ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
    apply PI.UnitaryGroupMassFormula.ClassNumImQInv.b_ne_rat hq ((2 * (m' - m) + n' - n) / (n - n'))
    push_cast
    rw [div_eq_iff hne]
    linear_combination (-2 : K) * hK

end PI.ClassNumImQ.ZetaNonvanishing₂.Loc
