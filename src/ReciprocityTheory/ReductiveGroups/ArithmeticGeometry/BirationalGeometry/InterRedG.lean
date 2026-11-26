module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedG
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

open Classical in
theorem blockDeg_single (q : Σ k, ι k) (m : ℕ) (k' : K) :
    ∑ i, (Finsupp.single q m : (Σ k, ι k) →₀ ℕ) ⟨k', i⟩ = if q.1 = k' then m else 0 := by
  obtain ⟨k0, i0⟩ := q
  by_cases h : k0 = k'
  · subst h
    simp [Finsupp.single_apply, Sigma.mk.inj_iff]
  · simp [Finsupp.single_apply, Sigma.mk.inj_iff, h]

def secOf (i : ∀ k, ι k) (b : K → ℕ) : MRing ι := ∏ k, X ⟨k, i k⟩ ^ b k

theorem secOf_eq (i : ∀ k, ι k) (b : K → ℕ) :
    secOf i b = monomial (∑ k, Finsupp.single (⟨k, i k⟩ : Σ k, ι k) (b k)) 1 := by
  rw [secOf, MvPolynomial.monomial_sum_one]
  simp [MvPolynomial.X_pow_eq_monomial]

theorem isMultiHomog_secOf (i : ∀ k, ι k) (b : K → ℕ) : IsMultiHomog (secOf i b) b := by
  classical
  intro m hm k
  rw [secOf_eq, MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.mem_singleton] at hm
  subst hm
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_comm]
  simp only [blockDeg_single]
  simp

theorem secOf_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) {i : ∀ k, ι k}
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι) ∉ P) (b : K → ℕ) : secOf i b ∉ P := by
  rw [secOf]
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 h
  exact hi k (hP.mem_of_pow_mem _ hk)

end Alg

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivPushB
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_divSupp_of_eval {P : Ideal (MRing ι)} {s : MRing ι} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) (h0 : eval z (map (Int.castRingHom ℂ) s) = 0) :
    ∃ W' ∈ divSupp P s, IsHorizontal W' ∧ z ∈ mcPts W' := by
  classical
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hφ : ∀ f, φ f = eval z (map (Int.castRingHom ℂ) f) := fun f => rfl
  haveI hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    rw [sup_le_iff, Ideal.span_le, Set.singleton_subset_iff]
    refine ⟨fun f hf => ?_, ?_⟩
    · rw [RingHom.mem_ker, hφ]
      exact hz.2 f hf
    · show s ∈ RingHom.ker φ
      rw [RingHom.mem_ker, hφ]
      exact h0
  obtain ⟨W', hW', hW'le⟩ := Ideal.exists_minimalPrimes_le hle
  have hmem : ∀ f ∈ W', eval z (map (Int.castRingHom ℂ) f) = 0 := fun f hf => by
    have := hW'le hf
    rwa [RingHom.mem_ker, hφ] at this
  refine ⟨W', ⟨hW', ?_⟩, ?_, ⟨hz.1, hmem⟩⟩
  · intro k
    obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun hX => hi (by simpa using hmem _ hX)⟩
  · show Ideal.comap _ W' = ⊥
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap] at hn
    rw [Ideal.mem_bot]
    have := hmem _ hn
    simpa using this

end ReciprocityTheory.ChartRestriction.G.Geo
end
end
