module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_right_version

theorem goal1 :
    ∀ {E Ω : Type} [inst : Field E] [inst_1 : Field Ω] [inst_2 : Algebra E Ω] (σ : Gal(Ω/E)) (y : Ω),
      IsIntegral E y → ∃ (n : ℕ), n ≠ 0 ∧ (σ ^ n) y = y := by
  intro E Ω _ _ _ σ y hy
  have hmem : ∀ k : ℕ, (σ ^ k) y ∈ (minpoly E y).rootSet Ω := by
    intro k
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hy, ?_⟩
    have h := Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) y (minpoly E y)
    rw [minpoly.aeval, map_zero] at h
    simpa using h
  obtain ⟨a, b, hab, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => (σ ^ k) y) hmem (Polynomial.rootSet_finite _ _)
  refine ⟨b - a, by omega, ?_⟩
  have hb : b = a + (b - a) := by omega
  rw [hb, pow_add, AlgEquiv.mul_apply] at he
  exact ((σ ^ a).injective he).symm

end Bl.general_b_fact_right_version
