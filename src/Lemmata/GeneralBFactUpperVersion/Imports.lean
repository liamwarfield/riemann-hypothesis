module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_upper_version

theorem goal1 :
    ∀ {R : Type} [inst : CommRing R] [IsDomain R] (ζ : R) (M : ℕ) (P : Ideal R),
      ζ ≠ 1 → ζ ^ M = 1 → ζ - 1 ∈ P → ↑M ∈ P := by
  intro R _ _ ζ M P h1 hM hP
  have hs : (∑ i ∈ Finset.range M, ζ ^ i) = 0 := by
    have h := geom_sum_mul ζ M
    rw [hM, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr h1)
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hP ⊢
  have h2 : Ideal.Quotient.mk P ζ = 1 := by
    rw [map_sub, map_one, sub_eq_zero] at hP
    exact hP
  have h3 := congrArg (Ideal.Quotient.mk P) hs
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, map_pow, h2] using h3

end Bl.general_b_fact_upper_version
