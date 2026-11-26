module

public import Mathlib

@[expose] public section

universe u_4

namespace Bl.FirstBlockLemmaB

theorem goal1 :
    ∀ {R : Type u_4} [inst : CommRing R] {P Q : Ideal R} [P.IsPrime],
      P ≤ Q → ∀ {x : R}, x ∈ Q → x ∉ P → ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  intro R _ P Q _ hPQ x hxQ hxP
  have hne : Ideal.Quotient.mk P x ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  refine ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hPQ)
    (Ideal.Quotient.factor_surjective hPQ) (r := Ideal.Quotient.mk P x)
    (mem_nonZeroDivisors_of_ne_zero hne) ?_
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact hxQ

end Bl.FirstBlockLemmaB
