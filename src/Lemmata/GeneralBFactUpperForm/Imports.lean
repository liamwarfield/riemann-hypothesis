module

public import Mathlib

@[expose] public section

universe u_3 u_4

namespace Bl.general_b_fact_upper_form

theorem goal1 :
    ∀ {LL : Type u_3} {M : Type u_4} [inst : Field LL] [inst_1 : AddCommGroup M]
      [inst_2 : _root_.Module LL M] (T : Module.End LL M) (W : Submodule LL M),
      (∀ x ∈ W, T x ∈ W) → ∀ (p : Polynomial LL), ∀ x ∈ W, ((Polynomial.aeval T) p) x ∈ W := by
  intro LL M _ _ _ T W hW p
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a x hx
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact W.smul_mem a hx
  · intro p q hp hq x hx
    rw [map_add (f := _), LinearMap.add_apply]
    exact W.add_mem (hp x hx) (hq x hx)
  · intro n a h x hx
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact h (T x) (hW x hx)

end Bl.general_b_fact_upper_form
