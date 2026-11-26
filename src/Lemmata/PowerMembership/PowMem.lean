module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.PowerMembership

private lemma powMem {R : Type u_1} {M : Type u_2} [CommRing R] [AddCommGroup M] [Module R M]
    (S : Submodule R M) (f : Module.End R M) (hf : ∀ v : M, v ∈ S → f v ∈ S) (n : ℕ) :
    ∀ {v : M}, v ∈ S → (f ^ n) v ∈ S := by
  induction n with
  | zero => intro v hv; simpa using hv
  | succ n ih => intro v hv; rw [pow_succ']; exact hf _ (ih hv)

theorem goal1 :
    ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M]
      [inst_2 : _root_.Module R M] (S : Submodule R M) (f : Module.End R M),
      (∀ v ∈ S, f v ∈ S) → ∀ (P : Polynomial R) {v : M}, v ∈ S → ((Polynomial.aeval f) P) v ∈ S := by
  intro R M _ _ _ S f hf P v hv
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), LinearMap.add_apply]; exact S.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact S.smul_mem a (powMem S f hf n hv)

end Bl.PowerMembership
