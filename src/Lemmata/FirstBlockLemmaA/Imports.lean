module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.FirstBlockLemmaA

theorem goal1 :
    ∀ {k : Type u_1} [inst : Field k] {σ : Type u_2} [Fintype σ] (H : MvPolynomial σ k) (d : ℕ),
      (∀ m ∈ H.support, Finsupp.degree m = d) →
        ∀ (c : k) (v : σ → k), (MvPolynomial.eval (c • v)) H = c ^ d * (MvPolynomial.eval v) H := by
  intro k _ σ _ H d h c v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [← h m hm, Finsupp.degree_eq_sum]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end Bl.FirstBlockLemmaA
