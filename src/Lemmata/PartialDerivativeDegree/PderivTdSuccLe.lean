module

public import Mathlib

@[expose] public section

universe u_1

namespace Bl.PartialDerivativeDegree

private lemma pderiv_td_succ_le {σ : Type u_1} (i : σ) (q : MvPolynomial σ Complex)
    (h : MvPolynomial.pderiv i q ≠ 0) :
    (MvPolynomial.pderiv i q).totalDegree + 1 ≤ q.totalDegree := by
  classical
  have hne : (MvPolynomial.pderiv i q).support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m, hm, hmax⟩ :=
    Finset.exists_mem_eq_sup _ hne (fun s : σ →₀ ℕ => s.sum fun _ e => e)
  have hc : AddMonoidAlgebra.coeff q (m + Finsupp.single i 1) ≠ 0 := by
    intro h0
    have h1 := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv, h0, zero_mul] at h1
    exact h1 rfl
  have hle := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl] at hle
  rw [MvPolynomial.totalDegree, hmax]
  exact hle

theorem goal1 :
    ∀ {σ : Type u_1} (i : σ) (q L : MvPolynomial σ ℂ),
      L.totalDegree ≤ 1 → ((MvPolynomial.pderiv i) q * L).totalDegree ≤ q.totalDegree := by
  intro σ i q L hL
  by_cases h : MvPolynomial.pderiv i q = 0
  · rw [h, zero_mul, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  · have hk := pderiv_td_succ_le i q h
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    omega

end Bl.PartialDerivativeDegree
