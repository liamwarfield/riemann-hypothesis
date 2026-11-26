module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_bis_other

theorem goal1 :
    ∀ {K : Type} [inst : Field K] [NumberField K] {r n : ℕ} (v : Fin n → Fin r → K) {x : Fin r → K},
      x ∈ Submodule.span K (Set.range v) →
        ∃ (d : ℤ), d ≠ 0 ∧ d • x ∈ Submodule.span (NumberField.RingOfIntegers K) (Set.range v) := by
  intro K _ _ r n v x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, hd'⟩ := hy
    obtain ⟨e, he, he'⟩ := hz
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]
      exact zsmul_mem hd' e
    · rw [mul_smul]
      exact zsmul_mem he' d
  | smul c y _ hy =>
    obtain ⟨d, hd, hd'⟩ := hy
    obtain ⟨e, he, hint⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) c)).exists_integral_multiple
    refine ⟨e * d, mul_ne_zero he hd, ?_⟩
    have key : ((⟨e • c, hint⟩ : NumberField.RingOfIntegers K)) • (d • y) = (e * d) • (c • y) := by
      rw [← algebraMap_smul K]
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]
      change ((e : K) * c) * ((d : K) * y i) = ((e * d : ℤ) : K) * (c * y i)
      push_cast
      ring
    rw [← key]
    exact Submodule.smul_mem _ _ hd'

end Bl.general_b_fact_bis_other
