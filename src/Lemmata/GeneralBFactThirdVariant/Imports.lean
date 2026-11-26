module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_third_variant

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] {Ψ : Finset (E →+* ℂ)},
      (∀ (σ : E →+* ℂ), σ ∈ Ψ ↔ NumberField.ComplexEmbedding.conjugate σ ∉ Ψ) →
        ∀ (x : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E) → ℝ),
          (∀ τ ∈ Ψ,
              ∑ k : Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers E),
                  ↑(x k) * τ ↑((NumberField.RingOfIntegers.basis E) k) =
                0) →
            x = 0 := by
  intro E _ _ Ψ hΨ x hx
  have hall : ∀ σ : RingHom E Complex, (Finset.univ.sum fun k =>
      (Complex.ofReal (x k)) * σ (NumberField.RingOfIntegers.val
        (NumberField.RingOfIntegers.basis E k))) = 0 := by
    intro σ
    by_cases hσ : σ ∈ Ψ
    · exact hx σ hσ
    · have hc : NumberField.ComplexEmbedding.conjugate σ ∈ Ψ := by
        by_contra hc
        exact hσ ((hΨ σ).mpr hc)
      have h2 := congrArg (starRingEnd Complex) (hx _ hc)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h2
      simpa only [map_mul, Complex.conj_ofReal, NumberField.ComplexEmbedding.conjugate_coe_eq,
        Complex.conj_conj] using h2
  have hli := (NumberField.canonicalEmbedding.latticeBasis E).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  funext k
  have h3 := hli (fun k => Complex.ofReal (x k)) (by
    funext σ
    rw [Finset.sum_apply]
    simp only [NumberField.canonicalEmbedding.latticeBasis_apply, Pi.smul_apply,
      NumberField.canonicalEmbedding.apply_at, NumberField.integralBasis_apply, smul_eq_mul,
      Pi.zero_apply]
    exact hall σ) k
  exact_mod_cast h3

end Bl.general_b_fact_third_variant
