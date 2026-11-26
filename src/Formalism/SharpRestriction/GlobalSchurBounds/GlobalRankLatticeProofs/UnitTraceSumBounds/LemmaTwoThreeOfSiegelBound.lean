module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
public import Formalism.SharpRestriction.GlobalSchurBounds.FirstClaimLemmaTwoFourOfLemmaTwoThree
public import Formalism.SharpRestriction.DesignExistsOfChoices
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns

@[expose] public section

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
namespace Formalism.MainNotions.Ext

open Polynomial Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.UnusedSlot33.HK

variable {R : Ranks} (H : Host R)

theorem exists_gen_K : ∃ x : H.K, x ^ 2 = ((-(H.d : ℤ) : ℤ) : H.K) ∧ IntermediateField.adjoin ℚ {x} = ⊤ := by
  have hb2 : H.sqd ^ 2 = ((-(H.d : ℤ) : ℤ) : H.E) := by
    push_cast
    exact H.sqd_sq
  obtain ⟨x, hxdef⟩ : ∃ x : H.K, (x : H.E) = H.sqd :=
    ⟨⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩, rfl⟩
  refine ⟨x, ?_, gen_top H x hxdef⟩
  apply Subtype.ext
  push_cast
  rw [hxdef, hb2]
  push_cast
  rfl

theorem finrank_K : Module.finrank ℚ H.K = 2 := by
  obtain ⟨x, hx, hadj⟩ := exists_gen_K H
  have hd := H.hyp.2.1
  have hsf : Squarefree (-(H.d : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact hd.squarefree
  have h1 : (-(H.d : ℤ)) ≠ 1 := by omega
  have hirr : Irreducible (X ^ 2 - C ((-(H.d : ℤ) : ℤ) : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat _ hsf h1)
  have hmon : (X ^ 2 - C ((-(H.d : ℤ) : ℤ) : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C ((-(H.d : ℤ) : ℤ) : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C ((-(H.d : ℤ) : ℤ) : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
  rw [hmin, natDegree_X_pow_sub_C _, hadj, IntermediateField.finrank_top'] at this
  exact this

theorem no_real_K : IsEmpty (H.K →+* ℝ) := by
  refine ⟨fun σ => ?_⟩
  obtain ⟨x, hx, -⟩ := exists_gen_K H
  have h := congrArg σ hx
  rw [map_pow, map_intCast] at h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have h2 := sq_nonneg (σ x)
  rw [h] at h2
  push_cast at h2
  linarith

end Formalism.MainNotions.Ext
end

section -- merged from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FamilyLogGammaSmallHolds
namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

theorem lamC_mem' {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {x : ℂ} (h : x ∈ Qbar) :
    lamC lam x = lam ⟨x, h⟩ := by
  unfold lamC; rw [dite_eq_left h]

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric NumberField

instance instUltraCp (p : ℕ) [Fact p.Prime] : IsUltrametricDist ℂ_[p] :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicComplex.isNonarchimedean p)

section Nu

variable {E : Type} [Field E] [NumberField E] {K : Type} [NormedField K] [IsUltrametricDist K] (ψ : E →+* K)

end Nu

noncomputable def psiT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E →+* ℂ_[p] :=
  lam.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))

theorem lamC_embT (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = psiT D lam τ x := lamC_mem' lam (embT_mem D τ x)

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Classical

end Formalism.MainNotions.GL3Columns

namespace Formalism.MainNotions.GL3Theta

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Theta

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions

end Formalism.MainNotions.GL3Columns

namespace Formalism.MainNotions.ShortIntervalPrimes

open Formalism.BasicNotions Formalism.MainNotions

end Formalism.MainNotions.ShortIntervalPrimes
end
