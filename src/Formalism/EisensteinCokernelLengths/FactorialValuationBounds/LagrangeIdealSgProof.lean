module

public import Formalism.LagrangeIdealLifts.LiftLagrangeIdealInt
public import Formalism.WindowSums.PowerSeriesRelationList

@[expose] public section

section -- merged from Formalism.EisensteinCokernelLengths.StatementLIFTV
noncomputable section

namespace Formalism.ZetaNonvanishing.LIFTV

def LagrangeIdealSg : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (R : Type) [CommRing R] [IsDomain R] (sg : ℕ) (S₁ S₂ : Finset ℤ)
    (c : ℤ → R), Disjoint S₁ S₂ →
    (∀ a ∈ S₁, ∀ b ∈ S₁ ∪ S₂, a ≠ b →
      Associated (c a - c b) ((ℓ : R) ^ (sg + padicValInt ℓ (a - b)))) →
    Polynomial.C ((ℓ : R) ^ (S₁.sup fun a =>
        (∑ b ∈ S₂, (sg + padicValInt ℓ (a - b))) + ∑ a' ∈ S₁.erase a, (sg + padicValInt ℓ (a - a')))) ∈
      Ideal.span ({∏ a ∈ S₁, (Polynomial.X - Polynomial.C (c a)),
        ∏ b ∈ S₂, (Polynomial.X - Polynomial.C (c b))} : Set (Polynomial R))

end Formalism.ZetaNonvanishing.LIFTV
end
end

namespace Formalism.ZetaNonvanishing.LIFTV

theorem lagrangeIdealSg_proof : LagrangeIdealSg := by
  intro ℓ _ R _ _ sg S₁ S₂ c hd hc
  exact Formalism.LIFT.lift_LagrangeIdeal R (ℓ : R) ℤ S₁ S₂ c (fun a b => sg + padicValInt ℓ (a - b)) hd hc

end Formalism.ZetaNonvanishing.LIFTV
