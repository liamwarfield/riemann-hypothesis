module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMul
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsInvertibleIndexMulSteps
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open GroundTheory.Heights₂.Heights

def LocalGen {Ω : Type} [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (m : Ideal B) (f : Ω) : Prop :=
  (∃ b : B, b ∉ m ∧ (b : Ω) * f ∈ X) ∧ ∀ z ∈ X, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * f

def LocalGenFamily.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (η : Type) [Fintype η] (f : η → Ω),
    Module.Finite ℤ B → (∀ b ∈ B, ∀ z ∈ X, b * z ∈ X) → (∀ i, f i ≠ 0) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * f i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B X m (f i)) →
      X ≠ ⊥ ∧ ∃ (ι : Type) (_ : Fintype ι) (a : ι → Ω), (∀ j, a j ∈ X) ∧
        (∀ j, ∃ c ∈ B, c ≠ 0 ∧ c * a j ∈ B) ∧
        ∀ m : Ideal B, m.IsMaximal → ∃ j, ∀ z ∈ X, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * a j

def LocallyPrincipalCoprimeField.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (B : Subring Ω) (M : AddSubgroup Ω) (ι : Type) [Fintype ι]
    (a : ι → Ω),
    Module.Finite ℤ B →
    (∀ b ∈ B, ∀ z ∈ M, b * z ∈ M) →
    (∀ i, a i ∈ M) →
    (∀ i, ∃ c ∈ B, c ≠ 0 ∧ c * a i ∈ B) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : Ω) * z = c * a i) →
    M ≠ ⊥ → ∀ s : B, s ≠ 0 →
      ∃ (β δ : B) (I : Ideal B), β ≠ 0 ∧ δ ≠ 0 ∧ I ⊔ Ideal.span {s} = ⊤ ∧
        ∀ x : Ω, x ∈ M ↔ ∃ y ∈ I, (β : Ω) * x = δ * y

def InvertibleProductRep.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (M N P : AddSubgroup Ω) (η : Type) [Fintype η] (g h : η → Ω)
    (β δ β' δ' : B) (I J : Ideal B),
    β ≠ 0 → δ ≠ 0 → β' ≠ 0 → δ' ≠ 0 →
    (∀ x : Ω, x ∈ M ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) →
    (∀ x : Ω, x ∈ N ↔ ∃ y ∈ J, (β' : Ω) * x = δ' * y) →
    (∀ b ∈ B, ∀ z ∈ P, b * z ∈ P) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i,
      LocalGen B M m (g i) ∧ LocalGen B N m (h i) ∧ LocalGen B P m (g i * h i)) →
      ∀ x : Ω, x ∈ P ↔ ∃ y ∈ I * J, ((β * β' : B) : Ω) * x = (δ * δ' : B) * y

def InvertibleIndexCharP.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (B : Subring Ω) (X : AddSubgroup Ω) (η : Type) [Fintype η] (f : η → Ω),
    ringChar Ω ≠ 0 → Module.Finite ℤ B → (∀ b ∈ B, ∀ z ∈ X, b * z ∈ X) → (∀ i, f i ≠ 0) →
    (∀ m : Ideal B, m.IsMaximal → ∃ i, LocalGen B X m (f i)) →
      genIndex X B.toAddSubgroup = 1

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsFnDegRelDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

def FnDegRelDeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
    (ι : K → Type) [∀ k, Fintype (ι k)] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hκv : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v)
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (i' : ∀ k', ι' k'),
    ReciprocityTheory.ChartRestriction.G.AI.I1.IsChart P' i' →
      haveI := hP'.isPrime
      ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg v P' i' = relDeg ⟨κ, hκv.1⟩ P'

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Targets
end
