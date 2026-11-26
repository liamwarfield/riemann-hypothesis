module

public import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
public import Formalism.LogVandermondeBounds.GaussOperatorProductFormula
public import Formalism.GL3MeanSquares.FourierTransformKernelSurjective

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
open Finset Filter Topology ArithmeticFunction
open scoped ENNReal

noncomputable section

namespace Formalism.HermitianLattices.GL2a2

open Formalism.HermitianLattices.GL2PrimeSums

def LogDerivSeries : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)) atTop
      (𝓝 (-(deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)))

def PsiZeroConst : Prop :=
  Tendsto (fun U : ℝ => ∫ u in (1 : ℝ)..U, (psumR (fun n => Λ n) u - u) / u ^ 2) atTop
    (𝓝 (-1 - Real.eulerMascheroniConstant))

end Formalism.HermitianLattices.GL2a2
end
end

section -- merged from Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
namespace Formalism.HermitianLattices.RamifiedHeckeModels

open Finset Matrix ComplexConjugate Formalism.HermitianLattices.LocalLatticeBases

def RationalMatrixPrimeOrderBound : Prop :=
  ∀ (n p : ℕ), p.Prime → ∀ A : Matrix (Fin n) (Fin n) ℚ, A ^ p = 1 → A ≠ 1 → p ≤ n + 1

def LemmaC_twist : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      (∀ s ∈ S, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R (S ⧸ (S.map ((ϖ ^ b) • U)).comap S.subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R S : ℕ)

def LemmaC_twist_ram : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (M : Type) [AddCommGroup M] [Module R M] (P S B : Submodule R M) (U D : M →ₗ[R] M) (e b : ℕ),
      S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B → B.map U ≤ S → S.map D ≤ B →
      P.map U ≤ P → P.map D ≤ P → (∀ x : M, ϖ • x ∈ P → x ∈ P) →
      (∀ s ∈ S ⊓ P, U (D s) = ϖ ^ e • s) → Module.Free R S → Module.Finite R S →
      Module.length R ((S ⊓ P : Submodule R M) ⧸ ((S ⊓ P).map ((ϖ ^ b) • U)).comap (S ⊓ P).subtype) ≤
        Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) +
          (e * Module.finrank R S : ℕ)

end Formalism.HermitianLattices.RamifiedHeckeModels
end
