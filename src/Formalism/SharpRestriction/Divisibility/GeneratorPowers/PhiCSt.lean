module

public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCSt
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

def PhiCSpanStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c) →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (β : SymB cj Y), (∀ a, 0 ≤ (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) →
    ∀ (k : ℕ) (x : Fin k → Y),
      (∀ y : Y, ∃ n : ℕ, 0 < n ∧ n • y ∈ Submodule.span (𝓞 E) (Set.range x)) →
      phiC cj β ≤ ∑ b, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • x b) (x b)

def PhiCMinimaStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (β : SymB cj Y),
      (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b i) (b j)).PosDef) →
      ∃ v : Fin (Module.finrank ℤ Y) → Y, LinearIndependent ℤ v ∧
        ∀ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (v i) (v i) / 2 ≤
          (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
              (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * phiC cj β

def PhiCTieStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E) (Y : Type) [AddCommGroup Y]
    [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (l : SymB cj Y →ₗ[ℝ] ℝ),
    (∀ β : SymB cj Y, (∀ a c, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l β = z) →
    ∃ (m : ℕ) (x x' : Fin m → Y), ∀ β : SymB cj Y,
      l β = ∑ i, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x i) (x' i)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.RoundingSum
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {Q : D.toPre.X → ℤ}

theorem Q_nonneg (hϖ : Irreducible ϖ) (hQ : IsQ D.toPre ϖ Q) (χ : D.toPre.X) : 0 ≤ Q χ := by
  by_cases hχ : χ = 0
  · rw [hχ, Q_zero hϖ (D := D) (Q := Q) (hQ := hQ)]
  · exact le_trans zero_le_one (Q_pos hϖ (D := D) (Q := Q) (hQ := hQ) hχ)

end Formalism.MainNotions.ModuliIntegralCharts.H1.RoundingSumAlt
end
end
