module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUnitApprox
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField

def UnitApprox.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (u : (F →+* ℂ) → ℝ),
    (∀ sg, u (ComplexEmbedding.conjugate sg) = u sg) → ∑ sg, u sg = 0 →
    ∃ C : ℝ, ∀ n : ℕ, ∃ ε : (𝓞 F)ˣ, ∀ sg : F →+* ℂ,
      |Real.log ‖sg ((ε : 𝓞 F) : F)‖ - n * u sg| ≤ C

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolySandwich
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def PolySandwich.Statement : Prop :=
  ∀ (D c : ℕ) (p q : Polynomial ℚ), q.natDegree ≤ D →
    (∀ᶠ n : ℕ in Filter.atTop, p.eval (n : ℚ) ≤ q.eval (n : ℚ) ∧ q.eval (n : ℚ) ≤ p.eval ((n : ℚ) + c)) →
    p.natDegree ≤ D ∧ p.coeff D = q.coeff D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPrimeComplexRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def PrimeComplexRadical.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    (P.map (MvPolynomial.map (Int.castRingHom ℂ))).IsRadical

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def ComplexMinimalPrimesContract.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℤ)), P.IsPrime →
    ∀ Q ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
      Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartSup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set

noncomputable section

def ChartSupBound.Statement : Prop :=
  ∀ (D : ℕ) (V K : Set (Fin D → ℂ)) (ψ ν : (Fin D → ℂ) → ℝ), IsOpen V → IsCompact K → K ⊆ V →
    ContDiffOn ℝ 2 ψ V → ContinuousOn ν V → (∀ z ∈ V, 0 < ν z) →
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ F : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ F V → ∀ w ∈ K,
      ENNReal.ofReal (‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w)) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ D) *
          ∫⁻ z in V, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-(n : ℝ) * ψ z) * ν z)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSerreGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def gradedSpan {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω) (n : ℕ) :
    AddSubgroup Ω :=
  AddSubgroup.closure {x | ∃ (l : Fin r) (μ : Fin q → ℕ), d l + ∑ j, μ j = n ∧ x = t l * ∏ j, w j ^ μ j}

def SerreGraded.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (q r : ℕ) (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω),
    (∃ j, w j ≠ 0) → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s : Ω,
      (∀ j, w j ≠ 0 → ∃ D : ℕ, s * w j ^ D ∈ gradedSpan w d t (n + D)) → s ∈ gradedSpan w d t n

theorem gradedSpan_gen_mem {Ω : Type*} [CommRing Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
    (l : Fin r) (μ : Fin q → ℕ) : t l * ∏ j, w j ^ μ j ∈ gradedSpan w d t (d l + ∑ j, μ j) :=
  AddSubgroup.subset_closure ⟨l, μ, rfl, rfl⟩

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonvanishDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def PolyNonvanishDense.Statement : Prop :=
  ∀ (e : ℕ) (D : MvPolynomial (Fin e) ℚ), D ≠ 0 → Dense {y : Fin e → ℂ | aeval y D ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootGridLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def RootGridLower.Statement : Prop :=
  ∀ (e m : ℕ) (Q : MvPolynomial (Fin e) ℤ), Q ≠ 0 → (∀ i, Q.degreeOf i < m) →
    ∃ ζ : Fin e → ℂ, (∀ i, ζ i ^ m = 1) ∧ 1 ≤ ‖eval ζ (map (Int.castRingHom ℂ) Q)‖

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def RootsBounded.Statement : Prop :=
  ∀ (e : ℕ) (G : Polynomial (MvPolynomial (Fin e) ℚ)), G.Monic → ∀ y₀ : Fin e → ℂ,
    ∃ R : ℝ, ∀ᶠ y in 𝓝 y₀, ∀ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 → ‖t‖ ≤ R

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsNear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def RootsNear.Statement : Prop :=
  ∀ (e : ℕ) (G : Polynomial (MvPolynomial (Fin e) ℚ)), G.Monic →
    ∀ (y₀ : Fin e → ℂ) (t₀ : ℂ), G.eval₂ (aeval y₀).toRingHom t₀ = 0 →
      ∀ ε > 0, ∀ᶠ y in 𝓝 y₀, ∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧ dist t t₀ < ε

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRatPrimeDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def RatPrimeDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)) (f : MvPolynomial σ ℚ), P.IsPrime → f ∉ P →
    {z : σ → ℂ | ∀ g ∈ P, aeval z g = 0} ⊆
      closure {z : σ → ℂ | (∀ g ∈ P, aeval z g = 0) ∧ aeval z f ≠ 0}

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedTopAlgebra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def MixedTopAlgebra.Statement : Prop :=
  ∀ (d : ℕ) (m : ℕ → ℝ), 2 ≤ d → (∀ i, 1 ≤ i → i ≤ d → 0 ≤ m i) → 0 < m d →
    (∀ q p : ℕ, 1 ≤ q → 1 ≤ p →
      0 < ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (q : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i →
      0 ≤ ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * (q : ℝ) ^ (d - 1 - i) * (p : ℝ) ^ i * m i) →
    0 ≤ m 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNoetherProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def NoetherProjection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)), P ≠ ⊤ →
    ∃ (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ),
      (∀ q : MvPolynomial (Fin e) ℚ, aeval ℓ q ∈ P → q = 0) ∧
      ∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
        p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRootsLiftToZeros
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

def RootsLiftToZeros.Statement : Prop :=
  ∀ (σ : Type) (P : Ideal (MvPolynomial σ ℚ)) (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ)
    (u : MvPolynomial σ ℚ) (G : Polynomial (MvPolynomial (Fin e) ℚ)),
    (∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
      p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P) →
    (∀ Q : Polynomial (MvPolynomial (Fin e) ℚ), Q.eval₂ (aeval ℓ).toRingHom u ∈ P → G ∣ Q) →
    ∀ (y : Fin e → ℂ) (t : ℂ), G.eval₂ (aeval y).toRingHom t = 0 →
      ∃ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) ∧ (fun j => aeval z (ℓ j)) = y ∧ aeval z u = t

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIndependentModBaseChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

def IndependentModBaseChange.Statement : Prop :=
  ∀ (σ : Type) (P : Ideal (MvPolynomial σ ℤ)) (r : ℕ) (g : Fin r → MvPolynomial σ ℤ),
    LinearIndependent ℤ (fun i => Ideal.Quotient.mk P (g i)) →
    LinearIndependent ℂ (fun i => Ideal.Quotient.mk (P.map (MvPolynomial.map (Int.castRingHom ℂ)))
      (MvPolynomial.map (Int.castRingHom ℂ) (g i)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsDescend
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def ConstantsDescend.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (R T : Subalgebra ℤ Ω), R.FG → Module.Finite ℤ T →
    (∀ w w' : ↥(R ⊔ T) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom) →
    ∃ m : ℕ, 1 ≤ m ∧ ∀ t ∈ T, (m : Ω) * t ∈ R

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDoubleComplexVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

def DoubleComplexVanish.Statement : Prop :=
  ∀ (C : ℕ → ℕ → Type) [∀ p n, AddCommGroup (C p n)] (P : ∀ p n, AddSubgroup (C p n))
    (δ : ∀ p n, C p n →+ C p (n + 1)) (κ : ∀ p n, C (p + 1) n →+ C p n) (R : ℕ),
    (∀ p n, ∀ x ∈ P p n, δ p n x ∈ P p (n + 1)) →
    (∀ p n, ∀ x ∈ P (p + 1) n, κ p n x ∈ P p n) →
    (∀ p n, ∀ x ∈ P p n, δ p (n + 1) (δ p n x) = 0) →
    (∀ p n, ∀ x ∈ P (p + 1) n, δ p n (κ p n x) = κ p (n + 1) (δ (p + 1) n x)) →
    (∀ p n, ∀ x ∈ P (p + 2) n, κ p n (κ (p + 1) n x) = 0) →
    (∀ n, ∀ x ∈ P 0 n, ∃ y ∈ P 1 n, κ 0 n y = x) →
    (∀ p n, ∀ x ∈ P (p + 1) n, κ p n x = 0 → ∃ y ∈ P (p + 2) n, κ (p + 1) n y = x) →
    (∀ p n, R < p → ∀ x ∈ P p n, x = 0) →
    (∀ p, 1 ≤ p → p ≤ R → ∀ n, ∀ x ∈ P p (n + 1), δ p (n + 1) x = 0 → ∃ y ∈ P p n, δ p n y = x) →
    ∀ n, ∀ x ∈ P 0 (n + 1), δ 0 (n + 1) x = 0 → ∃ y ∈ P 0 n, δ 0 n y = x

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFiniteSeparatingModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial Filter Topology

def FiniteSeparatingModel.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)) (f : MvPolynomial σ ℚ) (x : σ → ℂ),
    P.IsPrime → f ∉ P → (∀ g ∈ P, aeval x g = 0) →
    ∃ (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ) (u : MvPolynomial σ ℚ)
      (G : Polynomial (MvPolynomial (Fin e) ℚ)) (c D : MvPolynomial (Fin e) ℚ),
      G.Monic ∧ c ≠ 0 ∧ D ≠ 0 ∧
      (∀ i : σ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ), p.Monic ∧
        ∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
          p.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (z i) = 0) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        G.eval₂ (aeval fun j => aeval z (ℓ j)).toRingHom (aeval z u) = 0) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        aeval (fun j => aeval z (ℓ j)) c ≠ 0 → aeval z f ≠ 0) ∧
      (∀ (y : Fin e → ℂ) (t : ℂ), aeval y D ≠ 0 → G.eval₂ (aeval y).toRingHom t = 0 →
        ∃ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) ∧ (fun j => aeval z (ℓ j)) = y ∧ aeval z u = t) ∧
      (∀ z : σ → ℂ, (∀ g ∈ P, aeval z g = 0) →
        (fun j => aeval z (ℓ j)) = (fun j => aeval x (ℓ j)) → aeval z u = aeval x u → z = x)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
