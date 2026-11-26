module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
namespace ReciprocityTheory.ChartRestriction.G.AI

universe u

open Polynomial

def mix {V : Type*} {n : ℕ} (k : ℕ) (x y : V) : Fin n → V :=
  fun i => if (i : ℕ) < k then x else y

def IsSymmForm {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap (RingHom.id ℝ) (fun _ : Fin n => V) ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → V), I (v ∘ σ) = I v

def word {VW : Type*} (D k i : ℕ) (x₁ x₂ a : VW) : Fin D → VW :=
  fun j => if (j : ℕ) = 0 then x₂ else if (j : ℕ) < 1 + 2 * i then x₁ else
    if (j : ℕ) < 2 * k - 1 then x₂ else a

noncomputable def volPoly (D : ℕ) (J : ℕ → ℝ) : ℝ[X] :=
  ∑ j ∈ Finset.range (D + 1), C ((D.choose j : ℝ) * J j) * (-X) ^ j

noncomputable def tsgPoly (D : ℕ) (κ : ℕ → ℝ) (P : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1),
    if Odd n then C (((D : ℝ) + 1) * κ ((n + 1) / 2) / (((n + 1) / 2 : ℕ) : ℝ) * P.coeff n) * X ^ (n + 1)
    else 0

structure FibreSquare (D : ℕ) where
  V : Type u
  [acgV : AddCommGroup V]
  [modV : Module ℝ V]
  VW : Type u
  [acgW : AddCommGroup VW]
  [modW : Module ℝ VW]
  I : MultilinearMap (RingHom.id ℝ) (fun _ : Fin (D + 1) => V) ℝ
  IW : MultilinearMap (RingHom.id ℝ) (fun _ : Fin (D + 2) => VW) ℝ
  p₁ : V →ₗ[ℝ] VW
  p₂ : V →ₗ[ℝ] VW
  ξ : V
  A : V
  Φ : MultilinearMap (RingHom.id ℝ) (fun _ : Fin D => VW) ℝ
  symm : IsSymmForm I
  symmW : IsSymmForm IW
  comp_right_eq_zero_alt : ∀ v : Fin (D + 2) → V, IW (fun j => p₂ (v j)) = 0
  cons_comp_left : ∀ v : Fin (D + 1) → V, IW (Fin.cons (-(p₂ ξ)) (fun j => p₁ (v j))) = I v
  base : p₁ A = p₂ A
  diag : ∀ T : Fin D → VW,
    IW (Fin.cons (p₁ ξ) (Fin.cons (p₁ ξ) T)) - IW (Fin.cons (p₂ ξ) (Fin.cons (p₂ ξ) T)) = Φ T

attribute [instance] FibreSquare.acgV FibreSquare.modV FibreSquare.acgW FibreSquare.modW

end ReciprocityTheory.ChartRestriction.G.AI
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
namespace ReciprocityTheory.ChartRestriction.G.AI

open MeasureTheory

abbrev E3 := EuclideanSpace ℝ (Fin 3)

noncomputable abbrev S2 := Metric.sphere (0 : E3) 1

noncomputable def sphereMeasure : Measure S2 :=
  ((volume : Measure E3).toSphere Set.univ)⁻¹ • (volume : Measure E3).toSphere

noncomputable def gPoly (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.X 1 * ∑ j ∈ Finset.range (2 * k),
    (-1 : ℝ) ^ j • (MvPolynomial.X 0 ^ (2 * k - 1 - j) * MvPolynomial.X 1 ^ j)

noncomputable def dgPoly (k : ℕ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 (gPoly k))

noncomputable def kappa (k : ℕ) : ℝ :=
  -∫ n₁ : S2, ∫ n₂ : S2, (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (n₁ : E3) (n₂ : E3)) / 2) *
      MvPolynomial.eval ![(n₁ : E3) 2, (n₂ : E3) 2] (dgPoly k) ∂sphereMeasure ∂sphereMeasure

def SphereInvStatement : Prop :=
  IsProbabilityMeasure sphereMeasure ∧
  ∀ L : E3 ≃ₗᵢ[ℝ] E3,
    MeasurePreserving (fun n : S2 => (⟨L n, by simp⟩ : S2)) sphereMeasure sphereMeasure

def ArchimedesStatement : Prop :=
  ∀ (u v w : E3) (f : ℝ → ℝ), ‖u‖ = 1 → IntervalIntegrable f volume (-1) 1 →
    Integrable (fun n : S2 => f (inner ℝ (n : E3) u)) sphereMeasure ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) ∂sphereMeasure = (1 / 2) * ∫ t in (-1 : ℝ)..1, f t) ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v ∂sphereMeasure =
      (1 / 2) * ∫ t in (-1 : ℝ)..1, f t * t * inner ℝ u v) ∧
    (∫ n : S2, f (inner ℝ (n : E3) u) * inner ℝ (n : E3) v * inner ℝ (n : E3) w ∂sphereMeasure =
      (1 / 2) * ∫ t in (-1 : ℝ)..1, f t * (t ^ 2 * (inner ℝ u v * inner ℝ u w) +
        (1 - t ^ 2) / 2 * (inner ℝ v w - inner ℝ u v * inner ℝ u w)))

end ReciprocityTheory.ChartRestriction.G.AI
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
namespace ReciprocityTheory.ChartRestriction.G.AI

universe u v

open Module

noncomputable def ordMod {A : Type*} [CommRing A] (p : PrimeSpectrum A) (x : A) : ℕ∞ :=
  Ring.ord (A ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal x)

noncomputable def ordLoc {A : Type*} [CommRing A] (p : PrimeSpectrum A) (x : A) : ℕ∞ :=
  Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap A (Localization.AtPrime p.asIdeal) x)

def LocalLengthAdditivity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (M : Type v) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) ≠ ⊤ →
    length A (LinearMap.ker (LinearMap.lsmul A M x)) ≠ ⊤ ∧
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) =
      length A (LinearMap.ker (LinearMap.lsmul A M x)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            ordMod p x

def LocalLengthAdditivityTorsionFree : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.IsTorsionFree A M] (x : A),
    ringKrullDim A = 1 → x ≠ 0 →
    length A (M ⧸ LinearMap.range (LinearMap.lsmul A M x)) = (finrank A M : ℕ∞) * Ring.ord A x

def LocalLengthMultiplicativity : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (a b : A),
    ringKrullDim A = 2 → a ≠ 0 → b ≠ 0 →
    length A (A ⧸ Ideal.span {a, b}) ≠ ⊤ →
    (length A (A ⧸ Ideal.span {a, b}) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal),
          ordLoc p a * ordMod p b) ∧
    (length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) ∧
     length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤) ∧
    (∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b) =
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ b ∈ p.asIdeal), ordLoc p b * ordMod p a

end ReciprocityTheory.ChartRestriction.G.AI
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.IndexSt
namespace ReciprocityTheory.ChartRestriction.G.AI

def IndexStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : Subring K),
    Module.Free ℤ O → Module.Finite ℤ O → Module.finrank ℤ O = Module.finrank ℚ K →
    ∀ f : O, f ≠ 0 →
      (Nat.card (O ⧸ Ideal.span {f}) : ℝ) = |(Algebra.norm ℚ (f : K) : ℝ)| ∧
      Real.log (Nat.card (O ⧸ Ideal.span {f})) = ∑ σ : K →+* ℂ, Real.log ‖σ f‖

end ReciprocityTheory.ChartRestriction.G.AI
end
