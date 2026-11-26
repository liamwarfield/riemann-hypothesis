module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GradientAtPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace GradientAtPoint

variable {σ : Type*} (w : σ → ℂ)

def grad : MvPolynomial σ ℂ →ₗ[ℂ] (σ → ℂ) :=
  LinearMap.pi fun i => (aeval w).toLinearMap ∘ₗ (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap

theorem grad_apply (p : MvPolynomial σ ℂ) (i : σ) : grad w p i = eval w (pderiv i p) := by
  simp [grad]

theorem grad_mul (a b : MvPolynomial σ ℂ) :
    grad w (a * b) = eval w a • grad w b + eval w b • grad w a := by
  ext i
  simp only [grad_apply, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, Pi.add_apply, Pi.smul_apply]

theorem grad_X_sub_C [DecidableEq σ] (j : σ) : grad w (X j - C (w j)) = Pi.single j 1 := by
  ext i
  rw [grad_apply, map_sub, pderiv_C, sub_zero, pderiv_X]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem grad_mul_of_eval_eq_zero (r p : MvPolynomial σ ℂ) (hp : eval w p = 0) :
    grad w (r * p) = eval w r • grad w p := by
  rw [grad_mul, hp, zero_smul, add_zero]

def linPart [Fintype σ] (c : σ → ℂ) : MvPolynomial σ ℂ :=
  ∑ i, C (c i) * (X i - C (w i))

theorem sub_C_eval_mem_span (p : MvPolynomial σ ℂ) :
    p - C (eval w p) ∈ Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), show p + q - (C (eval w p) + C (eval w q)) = (p - C (eval w p)) + (q - C (eval w q)) by
      ring]
    exact Ideal.add_mem _ hp hq
  | mul_X p i hp =>
    rw [map_mul, eval_X, map_mul,
      show p * X i - C (eval w p) * C (w i) = (p - C (eval w p)) * X i + C (eval w p) * (X i - C (w i)) by ring]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp)
      (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem ker_eval_eq_span :
    RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) =
      Ideal.span (Set.range fun i => (X i - C (w i) : MvPolynomial σ ℂ)) := by
  apply le_antisymm
  · intro p hp
    have h := sub_C_eval_mem_span w p
    rwa [RingHom.mem_ker.1 hp, map_zero, sub_zero] at h
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]

theorem grad_eq_zero_of_mem_sq {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2) : grad w p = 0 := by
  rw [pow_two] at hp
  refine Submodule.mul_induction_on hp (fun a ha b hb => ?_) (fun x y hx hy => ?_)
  · rw [grad_mul, RingHom.mem_ker.1 ha, RingHom.mem_ker.1 hb, zero_smul, zero_smul, add_zero]
  · rw [map_add (f := _), hx, hy, add_zero]

theorem sub_linPart_mem_sq [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) :
    p - linPart w (grad w p) ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  classical
  rw [ker_eval_eq_span] at hp
  obtain ⟨a, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hp
  have hg : grad w (∑ i, a i * (X i - C (w i))) = fun i => eval w (a i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [grad_mul, grad_X_sub_C, map_sub, eval_X, eval_C, sub_self, zero_smul, add_zero]
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hg, linPart, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [← sub_mul, pow_two]
  refine Ideal.mul_mem_mul ?_ ?_
  · simp [RingHom.mem_ker]
  · simp [RingHom.mem_ker]

theorem mem_sq_of_grad_eq_zero [Fintype σ] {p : MvPolynomial σ ℂ}
    (hp : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) (hg : grad w p = 0) :
    p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) ^ 2 := by
  have h := sub_linPart_mem_sq w hp
  rwa [hg, linPart, Finset.sum_eq_zero (fun i _ => by simp), sub_zero] at h

end GradientAtPoint

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHausdorffNullComplementConnected
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory

def HausdorffNullComplementConnected.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (D C : Set E),
    IsOpen D → IsPreconnected D → μH[(Module.finrank ℝ E : ℝ) - 1] C = 0 → IsPreconnected (D \ C)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCriticalFlatNotInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def CriticalFlatNotInjective.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (a : Fin k → ℂ),
    2 ≤ k → IsOpen U → DifferentiableOn ℂ f U → a ∈ U →
    LinearMap.det (fderiv ℂ f a : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
    (∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 → fderiv ℂ f b = 0) →
    ¬ Set.InjOn f U

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperHolomorphicSurjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric

def ProperHolomorphicSurjective.Statement : Prop :=
  ∀ (k : ℕ) (Ω D : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen Ω → Ω.Nonempty → IsOpen D → IsPreconnected D → DifferentiableOn ℂ g Ω → Set.MapsTo g Ω D →
    (∀ L ⊆ D, IsCompact L → IsCompact (Ω ∩ g ⁻¹' L)) →
    g '' Ω = D

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegularSequenceLengthLeDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence

universe u

def RegularSequenceLengthLeDim.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (rs : List R),
    (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → (rs.length : WithBot ℕ∞) ≤ ringKrullDim R

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGridProductLowerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def GridProductLowerBound.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (N : ℕ) (Z : Set (σ → ℂ)) (z₀ : σ → ℂ),
    Bornology.IsBounded Z → z₀ ∉ closure Z →
    ∃ μ : ℝ, 0 < μ ∧ ∃ U ∈ 𝓝 z₀, ∀ z ∈ U, ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) ⊆ Z → s.card ≤ N →
      ∃ u : σ → Fin (N + 1), μ ≤ ‖∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i)‖

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChangeOfVariablesDegree
set_option maxSynthPendingDepth 1

open scoped ContDiff

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def ChangeOfVariablesDegree.Statement : Prop :=
  ∀ (n : ℕ) (φ : (Fin n → ℝ) → Fin n → ℝ), ContDiff ℝ ∞ φ →
    HasCompactSupport (fun x => φ x - x) →
      ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ x, f (φ x) * (fderiv ℝ φ x).det = ∫ x, f x

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFreeness
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v w

def GenericFreeness.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (B : Type v) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (M : Type w) [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M] [Module.Finite B M],
    ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def AnalyticRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (t₀ : Fin d → ℂ) (τ₀ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) t₀) →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable →
    τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
    ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ AnalyticOnNhd ℂ r O ∧ r t₀ = τ₀ ∧
      ∀ t ∈ O, r t ^ N + ∑ j, a j t * r t ^ (j : ℕ) = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNonIsolatedFibreCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

def NonIsolatedFibreCurve.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin m → ℂ) (p : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → p ∈ U → AccPt p (𝓟 {v | v ∈ U ∧ f v = f p}) →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → Fin k → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = p ∧
          Set.MapsTo γ (ball 0 r) {v | v ∈ U ∧ f v = f p}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthLocalizedQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

def LengthLocalizedQuotient.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B),
    minimalPrimes B = {P} → (∀ s ∉ P, s ∈ nonZeroDivisors B) → y ∉ P →
    ∀ (Q : Ideal (B ⧸ Ideal.span {y})) [Q.IsPrime], Q.comap (Ideal.Quotient.mk _) = P ⊔ Ideal.span {y} →
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicZeroSetDimH
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric
open scoped ENNReal

def HolomorphicZeroSetDimH.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (h : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ h U →
    (∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0) →
      dimH {v | v ∈ U ∧ h v = 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolomorphicKernelFibre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolomorphicKernelFibre.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ) (b : Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → b ∈ U →
    ∀ d : ℕ, Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) = d →
      ∃ (V : Set (Fin d → ℂ)) (y : Fin d → ℂ) (γ : (Fin d → ℂ) → Fin k → ℂ)
        (ℓ : (Fin k → ℂ) →L[ℂ] Fin d → ℂ),
        IsOpen V ∧ y ∈ V ∧ DifferentiableOn ℂ γ V ∧ Set.MapsTo γ V U ∧ Set.InjOn γ V ∧
          (∀ s ∈ V, ∀ t ∈ V, ℓ (f (γ s)) = ℓ (f (γ t)) → f (γ s) = f (γ t)) ∧
          fderiv ℂ (fun t => ℓ (f (γ t))) y = 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAuslanderBuchsbaumDepthLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

def AuslanderBuchsbaumDepthLower.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (ℓ : ℕ) (rs : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) ℓ → (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs →
      ∃ ms : List R, (∀ r ∈ ms, r ∈ maximalIdeal R) ∧ IsWeaklyRegular M ms ∧ ms.length = rs.length - ℓ

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutLocalizedModule
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

def LengthCutLocalizedModule.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] (P : Ideal B) [P.IsPrime] (y : B) (Q₀ : Ideal B) [Q₀.IsPrime]
    (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M],
    IsNilpotent P → y ∉ P → Q₀ = P ⊔ Ideal.span {y} → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length (Localization.AtPrime Q₀)
          (LocalizedModule Q₀.primeCompl (M ⧸ (Ideal.span {y} • ⊤ : Submodule B M))) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticImplicitChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def AnalyticImplicitChart.Statement : Prop :=
  ∀ (σ ι : Type) [Fintype σ] [Fintype ι] (h : ι → (σ → ℂ) → ℂ) (a : σ → ℂ) (W : Set (σ → ℂ)),
    (∀ j, AnalyticAt ℂ (h j) a) → (∀ j, h j a = 0) →
    LinearIndependent ℂ (fun j => fderiv ℂ (h j) a) → W ∈ 𝓝 a →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
      (g : (Fin d → ℂ) → σ → ℂ), d + Fintype.card ι = Fintype.card σ ∧ IsOpen O ∧ IsOpen V ∧ a ∈ V ∧
        V ⊆ W ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
        {z | z ∈ V ∧ ∀ j, h j z = 0} = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadical
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def GenericFibreRadical.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsRadical → ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      (K.map (MvPolynomial.map (eval t))).IsRadical

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticSimpleRootBranch
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def AnalyticSimpleRootBranch.Statement : Prop :=
  ∀ (d N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (y : Fin d → ℂ) (τ : ℂ),
    (∀ j, AnalyticAt ℂ (a j) y) →
    τ ^ N + ∑ j, a j y * τ ^ (j : ℕ) = 0 →
    (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).derivative.eval τ ≠ 0 →
    ∃ (U : Set (Fin d → ℂ)) (B : Set ℂ) (ψ : (Fin d → ℂ) → ℂ),
      IsOpen U ∧ y ∈ U ∧ IsOpen B ∧ τ ∈ B ∧ AnalyticOnNhd ℂ ψ U ∧ ψ y = τ ∧
        ∀ y' ∈ U, ψ y' ∈ B ∧ ∀ s ∈ B, (s ^ N + ∑ j, a j y' * s ^ (j : ℕ) = 0 ↔ s = ψ y')

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def GenericFibreRadicalPrime.Statement : Prop :=
  ∀ (σ : Type) [Finite σ] (ι : Type) [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))),
    K.IsPrime → ∃ F : MvPolynomial σ ℂ, F ≠ 0 ∧ ∀ t : σ → ℂ, eval t F ≠ 0 →
      (K.map (MvPolynomial.map (eval t))).IsRadical

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPowerSumsEsymmAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def PowerSumsEsymmAnalytic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (V : Set (σ → ℂ)) (d : ℕ) (Z : (σ → ℂ) → Multiset ℂ),
    IsOpen V → (∀ z ∈ V, Multiset.card (Z z) = d) →
    (∀ k, 1 ≤ k → k ≤ d → AnalyticOnNhd ℂ (fun z => ((Z z).map fun a => a ^ k).sum) V) →
    ∀ k, AnalyticOnNhd ℂ (fun z => (Z z).esymm k) V

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountLocallyConstant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedProperCountLocallyConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ ContinuousOn g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∀ y ∈ D, δ y ≠ 0 → {x | x ∈ Y ∧ A x = y}.Finite ∧
      ∀ᶠ y' in 𝓝 y, {x | x ∈ Y ∧ A x = y'}.encard = {x | x ∈ Y ∧ A x = y}.encard

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAuslanderBuchsbaumProjDimUpper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing CategoryTheory RingTheory.Sequence

universe u

def AuslanderBuchsbaumProjDimUpper.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] (n d : ℕ) (ms : List R),
    HasProjectiveDimensionLE (ModuleCat.of R M) n →
    (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
    (∀ r ∈ ms, r ∈ maximalIdeal R) → IsWeaklyRegular M ms →
      HasProjectiveDimensionLE (ModuleCat.of R M) (d - ms.length)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeDeepWeightMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def poincareDeepWeight (z : ℂ) : ℝ :=
  if Real.log (‖z‖ ^ 2) < -Real.exp 1 then (‖z‖ ^ 2 * Real.log (‖z‖ ^ 2) ^ 2)⁻¹ else 0

def TubeDeepWeightMass.Statement : Prop :=
  ∀ (d : ℕ) (R : ℝ),
    ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (poincareDeepWeight (z 0)) < ⊤

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRootSumHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def RootSumHolomorphic.Statement : Prop :=
  ∀ (d : ℕ) (m : Polynomial (MvPolynomial (Fin d) ℂ)) (W : Set (Fin d → ℂ)) (Φ : (Fin d → ℂ) → ℂ → ℂ),
    m.Monic → IsOpen W → (∀ y ∈ W, (m.map (MvPolynomial.eval y)).Separable) →
    (∀ y ∈ W, ∀ τ : ℂ, (m.map (MvPolynomial.eval y)).IsRoot τ →
      ∃ O : Set ((Fin d → ℂ) × ℂ), IsOpen O ∧ (y, τ) ∈ O ∧ ∃ Ψ : (Fin d → ℂ) × ℂ → ℂ,
        DifferentiableOn ℂ Ψ O ∧
        ∀ p ∈ O, (m.map (MvPolynomial.eval p.1)).IsRoot p.2 → Φ p.1 p.2 = Ψ p) →
    DifferentiableOn ℂ (fun y => ((m.map (MvPolynomial.eval y)).roots.map (Φ y)).sum) W

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolynomialChartInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def PolynomialChartInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (k : ℕ) (t : MvPolynomial σ ℂ) (f : Fin k → MvPolynomial σ ℂ) (w : σ → ℂ),
    k + 1 = Fintype.card σ →
    LinearIndependent ℂ (Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) :
      Fin (k + 1) → σ → ℂ) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) {z | z ∈ U ∧ ∀ j, eval z (f j) = 0}

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionBranchLocus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionBranchLocus.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → IsPreconnected D → D.Nonempty → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∃ δ : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
      ∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormRemainder
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def PrimitiveFormRemainder.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ)
    (N : ℕ) (δ : (Fin d → ℂ) → ℂ) (q : σ → Fin N → (Fin d → ℂ) → ℂ) (n : σ → ℕ)
    (c : (i : σ) → Fin (n i) → (Fin d → ℂ) → ℂ) (f : (σ → ℂ) → ℂ),
    AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) → (∀ i j, AnalyticAt ℂ (c i j) (A w)) →
    (∀ i (T : ℂ), T ^ n i + ∑ j, c i j (A w) * T ^ (j : ℕ) = (T - w i) ^ n i) →
    AnalyticAt ℂ f w →
    ∃ (M : ℕ) (R : Polynomial ((Fin d → ℂ) → ℂ)), (∀ k, AnalyticAt ℂ (R.coeff k) (A w)) ∧
      ∀ᶠ z in 𝓝 w, (∀ i, z i ^ n i + ∑ j, c i j (A z) * z i ^ (j : ℕ) = 0) →
        (∀ i, δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
        δ (A z) ^ M * f z = R.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ => ℂ) (A z)) (ℓ z)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeightedAreaFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def WeightedAreaFormula.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E) (H : E → ℝ),
    IsOpen A → DifferentiableOn ℝ f A → (∀ y, {x | x ∈ A ∧ f x = y}.Finite) →
    IntegrableOn (fun x => |(fderiv ℝ f x).det| * H x) A μ →
      Integrable (fun y => ∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x) μ ∧
        ∫ y, (∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x) ∂μ = ∫ x in A, |(fderiv ℝ f x).det| * H x ∂μ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassFiniteness
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def WeierstrassFiniteness.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (x : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    (∀ i, AnalyticAt ℂ (f i) x) →
    (∀ l : σ, ∃ (r : ℕ) (h : Fin k → (σ → ℂ) → ℂ) (h' : Fin d → (σ → ℂ) → ℂ),
      (∀ i, AnalyticAt ℂ (h i) x) ∧ (∀ j, AnalyticAt ℂ (h' j) x) ∧
      ∀ᶠ z in 𝓝 x, (z l - x l) ^ r = ∑ i, h i z * f i z + ∑ j, h' j z * (A z j - A x j)) →
    ∀ g : (σ → ℂ) → ℂ, AnalyticAt ℂ g x →
      ∃ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (h : Fin k → (σ → ℂ) → ℂ),
        (∀ j, AnalyticAt ℂ (a j) (A x)) ∧ (∀ i, AnalyticAt ℂ (h i) x) ∧
        ∀ᶠ z in 𝓝 x, g z ^ N + ∑ j, a j (A z) * g z ^ (j : ℕ) = ∑ i, h i z * f i z

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperSheetedFibreEsymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperSheetedFibreEsymm.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (l : (σ → ℂ) →L[ℂ] ℂ) (j : ℕ),
    IsOpen D → Set.MapsTo A Y D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ Y ∧ A x ∈ K}) →
    AnalyticOnNhd ℂ δ D →
    (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ D → W.Nonempty → ∃ t ∈ W, δ t ≠ 0) →
    (∀ x ∈ Y, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
      IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ Y ∩ V = g '' O) →
    ∃ F : (Fin d → ℂ) → ℂ, AnalyticOnNhd ℂ F D ∧
      ∀ t ∈ D, δ t ≠ 0 → ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) = {x | x ∈ Y ∧ A x = t} →
        F t = (s.val.map l).esymm j

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCircleArgumentPrinciple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

def CircleArgumentPrinciple.Statement : Prop :=
  ∀ (h : ℂ → ℂ) (O : Set ℂ) (c : ℂ) (r : ℝ),
    0 < r → IsOpen O → closedBall c r ⊆ O → DifferentiableOn ℂ h O → (∀ s ∈ sphere c r, h s ≠ 0) →
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) ∧
      ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ O →
        (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv h s / h s) = (Z.map φ).sum

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIsolatedFibreLocalUnbranched
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsolatedFibreLocalUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ w ∈ X ∩ B, (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ B ∩ W, A x = A w → x = w) →
    ∃ (M : Set (σ → ℂ)) (g : (Fin d → ℂ) → ℂ), M ∈ 𝓝 w ∧ AnalyticAt ℂ g (A w) ∧
      (¬ ∀ᶠ y in 𝓝 (A w), g y = 0) ∧
      ∀ x ∈ X ∩ B ∩ M, g (A x) ≠ 0 →
        ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolynomialRootPredicateFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PolynomialRootPredicateFactor.Statement : Prop :=
  ∀ (d N : ℕ) (B : Set (Fin d → ℂ)) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
    (P : (Fin d → ℂ) → ℂ → Prop),
    IsOpen B → Convex ℝ B → (∀ j, AnalyticOnNhd ℂ (a j) B) → AnalyticOnNhd ℂ δ B → (∃ t ∈ B, δ t ≠ 0) →
    (∀ t ∈ B, δ t ≠ 0 →
      (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    (∀ t₀ ∈ B, δ t₀ ≠ 0 → ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧ (P s (r s) ↔ P t₀ τ₀)) →
    ∃ C E : (Fin d → ℂ) → ℂ → ℂ,
      (∀ t ∈ B, ∀ T : ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => C u.1 u.2) (t, T) ∧
        AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => E u.1 u.2) (t, T)) ∧
      (∀ t ∈ B, ∀ T : ℂ, C t T * E t T = T ^ N + ∑ j, a j t * T ^ (j : ℕ)) ∧
      ∀ t ∈ B, δ t ≠ 0 → ∀ τ : ℂ, τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0 →
        (C t τ = 0 ↔ P t τ) ∧ (E t τ = 0 ↔ ¬ P t τ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionCover.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → IsPreconnected D → D.Nonempty → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∃ (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
      AnalyticOnNhd ℂ δ D ∧ (∃ y ∈ D, δ y ≠ 0) ∧
      (∀ y ∈ D, δ y ≠ 0 → {x | x ∈ X ∩ B ∧ A x = y}.encard = N) ∧
      (∀ x ∈ X ∩ B, δ (A x) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (g : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧ X ∩ B ∩ V = g '' O) ∧
      X ∩ B ⊆ closure {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalizationAtPrimeQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

noncomputable section

def LocalizationAtPrimeQuotient.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (I : Ideal A) (T : Submonoid (A ⧸ I)) (P : Ideal (Localization T)) [P.IsPrime]
    (W : Ideal A) [W.IsPrime],
    P.comap ((algebraMap (A ⧸ I) (Localization T)).comp (Ideal.Quotient.mk I)) = W →
      ∃ e : Localization.AtPrime P ≃+* (Localization.AtPrime W ⧸ I.map (algebraMap A (Localization.AtPrime W))),
        ∀ a : A,
          e (algebraMap (Localization T) (Localization.AtPrime P)
              (algebraMap (A ⧸ I) (Localization T) (Ideal.Quotient.mk I a))) =
            Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime W)))
              (algebraMap A (Localization.AtPrime W) a)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProperOpenProjectionLocalUnbranched
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def ProperOpenProjectionLocalUnbranched.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X B : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)),
    IsOpen B → (∀ i, AnalyticOnNhd ℂ (f i) B) → X ∩ B = {z | z ∈ B ∧ ∀ i, f i z = 0} →
    IsOpen D → Set.MapsTo A (X ∩ B) D →
    (∀ K ⊆ D, IsCompact K → IsCompact {x | x ∈ X ∩ B ∧ A x ∈ K}) →
    (∀ x ∈ X ∩ B, ∀ V ∈ 𝓝 x, A '' (X ∩ B ∩ V) ∈ 𝓝 (A x)) →
    ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ),
      IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
      (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
      ∀ y ∈ U, g y ≠ 0 →
        ∀ x ∈ X ∩ B, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧
          X ∩ B ∩ V = h '' O

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GenericCountCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def IsGenericCountCover {σ : Type} [Fintype σ] {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (D : Set (Fin d → ℂ)) (N : ℕ) : Prop :=
  (∀ y ∈ D, {x | x ∈ Y ∧ A x = y}.encard ≤ N) ∧
  ∀ y₀ ∈ D, ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → ℂ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ D ∧ AnalyticOnNhd ℂ g U ∧
    (∀ W : Set (Fin d → ℂ), IsOpen W → W ⊆ U → W.Nonempty → ∃ t ∈ W, g t ≠ 0) ∧
    ∀ y ∈ U, g y ≠ 0 → {x | x ∈ Y ∧ A x = y}.encard = N ∧
      ∀ x ∈ Y, A x = y → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ)) (h : (Fin d → ℂ) → σ → ℂ),
        IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ h O ∧ (∀ y' ∈ O, A (h y') = y') ∧ Y ∩ V = h '' O

noncomputable def fibreDiscr {σ : Type} [Fintype σ] {d : ℕ} (Y : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (l : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (y : Fin d → ℂ) : ℂ :=
  if h : {x | x ∈ Y ∧ A x = y}.encard = N then
    ∏ p ∈ (Set.finite_of_encard_eq_coe h).toFinset.offDiag, (l p.1 - l p.2)
  else 0

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
