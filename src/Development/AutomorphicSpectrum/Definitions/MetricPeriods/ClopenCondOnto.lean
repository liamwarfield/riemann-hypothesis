module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix Metric GroundTheory.Heights₂.Heights.Regular

structure LogPeriods (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] where
  a_le : a ≤ n
  free : Module.Free ℤ Λ
  fin : Module.Finite ℤ Λ
  rank : Module.finrank ℤ Λ = 2 * g

  E : LinearMap.BilinForm ℤ Λ
  alt : ∀ x, E x x = 0
  unimod : Function.Bijective E

  P : (Fin n → ℂ) → (Λ →+ (Fin g → ℂ))
  hol : ∀ x, DifferentiableOn ℂ (fun w => P w x) (logCover a_le)

  H : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ
  herm : ∀ w ∈ logCover a_le, (H (expCover a w)).IsHermitian
  pos : ∀ w ∈ logCover a_le, ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H (expCover a w) *ᵥ star z).re
  im : ∀ w ∈ logCover a_le, ∀ x y, (P w x ⬝ᵥ H (expCover a w) *ᵥ star (P w y)).im = E x y

  T : Fin a → (Λ →ₗ[ℤ] Λ)
  mono : ∀ i, ∀ w ∈ logCover a_le, ∀ x,
    P (w + Pi.single (Fin.castLE a_le i) (2 * Real.pi * Complex.I)) x = P w (T i x)

  W : Submodule ℤ Λ
  coiso : ∀ x, (∀ y ∈ W, E x y = 0) → ∃ k : ℤ, k ≠ 0 ∧ k • x ∈ W

  s : W → (Fin n → ℂ) → (Fin g → ℂ)
  s_hol : ∀ x, DifferentiableOn ℂ (s x) (ball 0 1)
  s_eq : ∀ x, ∀ w ∈ logCover a_le, s x (expCover a w) = P w x
  span : Submodule.span ℂ (Set.range fun x => s x 0) = ⊤

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ptsOver (𝕜 : Type) [Field 𝕜] (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → 𝕜) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, aeval z f = 0}

def algPts (p : ℕ) [Fact p.Prime] (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → PadicAlgCl p) :=
  {z | z ∈ ptsOver (PadicAlgCl p) P ∧ ∀ q, IsAlgebraic ℚ (z q)}

def HasVal (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [Field 𝕜] (z : (Σ k, ι k) → 𝕜) (w : 𝕜) : Prop :=
  ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + a k) ∧
    aeval y g = s * aeval y h ∧ aeval z h ≠ 0 ∧ aeval z g = w * aeval z h

def ValLe (y : (Σ k, ι k) → Ω) (a : K → ℤ) (s : Ω) {𝕜 : Type} [NormedField 𝕜] (z : (Σ k, ι k) → 𝕜) (r : ℝ) :
    Prop :=
  ∀ w, HasVal y a s z w → ‖w‖ ≤ r

def supMet {𝕜 : Type} [NormedField 𝕜] (a : K → ℤ) (z : (Σ k, ι k) → 𝕜) : ℝ :=
  ∏ k, ‖fun i : ι k => z ⟨k, i⟩‖ ^ a k

def IsFormOff (P : Ideal (MRing ι)) (u : MRing ι) : Prop :=
  (∃ d, IsMultiHomog u d) ∧ u ∉ P

def powH (A : HermLine ι) (q : ℕ) : HermLine ι where
  a := fun k => (q : ℤ) * A.a k
  h z := A.h z ^ q
  pos z hz := pow_pos (A.pos z hz) q
  smul c z hc := by
    rw [A.smul c z hc, mul_pow, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [mul_comm, zpow_mul, zpow_natCast]

def shiftH (A : HermLine ι) (t : ℝ) : HermLine ι where
  a := A.a
  h z := Real.exp t * A.h z
  pos z hz := mul_pos (Real.exp_pos t) (A.pos z hz)
  smul c z hc := by rw [A.smul c z hc]; ring

def normHt (II : IntersectionSystem) (P : Ideal (MRing ι)) (A : HermLine ι) (D : ℕ) : ℝ :=
  II K ι P (D + 1) (fun _ => A) / (((D : ℝ) + 1) * geomDeg P A D)

structure IsNefH (P : Ideal (MRing ι)) (M : HermLine ι) : Prop where
  semipos : ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P M
  conj : IsConjInvariantH M
  nef : NefOnFibres P M.a

structure IsGenH (P : Ideal (MRing ι)) (L : HermLine ι) (Λ : ℝ) : Prop where
  pos : 0 < Λ
  semipos : ∃ P0, P0 ≤ P ∧ IsSemipositiveRel P0 P L
  conj : IsConjInvariantH L
  mono : ∃ a : K → ℕ, (L.a = fun k => (a k : ℤ)) ∧ ∀ z ∈ mcPts P, ∀ μ : (Σ k, ι k) →₀ ℕ,
    (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ Λ * L.h z

end GlobalTheory.CompanionTheory.Ar.Small
end
end
