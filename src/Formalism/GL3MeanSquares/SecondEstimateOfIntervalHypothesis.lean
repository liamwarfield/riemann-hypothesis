module

public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP
public import Formalism.FrobeniusOrbits.HostThickExists
public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
open Finset ArithmeticFunction Classical

noncomputable section

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

def X1 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5))

def X2 (ε x : ℝ) : ℝ := Real.exp (x ^ (ε / 5) * Real.log x ^ 2)

def logDerivLAtOne {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

def Gchi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) * ((y / n - 1 : ℝ) : ℂ)) + (y : ℂ) * logDerivLAtOne χ

def G1 (y : ℝ) : ℝ :=
  (∑ n ∈ Icc 1 ⌊y⌋₊, Λ n * (y / n - 1)) - y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def cN (x : ℝ) (n : ℕ) : ℝ := Λ n * min 1 (x / n)

def Sz {q : ℕ} (χ : DirichletCharacter ℂ q) (x z : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 ⌊z⌋₊, ((cN x n : ℝ) : ℂ) * χ (n : ZMod q)

def tailL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : ℝ) : ℂ :=
  - logDerivLAtOne χ - ∑ n ∈ Icc 1 ⌊z⌋₊, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) / (n : ℂ)

def qc (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

def chi8 : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)

instance neZeroMulPrime {t q : ℕ} [NeZero t] [Fact q.Prime] : NeZero (t * q) :=
  ⟨Nat.mul_ne_zero (NeZero.ne t) (Fact.out : q.Prime).ne_zero⟩

def tw {t : ℕ} (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ (t * q) :=
  DirichletCharacter.changeLevel (Dvd.intro q rfl) θ * DirichletCharacter.changeLevel (Dvd.intro_left t rfl) (qc q)

def ZeroFreeBox {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - 1 / 400 < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0

def GoodFor {N : ℕ} [NeZero N] (Q : ℝ) (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ (N : ℝ) ≤ Q ∧ ZeroFreeBox Q χ

def PPset (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Icc 1 ⌊X⌋₊).filter (fun q => q.Prime ∧ q % m₀ = a₀ % m₀ ∧ X ^ (1 / 2 : ℝ) < (q : ℝ))

def oddM (y : ℝ) (q₁ : ℕ) : ℕ := q₁ * ∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p

def IsNormOne (d N p : ℕ) : Prop :=
  ∃ u v : ℤ, (N : ℤ) ∣ u - 1 ∧ (N : ℤ) ∣ v ∧ (p : ℤ) = u ^ 2 + u * v + (((d + 1) / 4 : ℕ) : ℤ) * v ^ 2

def normPrimes (d N : ℕ) (lo hi : ℝ) : Finset ℕ :=
  (Icc 1 ⌊hi⌋₊).filter (fun p => p.Prime ∧ lo < (p : ℝ) ∧ IsNormOne d N p)

def rho (c Cρ B X : ℝ) : ℝ :=
  Cρ * Real.exp (-c * Real.log X / Real.log B) + Cρ * Real.exp (-c * Real.log X ^ (1 / 2 : ℝ))

def BoxCountHyp (C : ℝ) : Prop :=
  ∀ (t : ℕ) [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (S : Finset ℕ), θ.IsPrimitive → θ ^ 2 = 1 →
    (∀ q ∈ S, ∃ _ : Fact q.Prime, q % 4 = 3 ∧ q.Coprime t ∧ ((t * q : ℕ) : ℝ) ≤ Q ∧ ¬ ZeroFreeBox Q (tw θ q)) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

def BoxTailHyp (ε C x₀ : ℝ) : Prop :=
  ∀ (x Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), x₀ ≤ x → x ^ (ε / 6) ≤ Real.log Q →
    Real.log Q ≤ x ^ (ε / 4) → χ ≠ 1 → GoodFor Q χ →
    ‖(x : ℂ) * tailL χ (x ^ 400)‖ ≤ x ^ ε ∧ ‖logDerivLAtOne χ‖ ≤ C * Real.log x

def IntervalHyp (C₀ c Cρ c₃ : ℝ) : Prop :=
  ∀ (d N : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 1 ≤ N → (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ C₀ ≤ X →
    rho c Cρ (4 * (d : ℝ) * (N : ℝ) ^ 2) X ≤ h / 100 → 0 < h → h ≤ 1 →
    (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ 7 ≤ h * X ^ (1 / 3 : ℝ) →
    c₃ * h * (4 * (d : ℝ) * (N : ℝ) ^ 2) ^ (-6 : ℝ) * X / Real.log X ≤ ((normPrimes d N X (X * (1 + h))).card : ℝ)

def GFiniteSplit : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (x z : ℝ), 0 < x → x ≤ z →
    Gchi χ x = - Sz χ x z - (x : ℂ) * tailL χ z

def UnitModulusIncrementConditions : Prop :=
  ∀ ε C : ℝ, 0 < ε → ε ≤ 1 → 0 < C → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    x ^ 400 < X1 ε x ^ (1 / 2 : ℝ) ∧ 2 ≤ x ^ (ε / 5) ∧
    (1 / 4) * Real.log x ^ 2 * Real.log 8 ≤ Real.log (X1 ε x) ∧
    Real.log x ^ 2 * Real.log (8 * (x ^ 400) ^ 2) ≤ Real.log (X1 ε x) ∧
    x ^ (ε / 6) ≤ Real.log (X1 ε x) ∧
    x ^ (ε / 6) ≤ Real.log (8 * X1 ε x) ∧ Real.log (8 * X1 ε x) ≤ x ^ (ε / 4) ∧
    C * x * Real.log x / (x ^ (1 / 2 + ε) / 2) ^ 2 ≤ x ^ (-ε) ∧ x ^ (-ε) ≤ 1 / 8 ∧
    2 * (C * (8 * X1 ε x) ^ (1 / 4 : ℝ)) ≤ X1 ε x ^ (9 / 10 : ℝ) / 2

def TwEval : Prop :=
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime] (n : ℕ),
    tw θ q (n : ZMod (t * q)) = θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)

def TwPrimitive : Prop :=
  (chi8.IsPrimitive ∧ chi8 ^ 2 = 1) ∧
  ∀ (t : ℕ) (θ : DirichletCharacter ℂ t) (q : ℕ) [Fact q.Prime], θ.IsPrimitive → q ≠ 2 → q.Coprime t →
    (tw θ q).IsPrimitive ∧ tw θ q ≠ 1 ∧ (θ ^ 2 = 1 → tw θ q ^ 2 = 1)

def SmoothingSizeBounds : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ y lam : ℝ, Real.exp (x ^ (ε / 3)) / 3 ≤ y → 0 < lam →
    lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    x ^ (ε / 3) / 2 ≤ Real.log y ∧ x ^ (2 * ε / 15) / (4 * Real.log x ^ 2) ≤ Real.log y / lam ∧
    x ^ (ε / 6) / 2 ≤ Real.sqrt (Real.log y)

def ThinIntegral : Prop :=
  ∀ ε c : ℝ, 0 < ε → 0 < c → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ V lam : ℝ, x ^ (ε / 3) / 2 ≤ V → 1 ≤ lam →
    lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    MeasureTheory.IntegrableOn (fun v : ℝ => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) (Set.Ioi V) ∧
    (∫ v in Set.Ioi V, (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v))) ≤ Real.exp (-c' * x ^ (ε / 8))

def TailIntegralBoundOfPsiBound : Prop :=
  ∀ ε c C : ℝ, 0 < ε → 0 < c → 0 < C → ∃ c' x₀ : ℝ, 0 < c' ∧ ∀ x : ℝ, x₀ ≤ x → ∀ (y lam : ℝ) (psi0 : ℝ → ℂ),
    Real.exp (x ^ (ε / 3)) / 3 ≤ y → 1 ≤ lam → lam ≤ 2 * x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ u : ℝ, y ≤ u → ‖psi0 u‖ ≤
      C * u * (Real.log u + lam) ^ 2 * Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) →
    ‖(y : ℂ) * ∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ y * Real.exp (-c' * x ^ (ε / 8))

end Formalism.HermitianLattices.ZeroFreeRegionGL2
end
end

section -- merged from Formalism.GL3MeanSquares.OrbitPointsDistinct
open NumberField IntermediateField Ideal IsDedekindDomain
open scoped Pointwise TensorProduct

noncomputable section

namespace Formalism.HermitianLattices.FiltrationBoundaryCriterion

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

def PartnerFormula : Prop :=
  ∀ (e : ℕ) (h t : HGrp e),
    cc e * ((c0, h) : GG e) * ((1, t) : GG e) = ((1, h * t) : GG e) ∧
    cc e * ((c0, h) : GG e) * (((sg e).1, t) : GG e) = (((sg e).1, h * t) : GG e) ∧
    cc e * ((((1 : ℤˣ), (-1 : ℤˣ)), h) : GG e) * ((1, t) : GG e) = (((sg e).1, h * t) : GG e) ∧
    cc e * ((((1 : ℤˣ), (-1 : ℤˣ)), h) : GG e) * (((sg e).1, t) : GG e) = ((1, h * t) : GG e)

def FrobArith : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
  ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
    (u : (ZMod (2 ^ (e + 2)))ˣ), (u : ZMod (2 ^ (e + 2))) = (p : ZMod (2 ^ (e + 2))) →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
    ((∀ x : 𝓞 (hostE ζ a b), σ • x - x ^ p ∈ P) ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        (galE e ζ a b σ).2 = hcl e u)) ∧
    ((∀ x : 𝓞 (hostE ζ a b), σ⁻¹ • x - x ^ p ∈ P) ↔
      ((((galE e ζ a b σ).1.1 : ℤˣ) : ℤ) = jacobiSym (-(q : ℤ)) p ∧
        (((galE e ζ a b σ).1.2 : ℤˣ) : ℤ) = jacobiSym (-(d : ℤ)) p ∧
        (galE e ζ a b σ).2 = (hcl e u)⁻¹))






def DiffStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b,
    σ • differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) =
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))

def PrincipalStable : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ c : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b c = cc e →
  ∀ 𝔭₂ 𝔭q : Ideal (𝓞 (KinE ζ a b)), 𝔭₂.IsPrime → 𝔭q.IsPrime →
    ((2 : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭₂ → ((q : ℤ) : 𝓞 (KinE ζ a b)) ∈ 𝔭q →
    ∃ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
      differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (c • 𝔟) ∧
      (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟 →
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
        P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) ∧
      𝔟 ⊔ c • 𝔟 = ⊤ ∧
      (∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ ∈ Psi e → σ • 𝔟 = 𝔟) ∧
      ∀ 𝔟' : Ideal (𝓞 (hostE ζ a b)),
        differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟' * (c • 𝔟') →
        (∀ P : Ideal (𝓞 (hostE ζ a b)), P.IsPrime → P ∣ 𝔟' →
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭₂ ∨
          P.comap (algebraMap (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b))) = 𝔭q) →
        𝔟' = 𝔟

end Formalism.HermitianLattices.FiltrationBoundaryCriterion
end
end

section -- merged from Formalism.GL3MeanSquares.SignsFromTrianglesSquares
noncomputable section

namespace Formalism.HermitianLattices.WeilRepresentation

open Finset Formalism.HermitianLattices.IntegralLatticeDensity

def ImHGenusOne : Prop :=
  ∀ (d x0 x1 y0 y1 : ℝ), 0 < d →
    (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).im /
        (Real.sqrt d / 2) = x1 * y0 - x0 * y1 ∧
    2 * (((x0 : ℂ) + x1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2)) *
      (starRingEnd ℂ) ((y0 : ℂ) + y1 * ((1 + (Real.sqrt d : ℂ) * Complex.I) / 2))).re =
        2 * (x0 * y0 + x0 * y1 + (1 + d) / 4 * (x1 * y1)) + (x1 * y0 - x0 * y1)

def Heisenberg₂ {V : Type} [AddCommGroup V] (H : V → V → ℂ) (x : V) (F : V → ℂ) (z : V) : ℂ :=
  F (z + x) * Complex.exp (-(Real.pi : ℂ) * H z x - Real.pi * H x x / 2)

def HeisenbergCocycle : Prop :=
  ∀ (V : Type) [AddCommGroup V] (H : V → V → ℂ),
    (∀ x x' y, H (x + x') y = H x y + H x' y) → (∀ x y, H y x = (starRingEnd ℂ) (H x y)) →
    ∀ (F : V → ℂ) (x y z : V),
      Heisenberg₂ H x (Heisenberg₂ H y F) z =
        Complex.exp (-((Real.pi : ℂ) * Complex.I * ((H x y).im : ℂ))) * Heisenberg₂ H (x + y) F z

end Formalism.HermitianLattices.WeilRepresentation
end
end
