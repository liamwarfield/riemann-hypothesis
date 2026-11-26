module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

def Zr (k r : ℕ) (g : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun a b => g (esI k r a) (eI k r b)

def BlockAnti {r : ℕ} (β : Fin r → ℕ) (Z : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  Monotone β ∧ Z.det ≠ 0 ∧ (∀ a b, Z a b ≠ 0 → β a = β b) ∧
    ∀ a b a' b', Z a b ≠ 0 → Z a' b' ≠ 0 → β a = β a' → ‖Z a b‖ = ‖Z a' b'‖ ∧ (a = a' → b = b') ∧ (a < a' → b' < b)

def IsNormal (k r : ℕ) (β : Fin r → ℕ) (g : Mat k r) : Prop :=
  g ∈ GG k r ∧ (∀ a : Fin r, g⁻¹ *ᵥ bvec (eI k r a) ∈ Xst k r ∧ g *ᵥ bvec (eI k r a) ∈ Xst k r) ∧ BlockAnti β (Zr k r g)

def lebR (k r : ℕ) (β : Fin r → ℕ) : Measure (Mt k r) :=
  (volume : Measure (UTin β → ℂ)).map fun x => Matrix.of.symm (uEmb k r (upperIn β x))

def NormR (k r : ℕ) (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)) : Prop :=
  ∃ n₁ ∈ Nset k r, ∃ n₂ ∈ Nset k r, ∃ (g₀ : Mat k r) (β : Fin r → ℕ), IsNormal k r β g₀ ∧ γ = n₁ * g₀ * n₂ ∧
    μR = (ENNReal.ofReal s • lebR k r β).map (conjM n₂⁻¹)

def muProd {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) :=
  (μW.prod μN).map fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2

def OneSide {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (c : ℝ) : Prop :=
  inWb k r z ∧ 0 < Tz k r z ∧ Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π ∧
    IsHaarOn (GG k r) μG ∧ IsHaarOn (UWset k r z) μW ∧ μW Set.univ = 1 ∧ IsHaarOn (Nset k r) μN ∧
    IsQuotMeas μG (muProd μW μN) νS ∧ (∀ n ∈ Nset k r, ‖ψ n‖ = 1) ∧ IsSPsiEquiv z ψ π Φ ∧ ContinuousOn Φ (GG k r) ∧
    0 < c ∧ l2SG νS Φ = ENNReal.ofReal (c * Module.finrank ℂ Wp)

def MomBd {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r))
    (Φ : Mat k r → Wp) (q : ℕ) (H₁ : ℝ) : Prop :=
  ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal (lA k r z (Matrix.of x) a ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤
    ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ

def absBd (k r : ℕ) (H₁ De D : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (44 * r ^ 3) * H₁ ^ (24 * r ^ 3) * De ^ (14 * r ^ 2) *
    (8 * Real.pi * Real.exp 1 / k) ^ (r * (k - 2 - r)) * (D ^ (k - 2 - r))⁻¹

end GlobalTheory.Amp
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagMeas

open Formalism.MainNotions.S GlobalTheory.Count

def flagAt (I : AutInst) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (v : InfinitePlace I.F) :
    Fin (a + 1) → Submodule ℂ (Fin I.n → ℂ) :=
  fun i => Submodule.span ℂ ((fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) '' (S i : Set _))

def IsSatFlag (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) : Prop :=
  S 0 = ⊥ ∧ Monotone S ∧ (∀ i : Fin a, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i) ∧
    (∀ i, ∀ y, y ∈ S i ↔ y ∈ Λ ∧ y ∈ Submodule.span I.E (S i : Set (Fin I.n → I.E))) ∧
    ∀ x ∈ S (Fin.last a), ∀ y ∈ S (Fin.last a), Formalism.UG.hform (starRingEnd I.E) I.J x y = 0

def IsGaugeAll (I : AutInst) (c : InfinitePlace I.F → ℝ) : Prop := ∀ v, IsGauge (I.ε v) (c v)

def cIw (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : ℝ :=
  (2 : ℝ) ^ (-((dimN (p + q) j : ℝ) / 2)) * (volU p * volU q) /
    ((∏ i, volU (j i) * (2 : ℝ) ^ (((j i : ℝ)) ^ 2 / 2)) * volU (p - ∑ i, j i) * volU (q - ∑ i, j i))

def rankFac (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) * ((M : ℝ) - 1 / 2)) * Formalism.HermitianLatticesTheory.lValEta E M

end GlobalTheory.FlagMeas
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
namespace GlobalTheory.ThA

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.KB Finset NumberField MeasureTheory Formalism.QuantumDeterminants

noncomputable section

open Classical

section place

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end place

def PlExists : Prop :=
  ∃ Cb : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r) (l0 : ℕ),
    1 ≤ l0 → l0 ≤ P.k → 2 ≤ P.k → Bs.μW Set.univ = 1 → Bs.μW' Set.univ = 1 → Bs.μN = D.muN P.k P.r →
    D.IsBaseFrame Bs ν' m₀ → Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∃ p : Pl P Wp Wq, p.l0 = l0 ∧ p.T.base = Bs ∧ p.ν' = ν' ∧ p.m₀ = m₀ ∧ InDDplus2 P l0 p.T.base Cb p.Θ

end

end GlobalTheory.ThA
end
