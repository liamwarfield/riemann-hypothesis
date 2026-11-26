module

public import Formalism.SizeWindowBrackets.SChain
public import Formalism.SizeWindowBrackets.WindowSettingSatisfiable

@[expose] public section

section -- merged from Formalism.SizeWindowBrackets.Chain2aCoreNoAnalytic
open Module NumberField Matrix
open Formalism.HN

noncomputable section

namespace Formalism.LFunctionChainParameters.LChain2

open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain

instance decFinPl (K : Type) [Field K] [NumberField K] : DecidableEq (slopeLatticeData.FinPl K) := Classical.decEq _

section Places
variable {K : Type} [Field K] [NumberField K]

def ramE (w : slopeLatticeData.FinPl K) : ℝ := (w.1.ramificationIdx ℤ : ℝ)

end Places

structure Fam (I : Type) (m : ℕ) where

  K : Type
  [indexKFirst : Field K]
  [indexKSecond : NumberField K]
  [indexKThird : StarRing K]
  [indexKFourth : _root_.NumberField.IsTotallyComplex K]

  Wd : Type
  [indexWFirst : AddCommGroup Wd]
  [indexWSecond : Module K Wd]
  [indexWThird : Module (𝓞 K) Wd]
  [indexWFourth : IsScalarTower (𝓞 K) K Wd]

  κ : Type
  [firstRealIndex : Fintype κ]
  [secondRealIndex : DecidableEq κ]

  κ₁ : Type
  [firstRationalIndex : Fintype κ₁]
  [secondRationalIndex : DecidableEq κ₁]

  V : I → Type
  [indexVFirst : ∀ i, AddCommGroup (V i)]
  [indexVSecond : ∀ i, Module K (V i)]
  [indexVThird : ∀ i, Module (𝓞 K) (V i)]
  [indexVFourth : ∀ i, IsScalarTower (𝓞 K) K (V i)]

  ι : I → Type
  [indexCFirst : ∀ i, Fintype (ι i)]
  [indexCSecond : ∀ i, DecidableEq (ι i)]

  Vf : I → Type
  [indexFFirst : ∀ i, AddCommGroup (Vf i)]
  [indexFSecond : ∀ i, Module K (Vf i)]
  [indexFThird : ∀ i, Module (𝓞 K) (Vf i)]
  [indexFFourth : ∀ i, IsScalarTower (𝓞 K) K (Vf i)]

  ιf : I → Type
  [indexDFirst : ∀ i, Fintype (ιf i)]
  [indexDSecond : ∀ i, DecidableEq (ιf i)]
  b' : Basis κ K Wd
  X' : InfinitePlace K → Matrix κ κ ℂ

  cc : Submodule (𝓞 K) Wd
  b : ∀ i, Basis (ι i) K (V i)
  X : ∀ i, InfinitePlace K → Matrix (ι i) (ι i) ℂ

  M : ∀ i, Submodule (𝓞 K) (V i)

  N0 : ∀ i, Submodule (𝓞 K) (V i)
  bf : ∀ i, Basis (ιf i) K (Vf i)
  Xf : ∀ i, InfinitePlace K → Matrix (ιf i) (ιf i) ℂ

  Mf : ∀ i, Submodule (𝓞 K) (Vf i)

  σ : I → slopeLatticeData.FinPl K →₀ ℤ

  τ : slopeLatticeData.FinPl K →₀ ℤ

  B : ∀ i, V i →ₗ[K] Wd

  v : InfinitePlace K
  Y : ∀ i, Matrix (ι i) (ι i) ℂ
  Y' : Matrix κ κ ℂ
  Ball : ∀ i, Matrix (κ ⊕ κ₁) (ι i) ℂ
  γ : I → ℝ
  Bf : ∀ i, Matrix (κ ⊕ κ₁) (ιf i) ℂ
  Vr : ∀ i, Matrix (ιf i) (ι i) ℂ

  S : Finset (slopeLatticeData.FinPl K)
  gain : Fin m → slopeLatticeData.FinPl K → ℝ
  Fj : Fin m → slopeLatticeData.FinPl K → ℝ
  Ej : I → Fin m → slopeLatticeData.FinPl K → ℝ

  iop : ℕ → ℝ

  T : I → ℕ

  h : I → ℝ

  lam : I → ℝ
  Dstar : ℝ
  η0 : ℝ
  η1 : ℝ
  e0 : ℝ

attribute [instance] Fam.indexKFirst Fam.indexKSecond Fam.indexKThird Fam.indexKFourth Fam.indexWFirst Fam.indexWSecond Fam.indexWThird Fam.indexWFourth Fam.firstRealIndex Fam.secondRealIndex Fam.firstRationalIndex Fam.secondRationalIndex
  Fam.indexVFirst Fam.indexVSecond Fam.indexVThird Fam.indexVFourth Fam.indexCFirst Fam.indexCSecond Fam.indexFFirst Fam.indexFSecond Fam.indexFThird Fam.indexFFourth Fam.indexDFirst Fam.indexDSecond

namespace Fam

variable {I : Type} {m : ℕ} (F : Fam I m)

def N' (u : I) : Submodule (𝓞 F.K) (F.V u) := slopeLatticeData.modLat (F.σ u) (F.N0 u)

def du (u : I) : ℝ := (Fintype.card (F.ι u) : ℝ)

end Fam

structure Glob where

  x : ℝ

  ε : ℝ

  k : ℝ

  La : ℝ

  v : ℝ

  lg : ℝ

  delBar : ℝ

  etaBar : ℝ

  eBar : ℝ

section Data
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

variable [∀ u0, Nonempty (W u0)]

end Data

section Loss
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {Ω : Type} {W : Ω → H → Type} {m : ℕ}

variable [Fintype Ω] [∀ o u0, Fintype (W o u0)]

end Loss

section DataD
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataD

section DataL
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataL

section DataT
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}

end DataT

section LossC
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}

end LossC

end Formalism.LFunctionChainParameters.LChain2
end
end

section -- merged from Formalism.SizeWindowBrackets.PrimeClassLossHypothesesSatisfiable
namespace Formalism.LFunctionChainParameters.SmallOrderPrimeLosses

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

noncomputable section

def clr (P : Par) : Par := { P with β := 0, s₀ := 0 }

def WindowsD (P : Par) (e K : ℝ) : Prop :=
  0 < P.ε ∧ P.ε ≤ 1 ∧ 0 ≤ e ∧ 1 ≤ K ∧
  (P.x ^ 2 ≤ (2 : ℝ) ^ P.e₂ ∧ (2 : ℝ) ^ P.e₂ ≤ P.n) ∧ P.n ≤ P.x ^ e ∧
  P.x ^ 2 ≤ P.k ∧ P.k ≤ P.x ^ e ∧
  0 ≤ P.N ∧ P.N ≤ P.x ^ e ∧ 0 ≤ P.t ∧ P.t ≤ P.x ^ e ∧
  P.x ^ 4 + 1 ≤ (P.p₀ : ℝ) ∧ (P.p₀ : ℝ) ≤ P.x ^ e ∧
  0 ≤ P.La ∧ P.La ≤ P.x ^ (2 * P.ε) ∧
  0 ≤ P.rG ∧ P.rG ≤ P.x ^ e ∧
  0 ≤ P.Sc ∧ P.Sc ≤ Real.exp (P.x ^ (P.ε / 4)) ∧ 0 ≤ P.η ∧ P.η ≤ Real.exp (P.x ^ (P.ε / 4)) ∧
  0 ≤ P.ρ ∧ P.ρ ≤ (P.x ^ 2)⁻¹ ∧
  0 ≤ P.th ∧ P.th ≤ P.x⁻¹ ∧
  P.x ^ 2 ≤ P.K₀ ∧ P.x ^ 2 ≤ (P.d : ℝ) ∧
  0 ≤ P.C ∧ P.C ≤ K ∧ 0 ≤ P.Cord ∧ P.Cord ≤ K ∧
  1 ≤ P.Y ∧ P.Y ≤ 2 * P.Xp ∧
  0 ≤ P.bo ∧ P.bo ≤ Real.exp (P.x ^ P.ε / 2)

def WindowsDIff : Prop :=
  ∀ (P : Par) (e K : ℝ), WindowsD P e K ↔ Windows (clr P) e K

def WindowsDOf : Prop :=
  ∀ (P : Par) (e K : ℝ), Windows P e K → WindowsD P e K

variable {ι κ τ : Type}

def lhsW (cand : Finset ℕ) (θ : ℝ) (Sig : ℕ → ℝ) : ℝ :=
  ∑ p ∈ cand, Real.log p / p * ((if θ < Sig p then 2 else 0) + 4 * Sig p)

def badPrimeLogWeightedCount (PR : Finset ℕ) (TT : Finset τ) (BAD : ℕ → τ → Prop) : ℝ :=
  ∑ p ∈ PR, Real.log p / p * ((TT.filter fun t => BAD p t).card : ℝ)

def OutD : Prop :=
  ∀ (τ : Type) (Ps PR : Finset ℕ) (cl : ℕ → PClass) (TT : Finset τ) (TTp : ℕ → Finset τ) (BAD : ℕ → τ → Prop)
    (m a R : ℝ), 0 ≤ m → 0 ≤ a → badPrimeLogWeightedCount PR TT BAD ≤ R →
    (∀ p ∈ Ps, cl p = PClass.served → ∀ t ∈ TT \ TTp p, p ∈ PR ∧ BAD p t) →
    ∑ p ∈ Ps.filter (fun p => cl p = PClass.served), 4 * m * a * (Real.log p / p) * ((TT \ TTp p).card : ℝ) ≤
      4 * a * m * R

def SecondD : Prop :=
  ∀ (Ps cand : Finset ℕ) (cl : ℕ → PClass) (Sig : ℕ → ℝ) (θ m T a R : ℝ), 0 ≤ m → 0 ≤ T → 0 ≤ a →
    (∀ p ∈ cand, 0 ≤ Sig p) → lhsW cand θ Sig ≤ R →
    (∀ p ∈ Ps, cl p = PClass.second → p ∈ cand ∧ θ < Sig p) →
    4 * m * T * a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.second), Real.log p / p) ≤ 2 * a * m * T * R

def IoD : Prop :=
  ∀ (cand : Finset ℕ) (Sig io : ℕ → ℝ) (θ m T a R : ℝ), 0 ≤ m → 0 ≤ T → 0 ≤ a → lhsW cand θ Sig ≤ R →
    (∀ p ∈ cand, io p ≤ 2 * Sig p * (2 * (m * T * a) / p)) →
    ∑ p ∈ cand, Real.log p * io p ≤ a * m * T * R

def tOutD (P : Par) (m T : ℝ) : ℝ := 4 * P.a * m * (T * P.x ^ (-2 + P.ε))

def tSecondD (P : Par) (m T : ℝ) : ℝ := 2 * P.a * m * T * (P.x ^ 9)⁻¹

def tIoD (P : Par) (m T : ℝ) : ℝ := P.a * m * T * (P.x ^ 9)⁻¹

def tDetD (P : Par) (m T : ℝ) : ℝ :=
  tFloors P m + tCp P m T + tPrLow P m T + tPrHigh P m T + tOr P m T + tOutD P m T + tOrders P m T
    + tBand P m T + tHigh P m T + tD P m T + tSecondD P m T

def ExplicitSizeBoundUnderWindows : Prop :=
  ∀ (P : Par) (e K m T : ℝ), WindowsD P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tDetD P m T ≤ (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P m T

def PrimeClassLossHypotheses (P : Par) {U : Type} (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ) : Prop :=
  TT.Nonempty ∧ (∀ p ∈ Ps, p.Prime ∧ p ≠ 2) ∧ (∀ p ∈ cand, 0 ≤ Sig p) ∧
  lhsW cand P.θ Sig ≤ (P.x ^ 9)⁻¹ ∧
  badPrimeLogWeightedCount PR TT BAD ≤ (TT.card : ℝ) * P.x ^ (-2 + P.ε) ∧
  (∀ υ, ∀ p ∈ cand, io υ p ≤ 2 * Sig p * (2 * ((J.card : ℝ) * TT.card * P.a) / p)) ∧
  (∀ υ, ParametersHyp P Ps J TT (D υ) ∧ FirstHyp P Ps (D υ).cl ∧
    (∀ p ∈ Ps, (D υ).cl p = PClass.second → p ∈ cand ∧ P.θ < Sig p) ∧
    (∀ p ∈ Ps, (D υ).cl p = PClass.served → ∀ t ∈ TT \ (D υ).TTp p, p ∈ PR ∧ BAD p t))

def ExcessAndPrimeLogSumUnitBounds (P : Par) {U : Type} (Ps cand : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (io : U → ℕ → ℝ) (D : U → LD ι κ τ) : Prop :=
  (∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤ (3 * P.C + 13) * unitU P J.card TT.card) ∧
  ∀ υ, ∑ p ∈ cand, Real.log p * io υ p ≤ unitU P J.card TT.card

def ExplicitLossAndPrimeLogSumBounds (P : Par) (K : ℝ) {U : Type} (Ps cand : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (io : U → ℕ → ℝ) (D : U → LD ι κ τ) : Prop :=
  (∀ υ, (D υ).ASK P.d Ps J TT - (D υ).Ga J ≤ (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P J.card TT.card) ∧
  ∀ υ, ∑ p ∈ cand, Real.log p * io υ p ≤ sg P K * unitU P J.card TT.card

def LossBoundsUnderSizeWindows : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → WindowsD P e K → LargeX P.x P.ε e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D → ExcessAndPrimeLogSumUnitBounds P Ps cand J TT io D

def LossBoundsEventually : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε e K : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₀ : ℝ,
    ∀ (P : Par), P.ε = ε → P.Cord = Cord → x₀ ≤ P.x → WindowsD P e K →
    ∀ (ι κ τ U : Type) (Ps cand PR : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → ℝ) (io : U → ℕ → ℝ) (D : U → LD ι κ τ),
      PrimeClassLossHypotheses P Ps cand PR J TT BAD Sig io D → ExcessAndPrimeLogSumUnitBounds P Ps cand J TT io D



end

end Formalism.LFunctionChainParameters.SmallOrderPrimeLosses
end
