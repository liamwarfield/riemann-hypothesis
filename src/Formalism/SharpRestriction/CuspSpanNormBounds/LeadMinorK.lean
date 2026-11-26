module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliarySlotStates

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.ThB

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.BasicNotions

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

def IsCloud {n k : ℕ} (u : Fin k → ℝ) (lam : Fin n → ℝ) (s : Fin n) : Prop :=
  (∃ i, lam s < u i) ∧ (∃ i, u i < lam s)

def ShapeS {n k : ℕ} (u : Fin k → ℝ) (lam : Fin n → ℝ) (bv : ℝ) : Prop :=
  ∀ s, (IsCloud u lam s → 0 ≤ lam s ∧ lam s ≤ bv / 8) ∧
    (¬ IsCloud u lam s → -2 * bv ≤ lam s ∧ lam s ≤ -bv)

def AllGaps {n : ℕ} (lam : Fin n → ℝ) (g : ℝ) : Prop := ∀ s s', s ≠ s' → g ≤ |lam s - lam s'|

def HasSeparatingGap {n k : ℕ} (u : Fin k → ℝ) (lam : Fin n → ℝ) (L : ℝ) : Prop :=
  ∃ (l : ℕ) (h : l + 1 < k), L ≤ u ⟨l, by omega⟩ - u ⟨l + 1, h⟩ ∧
    (∃ s, IsCloud u lam s ∧ u ⟨l, by omega⟩ ≤ lam s) ∧ (∃ s, IsCloud u lam s ∧ lam s ≤ u ⟨l + 1, h⟩)

def HasCut {k : ℕ} (u u' : Fin k → ℝ) (L : ℝ) : Prop :=
  ∃ a b : ℝ, IsCutS u u' (Set.Icc a b) ∧ L ≤ b - a

def StdHyp (Ch Cg : ℝ) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (u u' : Fin k → ℝ) (T T' ka b : ℝ) : Prop :=
  IsHCParam lam ∧ InterlaceS (by omega) u lam ∧ InterlaceS (by omega) u' lam ∧
  0 < ka ∧ ka ≤ b ^ Ch ∧ ka⁻¹ ≤ b ^ Ch ∧
  1 ≤ T ∧ 1 ≤ T' ∧ T ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ∧ T' ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ∧
  (∀ s, |lam s| ≤ b) ∧ (∀ i, |u i| ≤ b) ∧ (∀ i, |u' i| ≤ b) ∧
  AllGaps lam (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3) ∧
  GapAtLeast ε lam (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
  (∃ bv : ℝ, Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧ ShapeS u lam bv) ∧
  ((u = u' ∧ HasSeparatingGap u lam (2 * (Cg * ((r : ℝ) + 1) ^ 2) + 1)) ∨ (u ≠ u' ∧ HasCut u u' (Cg * ((r : ℝ) + 1) ^ 2)))

def StdHyp0 (Ch Cg : ℝ) (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (lam : Fin (2 * r + k + 1) → ℝ) (u u' : Fin k → ℝ) (T T' ka b : ℝ) : Prop :=
  IsHCParam lam ∧ InterlaceS (by omega) u lam ∧ InterlaceS (by omega) u' lam ∧
  0 < ka ∧ ka ≤ b ^ Ch ∧ ka⁻¹ ≤ b ^ Ch ∧
  1 ≤ T ∧ 1 ≤ T' ∧ T ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ∧ T' ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ)) ∧
  (∀ s, |lam s| ≤ b) ∧ (∀ i, |u i| ≤ b) ∧ (∀ i, |u' i| ≤ b) ∧
  AllGaps lam (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3) ∧
  GapAtLeast ε lam (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
    (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ∧
  (∃ bv : ℝ, Cg * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv ∧ ShapeS u lam bv) ∧
  (u = u' → HasSeparatingGap u lam (2 * (Cg * ((r : ℝ) + 1) ^ 2) + 1))

theorem StdHyp.to0 {Ch Cg : ℝ} {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {u u' : Fin k → ℝ} {T T' ka b : ℝ} (h : StdHyp Ch Cg k r ε lam u u' T T' ka b) :
    StdHyp0 Ch Cg k r ε lam u u' T T' ka b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, fun e => ?_⟩
  rcases h17 with h | h
  · exact h.2
  · exact absurd e h.1

def LocOk (D : D7) (Ch Cg : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ) : Prop :=
  1 ≤ D.R.k ∧ L.ε = epsSH D.R ∧ L.c = cOfDpsi (κ : ℂ) ∧ 0 < L.κN ∧ L.κN ≠ ⊤ ∧
    StdHyp Ch Cg D.R.k D.R.rS L.ε lam0 L.u L.u' (Tz D.R.k D.R.rS L.z * (κ / ka) ^ (2 * D.R.rS))
      (Tz D.R.k D.R.rS L.z' * (κ / ka) ^ (2 * D.R.rS)) ka b ∧
    1 ≤ Tz D.R.k D.R.rS L.z * κ ^ (2 * D.R.rS) ∧ 1 ≤ Tz D.R.k D.R.rS L.z' * κ ^ (2 * D.R.rS)

def LocOk0 (D : D7) (Ch Cg : ℝ) (L : LocBessel D.R.k D.R.rS) (lam0 : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (ka b κ : ℝ) : Prop :=
  1 ≤ D.R.k ∧ L.ε = epsSH D.R ∧ L.c = cOfDpsi (κ : ℂ) ∧ 0 < L.κN ∧ L.κN ≠ ⊤ ∧
    StdHyp0 Ch Cg D.R.k D.R.rS L.ε lam0 L.u L.u' (Tz D.R.k D.R.rS L.z * (κ / ka) ^ (2 * D.R.rS))
      (Tz D.R.k D.R.rS L.z' * (κ / ka) ^ (2 * D.R.rS)) ka b ∧
    1 ≤ Tz D.R.k D.R.rS L.z * κ ^ (2 * D.R.rS) ∧ 1 ≤ Tz D.R.k D.R.rS L.z' * κ ^ (2 * D.R.rS)

def jNorm2 {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ENNReal :=
  jNormSq k r (Tz k r L.z) (Tz k r L.z') (fun p => Real.sqrt (hsNormSq (L.J F (bigCell k r p.1 (μsec p.2)))))

def Gpt {r : ℕ} (T T' : ℝ) (γ : Point ℂ (r + 1)) : ℝ :=
  Complex.normSq (leadMinor (ptMat γ) (r + 1) le_rfl) -
    T * T' * Complex.normSq (leadMinor (ptMat γ) r (Nat.le_succ r))

def orbSq {k r : ℕ} (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) : ENNReal :=
  ⨆ (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r))
    (_ : IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν),
    ENNReal.ofReal (hsNormSq (OrbInt L F g ν))

def hNC {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) : ℝ :=
  sInf {x | ∃ a b : Fin n, ε a ≠ ε b ∧ x = |lam a - lam b|}

def cloudGap {n k : ℕ} (u : Fin k → ℝ) (lam : Fin n → ℝ) : ℝ :=
  sInf {x | ∃ a b : Fin n, a ≠ b ∧ IsCloud u lam a ∧ IsCloud u lam b ∧ x = |lam a - lam b|}

def q0 {n k : ℕ} (Cq : ℝ) (m : ℕ) (ε : Fin n → Bool) (u : Fin k → ℝ) (lam : Fin n → ℝ) : ℝ :=
  min (hNC ε lam / (Cq * Real.sqrt m)) (cloudGap u lam) / Cq

def l1 {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ a, |x a - y a|

def shell {k r : ℕ} (L : LocBessel k r) (P : Mx k r) (j : ℕ) : Submodule ℂ L.Hs :=
  Submodule.span ℂ {v | ∃ (Λ' ν : Fin (2 * r + k + 1) → ℝ) (S : Submodule ℂ L.Hs),
    IsKTypeOf L.ε (fun g => L.σ (P⁻¹ * g * P)) Λ' S ∧ v ∈ S ∧
      IsWtOn (Formalism.REAL.Kset L.ε) (fun g => L.σ (P⁻¹ * g * P)) ν v ∧
      l1 Λ' (lowK L.ε L.lam) ≤ j ∧ l1 ν (lowK L.ε L.lam) ≤ j}

def frob {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j))

section Glob

variable (D : D7)

def leadMinorK {K : Type*} [CommRing K] {N : ℕ} (A : Matrix (Fin N) (Fin N) K) (l : ℕ) (hl : l ≤ N) : K :=
  (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def blockEnds : ℕ → List (D.host.E × ℕ) → List ℕ
  | _, [] => []
  | acc, (_, s) :: bs => (acc + s) :: blockEnds (acc + s) bs

def ptLoc (v : D.what₂.Tau) {i : ℕ} (γ : Point D.host.E i) : Point ℂ i :=
  ptLocS D (rhoReal D) (rhoReal_ne D) v γ

def Gglob (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) : D.host.E :=
  leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl * D.host.conj (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl) -
    (T : D.host.E) * (T' : D.host.E) *
      (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _) * D.host.conj (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _)))

def IsBPt (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) : Prop :=
  (∃ Z : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E, (∀ i j, IsIntegral ℤ (Z i j)) ∧ IsInCell Z γ) ∧
    Gglob D T T' γ ≠ 0 ∧ IsIntegral ℤ (Gglob D T T' γ)

def absV (v : D.what₂.Tau) (x : D.host.E) : ℝ := ‖plEmb D v x‖

def wPt (γ : Point D.host.E (D.R.rS + 1)) : ℝ :=
  ((blockEnds D 0 γ.1).map fun l =>
    if hl : l ≤ D.R.rS + 1 then ∏ v, (1 + absV D v (leadMinorK (ptMat γ) l hl) ^ 2) ^ 2 else 1).prod

def NE (x : D.host.E) : ℝ := ∏ v, absV D v x ^ 2

def NF (x : D.host.E) : ℝ := ∏ v, absV D v x

def normWt (T T' : ℕ) (γ : Point D.host.E (D.R.rS + 1)) : ℝ :=
  NF D (Gglob D T T' γ) * ((blockEnds D 0 γ.1).map fun l =>
    if hl : l ≤ D.R.rS + 1 then NE D (leadMinorK (ptMat γ) l hl) else 1).prod

def kaRe : ℝ := D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))

structure BData (Ch Cg : ℝ) (T T' : ℕ) (b dist : ℝ) where
  L : D.what₂.Tau → LocBessel D.R.k D.R.rS
  f : ∀ v, Mx D.R.k D.R.rS → ((L v).Wq →L[ℂ] (L v).Wp)
  μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ
  hL : ∀ v, LocOk D Ch Cg (L v) (lamSH D.R (D.hc v)) (kaRe D) b (kaRe D)
  hnear : ∀ v, l1 (L v).lam (lamSH D.R (D.hc v)) ≤ dist
  hcoef : ∀ v, IsKFinCoefH (L v).σ (f v)
  hsec : ∀ v, IsSection D.R.k D.R.rS (L v).z (L v).z' (μsec v)
  hT : ∀ v, Tz D.R.k D.R.rS (L v).z = T ∧ Tz D.R.k D.R.rS (L v).z' = T'

def jSqG {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist) : ENNReal :=
  ∏ v, jNorm2 (X.L v) (X.f v) (X.μsec v)

end Glob

structure TensorDS (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) where
  Sm : Finset (Fin n)
  Hs : Fin n → Type
  [nH : ∀ s, NormedAddCommGroup (Hs s)]
  [iH : ∀ s, InnerProductSpace ℂ (Hs s)]
  [cH : ∀ s, CompleteSpace (Hs s)]
  σs : ∀ s, Matrix (Fin n) (Fin n) ℂ → (Hs s →L[ℂ] Hs s)
  ds : ∀ s ∈ Sm, IsHCParam (μ + Pi.single s 1) ∧ IsDS ε (μ + Pi.single s 1) (σs s)
  inequiv : ∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ¬ ∃ U : Hs s ≃ₗᵢ[ℂ] Hs s',
    ∀ g ∈ UJset ε, ∀ x, U (σs s g x) = σs s' g (U x)
  toSum : ∀ (v w : H) (x y : Fin n → ℂ), IsKFin ε σ v → IsKFin ε σ w →
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hs (sI i)),
      (∀ i, sI i ∈ Sm ∧ IsKFin ε (σs (sI i)) (vI i) ∧ IsKFin ε (σs (sI i)) (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σ g v⟫_ℂ * (star y ⬝ᵥ (g *ᵥ x)) = ∑ i, ⟪wI i, σs (sI i) g (vI i)⟫_ℂ
  ofSum : ∀ s ∈ Sm, ∀ v w : Hs s, IsKFin ε (σs s) v → IsKFin ε (σs s) w →
    ∃ (ι : Type) (_ : Fintype ι) (vI wI : ι → H) (xI yI : ι → Fin n → ℂ),
      (∀ i, IsKFin ε σ (vI i) ∧ IsKFin ε σ (wI i)) ∧
      ∀ g ∈ UJset ε, ⟪w, σs s g v⟫_ℂ = ∑ i, ⟪wI i, σ g (vI i)⟫_ℂ * (star (yI i) ⬝ᵥ (g *ᵥ xI i))

attribute [instance] TensorDS.nH TensorDS.iH TensorDS.cH

def BpIneq (D : D7) (Cb : ℝ) (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (b : ℝ) (γ : Point ℂ (D.R.rS + 1)) : Prop :=
  ENNReal.ofReal (ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) * orbSq L f γ ≤
    ENNReal.ofReal (b ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4) *
        (max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ)) ^ (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2)) *
      jNorm2 L f μsec

end Formalism.MainNotions.S.ThB
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
noncomputable section

namespace Formalism.MainNotions.S

open Formalism.BasicNotions NumberField IsDedekindDomain

variable (D : D7)

def vOne (τ : D.what₂.Tau) (l : ℕ) : ℝ :=
  if h : 1 ≤ l ∧ l ≤ D.R.k - 1 then ((D.hc τ).v ⟨l - 1, by omega⟩ : ℝ) else 0

def bOne (τ : D.what₂.Tau) (j : ℕ) : ℝ :=
  if h : 1 ≤ j ∧ j ≤ D.R.m then ((D.hc τ).b ⟨j - 1, by omega⟩ : ℝ) else 0

def uS (u : D.what₂.Word) (τ : D.what₂.Tau) : Fin D.R.k → ℝ := fun i => ((D.hcW u τ).u i : ℝ)

def uOne (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ D.R.k then uS D u τ ⟨i - 1, by omega⟩ else 0

def IsTop (τ : D.what₂.Tau) : Prop :=
  ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t

def bTop (τ : D.what₂.Tau) : ℝ := -uOne D D.u₀ τ D.R.k

def gg : ℝ := (D.host.g 0 : ℝ) * D.host.g 1

def typedPl : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {p | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}

abbrev SplitsE (p : ℕ) : Prop := SplitsCompl D.host.E p

def VV (τ : D.what₂.Tau) : ℝ := D.dsig τ * ∏ i ∈ Finset.range D.R.r, (i.factorial : ℝ)

def Tcrit (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  (D.host.ka ^ (-(((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2)) *
    D.host.rdE ^ (-(((D.R.m : ℝ) - 1) / 2)) *
    gg D ^ ((D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2) *
    VV D τ / vand (uS D u τ)) ^ ((1 : ℝ) / D.R.k)

def Tr (u : D.what₂.Word) : ℝ := ((D.mem u).A.T : ℝ)

def tV (u u' : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  Real.sqrt (Tcrit D u τ * Tcrit D u' τ / (Tr D u * Tr D u'))


open Classical in
def aEff (u : D.what₂.Word) (τ : D.what₂.Tau) : ℝ :=
  if IsTop D τ then uOne D u τ 1 * bTop D τ / ((D.R.k : ℝ) * D.s.Del) else uOne D u τ 1 - vOne D τ 1

def gaG : ℝ :=
  ∏ᶠ p ∈ typedPl D, ∏ i ∈ Finset.Icc 1 D.R.k, ((Ideal.absNorm p.asIdeal : ℝ) ^ i - 1)


open Classical in
def genScal (u u' : D.what₂.Word) : ℝ :=
  (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) * gaG D *
    (∑' P : D.s.Pair u u',
      if Formalism.MainNotions.S.scalarP D.s P ∧
          D.s.Gterm (D.s.pfst P) ≠ 0 ∧ D.s.Gterm (D.s.psnd P) ≠ 0
      then D.s.pval P else 0).re

def IsSat {u u' : D.what₂.Word} (Φ : Set (D.s.Term u u')) : Prop :=
  Φ = famG D.s ∨ Φ = famNG D.s ∨ Φ = {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t} ∨
    Φ = {t | D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def StandingNumericalData (C0 : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let Del : ℝ := D.s.Del
  (∀ τ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l ∧ vOne D τ l ≤ 4 * k * Del) ∧
  (∀ u (l : ℕ), 1 ≤ l → l ≤ D.R.k - 2 →
    (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2) ∨ (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2 - Del)) ∧
  (∀ u τ, 4 * k * Del ≤ uOne D u τ 1 - vOne D τ 1) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ 1 - vOne D τ 1 ≤ 8 * k * Del) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) ∧
  (∀ τ, IsTop D τ → 3 ≤ bOne D τ 1 - bTop D τ ∧ bOne D τ 1 / 2 ≤ bTop D τ) ∧
  (∀ u τ, InterlaceS (show D.R.k ≤ D.R.r by have := D.R.two_le_m; unfold Formalism.BasicNotions.Ranks.r; omega)
    (uS D u τ) (lamS D.R (D.hc τ))) ∧
  (∀ u u', u ≠ u' → ∀ τ, uS D u τ ≠ uS D u' τ) ∧
  (∀ u, SplitsE D (D.mem u).A.T ∧
    (D.mem u).A.T % (D.host.g 0 * D.host.g 1) ^ 2 = 1 % (D.host.g 0 * D.host.g 1) ^ 2) ∧
  (∀ u, (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar / C0 ≤ (D.duS u : ℝ) ∧
    (D.duS u : ℝ) ≤ (D.mem u).A.GamP ^ (-2 : ℤ) * D.what₂.Dstar * C0) ∧
  SplitsE D (D.host.g 0) ∧ SplitsE D (D.host.g 1) ∧

  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  (∀ u, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)

def StandingHypotheses (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let m : ℝ := D.R.m
  let f : ℝ := D.R.f
  let n : ℝ := D.R.r
  let r : ℝ := D.R.rS
  let L : ℝ := large₂.sc.L
  let b : ℝ := large₂.sc.b
  let Del : ℝ := D.s.Del
  let g1 : ℝ := D.host.g 0
  let g2 : ℝ := D.host.g 1
  8 * large₂.CGam ≤ C' ∧ C' * m ^ 5 * f * L ≤ k ∧
  D.R.m ^ 4 ≤ D.R.f ∧ D.R.f ≤ D.R.k ∧
  Real.log f ≤ Real.sqrt r ∧
  Cl * L ≤ f * Real.log k ∧
  Cl * (m ^ 2 * L) ≤ k ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → Cl * (m * k * Del) ≤ bOne D τ j) ∧
  Cl * (m * Real.log D.host.v) ≤ k ∧
  Cl * (m ^ 3 * L * Real.log D.host.rdE) ≤ k * Real.log k ^ 2 ∧
  Real.log D.host.rdE ≤ L / Cl ∧
  (k * b) ^ 8 ≤ g1 ∧ g1 ≤ b ^ Cg ∧ (k * b) ^ 8 ≤ g2 ∧ g2 ≤ b ^ Cg ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → max (k ^ Cl) (b ^ cb) ≤ bOne D τ j ∧ bOne D τ j ≤ b ^ (2 : ℝ)) ∧
  (∀ τ, bOne D τ D.R.m ≤ 2 * bOne D τ 1) ∧
  (∀ u τ, uOne D u τ 1 ≤ b ^ Cu) ∧
  1 ≤ D.host.v ∧
  (k * f * L) ^ Cl ≤ Del ∧
  (∀ τ j, 1 ≤ j → j + 1 ≤ D.R.m → Cl * n ^ 19 * f ^ 5 * L ≤ bOne D τ (j + 1) - bOne D τ j) ∧
  (∀ τ (i : Fin D.R.r) (h : i.1 + 1 < D.R.r),
    Cl * k * m ^ 4 + n * m ^ 10 < lamS D.R (D.hc τ) i - lamS D.R (D.hc τ) ⟨i.1 + 1, h⟩) ∧
  (∀ u, b ^ (cT * m) ≤ Tr D u ∧ Tr D u ≤ b ^ (CT * m)) ∧
  Cl ≤ m ∧ 0 < Cl

open scoped nonZeroDivisors

def eSum (Ce : ℝ) : ℝ :=
  Ce * ∑' p : HeightOneSpectrum (𝓞 D.host.F),
    (Ideal.absNorm p.asIdeal : ℝ) ^ (-((D.R.k : ℝ) - 2 * D.R.rS - 3))

def ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F)) :
    Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

def gE : D.host.E := ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E)

def IsLatGLOB (L : LatticeDataWithDual D) : Prop :=
  ∀ i s : ℕ,
    L.aaV i s = ddE D ^ (-((2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1)) + 1)) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹ ∧
    L.aaP i s = ddE D ^ (-(2 * ((D.R.rS : ℤ) + 1) - i - (i + s - 1))) *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (gE D))⁻¹ ∧
    L.ρ i s = rhoReal D i s

def IsLocA (u u' : D.what₂.Word) (x : D.what₂.Tau → LocalDataRealPlace D) : Prop :=
  ∀ τ, (x τ).lam = lamSH D.R (D.hc τ) ∧ (x τ).u = uS D u τ ∧ (x τ).u' = uS D u' τ

def NA : ℝ := 4 * 5 * ((D.R.rS : ℝ) + 1)

def ThA (CA : ℝ) (u u' : D.what₂.Word) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) : ℝ :=
  ThS D CA CA (NA D) (Tr D u) (Tr D u') (gE D) x L

def IsLocC (u u' : D.what₂.Word) (l : ℕ) (x : D.what₂.Tau → LocalDataRealPlace D) : Prop :=
  IsLocA D u u' x ∧ ∀ τ, (x τ).a = 5 / 2 - vOne D τ l ∧ (x τ).b = (D.s.Del : ℝ) / 2 - vOne D τ l ∧
    (x τ).a1 = 5 / 2 - vOne D τ l ∧ (x τ).b1 = NA D ^ 3 - vOne D τ l

end Formalism.MainNotions.S
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.WeightedMirrorLevelOperator
noncomputable section

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def Dr {r : ℕ} (x : Fin (r + 1) → ℂ) : ℂ := ∏ a : Fin r, cOf x a

def GG {r : ℕ} (T T' : ℝ) (x : Fin (r + 1) → ℂ) : ℂ := ((Complex.normSq (zOf x) - T * T' : ℝ) : ℂ)

def mulF {m : ℕ} (f : (Fin m → ℂ) → ℂ) : Op m E := fun φ x => f x • φ x

def mulE {m : ℕ} (e : (Fin m → ℂ) → E →L[ℂ] E) : Op m E := fun φ x => e x (φ x)

def one {m : ℕ} : Op m E := fun φ => φ

def vecT {m : ℕ} (M : Matrix (Fin 2) (Fin 2) (Op m E)) (v : Fin 2 → Op m E) : Fin 2 → Op m E :=
  fun a => ∑ b : Fin 2, M a b ∘ v b

def vv {r : ℕ} (Y : ℂ) : (i : ℕ) → i ≤ r → Fin 2 → Op (r + 1) E
  | 0, _ => ![one, 0]
  | i + 1, h => vecT (Tmat (⟨i, by omega⟩ : Fin (r + 1)) Y) (vv Y i (by omega))

def vvV {r : ℕ} (Y : ℂ) : (i : ℕ) → i ≤ r → Fin 2 → Op (r + 1) E
  | 0, _ => ![one, 0]
  | i + 1, h => vecT (TmatV (⟨i, by omega⟩ : Fin (r + 1)) Y) (vvV Y i (by omega))

def Ar (r : ℕ) (Y : ℂ) : Op (r + 1) E := vv Y r le_rfl 0

def Br (r : ℕ) (Y : ℂ) : Op (r + 1) E := vv Y r le_rfl 1

def ArV (r : ℕ) (Y : ℂ) : Op (r + 1) E := vvV Y r le_rfl 0

def BrV (r : ℕ) (Y : ℂ) : Op (r + 1) E := vvV Y r le_rfl 1

def Ahat (r : ℕ) (Y : ℂ) : Op (r + 1) E := mulF Dr ∘ Ar r Y

def AhatV (r : ℕ) (Y : ℂ) : Op (r + 1) E := mulF (fun x => star (Dr x)) ∘ ArV r Y

def Rhat (r : ℕ) (Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => star (Dr x)) ∘ (Q Y 1 0 ∘ Ar r Y + Q Y 1 1 ∘ Br r Y)

def dZ (r : ℕ) : Op (r + 1) E := wirt (Fin.last r)

def dZb (r : ℕ) : Op (r + 1) E := wirtBar (Fin.last r)

def nabla (r : ℕ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E := dZ r + mulE h

def l0 (r : ℕ) (T T' : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  -nabla r h - mulF (fun x => (Y + 1 / 2) * star (zOf x) / GG T T' x)

def m0 (r : ℕ) (T T' : ℝ) (hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  dZb r - mulE hs - mulF (fun x => (Y - 1 / 2) * zOf x / GG T T' x)

section Lines

variable {k0 : ℕ} {Rho : Type*}

def xFib {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, xPoly (ρp ρ) Y • P ρ x

def xInvFib {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) :
    (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, (xPoly (ρp ρ) Y)⁻¹ • P ρ x

def shInv {r : ℕ} (ρp : Rho → Fin k0 → ℝ) (P : Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E) (l : Fin k0)
    (Y : ℂ) : (Fin (r + 1) → ℂ) → E →L[ℂ] E :=
  fun x => ∑ᶠ ρ, (Y + (ρp ρ l : ℂ))⁻¹ • P ρ x

end Lines

def SSnat {r : ℕ} (s : (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Op (r + 1) E :=
  mulF (fun x => star (Dr x) / Dr x) ∘ mulE s

def R0 (r : ℕ) (T T' : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => star (Dr x) * GG T T' x) ∘ (l0 r T T' h Y ∘ Ar r Y + Br r Y)

def weightedMirrorLevelOperator (r : ℕ) (T T' : ℝ) (hs : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (Y : ℂ) : Op (r + 1) E :=
  mulF (fun x => Dr x * GG T T' x) ∘ (m0 r T T' hs Y ∘ ArV r Y + BrV r Y)

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

structure Base (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] where

  k0 : ℕ
  T : ℝ
  T' : ℝ
  u : Fin (k0 + 1) → ℝ
  u' : Fin (k0 + 1) → ℝ
  I : Set ℝ

  sgn : ℂ

  hs : E → E → ℂ

  fadj : (E →L[ℂ] E) → (E →L[ℂ] E)

  Rho : Type

  IsType : Rho → Prop

  rhoP : Rho → Fin k0 → ℝ

structure Ctx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Base E) (r : ℕ) where

  Dom : Set (Fin (r + 1) → ℂ)

  cls : Set ((Fin (r + 1) → ℂ) → E)

  clsF : Set ((Fin (r + 1) → ℂ) → E)

  beta : ((Fin (r + 1) → ℂ) → E) → ((Fin (r + 1) → ℂ) → E) → ℂ

  P : B.Rho → (Fin (r + 1) → ℂ) → E →L[ℂ] E

  Q : ℂ → Matrix (Fin 2) (Fin 2) (Op (r + 1) E)

  AA : Set (Op (r + 1) E)

  RR : (w : List (Bool × ℝ)) → Matrix (Fin w.length → Fin 2) (Fin w.length → Fin 2) (Op (r + 1) E)

  TT : (w : List (Bool × ℝ)) → ℂ →
    Matrix (Fin 2) (Fin 2) (Matrix (Fin w.length → Fin 2) (Fin w.length → Fin 2) (Op (r + 1) E))

  qw : List (Bool × ℝ) → ℂ → ℂ

  uw : (w : List (Bool × ℝ)) → (Fin w.length → Fin 2) → Op (r + 1) E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Ctx

variable {B : Base E} {r : ℕ} (C : Ctx B r)

def IsPlus (w : List (Bool × ℝ)) : Prop := ∀ a ∈ w, a.1 = true

end Ctx

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev GOp (n : ℕ) (E : Type*) := (Matrix (Fin n) (Fin n) ℂ → E) → Matrix (Fin n) (Fin n) ℂ → E

structure GCtx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (r : ℕ) where

  nV : ℕ

  Eop : Fin nV → Fin nV → GOp nV E

  H : Matrix (Fin nV) (Fin nV) ℂ

  eIdx : Fin r → Fin nV

  Rad : GOp nV E → Op (r + 1) E → Prop

  PolyInv : Set (GOp nV E)

namespace GCtx

variable {r : ℕ} (Γ : GCtx E r)

def cminor (n : ℕ) (hn : n ≤ r) (u : ℂ) : GOp Γ.nV E := fun f g =>
  ∑ b : Fin n → Fin Γ.nV, if StrictMono b then
    (Matrix.det (Matrix.of fun (a j : Fin n) =>
      herm Γ.H (g.mulVec (Pi.single (b j) 1)) (Pi.single (Γ.eIdx ⟨a, by omega⟩) 1))) •
      qminorOp Γ.Eop (fun a : Fin n => Γ.eIdx ⟨a, by omega⟩) b u f g
  else 0

end GCtx

def DnVn {r : ℕ} (n : ℕ) (hn : n ≤ r) (Y : ℂ) (i : Fin 2) : Op (r + 1) E :=
  mulF (fun x => ∏ a : Fin n, cOf x ⟨a, by omega⟩) ∘ vv Y n hn i

def NoPoleRho (B : Base E) (Y : ℂ) : Prop := ∀ ρ : B.Rho, B.IsType ρ → ∀ l : Fin B.k0, Y + (B.rhoP ρ l : ℂ) ≠ 0

namespace Ctx

variable {B : Base E} {r : ℕ} (C : Ctx B r)

end Ctx

namespace Ctx

section Shape

variable {B : Base E} {r : ℕ} {C : Ctx B r} {SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E} {b : Bool}

end Shape

end Ctx

def prW (k : ℕ) (zb : Fin (k + 1) → ℂ) (v : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ :=
  v - (herm (Hb k) v zb / herm (Hb k) zb zb) • zb

def bordDet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) : ℂ :=
  Matrix.det (Matrix.of fun (a b : Fin (r + 1)) =>
    herm (Hpk k r) (Matrix.mulVec g (fvec k r z' b)) (if a = Fin.last r then w else fvec k r z a))

def omG (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  prW k (wbPart k r z) (fun j => Hb k j j * bordDet k r z z' g (bvec (wI k r j)))

def omG' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Fin (k + 1) → ℂ :=
  omG k r z' z (Hpk k r * g.conjTranspose * Hpk k r)

def evG {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) : ℂ :=
  MvPolynomial.eval (Sum.elim (fun ij => g ij.1 ij.2) (fun ij => star (g ij.1 ij.2))) p

end Formalism.MainNotions.S.LevR

noncomputable section

set_option linter.unusedVariables false

namespace Formalism.MainNotions.S.LevR

open Formalism.QuantumDeterminants
open Formalism.MainNotions.S.TopsChoicePartA

end Formalism.MainNotions.S.LevR
end
end
end
end
end
