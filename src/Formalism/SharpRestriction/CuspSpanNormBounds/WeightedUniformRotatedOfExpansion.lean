module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
public import Formalism.SharpRestriction.CuspSpanNormBounds.StarVecMulDM

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.WeightedUniformRotatedOfExpansion
noncomputable section

open Finset

namespace Formalism.MainNotions.RotatedPoints

open MeasureTheory Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.S.Pv.Frames

section R

variable (D : D7)

def JSqR {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (γ : Point D.host.E (D.R.rS + 1)) : ENNReal :=
  ∏ v, orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ))

def BSumR {Ch Cg : ℝ} {T T' : ℕ} {b dist : ℝ} (X : BData D Ch Cg T T' b dist)
    (W : Point D.host.E (D.R.rS + 1) → ℝ) : ENNReal :=
  ∑' γ : {γ : Point D.host.E (D.R.rS + 1) // IsBPt D T T' γ},
    ENNReal.ofReal (wPt D γ.1 * ptWeightG D (rhoReal D) T T' γ.1.1 * W γ.1) * JSqR D X γ.1

def theoremBRotated (Aw Ch Cg Cb : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b 0),
    (∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) →
    BSumR D X (fun γ => normWt D T T' γ ^ (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) ≤
      ENNReal.ofReal (Real.exp (Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 * (Fintype.card D.what₂.Tau : ℝ) * Real.log b)) *
        jSqG D X

def OnePlaceR (Ch Cg dist : ℝ) (P : ∀ (T T' : ℕ) (b : ℝ), BData D Ch Cg T T' b dist → Prop) (A : ℕ) (CK : ℝ) (e : ℕ)
    (p : ℝ) : Prop :=
  ∀ (T T' : ℕ) (b : ℝ) (X : BData D Ch Cg T T' b dist), P T T' b X →
    ∀ γ : Point D.host.E (D.R.rS + 1), IsBPt D T T' γ → ∀ v,
    ENNReal.ofReal (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p) *
        orbSq (X.L v) (X.f v) (turnPt (ptLoc D v γ)) ≤
      ENNReal.ofReal (b ^ (CK * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ e) *
          max 1 (1 / absV D v (Gglob D T T' γ)) ^ A) * jNorm2 (X.L v) (X.f v) (X.μsec v)

variable {D}

theorem weighted_bound_rotated_of_one_place {Aw Ch Cg CK : ℝ} {A : ℕ} (hCg : 2 ≤ Cg)
    (hO : OnePlaceR D Ch Cg 0 (fun _ _ _ X => ∀ v, AllGaps (X.L v).lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) A CK 5
      (Aw * ((D.R.rS : ℝ) + 1) ^ 2)) : theoremBRotated D Aw Ch Cg (CK + 6) := by
  exact Formalism.MainNotions.BesselShellMomentBounds.theorem_B_weighted_bound_one_place (D := D) hCg hO

variable (D)

def PlaceOKR (Ch Cg : ℝ) (T T' : ℕ) (b dist : ℝ) (v : D.what₂.Tau) (L : LocBessel D.R.k D.R.rS)
    (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) : Prop :=
  LocOk D Ch Cg L (lamSH D.R (D.hc v)) (kaRe D) b (kaRe D) ∧ l1 L.lam (lamSH D.R (D.hc v)) ≤ dist ∧
    IsKFinCoefH L.σ f ∧ IsSection D.R.k D.R.rS L.z L.z' μsec ∧
    Tz D.R.k D.R.rS L.z = T ∧ Tz D.R.k D.R.rS L.z' = T'

variable {D}

end R

def WeightedBoundRotatedUniform : Prop :=
  ∀ Aw Ch : ℝ, 0 ≤ Aw → ∃ Cb Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, theoremBRotated D Aw Ch Cg Cb

end Formalism.MainNotions.RotatedPoints
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory
noncomputable section

open NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.LatticeIndexAndWeightTheory

export Formalism.MainNotions.S.UnitaryVolumeMass (KTwoParameterConditions Kpp)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

end Hyps

def IsInertiaCyclotomicGeneratorElement {D : D7} {u u' : D.what₂.Word} (t : D.s.Term u u') : Prop :=
  D.s.relevant t ∧ D.s.Gterm t = 0 ∧ ¬ D.s.isId t

section TermObj

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')

def Iof : Submodule D.host.E (hS D).V := Isp (X.fl t).fl (X.fl' t).fl

def OrthogonalComplementV0 : Submodule D.host.E (hS D).V := perpS (hS D) (Xplus (X.fl t) ⊔ Xplus (X.fl' t))

def jOf : ℕ := D.R.rS - Module.finrank D.host.E (Iof X t)

def NDl (l : ℕ) : ℝ := (Nloc (ddS D) D.R.rS l (Dl (X.fl t).fl (X.fl' t).fl l) : ℝ)

def DelJ : ℝ := NDl X t (jOf X t)

def ends : Finset ℕ := blockEnds (X.fl t).fl (X.fl' t).fl (jOf X t)

def sg (H1 : ℝ) (τ : D.what₂.Tau) : ℝ :=
  (ends X t).fold max 1 (fun l =>
    absReal D.host.rdE (embS D τ) D.R.rS l (Dl (X.fl t).fl (X.fl' t).fl l) / (2 * H1) ^ (2 * D.R.rS))

def FrameHyp : Prop :=
  (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u ∧ IsRowLat D (X.fl t).fl (X.abelian₂ t) ∧
    FrameOK D (X.abelian₂ t) (X.fl' t)

end TermObj

def NF {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u') : Prop :=
  ∃ j : ℕ, j ≤ D.R.rS ∧ (u = u' → 1 ≤ j) ∧
    (∀ a : ℕ, (∃ x ∈ Iof X t, x ≠ 0 ∧ (X.fl t).fl.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ D.R.rS)) ∧
    (∀ a : ℕ, (∃ x ∈ Iof X t, x ≠ 0 ∧ (X.fl' t).fl.level x = a) ↔ (j + 1 ≤ a ∧ a ≤ D.R.rS)) ∧
    (∃ c : D.host.E, (X.fl' t).fl.z - c • (X.fl t).fl.z ∈ Xsp (X.fl t) ⊔ Xsp (X.fl' t) ∧
      c * star c * ((Tu D u : ℕ) : D.host.E) = ((Tu D u' : ℕ) : D.host.E)) ∧
    Dl (X.fl t).fl (X.fl' t).fl j ≠ 0 ∧
    (OrthogonalComplementV0 X t ⊓ Xsp (X.fl t) = Iof X t ∧ OrthogonalComplementV0 X t ⊔ Xsp (X.fl t) = (X.fl t).fl.XplusPerp) ∧
    (OrthogonalComplementV0 X t ⊓ Xsp (X.fl' t) = Iof X t ∧ OrthogonalComplementV0 X t ⊔ Xsp (X.fl' t) = (X.fl' t).fl.XplusPerp)

section Datum

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word}

def SameDC {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T') : Prop :=
  ∃ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
    (∀ a : Fin D.R.rS, σ (F.fl.e a) - F.fl.e a ∈ Xflag F a.val) ∧ σ F.fl.z - F.fl.z ∈ Xsp F ∧
    (∀ a : Fin D.R.rS, σ (F₁.fl.e a) - F₂.fl.e a ∈ Xflag F₂ a.val) ∧ σ F₁.fl.z - F₂.fl.z ∈ Xsp F₂

def TermInj (u : D.what₂.Word) : Prop :=
  ∀ t t' : D.s.Term u u, X.abelian₂ t = X.abelian₂ t' → TEqv D (X.abelian₂ t) (X.fl t) (X.fl' t) (X.fl' t') → t = t'

def NormOK (u : D.what₂.Word) : Prop :=
  (∀ p : D.s.Pair u u, X.wRow p = Formalism.MainNotions.S.wRow D (X.fl (D.s.pfst p)).fl (X.abelian₂ (D.s.pfst p))) ∧
  ∀ t : D.s.Term u u, IsInertiaCyclotomicGeneratorElement t → ∃ p : D.s.Pair u u, D.s.pfst p = t ∧ D.s.psnd p = t ∧
    X.beta p = LinearEquiv.refl D.host.E (hS D).V ∧
    D.s.pval p = ((Formalism.MainNotions.S.wRow D (X.fl t).fl (X.abelian₂ t) * hsNormSq (X.Jt t) : ℝ) : ℂ)

def IndW (D : D7) (σ : (hS D).V ≃ₗ[D.host.E] (hS D).V) (h : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) : Prop :=
  ∀ w, σ (D.sp.iXY 0 w) - D.sp.iXY 0 (h w) ∈ Submodule.span D.host.E (Set.range D.sp.hypE)

def AmpOK : Prop :=
  (∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), (X.fl t).fl.e = D.sp.hypE ∧ (X.fl t).fl.z = D.zmOf u) ∧
  ∃ (ρ : ∀ u : D.what₂.Word, ((D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V) → (X.Hpi u →L[ℂ] X.Hpi u))
    (δ : ∀ u u' : D.what₂.Word, D.s.Term u u' → ((hS D).V ≃ₗ[D.host.E] (hS D).V)),
    (∀ u, ρ u 1 = ContinuousLinearMap.id ℂ (X.Hpi u) ∧
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ρ u (h * h') = (ρ u h).comp (ρ u h')) ∧
    (∀ u (K : Submodule ℂ (X.Hpi u)), (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ x ∈ K, ρ u h x ∈ K) → K = ⊥ ∨ K = ⊤) ∧
    (∀ u u', u ≠ u' → ∀ P : X.Hpi u' →L[ℂ] X.Hpi u,
      (∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, (ρ u h).comp P = P.comp (ρ u' h)) → P = 0) ∧
    (∀ u u' (t : D.s.Term u u'), δ u u' t ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT ∧
      (∀ a, δ u u' t (D.sp.hypE a) = (X.fl' t).fl.e a) ∧ δ u u' t (D.zmOf u') = (X.fl' t).fl.z) ∧
    (∀ u u' (t : D.s.Term u u'), ∀ σ ∈ Formalism.HermitianLatticesTheory.isom (hS D).hT,
      (∀ x ∈ Xplus (X.fl t) ⊔ Xplus (X.fl' t), σ x = x) →
      ∀ h ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT, ∀ h' ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        IndW D σ h → IndW D ((δ u u' t)⁻¹ * σ * δ u u' t) h' → (ρ u h).comp (X.Jt t) = (X.Jt t).comp (ρ u' h')) ∧
    ∀ u (t : D.s.Term u u), IsInertiaCyclotomicGeneratorElement t → NF X t → ∀ x ∈ OrthogonalComplementV0 X t, δ u u t x - x ∈ Xsp (X.fl' t)

def TieOK (u : D.what₂.Word) : Prop :=
  (∀ t : D.s.Term u u, FrameHyp X t) ∧ TermInj X u ∧ NormOK X u ∧ AmpOK X

end Datum

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Terms

section Size

variable (D : D7) (large₂ : SizeData₂ D)

end Size

section Mass

variable (D : D7) (large₂ : SizeData₂ D)

end Mass

section Targets

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Targets

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

end Family

end Formalism.MainNotions.LatticeIndexAndWeightTheory

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
noncomputable section

namespace Formalism.MainNotions.AdmissibleBoundsFromSource

export Formalism.MainNotions.S.UnitaryVolumeMass (f3 Kpp)

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain
open scoped InnerProductSpace nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Letters

variable (D : D7) (large₂ : SizeData₂ D)

def Gam : ℝ := (D.mem D.u₀).A.GamP

def du (u : D.what₂.Word) : ℝ := D.duS u

def Dall : ℝ := D.what₂.Dall

def Dst : ℝ := D.what₂.Dstar

def eta0 : ℝ := large₂.sc.b ^ (-(6 : ℝ))

def xK : ℝ := Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))
end Letters

section Hyp

variable (D : D7) (large₂ : SizeData₂ D)

def hyp (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0

def DiagonalKernelBoundParameters (Cl Cg CT : ℝ) : Prop :=
  UnitaryVolumeMass.KTwoParameterConditions D large₂ Cl Cg CT

def WordPairStandingData (u u' : D.what₂.Word) : Prop :=
  1 ≤ D.R.rS ∧
  (Lat.Tu D u).Prime ∧ (Lat.Tu D u').Prime ∧ 3 ≤ Lat.Tu D u ∧ 3 ≤ Lat.Tu D u' ∧
  Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u) ∧ Lat.SplitsCompletely (E := D.host.E) (Lat.Tu D u') ∧
  (D.host.g 0).Prime ∧ (D.host.g 1).Prime ∧ D.host.g 0 ≠ D.host.g 1 ∧
  (∀ i, Lat.SplitsCompletely (E := D.host.E) (D.host.g i)) ∧
  Nat.Coprime (Lat.gS D) (Lat.Tu D u * Lat.Tu D u') ∧ Lat.Tu D u ≡ Lat.Tu D u' [MOD Lat.gS D]

def WordPairParameters (u u' : D.what₂.Word) (Cl A : ℝ) : Prop :=
  WordPairStandingData D u u' ∧
  Tr D u' / Tr D u ≤ A ∧ Tr D u / Tr D u' ≤ A ∧
  Cl * ((D.R.m : ℝ) ^ 6 * large₂.sc.L) ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  Real.log (D.R.f : ℝ) ^ 2 ≤ A * ((D.R.m : ℝ) ^ 2 * large₂.sc.L) ∧
  Real.log (D.R.f : ℝ) ≤ A * (D.R.rS : ℝ) ^ 2 ∧
  ∀ τ, vand (uS D u' τ) ≤ A ^ D.R.k * vand (uS D u τ) ∧ vand (uS D u τ) ≤ A ^ D.R.k * vand (uS D u' τ)

def CountTheoremHypotheses (n0 : ℕ) (A C cb : ℝ) : Prop :=
  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  n0 ≤ D.R.r ∧ (D.R.rS + 1) ^ 2 ≤ D.R.r ∧
  Real.log (Real.log D.host.rdE) ≤ (D.R.r : ℝ) ∧
  (∀ (τ : D.what₂.Tau) (i : Fin D.R.r), |lamS D.R (D.hc τ) i| ≤ large₂.sc.b ^ 2) ∧
  gg D ≤ large₂.sc.b ^ A ∧ 4 * D.R.r < D.host.g 0 ∧ SplitsE D (D.host.g 0) ∧
  (∀ τ : D.what₂.Tau, Formalism.QuantumDeterminants.GapAtLeast (epsS D.R) (lamS D.R (D.hc τ))
    (C * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * Real.log (large₂.sc.b * D.host.rdE))) ∧
  Real.log (D.R.f : ℝ) ≤ Real.sqrt (D.R.r : ℝ) ∧ 2 ≤ large₂.sc.b ∧
  Real.log (Real.log large₂.sc.b) ≤ cb * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)

end Hyp

structure AdmC where

  A5 : ℝ
  cL : ℝ

  cN : ℝ
  CN : ℝ

  CE : ℝ

  CA : ℝ
  CA' : ℝ
  Ce : ℝ

  n7 : ℕ
  A7 : ℝ
  C7 : ℝ
  cb7 : ℝ
  c7 : ℝ

  ep0 : ℝ
  CV : ℝ

  C1 : ℝ
  C2 : ℝ
  c5 : ℝ

section admitted

variable (D : D7) (large₂ : SizeData₂ D)

def adm1 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.cExp D

def adm2 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.cIdOne D

def adm3 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → DiagonalKernelBoundParameters D large₂ Cl Cg CT → UnitaryVolumeMass.cK2off D

def ArchimedeanSignatureMatching (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.c2aG D

def adm5 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → DiagonalKernelBoundParameters D large₂ Cl Cg CT →
    ∀ u : D.what₂.Word, hsNormSq (Kpp D u u) ≤ du D u * xK D

def adm6 (C0 C' Cl Cg cb Cu cT CT A c : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → ∀ u u' : D.what₂.Word, WordPairParameters D large₂ u u' Cl A → UnitaryVolumeMass.LoopPairSumBound D u u' c

def adm7 (C0 C' Cl Cg cb Cu cT CT c C : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.NonGenericKernelBound D large₂ c C

def adm8 (C0 C' Cl Cg cb Cu cT CT C : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → UnitaryVolumeMass.GenericScalarPairSum D large₂ C

def adm9 (C0 C' Cl Cg cb Cu cT CT CA CA' Ce : ℝ) : Prop :=
  let N : ℝ := NA D
  let r : ℝ := D.R.rS
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word, u ≠ u' → ∀ (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D),
    IsLocA D u u' x → IsLatGLOB D L →
    (∀ τ, IsCutS (uS D u τ) (uS D u' τ) (Set.Icc (x τ).a (x τ).b) ∧
      CA * ((D.R.k : ℝ) * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ (x τ).b - (x τ).a ∧
      (x τ).a ≤ (x τ).a1 ∧ (x τ).b1 ≤ (x τ).b ∧ N ^ 3 / 2 ≤ (x τ).b1 - (x τ).a1) →
    (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ) ≤ 1 → CA' ≤ ThA D CA u u' x L →
    genScal D u u' ≤ (1 + CA * (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ)) * (1 + eSum D Ce) *
      f3 D * du D u * du D u' / Dst D

def adm10 (n0 : ℕ) (A C cb c : ℝ) : Prop := CountTheoremHypotheses D large₂ n0 A C cb →
  |Dall D - Dst D| ≤ Real.exp (-(c * D.R.r * D.R.f * Real.log D.R.r)) * Dst D

def WeylDimensionFormula (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u τ, (dimPiU D.R.k (uS D u τ) : ℝ) = vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)

def FilteredProjectionCriterion (C0 C' Cl Cg cb Cu cT CT ep0 : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ τ, (1 - ep0) * vand (lamSH D.R (D.hc τ)) ≤ VV D τ

def VandermondeUpperBound (C0 C' Cl Cg cb Cu cT CT C : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ τ, VV D τ ≤ Real.exp (C * D.R.k * D.R.m * large₂.sc.L) * vand (lamSH D.R (D.hc τ))

def adm11 (C0 C' Cl Cg cb Cu cT CT ep0 C : ℝ) : Prop :=
  WeylDimensionFormula D large₂ C0 C' Cl Cg cb Cu cT CT ∧ FilteredProjectionCriterion D large₂ C0 C' Cl Cg cb Cu cT CT ep0 ∧
    VandermondeUpperBound D large₂ C0 C' Cl Cg cb Cu cT CT C

def adm12 : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

def adm13 (C0 C' Cl Cg cb Cu cT CT C1 C2 c5 CA : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  UnitaryVolumeMass.cTvA D ∧ UnitaryVolumeMass.cTvB D C1 ∧ UnitaryVolumeMass.cTvC D C2 ∧ UnitaryVolumeMass.cTvF D large₂ c5 CA

def adm14 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word,
    (∀ t : D.s.Term u u', ¬ D.s.relevant t → D.s.aTerm u u' t = 0) ∧
    (∀ t : D.s.Term u u', D.s.isId t → D.s.Gterm t = 0) ∧
    (∀ p : D.s.Pair u u', D.s.Gterm (D.s.pfst p) ≠ 0 → D.s.Gterm (D.s.psnd p) ≠ 0 → 1 ≤ D.s.s0 p)

def adm15 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ u u' : D.what₂.Word, Summable (fun p : D.s.Pair u u' => ‖D.s.pval p‖)

def fixAt (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    Submodule ℂ ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
  (D.mem u).A.Mu0 ⊓ ⨅ c : ((D.mem u).A.Fv v)ˣ, LinearMap.ker ((D.mem u).A.rhoT v c - LinearMap.id)

def adm16 (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop := hyp D large₂ C0 C' Cl Cg cb Cu cT CT →
  ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT), (Module.finrank ℂ (fixAt D u v) : ℝ) = du D u / (Tr D u - 1)

def Adm1 (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmC) : Prop :=
  adm1 D large₂ C0 C' Cl Cg cb Cu cT CT ∧ adm2 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm3 D large₂ C0 C' Cl Cg cb Cu cT CT ∧ ArchimedeanSignatureMatching D large₂ C0 C' Cl Cg cb Cu cT CT ∧ adm5 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm6 D large₂ C0 C' Cl Cg cb Cu cT CT ca.A5 ca.cL ∧ adm7 D large₂ C0 C' Cl Cg cb Cu cT CT ca.cN ca.CN ∧
    adm8 D large₂ C0 C' Cl Cg cb Cu cT CT ca.CE ∧ adm9 D large₂ C0 C' Cl Cg cb Cu cT CT ca.CA ca.CA' ca.Ce ∧
    adm11 D large₂ C0 C' Cl Cg cb Cu cT CT ca.ep0 ca.CV ∧ adm12 ∧
    adm13 D large₂ C0 C' Cl Cg cb Cu cT CT ca.C1 ca.C2 ca.c5 ca.CA ∧ adm14 D large₂ C0 C' Cl Cg cb Cu cT CT ∧
    adm15 D large₂ C0 C' Cl Cg cb Cu cT CT

def admitted (C0 C' Cl Cg cb Cu cT CT : ℝ) (ca : AdmC) : Prop :=
  Adm1 D large₂ C0 C' Cl Cg cb Cu cT CT ca ∧ adm10 D large₂ ca.n7 ca.A7 ca.C7 ca.cb7 ca.c7 ∧
    adm16 D large₂ C0 C' Cl Cg cb Cu cT CT

end admitted

section Conclusion₂

variable (D : D7) (large₂ : SizeData₂ D)

def Conclusion1 : Prop :=
  (∀ u u' : D.what₂.Word, u ≠ u' → Kpp D u u' = 0) ∧
  (∀ u, hsNormSq (Kpp D u u) ≤ du D u * xK D) ∧
  (∀ u u' : D.what₂.Word, u ≠ u' →
    hsNormSq (Kmat D.s u u' - Kpp D u u') ≤ (1 + eta0 D large₂) * du D u * du D u' / Dst D) ∧
  (∀ u, hsNormSq (Kmat D.s u u - Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) ≤
    Gam D * du D u ^ 2 / Dst D)

end Conclusion₂

structure GivC where
  C0 : ℝ
  Cg : ℝ
  cb : ℝ
  Cu : ℝ
  cT : ℝ
  CT : ℝ

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.AdmissibleBoundsFromSource
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.ChainLength
noncomputable section

namespace Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

section LocalTheory

open Formalism.MainNotions.S.Loc MeasureTheory ComplexConjugate


def FamilyVolumeFourth {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E) (r k n : ℕ) (C : ℝ) : Prop :=
  ∀ (ϖ : 𝒪[F]), Irreducible ϖ →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  (∀ (t : Term V M r), H.IsGeneric t →
    |H.dens ϖ t.abelian₂ (H.gram (H.MMfam t)) - 1| ≤
      C * (2 * (r : ℝ) + 2) * (Nat.card 𝓀[F] : ℝ) ^ (-((k : ℤ) - 2 * r - 2))) ∧
  (∀ (t₁ t₂ : Term V M r), H.IsGeneric t₁ → H.IsGeneric t₂ → H.IsScalarPair t₁ t₂ →
    H.dens ϖ t₁.abelian₂ (H.gram (H.MMfam t₁)) = H.dens ϖ t₂.abelian₂ (H.gram (H.MMfam t₂)))

end LocalTheory

def adm6 (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ U : ∀ p : PlF D, AddSubgroup (D.s.atP p).Ep, (∀ p, IsOpen (U p : Set (D.s.atP p).Ep)) →
    {p | (U p : Set (D.s.atP p).Ep) ≠ ((D.s.atP p).O : Set (D.s.atP p).Ep)}.Finite →
    ∀ x : ∀ p, (D.s.atP p).Ep, {p | x p ∉ (D.s.atP p).O}.Finite →
      ∃ t : D.host.E, ∀ p, (D.s.atP p).ιE t - x p ∈ U p

def adm7 (D : Formalism.BasicNotions.D7) : Prop :=
  (∀ M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep, (∀ p, (M p).OK) →
    ∀ x : D.host.E, x ≠ 0 →
      (Function.mulSupport fun p => (M p).modK ((D.s.atP p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹) ∧
  (∀ x : D.host.E,
    (Function.mulSupport fun p : PlF D => (D.s.atP p).psiE ((D.s.atP p).ιE x)).Finite ∧
    ∏ᶠ p : PlF D, (D.s.atP p).psiE ((D.s.atP p).ιE x) =
      Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ D.host.E x : ℚ) : ℂ))))

def Gfin (δ : ∀ p, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (T T' : ℕ) : Prop :=
  (∀ (n : ℕ) (w w' : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => locK M δ T T' p n w w').Finite) ∧
  (∀ (n : ℕ) (h : Point D.host.E n), n ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => detNrmP M δ T T' p h).Finite) ∧
  (∀ (a s : ℕ) (t : D.host.E), t ≠ 0 → 1 ≤ a → 1 ≤ s → a + s - 1 ≤ D.R.rS + 1 →
    (Function.mulSupport fun p => (M p).modK (blkMod δ T T' p a s t)).Finite) ∧
  (∀ w w' : Point D.host.E (D.R.rS + 1), (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

end Family

end Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.DoubleBoundAndExtensionOfSmooth
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.DoubleDerivativeSmoothness

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BridgeLemma₄

section Side

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

def FI (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (σ : Mx k r → (H →L[ℂ] H))
    (u v : H) : Mt k r × Mt k r → (Wp →L[ℂ] Wp) := fun p =>
  (⟪v, σ (Matrix.of p.1 * Matrix.of p.2) u⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹

end Side

end Formalism.MainNotions.DoubleDerivativeSmoothness
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.RatioInvLeFrameFactor
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

section Pts

variable {k r : ℕ} {κ τ : ℝ}

theorem scaleBlocks_map_snd (κ τ : ℝ) (r acc : ℕ) (bs : List (ℂ × ℕ)) :
    (scaleBlocks κ τ r acc bs).map Prod.snd = bs.map Prod.snd := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBlocks, List.map_cons, ih]

theorem scaleBlocks_blocks (hκ : 0 < κ) (hτ : 0 < τ) (acc : ℕ) (bs : List (ℂ × ℕ))
    (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) : ∀ b ∈ scaleBlocks κ τ r acc bs, b.1 ≠ 0 ∧ 1 ≤ b.2 := by
  induction bs generalizing acc with
  | nil => intro b hb; simp [scaleBlocks] at hb
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    intro x hx
    simp only [scaleBlocks, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have h0 := h (t, s) (by simp)
      refine ⟨mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity)) h0.1, h0.2⟩
    · exact ih (acc + s) (fun b hb => h b (by simp [hb])) x hx

def ptTr (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) : Point ℂ (r + 1) :=
  ⟨scaleBlocks κ τ r 0 γ.1, scaleBlocks_blocks hκ hτ 0 γ.1 γ.2.1, by rw [scaleBlocks_map_snd]; exact γ.2.2⟩

theorem ptTr_val (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) :
    (ptTr κ τ hκ hτ γ).1 = scaleBlocks κ τ r 0 γ.1 := rfl

theorem ptEntry_scaleBlocks (acc : ℕ) (bs : List (ℂ × ℕ)) (i j : ℕ)
    (h : acc + (bs.map Prod.snd).sum ≤ r + 1) :
    ptEntry (scaleBlocks κ τ r acc bs) i j =
      ((tF r κ τ (acc + i) * tF r κ τ (acc + j) : ℝ) : ℂ) * ptEntry bs i j := by
  induction bs generalizing acc i j with
  | nil => simp [scaleBlocks, ptEntry]
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.map_cons, List.sum_cons] at h
    simp only [scaleBlocks, ptEntry]
    by_cases h1 : i < s ∧ j < s
    · rw [if_pos h1, if_pos h1]
      by_cases h2 : i + j + 1 = s
      · rw [if_pos h2, if_pos h2]
        have e : 2 * (r + 1 - (acc + s)) + (s - 1) = (r - (acc + i)) + (r - (acc + j)) := by omega
        rw [e, tF, tF, pow_add]; push_cast; ring
      · rw [if_neg h2, if_neg h2, mul_zero]
    · rw [if_neg h1, if_neg h1]
      by_cases h3 : s ≤ i ∧ s ≤ j
      · rw [if_pos h3, if_pos h3, ih (acc + s) (i - s) (j - s) (by omega),
          show acc + s + (i - s) = acc + i by omega, show acc + s + (j - s) = acc + j by omega]
      · rw [if_neg h3, if_neg h3, mul_zero]

theorem ptMat_ptTr (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) (a b : Fin (r + 1)) :
    ptMat (ptTr κ τ hκ hτ γ) a b = ((tF r κ τ a * tF r κ τ b : ℝ) : ℂ) * ptMat γ a b := by
  have := ptEntry_scaleBlocks (κ := κ) (τ := τ) (r := r) 0 γ.1 a.val b.val (by rw [γ.2.2]; omega)
  rw [zero_add, zero_add] at this
  exact this

theorem prod_filter_lt (f : ℕ → ℝ) (l : ℕ) (hl : l ≤ r + 1) :
    ∏ a : Fin (r + 1) with a.val < l, f a = ∏ a ∈ range l, f a := by
  rw [Finset.prod_filter, Fin.prod_univ_eq_prod_range (fun a => if a < l then f a else 1), ← Finset.prod_filter]
  congr 1
  ext a; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem prod_range_tF_sq (l : ℕ) :
    ∏ a ∈ range l, tF r κ τ a ^ 2 = τ ^ (2 * l) * κ ^ (∑ a ∈ range l, (r - a) * 2) := by
  simp_rw [tF, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, Finset.prod_pow_eq_pow_sum, ← pow_mul]

theorem sum_range_sub_mul_two (r : ℕ) : ∑ a ∈ range (r + 1), (r - a) * 2 = r * (r + 1) := by
  have h1 : ∑ a ∈ range (r + 1), (r - a) = ∑ a ∈ range (r + 1), a := by
    rw [← Finset.sum_range_reflect (fun a => a) (r + 1)]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Nat.add_sub_cancel]
  have h2 := Finset.sum_range_id_mul_two (r + 1)
  rw [← Finset.sum_mul, h1, h2, Nat.add_sub_cancel, mul_comm]

theorem sum_range_sub_mul_two' (r : ℕ) : ∑ a ∈ range r, (r - a) * 2 = r * (r + 1) := by
  have := sum_range_sub_mul_two r
  rw [Finset.sum_range_succ, Nat.sub_self, zero_mul, add_zero] at this
  exact this

theorem leadMinor_ptTr (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) (l : ℕ) (hl : l ≤ r + 1) :
    leadMinor (ptMat (ptTr κ τ hκ hτ γ)) l hl =
      ((∏ a : Fin (r + 1) with a.val < l, tF r κ τ a ^ 2 : ℝ) : ℂ) * leadMinor (ptMat γ) l hl := by
  unfold leadMinor
  set d : Fin l → ℂ := fun i => ((tF r κ τ i.val : ℝ) : ℂ) with hd
  have hM : (ptMat (ptTr κ τ hκ hτ γ)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal d * (ptMat γ).submatrix (Fin.castLE hl) (Fin.castLE hl) * Matrix.diagonal d := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, Matrix.submatrix_apply, ptMat_ptTr]
    simp only [hd, Fin.val_castLE]; push_cast; ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_filter_lt (fun a => tF r κ τ a ^ 2) l hl,
    ← Fin.prod_univ_eq_prod_range (fun a => tF r κ τ a ^ 2) l]
  push_cast
  rw [Finset.prod_pow]; ring

theorem GPoint_ptTr (hκ : 0 < κ) (hτ : 0 < τ) (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    Gpt (τ ^ 2 * T) (τ ^ 2 * T') (ptTr κ τ hκ hτ γ) = κ ^ (2 * r * (r + 1)) * τ ^ (4 * (r + 1)) * Gpt T T' γ := by
  unfold Gpt
  rw [leadMinor_ptTr, leadMinor_ptTr, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_ofReal, prod_filter_lt (fun a => tF r κ τ a ^ 2) _ le_rfl,
    prod_filter_lt (fun a => tF r κ τ a ^ 2) _ (Nat.le_succ r), prod_range_tF_sq, prod_range_tF_sq,
    sum_range_sub_mul_two, sum_range_sub_mul_two']
  ring

theorem blockIdx_scaleBlocks (acc : ℕ) (bs : List (ℂ × ℕ)) (p : ℕ) :
    blockIdx (scaleBlocks κ τ r acc bs) p = blockIdx bs p := by
  induction bs generalizing acc p with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    simp only [scaleBlocks, blockIdx, ih]

theorem rootPat_ptTr (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) :
    rootPat (ptTr κ τ hκ hτ γ) = rootPat γ := by
  simp only [rootPat, ptTr_val, blockIdx_scaleBlocks]

def frStart : List (ℂ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (_, s) :: bs, p => if p < s then 0 else s + frStart bs (p - s)

theorem frStart_le : ∀ (bs : List (ℂ × ℕ)) (p : ℕ), frStart bs p ≤ p
  | [], p => Nat.zero_le p
  | (t, s) :: bs, p => by
    simp only [frStart]
    split_ifs with h
    · exact Nat.zero_le p
    · have := frStart_le bs (p - s); omega

theorem blockIdx_eq_iff : ∀ (bs : List (ℂ × ℕ)) (a b : ℕ), a < b →
    (blockIdx bs a = blockIdx bs b ↔ frStart bs b ≤ a)
  | [], a, b, _ => by simp [blockIdx, frStart]
  | (t, s) :: bs, a, b, hab => by
    simp only [blockIdx, frStart]
    by_cases hb : b < s
    · have ha : a < s := by omega
      rw [if_pos ha, if_pos hb, if_pos hb]; simp
    · by_cases ha : a < s
      · rw [if_pos ha, if_neg hb, if_neg hb]; constructor <;> intro h <;> omega
      · rw [if_neg ha, if_neg hb, if_neg hb]
        have := blockIdx_eq_iff bs (a - s) (b - s) (by omega)
        constructor
        · intro h; have := this.mp (by omega); omega
        · intro h; have := this.mpr (by omega); omega

theorem sum_rootPat (g : ℕ → ℕ → ℕ) (γ : Point ℂ (r + 1)) :
    ∑ p ∈ rootPat γ, g p.1.val p.2.val = ∑ b ∈ range (r + 1), ∑ a ∈ Ico (frStart γ.1 b) b, g a b := by
  have key : ∀ b : Fin (r + 1), (∑ a : Fin (r + 1),
      if a < b ∧ blockIdx γ.1 a.val = blockIdx γ.1 b.val then g a.val b.val else 0) =
      ∑ a ∈ Ico (frStart γ.1 b) b, g a b := by
    intro b
    have hsub : Ico (frStart γ.1 b) b.val ⊆ range (r + 1) := fun x hx => by
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega
    rw [← Finset.inter_eq_right.mpr hsub, ← Finset.sum_ite_mem,
      Finset.sum_range (fun a => if a ∈ Ico (frStart γ.1 b) b.val then g a b else 0)]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hiff : (a < b ∧ blockIdx γ.1 a.val = blockIdx γ.1 b.val) ↔ a.val ∈ Ico (frStart γ.1 b) b.val := by
      rw [Finset.mem_Ico, Fin.lt_def]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨(blockIdx_eq_iff γ.1 a b h1).mp h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, (blockIdx_eq_iff γ.1 a b h2).mpr h1⟩
    by_cases h : a < b ∧ blockIdx γ.1 a.val = blockIdx γ.1 b.val
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  rw [rootPat, Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product_right,
    Finset.sum_range (fun b => ∑ a ∈ Ico (frStart γ.1 b) b, g a b)]
  exact Finset.sum_congr rfl fun b _ => key b

theorem card_rootPat_le (γ : Point ℂ (r + 1)) : 2 * (rootPat γ).card ≤ r * (r + 1) := by
  have h1 : (rootPat γ).card = ∑ b ∈ range (r + 1), ∑ a ∈ Ico (frStart γ.1 b) b, 1 := by
    rw [Finset.card_eq_sum_ones]; exact sum_rootPat (fun _ _ => 1) γ
  have h2 : ∑ b ∈ range (r + 1), ∑ a ∈ Ico (frStart γ.1 b) b, (1 : ℕ) ≤ ∑ b ∈ range (r + 1), b :=
    Finset.sum_le_sum fun b _ => by
      rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one]; exact Nat.sub_le _ _
  have h3 := Finset.sum_range_id_mul_two (r + 1)
  rw [Nat.add_sub_cancel] at h3
  rw [h1]
  calc 2 * ∑ b ∈ range (r + 1), ∑ a ∈ Ico (frStart γ.1 b) b, 1 ≤ 2 * ∑ b ∈ range (r + 1), b := by omega
    _ = r * (r + 1) := by rw [mul_comm, h3, mul_comm]

theorem one_le_max_inv {x : ℝ} (hx : 0 < x) : 1 ≤ max x x⁻¹ := by
  rcases le_total x 1 with h | h
  · exact le_max_of_le_right ((one_le_inv₀ hx).mpr h)
  · exact le_max_of_le_left h

theorem pow_le_maxRpow {x : ℝ} (hx : 0 < x) {n : ℕ} {y : ℝ} (hny : (n : ℝ) ≤ y) :
    x ^ n ≤ max x x⁻¹ ^ y ∧ x⁻¹ ^ n ≤ max x x⁻¹ ^ y := by
  have h1 : max x x⁻¹ ^ n ≤ max x x⁻¹ ^ y := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (one_le_max_inv hx) hny
  exact ⟨(pow_le_pow_left₀ hx.le (le_max_left _ _) n).trans h1,
    (pow_le_pow_left₀ (inv_pos.mpr hx).le (le_max_right _ _) n).trans h1⟩

theorem frame_exps {Cf : ℝ} (hCf : 2 ≤ Cf) {c : ℕ} (hc : 2 * c ≤ r * (r + 1)) :
    ((4 * (r + 1) : ℕ) : ℝ) ≤ Cf * ((2 * r + 2 : ℕ) : ℝ) ∧
    ((2 * r * (r + 1) + 2 * c : ℕ) : ℝ) ≤ Cf * ((2 * r + 2 : ℕ) : ℝ) ^ 2 := by
  have hc' : ((2 * c : ℕ) : ℝ) ≤ ((r * (r + 1) : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at hc' ⊢
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  constructor
  · nlinarith
  · have h8 : (0 : ℝ) ≤ (2 * r + 2) ^ 2 := by positivity
    nlinarith

theorem ratio_inv_le_frameFactor (hκ : 0 < κ) (hτ : 0 < τ) {Cf : ℝ} (hCf : 2 ≤ Cf) {c : ℕ}
    (hc : 2 * c ≤ r * (r + 1)) :
    τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1) + 2 * c) ≤
      max κ κ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ) ^ 2) * max τ τ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)) := by
  obtain ⟨e1, e2⟩ := frame_exps hCf hc
  rw [mul_comm (τ ^ _)]
  exact mul_le_mul (pow_le_maxRpow hκ e2).1 (pow_le_maxRpow hτ e1).1 (by positivity)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_max_inv hκ)) _)

theorem ratio_le_frameFactor (hκ : 0 < κ) (hτ : 0 < τ) {Cf : ℝ} (hCf : 2 ≤ Cf) {c : ℕ}
    (hc : 2 * c ≤ r * (r + 1)) :
    (τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1) + 2 * c))⁻¹ ≤
      max κ κ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ) ^ 2) * max τ τ⁻¹ ^ (Cf * ((2 * r + 2 : ℕ) : ℝ)) := by
  obtain ⟨e1, e2⟩ := frame_exps hCf hc
  rw [mul_inv, ← inv_pow, ← inv_pow, mul_comm ((τ⁻¹) ^ _)]
  exact mul_le_mul (pow_le_maxRpow hκ e2).2 (pow_le_maxRpow hτ e1).2 (by positivity)
    (Real.rpow_nonneg (zero_le_one.trans (one_le_max_inv hκ)) _)

end Pts

end Formalism.MainNotions.FrameBoundFromBesselTorus
end
end
