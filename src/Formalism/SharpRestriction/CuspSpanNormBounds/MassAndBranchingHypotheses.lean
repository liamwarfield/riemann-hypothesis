module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusMass

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal NNReal InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Conclusion₂

variable (D : D7)

def Conclusion1 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ) : Prop :=
  UnitaryVolumeMass.stX D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c

def Conclusion2 : Prop :=
  UnitaryVolumeMass.stLem3 D

def PointsLemma (u : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stLem3L0 D u

def Conclusion4 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.congruence_at_split_frobenius_holds D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def Conclusion5 (large₂ : SizeData₂ D) (CH C : ℝ) : Prop :=
  UnitaryVolumeMass.SubmoduleIndexCount D large₂ CH C

def Conclusion6 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A Ad C : ℝ) : Prop :=
  UnitaryVolumeMass.MeanFlagPairCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C

def division_rows_rational_lattice (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

end Conclusion₂

section admitted

variable (D : D7)

def adm1 : Prop :=
  UnitaryVolumeMass.stMassRatio D

def adm2 : Prop :=
  UnitaryVolumeMass.stMassL D

def adm16 (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  UnitaryVolumeMass.stMassVol D G

def adm3 : Prop :=
  UnitaryVolumeMass.stBRmult

def ArchimedeanSignatureMatching : Prop :=
  UnitaryVolumeMass.stBRhad

def adm14 : Prop :=
  UnitaryVolumeMass.stBRtrans

def adm15 : Prop :=
  UnitaryVolumeMass.stBRmink

def adm5 : Prop :=
  UnitaryVolumeMass.stLem1 D

def adm6 : Prop :=
  UnitaryVolumeMass.HyperplaneRankAllWords D

def adm7 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def adm20 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  UnitaryVolumeMass.stForm D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

def adm8 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

def adm9 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

end admitted

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def adm10 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm11 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm12 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm17 (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def adm18 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm13 (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def adm19 (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

end Loc

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

def admitted (C' Cl Cg cb Cu cT CT C0 A CSW δ Cn C1 Cq CPT CDl hilbertNinetyConstant CMo CK : ℝ) : Prop :=
  adm1 D ∧ adm2 D ∧ adm3 ∧ ArchimedeanSignatureMatching ∧ adm5 D ∧ adm6 D ∧
  adm7 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW ∧ adm8 D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧ adm9 D large₂ C' Cl Cg cb Cu cT CT C0 ∧
  adm10 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ adm11 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ adm12 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧
  adm13 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧ adm14 ∧ adm15 ∧ adm16 D G ∧
  adm17 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧ adm18 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧ adm19 D large₂ C' Cl Cg cb Cu cT CT C0 C1 CK ∧
  adm20 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

def Conclusion₂ (C' Cl Cg cb Cu cT CT C0 A Ad CH C c : ℝ) : Prop :=
  Conclusion1 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c ∧ Conclusion2 D ∧ PointsLemma D u ∧ Conclusion4 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C ∧ Conclusion5 D large₂ CH C ∧
  Conclusion6 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C ∧ division_rows_rational_lattice D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def Stmt (C' Cl Cg cb Cu cT CT C0 A CSW δ Cn C1 Cq CPT CDl hilbertNinetyConstant CMo CK Ad CH C c : ℝ) : Prop :=
  admitted D large₂ u u' G C' Cl Cg cb Cu cT CT C0 A CSW δ Cn C1 Cq CPT CDl hilbertNinetyConstant CMo CK → Conclusion₂ D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad CH C c

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def Conclusion3Family : Prop := ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, PointsLemma (Fm.D x i) u

end Family

end Formalism.MainNotions.VanishingOnXAndXPlusMass

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
noncomputable section

namespace Formalism.MainNotions.LocalBesselAndTopKernel.TOP

open ValuativeRel MeasureTheory ComplexConjugate ComplexOrder
open Formalism.MainNotions.S.Loc

end Formalism.MainNotions.LocalBesselAndTopKernel.TOP

namespace Formalism.MainNotions.LocalBesselAndTopKernel.GLOB

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

def CNT {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (X : TermLoc D Y δ M u u') (c : ℝ) : Prop :=
  0 < c ∧
  ∀ w : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 →
    {γ : D.s.Term u u' | D.s.generic γ ∧ D.s.ptOf γ = w}.Finite ∧
    (¬ TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) → ∀ γ : D.s.Term u u', D.s.generic γ → D.s.ptOf γ ≠ w) ∧
    ∀ _ : TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w),
    ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
    ∀ γ₀ : D.s.Term u u', D.s.generic γ₀ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ₀) ≠ 0 →
      ∑' γ : {γ : D.s.Term u u' // D.s.generic γ ∧ D.s.ptOf γ = w ∧
          kind (D.s.ptOf γ₀) = kind w ∧ ∀ p, thCls X γ p = thCls X γ₀ p},
        (X.massT γ.1 : ℂ) * D.s.cTerm γ.1 =
      (n0 c (D.mem u).A.T (D.mem u').A.T w : ℂ) * (densT X ϖ γ₀ : ℂ) *
        BBG M δ (D.mem u).A.T (D.mem u').A.T w (kind (D.s.ptOf γ₀)) (thCls X γ₀) / autG M (thCls X γ₀)

end Formalism.MainNotions.LocalBesselAndTopKernel.GLOB

namespace Formalism.MainNotions.LocalBesselAndTopKernel.SW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

end Ext

open Formalism.BasicNotions

end Formalism.MainNotions.LocalBesselAndTopKernel.SW

namespace Formalism.MainNotions.LocalBesselAndTopKernel

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def hyp (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  StandingNumericalData D C0 ∧ StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ 1 ≤ C0


open Classical in
def gsFam (D : D7) (u u' : D.what₂.Word) : D.s.Pair u u' → ℂ := fun P =>
  if scalarP D.s P ∧ D.s.Gterm (D.s.pfst P) ≠ 0 ∧ D.s.Gterm (D.s.psnd P) ≠ 0 then D.s.pval P else 0

def Conclusion1 (D : D7) (CA CA' Ce : ℝ) : Prop :=
  let N : ℝ := NA D
  let r : ℝ := D.R.rS
  ∀ u u' : D.what₂.Word, u ≠ u' → Summable (gsFam D u u') ∧
  ∀ (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D),
    IsLocA D u u' x → IsLatGLOB D L →
    (∀ τ, IsCutS (uS D u τ) (uS D u' τ) (Set.Icc (x τ).a (x τ).b) ∧
      CA * ((D.R.k : ℝ) * N * (r + 1) ^ 2 + N ^ 2 * (r + 1) ^ 2 + N ^ 3) ≤ (x τ).b - (x τ).a ∧
      (x τ).a ≤ (x τ).a1 ∧ (x τ).b1 ≤ (x τ).b ∧ N ^ 3 / 2 ≤ (x τ).b1 - (x τ).a1) →
    (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ) ≤ 1 → CA' ≤ ThA D CA u u' x L →
    genScal D u u' ≤ (1 + CA * (r + 1) * (CA / ThA D CA u u' x L) ^ (D.R.f : ℝ)) * (1 + eSum D Ce) *
      (∏ᶠ p ∈ typedPl D, (1 + 3 / (Ideal.absNorm p.asIdeal : ℝ))) *
      (D.duS u : ℝ) * (D.duS u' : ℝ) / D.what₂.Dstar

def projection_sandwich_lattice (D : D7) : Prop :=
  UnitaryVolumeMass.cTvA D

def MassRatio₂ (D : D7) (C1 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvB D C1

def kernel_index_full_lattice (D : D7) (C2 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvC D C2

def gram_det_kernel_dual_lattice (D : D7) (C3 : ℝ) : Prop :=
  UnitaryVolumeMass.cTvD D C3

def MidVolumeChain (D : D7) (large₂ : SizeData₂ D) (ep0 CV : ℝ) : Prop :=
  UnitaryVolumeMass.cTvG D large₂ ep0 CV

def AdmittedWeylDimension : Prop :=
  ∀ (k' : ℕ) (u : Fin k' → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Matrix (Fin k') (Fin k') ℂ → (H →L[ℂ] H)), StrictAnti u → IsHCTypeU k' u π →
    (Module.finrank ℂ H : ℝ) = vand u / ∏ i ∈ Finset.range k', (i.factorial : ℝ)

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

def FamilySchurFormalDegree (D : D7) : Prop :=
  UnitaryVolumeMass.stMassRatio D

def GL5LogLValueBoundByZeta (D : D7) : Prop :=
  ∀ i : ℕ, 3 ≤ i →
    |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E i)| ≤ (D.R.f : ℝ) * Real.log (riemannZeta (i : ℂ)).re

def cardGL (q : ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, (q ^ n - q ^ i)

def dimNS (D : D7) : ℕ := D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)

def idxRows (D : D7) : ℝ :=
  ∏ᶠ p ∈ typedPl D, cardGL (Ideal.absNorm p.asIdeal : ℝ) D.R.r /
    ((Ideal.absNorm p.asIdeal : ℝ) ^ dimNS D * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))

def FamilyMidVolume (D : D7) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
    (L : Submodule (𝓞 D.host.E) V), h.IsSymm →
    (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word,
      (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * gaG D *
        (∏ τ, vand (uS D u τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (Tr D u ^ D.R.k - 1) ^ D.R.f) ∧
    (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r →
      D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * idxRows D * ∏ τ, D.dsig τ)

def nPl {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = true)).card
def nMi {N : ℕ} (ε : Fin N → Bool) : ℕ := (Finset.univ.filter (fun a => ε a = false)).card

section Glob

open Formalism.MainNotions.S.LocalSplitGroups

variable {D : D7}

variable (D)

variable {D}

variable (D)

end Glob

section One

open Formalism.MainNotions.S.LocalSplitGroups

def FamilyExpansionSecond (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  FamilySchurFormalDegree D → GL5LogLValueBoundByZeta D → FamilyMidVolume D → hyp D large₂ C0 C' Cl Cg cb Cu cT CT → projection_sandwich_lattice D
def SecondBoundHyp (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT C1 : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MassRatio₂ D C1
def LocalTiedPairs (D : D7) (large₂ : SizeData₂ D) (C0 C' Cl Cg cb Cu cT CT ep0 CV C3' : ℝ) : Prop :=
  hyp D large₂ C0 C' Cl Cg cb Cu cT CT → MidVolumeChain D large₂ ep0 CV → gram_det_kernel_dual_lattice D C3'

end One

section Family

open Formalism.MainNotions.S.LocalSplitGroups

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def UnderF (C0 Cg cb Cu cT CT : ℝ) (P : ∀ D : D7, SizeData₂ D → Prop) : Prop :=
  OwnEv Fm fun C' Cl x i =>
    hyp (Fm.D x i) (Fm.L x i) C0 C' Cl Cg cb Cu cT CT → P (Fm.D x i) (Fm.L x i)

def SecondSizeStatement : Prop := ∀ x (i : Fm.Ix x), FamilySchurFormalDegree (Fm.D x i)
def BesselFormLine : Prop := ∀ x (i : Fm.Ix x), GL5LogLValueBoundByZeta (Fm.D x i)
def FamilyRanksHypothesis (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => FamilyMidVolume D

def FamilyBesselBoundFirstPart (C0 Cg cb Cu cT CT : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => projection_sandwich_lattice D
def TheoremThreePassage (C0 Cg cb Cu cT CT C1 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => MassRatio₂ D C1
def FamilyLowestKType (C0 Cg cb Cu cT CT C2 : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => kernel_index_full_lattice D C2
def LocalSplitExponents (C0 Cg cb Cu cT CT C3' : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D _ => gram_det_kernel_dual_lattice D C3'
def FamilyTopBound (C0 Cg cb Cu cT CT ep0 CV : ℝ) : Prop := UnderF Fm C0 Cg cb Cu cT CT fun D large₂ => MidVolumeChain D large₂ ep0 CV

def FamilyUnfoldingCount (C0 Cg cb Cu cT CT : ℝ) : Prop :=
  SecondSizeStatement Fm → BesselFormLine Fm → FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT → FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT

end Family

section Closed

open Formalism.MainNotions.S.LocalSplitGroups

end Closed

end Formalism.MainNotions.LocalBesselAndTopKernel
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
open MeasureTheory Matrix Finset Filter Topology
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusBranching

export Formalism.MainNotions.S.UnitaryVolumeMass (volU ForAmpH)

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Cnt

section admitted

variable (D : D7) (large₂ : SizeData₂ D)

def adm1 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm2 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def adm3 (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def adm5 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

def adm9 (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def adm10 (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

end admitted

section Adm2

variable (D : D7) (large₂ : SizeData₂ D)

def adm11 (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stSchur D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def adm12 : Prop :=
  UnitaryVolumeMass.stWeyl D

end Adm2

def adm6 : Prop :=
  UnitaryVolumeMass.stBRmult

def adm7 : Prop :=
  UnitaryVolumeMass.stBRhad

section Conclusion₂

variable (D : D7) (large₂ : SizeData₂ D)

def Conclusion1 (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def Conclusion2 (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.L2PointwiseLoss D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def PointsLemma (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  UnitaryVolumeMass.stL2prod D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def Conclusion4 (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stABS D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def PrimeSumLogBound (C' Cl Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  UnitaryVolumeMass.stABSconv D large₂ C' Cl Cg cb Cu cT CT C0 A C1

def Conclusion5 (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  UnitaryVolumeMass.stABSprod D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def Conclusion6 (C' Cl Cg cb Cu cT CT C0 A C1 C δ : ℝ) : Prop :=
  UnitaryVolumeMass.stMIN D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ

def division_rows_rational_lattice (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ : ℝ) : Prop :=
  UnitaryVolumeMass.stDEC D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

def aux₃ (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ : ℝ) : Prop :=
  Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 C ∧ Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
  PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧ Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
  PrimeSumLogBound D large₂ C' Cl Cg cb Cu cT CT C0 A C1 ∧
  Conclusion5 D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧ Conclusion6 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ ∧
  division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

def admitted (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CPT CDl CMo hilbertNinetyConstant CS : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧
  adm3 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧ adm5 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ adm6 ∧ adm7 ∧
  adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧ adm10 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧
  adm11 D large₂ C' Cl Cg cb Cu cT CT C0 C1 CS ∧ adm12 D

def IntegralityFromMetric (C' Cl Cg cb Cu cT CT C0 C1 CS C : ℝ) : Prop :=
  adm11 D large₂ C' Cl Cg cb Cu cT CT C0 C1 CS → adm12 D → Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def HodgeTateFromSandwich (C' Cl Cg cb Cu cT CT C0 A Cn C1 CPT Cc C : ℝ) : Prop :=
  adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT → Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 C1 Cc →
    Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def TowerRallisLemma (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop := PointsLemma D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def GGFromIrreducibility (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop := Conclusion5 D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def ShareFromInputs (C' Cl Cg cb Cu cT CT C0 A C1 Ca C δ : ℝ) : Prop :=
  adm5 D large₂ C' Cl Cg cb Cu cT CT C0 → Conclusion2 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Ca →
    Conclusion4 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Ca → Conclusion6 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ

end Conclusion₂

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF5 (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm5 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def admF9 (Cg cb Cu cT CT C0 C1 : ℝ) : Prop :=
  ∀ Cn, OwnEv Fm fun C' Cl x i => adm9 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1

def FamilyTwelfthHypothesis : Prop := ∀ x (i : Fm.Ix x), adm12 (Fm.D x i)

end Family

end Formalism.MainNotions.VanishingOnXAndXPlusBranching
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
noncomputable section

open ValuativeRel NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.NonGenericAndKTwoTheorems

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NonGenericLocalBound (k r : ℕ) (C : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → LocNG.NGAt k P C

def Conclusion1 (D : D7) (C : ℝ) : Prop := 4 * D.R.rS + 7 ≤ D.R.k → NonGenericLocalBound D.R.k D.R.rS C

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

def KTwoParameterConditions (Cl Cg CT : ℝ) : Prop :=
  Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  (∀ i : Fin 2, ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ large₂.sc.b ^ Cg) ∧
  (∀ (τ : D.what₂.Tau) (a c : Fin D.R.r), a ≠ c →
    Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 < |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) c|) ∧
  Cl * Real.log D.host.rdE ≤ large₂.sc.L ∧
  Real.log (D.R.f : ℝ) ≤ (D.R.rS : ℝ) ^ 2 ∧
  (∀ u : D.what₂.Word, ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) ∧
    Nat.Coprime (D.mem u).A.T (D.host.g 0 * D.host.g 1)) ∧
  Formalism.HermitianLatticesTheory.IsCMUnram D.host.E

def KTwoHypotheses (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ KTwoParameterConditions D large₂ Cl Cg CT

end Hyps

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Terms

def adm7 : Prop :=
  ∀ (k : ℕ) (u u' : Fin k → ℝ) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H')),
    IsHCTypeU k u π → IsHCTypeU k u' ρ → u ≠ u' →
    ∀ P : H' →L[ℂ] H, (∀ h ∈ UJset (allPos k), P.comp (ρ h) = (π h).comp P) → P = 0

section Size

variable (D : D7) (large₂ : SizeData₂ D)

end Size

section Mass

end Mass

section L3

variable (D : D7)

end L3

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Gv : GaugeVol D)

def NonGenericLocalBoundOfLargeRank (CN : ℝ) : Prop := Conclusion1 D CN

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, GaugeVol (Fm.D x i))

def Conclusion1Family (CN : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) CN

def FamilyNonGenericLocalBound (CN : ℝ) : Prop := Conclusion1Family Fm CN

end Family

end Formalism.MainNotions.NonGenericAndKTwoTheorems

end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
noncomputable section

namespace Formalism.MainNotions.UniformConstantsAndStatements

export Formalism.MainNotions.S.UnitaryVolumeMass (Kng scalG)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants ValuativeRel IsDedekindDomain NumberField
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def adm5 (D : D7) (C : ℝ) : Prop :=
  UnitaryVolumeMass.stNG D C

structure Given where
  C0 : ℝ
  Cg : ℝ
  cb : ℝ
  Cu : ℝ
  cT : ℝ
  CT : ℝ
  one_le_window_constant : 1 ≤ C0
  cb_pos : 0 < cb
  cT_pos : 0 < cT

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (g : Given)

def admF5 (C : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i) C

end Fam

end Formalism.MainNotions.UniformConstantsAndStatements
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.AuxiliaryNormPrimes
noncomputable section

namespace Formalism.MainNotions.AuxiliaryNormPrimes

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt NumberField Matrix Module
open scoped ENNReal NNReal InnerProductSpace

section B3

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def aux₃ (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A c : ℝ) : Prop :=
  UnitaryVolumeMass.VolumeRatioBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c

end B3

section Mass

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FamilySchurFormalDegree (D : D7) : Prop :=
  UnitaryVolumeMass.stMassRatio D

def GL5LogLValueBoundByZeta (D : D7) : Prop :=
  UnitaryVolumeMass.stMassL D

def RankTwoMassBound (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stMass2 D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def MassVolumeForGaugeFamily (D : D7) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig) : Prop :=
  UnitaryVolumeMass.stMassVol D G

end Mass

section BR

def UnitaryBranchingMultiplicityOne : Prop :=
  UnitaryVolumeMass.stBRmult

def HadamardDeterminantInequality : Prop :=
  UnitaryVolumeMass.stBRhad

def BanaszczykTransferenceBound : Prop :=
  UnitaryVolumeMass.stBRtrans

def MinkowskiFiniteSubgroupOrder : Prop :=
  UnitaryVolumeMass.stBRmink

end BR

section Rows

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def CharacterCutVolume (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def SpectralWeightsCM (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  UnitaryVolumeMass.stForm D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

end Rows

def TemperatureProductAsymptotic (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

def CriticalTemperatureLowerBound (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def PlancherelBoundOneParameter (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PlancherelBoundFiniteSums (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTsum D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def PlancherelBoundDifferenceOperator (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPTDl D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def BesselDegreeNormalization (C' Cl Cg cb Cu cT CT C0 Cn C1 : ℝ) : Prop :=
  UnitaryVolumeMass.PieriNormDegreeFormula D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1

def DegreeRatioUnitStepBound (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.FormalDegreeUnitStepRatio D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

def ArchimedeanMomentBound (C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C : ℝ) : Prop :=
  UnitaryVolumeMass.stMOM D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq C

def DimensionConstantBound (C' Cl Cg cb Cu cT CT C0 C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

end Loc

section Comparison₂

open Formalism.MainNotions.S.Lat MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def TermVolumeSmallCellBound (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stVol D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A C

end Comparison₂

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ) (Y : LoopTie D large₂ X u u' C1)
  (G : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

def admitted (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV : ℝ) : Prop :=
  FamilySchurFormalDegree D ∧ GL5LogLValueBoundByZeta D ∧ RankTwoMassBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CM ∧ MassVolumeForGaugeFamily D G ∧
  UnitaryBranchingMultiplicityOne ∧ HadamardDeterminantInequality ∧ BanaszczykTransferenceBound ∧ MinkowskiFiniteSubgroupOrder ∧
  CharacterCutVolume D large₂ u u' C' Cl Cg cb Cu cT CT C0 A CSW ∧ SpectralWeightsCM D large₂ u u' C' Cl Cg cb Cu cT CT C0 A ∧
  TemperatureProductAsymptotic D large₂ C' Cl Cg cb Cu cT CT C0 δ ∧ CriticalTemperatureLowerBound D large₂ C' Cl Cg cb Cu cT CT C0 ∧
  PlancherelBoundOneParameter D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧ PlancherelBoundFiniteSums D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CPT ∧
  PlancherelBoundDifferenceOperator D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CDl ∧ BesselDegreeNormalization D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 ∧
  DegreeRatioUnitStepBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant ∧ ArchimedeanMomentBound D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 Cq CMo ∧
  DimensionConstantBound D large₂ C' Cl Cg cb Cu cT CT C0 C1 CK ∧ TermVolumeSmallCellBound D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A CV

def Stmt (C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV c : ℝ) : Prop :=
  admitted D large₂ X u u' C1 Y G C' Cl Cg cb Cu cT CT C0 A CM CSW δ Cn Cq CPT CDl hilbertNinetyConstant CMo CK CV →
    aux₃ D large₂ u u' C' Cl Cg cb Cu cT CT C0 A c

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyTemperatureProductAsymptotic (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => TemperatureProductAsymptotic (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 δ

variable (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Family

end Formalism.MainNotions.AuxiliaryNormPrimes
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusProjectedBounds
noncomputable section

namespace Formalism.MainNotions.FrobeniusProjectedBounds

open Formalism.BasicNotions Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Letters

variable (D : D7)

def kR : ℝ := D.R.k

def mR : ℝ := D.R.m

def fR : ℝ := D.R.f

def rR : ℝ := D.R.rS

def nR : ℝ := D.R.r

def du (u : D.what₂.Word) : ℝ := D.duS u

def Dall : ℝ := D.what₂.Dall

def Dst : ℝ := D.what₂.Dstar

def Gam : ℝ := (D.mem D.u₀).A.GamP

end Letters

section Flags

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

end Flags

section Parts

variable (D : D7)

end Parts

def Hyp (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT ∧ StandingNumericalData D C0 ∧ 1 ≤ C0

section Statements

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (C' Cl Cg cb Cu cT CT C0 : ℝ)

def adm5 (c C : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  ∀ u u' : D.what₂.Word, hsNormSq (KOf D.s u u' (famNG D.s)) ≤
    (Real.exp (-(c * kR D * fR D * Real.log (kR D))) +
      (2 : ℝ) ^ (-(kR D - 2 * rR D - 5)) * Real.exp (C * mR D ^ 5 * fR D * large₂.sc.L)) *
      (du D u * du D u') / Dst D

def adm7 (c : ℝ) : Prop := Hyp D large₂ C' Cl Cg cb Cu cT CT C0 →
  |Dall D - Dst D| ≤ Real.exp (-(c * nR D * fR D * Real.log (nR D))) * Dst D

def eF (D : D7) (C0 : ℝ) : ℝ := 2 * C0 / Gam D + 2 * Real.exp (-(kR D * fR D * Real.log (kR D)))

end Statements

section LinAlg

variable {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

end LinAlg

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Cg cb Cu cT CT C0 : ℝ)

end Family

end Formalism.MainNotions.FrobeniusProjectedBounds
end
end
