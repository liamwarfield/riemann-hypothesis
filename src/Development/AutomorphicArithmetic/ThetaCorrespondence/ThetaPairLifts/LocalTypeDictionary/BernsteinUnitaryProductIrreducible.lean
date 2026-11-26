module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistAllPowersOfGaloisCohomologyClassField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Formalism.LocalToGlobal.CarriedPlMap
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.GlobalFormAnisoOfSiegelWeilFockAnisoNc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
section
namespace GlobalTheory.FunPr
structure ThetaLocalInputs : Prop where
  greenSeriesSt : GlobalTheory.Published.GreenSeriesSt
  linnik : GlobalTheory.Published.Linnik
  complexMultiplicationJSt : GlobalTheory.Published.ComplexMultiplicationJSt
  cuspidalMirabolic : GlobalTheory.Published.CuspidalMirabolic
  weylBranching : GlobalTheory.Published.WeylBranching
  bernsteinUnitaryProductIrreducible : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  zelevinskyPolynomialRing : GlobalTheory.Published.ZelevinskyPolynomialRing
  bernsteinZelevinskyFiniteness : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  cuspTraceClass : GlobalTheory.Published.CuspTraceClass
  flathFactorisation : GlobalTheory.Published.FlathFactorisation
  weilSiegelFormulaUnitary : GlobalTheory.Published.WeilSiegelFormulaUnitary
  rallisInnerProductConvergent : GlobalTheory.Published.RallisInnerProductConvergent
  doublingMethod : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL
  hermitianLocalGlobal : GlobalTheory.Published.HermitianLocalGlobal
  quadraticClassFieldTheory : GlobalTheory.Published.QuadraticClassFieldTheory
  borelCasselman : GlobalTheory.Published.BorelCasselman
  radfordShufflePolynomial : GlobalTheory.Published.RadfordShufflePolynomial
  dixmierMalliavinFactorisation : GlobalTheory.Published.DixmierMalliavinFactorisation
  schurOrthogonalitySquareIntegrable : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
  heckeLPartialContinuation : GlobalTheory.Published.HeckeLPartialContinuation
  logDerOne : GlobalTheory.Mem.An.LogDerOne
  kFiniteVectorsUnitary : GlobalTheory.Published.KFiniteVectorsUnitary
  discreteSeriesLowestKType : GlobalTheory.Published.DiscreteSeriesLowestKType
  holomorphicDiscreteSeries : GlobalTheory.Published.HolomorphicDiscreteSeries
  gKGlobalisation : GlobalTheory.Published.GKGlobalisation
  cuspBounded : GlobalTheory.Published.CuspBounded
  strongApproxSU : GlobalTheory.Published.StrongApproxSU
  heckeLEntireAndNonzeroAtOne : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne
  realMetaplecticRepresentation : GlobalTheory.Published.RealMetaplecticRepresentation
  cuspDecayBound : GlobalTheory.Published.CuspDecayBound
  gLHoweDuality : GlobalTheory.Published.GLHoweDuality
  kudlaSplittingSplitUnitary : GlobalTheory.Published.KudlaSplittingSplitUnitary
  metaplecticRepresentation : GlobalTheory.Published.MetaplecticRepresentation
  harishChandraModules : GlobalTheory.Published.HarishChandraModules
  discreteSeriesCover : GlobalTheory.Published.DiscreteSeriesCover
  idealInvariantsOneOrbitSt : GlobalTheory.Published.IdealInvariantsOneOrbitSt
  hermitianHassePrinciple : GlobalTheory.Published.HermitianHassePrinciple
  stoneVonNeumann : GlobalTheory.Published.StoneVonNeumann
  discreteSeriesUpqExists : GlobalTheory.Published.DiscreteSeriesUpqExists
  formalDegreeCompactDual : GlobalTheory.Published.FormalDegreeCompactDual
  thetaRationalInvariance : GlobalTheory.Published.ThetaRationalInvariance
  discreteSeriesHermitianUnique : GlobalTheory.Published.DiscreteSeriesHermitianUnique
  discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists
  harishChandraFinite : GlobalTheory.Published.HarishChandraFinite
  cuspRapidDecay : GlobalTheory.Published.CuspRapidDecay
  weilRepresentationUnitaryPair : GlobalTheory.Published.WeilRepresentationUnitaryPair
  discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists
  cuspDecaySobolev : GlobalTheory.Published.CuspDecaySobolev
  casselmanWallach : GlobalTheory.Published.CasselmanWallach
  howeDualityReal : GlobalTheory.Published.HoweDualityReal
  siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary
  weilRepresentationExists : GlobalTheory.Published.WeilRepresentationExists
end GlobalTheory.FunPr
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
section
namespace GlobalTheory.NRows
structure GeometricGaloisRepCompatibility : Prop where
  weil : GlobalTheory.Published.WeilRepresentationUnitaryPair
  ds : GlobalTheory.Published.DiscreteSeriesExists
  ana : GlobalTheory.Published.HarishChandraAnalyticity
  dsc : GlobalTheory.Published.DiscreteSeriesClassification
  trc : GlobalTheory.Published.CuspTraceClass
  dm : GlobalTheory.Published.DixmierMalliavinFactorisation
  flath : GlobalTheory.Published.FlathFactorisation
  sw : GlobalTheory.Published.WeilSiegelFormulaUnitary
  dbl : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  udbl : GlobalTheory.Published.UnramifiedDoublingGL
  hl : GlobalTheory.Published.HeckeLPartialContinuation
  ht : GlobalTheory.HeightCounting.HtCard
end GlobalTheory.NRows
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH _root_.Formalism.L2.Theta GlobalTheory.Mem.Th
structure HypAAlt : Prop where
  a1 : GlobalTheory.NT.RayField
  a2 : GlobalTheory.Published.PrincipalIdealSt
  a3 : GlobalTheory.Published.CMCurveGoodOutsidePrimeSt
  a5 : GlobalTheory.Published.HarishChandraModules
  a6 : GlobalTheory.Published.CuspRapidDecay
  a7 : GlobalTheory.Published.CasselmanWallach
  a8 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  a9 : GlobalTheory.Published.DiscreteSeriesExists
  a10 : GlobalTheory.Published.HarishChandraFinite
  a11 : GlobalTheory.Dec.DSInfChar
  a12 : GlobalTheory.Published.DiscreteSeriesUpqUnique
  a13 : Formalism.L2.SG.RowsDef.RowsFinDim
  a14 : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent
  a16 : Vol.DiscreteSeriesExist
  a17 : Vol.FormalDegreeFormula₂
  a18 : StandardLattice.SiegelMassRatioCM
  a19 : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ
  a20 : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)
  a21 : ∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam
  a22 : GlobalTheory.Published.GlobalArtinReciprocity
  a23 : GlobalTheory.Published.WeberRayFieldSt
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.DIV _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
end
end GlobalTheory.Mem.Top.Bl
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTowerCompatibility
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_tower_compatibility : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.CuspRapidDecay → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → ∀ D : D7, GlobalTheory.BottomRallis.SiegelWeilFockAniso D → GlobalTheory.BottomRallis.GlobalFormAniso D := by
  first | exact @_root_.GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso_nc | exact _root_.GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso_nc | (intros; apply _root_.GlobalTheory.BottomRallis.globalFormAniso_of_siegelWeilFockAniso_nc <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BesselMapUniqueOfBesselModelUniqueness
section
noncomputable section
open Matrix Topology Filter
open scoped ContDiff
namespace GlobalTheory.BesselMapOne
section Smooth
open Formalism.MainNotions.S _root_.Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {J : Matrix (Fin n) (Fin n) ℂ}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
end
end Smooth
section Frame
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k r : ℕ}
variable {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
end Frame
section Dual
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel
variable {k : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
end Dual
section Main
open PI.UpqRep PI.HwUniqW GlobalTheory.RealBessel PI.BesselMapUniq GlobalTheory.SmVec
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
end Main
end GlobalTheory.BesselMapOne
end
end
end
