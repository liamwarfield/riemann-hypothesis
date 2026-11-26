module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameOfFrobeniusDense
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstCharacterTrivialWildInertiaTypePrimeStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeightsDeRham
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraicModularFormsStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustion
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIsotEqIsotL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceInputsImplyCuspidalTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealStableOfCharacters
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSeparationOfIwahoriTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalOperatorsVanishingRadicalIntegralsUnitarStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalTraceMultiplicityGiven
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InfinitesimalCharacterReference
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsPositiveScalarsWithoutCongruenceLengths
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RallisConvOfHypotheses
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftRowsInjectiveAndTypePropertiesOfNonvanishing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFock
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanish
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupport
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesLocalOfHypothesis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenExport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualCompatibleRows
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableGoodFormsMeetGenericType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalAwayFromTypes
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.PeriodBoundOfPlaceBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutantFullOfLocalLanglands
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

section Gen
open _root_.Formalism.L2.Theta _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cf : CharFrame D}
  {g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1}

end Gen

section Gen2

def bsTw {D : D7} {cf : CharFrame D} {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ} (Bs : SideB D cf Rw low Pq S hL eig θ)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) :
    SideB (thTw D th).toD7 ((thTw D th).cf cf) ((thTw D th).row Rw) low Pq ((thTw D th).rat S) hL eig θ :=
  { Bs with
    twF := { Bs.twF with }
    tw := { Bs.tw with }
    chiD := { Bs.chiD with }
    chi := { Bs.chi with }
    exp :=
      { Bs.exp with
        mtV := fun i j b k Q ψ h1 h2 h =>
          letI : AddCommGroup (Bs.exp.Wt i j b) := Bs.exp.acgWt i j b
          letI : Module (FractionRing ((thTw D th).toD7.ntw.O i)) (Bs.exp.Wt i j b) := Bs.exp.modWt i j b
          { Bs.exp.mtV i j b k Q ψ h1 h2 h with } } }

def lamTw {D : D7} (N : TwNew D) (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat N.toD7 := ⟨N.cf Z.C, Z.q0, Z.w0, Z.c, Z.chi⟩

theorem lam_thTw {D : D7} (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) {cf : CharFrame D}
    (h : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z) :
    ∃ Z : GlobalTheory.LamTie.LamDat (thTw D th).toD7, Z.Ok ∧ Z.Teich ∧ Z.C = (thTw D th).cf cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 (thTw D th).toD7 ∧
      GlobalTheory.LamTie.IsLamTieFull (thTw D th).toD7.ntw Z := by
  obtain ⟨Z, h1, h2, h3, h4, h5⟩ := h
  exact ⟨lamTw (thTw D th) Z, ⟨h1.places, h1.aux, h1.big⟩, h2, congrArg (TwNew.cf (thTw D th)) h3, h4, h5⟩
end Gen2

section MtCopy
variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

end MtCopy

end GlobalTheory.HeightCounting.Up
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointStatementsOfPublished
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Up

namespace PointStatements

section Loc

variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb} {A : SideA D cf jE} {M : MtFam D} {C : NChoice D}
  {tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E}

end Loc

theorem allSt_mono {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) (hp : AllSt p) : AllSt q :=
  hp.trans (StepW.of_all fun _ _ _ _ _ _ _ H P x => h _ _ _ _ _ P x (H P x))

theorem allSt_and {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (hp : AllSt p) (hq : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  (StepW.and hp hq).trans (StepW.of_all fun _ _ _ _ _ _ _ H P x => ⟨H.1 P x, H.2 P x⟩)

end PointStatements


end GlobalTheory.HeightCounting.Up

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalChartsForFanOfToroidalForFanKS
namespace GlobalTheory

theorem toroidalChartsForFan_of_toroidalForFanKS :
    GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.ToroidalChartsForFan :=
  fun h => h.toroidalChartsForFan

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideDataOverSetLevels
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up

def sideB_congr {D : D7} {cf cf' : CharFrame D} {Rw Rw' : RowSide D} {low low' : Finset ℕ}
    {Pq Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S S' : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {hL' : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S'.WL j)}
    {eig eig' : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0} {θ θ' : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (e1 : cf = cf') (e2 : Rw = Rw') (e3 : low = low') (e4 : Pq = Pq') (e5 : S = S') (e6 : HEq hL hL') (e7 : eig = eig')
    (e8 : θ = θ') (h : SideB D cf Rw low Pq S hL eig θ) : SideB D cf' Rw' low' Pq' S' hL' eig' θ' := by
  subst e1 e2 e3 e4 e5 e7 e8
  cases e6
  exact h

end GlobalTheory.HeightCounting.Up
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPlaceData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

theorem exists_heq_of_eq {F : D7 → Sort _} {D₁ D₂ : D7} (h : D₁ = D₂) (x : F D₁) : ∃ y : F D₂, HEq y x := by
  subst h; exact ⟨x, HEq.rfl⟩


end GlobalTheory.RowTriple.Lay

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho



end GlobalTheory.RowTriple.Lay

namespace GlobalTheory.RowTriple.Lay

open GlobalTheory.TwInputs Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting.FitRho

theorem heq_cf_of_pack {p q : Σ (D₁ : D7) (c₁ : CharFrame D₁) (C₁ : NChoice D₁), TupTied D₁ c₁ C₁} (h : p = q) :
    HEq p.2.1 q.2.1 := by
  subst h; rfl


end GlobalTheory.RowTriple.Lay
end
end
