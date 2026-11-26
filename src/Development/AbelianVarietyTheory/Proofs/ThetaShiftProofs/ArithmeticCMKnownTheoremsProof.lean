module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEigenLineDegreeFormula
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem known_holds : Known :=
  have hL := GlobalTheory.firstFiveLaws
  have hh : GlobalTheory.CM.HomExtDvr := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr
  { laws := hL.1
    laws2 := hL.2.1
    ubc := hL.2.2.2.1.unifBaseChange
    laws5 := hL.2.2.2.2
    theta := GlobalTheory.thetaUnifAV_all
    n1ab := GlobalTheory.Moduli.jointExistence_and_moduliScheme.2
    n1c := GlobalTheory.closing_of_abelianSchemeLaws
    n5 := GlobalTheory.arcClause_closed
    models := GlobalTheory.Moduli.jointExistence_and_moduliScheme.1
    hom := hh
    key := GlobalTheory.KeyFam.keyFormula_holds
    cm := GlobalTheory.cmExists_closed
    deg := GlobalTheory.CM.PureDeg.degSt GlobalTheory.cmCurve_closed GlobalTheory.thetaUnifAV_all hL.1 hh
    ev := fun E _ _ _ H Dw l Xo c => (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1 }

end GlobalTheory.ArcCM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmeticCMKnownTheorems_proof : Known := by
  first | exact @GlobalTheory.ArcCM.known_holds | exact GlobalTheory.ArcCM.known_holds | (intros; apply GlobalTheory.ArcCM.known_holds <;> assumption)
end
