module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuFrameExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplaneMid
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubsetDiffConst
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PCutRestrLenExact
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.SnapperHyperplane
namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem snapperHyperplane : SnapperHyperplane.Statement.{u, w} :=
  SnapperHyperplane.proof SnapperQuotAdd.closed SnapperQuotDevissage.closed SnapperHyperplaneMid.proof

theorem mixedTwistShift : MixedTwistShift.Statement.{u, w} :=
  MixedTwistShift.proof snapperHyperplane SnapperSection.full SnapperDiffPoly.proof RestrLenEuler.proof
    SubsetDiffConst.proof

theorem interNumEventual : InterNumEventual.Statement.{u, w} :=
  InterNumEventual.proof snapperHyperplane SnapperSection.full

theorem interNumAdditive : InterNumAdditive.Statement.{u, w} :=
  InterNumAdditive.proof interNumEventual (InterSumTopVanish.proof mixedTwistShift)

end PositivityTheory.HtPt.Kra
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.InterNumPointDeg
namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem surjectiveClosed : SurjectiveClosed.Statement.{u, w} :=
  SurjectiveClosed.proof Extension.proof IdealTwistFamily.proof (TildeVanish.proof SerreVanish.full)

theorem finiteSections : FiniteSections.Statement.{u, w} :=
  FiniteSections.proof Extension.proof (TildeTail.proof SerreTail.full)

theorem intersectionNumberCut_of_mixedTwistShift (h : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  InterNumCut.proof (CycleSplit.Filt.proof (CycleSplit.Filt.Step.proof surjectiveClosed finiteSections))
    (CutRestrLenExact.proof surjectiveClosed finiteSections) h

theorem interNumPointDeg : InterNumPointDeg.Statement.{u, w} :=
  InterNumPointDeg.proof (InterNumRestrict.proof
    (RestrLenRestrict.proof surjectiveClosed PrimeFiltration.RestrictQuot.proof))

end PositivityTheory.HtPt.Kra
end

namespace PositivityTheory.HtPt.Kra

universe u w

theorem kleiman_input : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{u, w} :=
  GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.proof interNumEventual interNumAdditive
    (intersectionNumberCut_of_mixedTwistShift mixedTwistShift) interNumPointDeg

theorem kleiman_input_universe_zero : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} := kleiman_input

end PositivityTheory.HtPt.Kra
