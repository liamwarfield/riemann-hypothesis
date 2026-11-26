module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
public import Formalism.SharpRestriction.InertJacobiLevels.SecondTorsionCardPos
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsDerivedOnOfIsKMod
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKTypeMultiplicityOneUnconditional
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND

@[expose] public section

namespace GlobalTheory.CompanionTheory.Front

theorem discreteSeriesUpqUnique : GlobalTheory.Published.DiscreteSeriesUpqUnique :=
  fun n ε lam hlam H H' _ _ _ _ σ σ' hσ hσ' =>
    GlobalTheory.CompanionTheory.DSUniq.ds_unique
      _root_.CompanionTheory.D.LK.hMultAlg _root_.CompanionTheory.D.LK.hKModExists
      _root_.CompanionTheory.D.LK.hOrthCyc n ε lam H H' σ σ' hlam hσ hσ'

end GlobalTheory.CompanionTheory.Front
