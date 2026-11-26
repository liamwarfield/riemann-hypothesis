module

public import Formalism.MahlerMeasure.CoarseLevelSlackInequalities
public import Formalism.SharpRestriction.GrowthBounds.ObjSeg
public import Formalism.MahlerMeasure.MahlerMeasureProofs.BadCrit
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.LocalRingCardinality.DataRows
public import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.HomRelationHolds
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Discharge
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.HighestVectorProjection
public import Formalism.PolynomialDimension.ChainOrderLetters
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.SumFinsuppAntidiagEqSumPiFinset
public import Formalism.DegreeFormula.FlagDegFormula
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
public import Formalism.SharpRestriction.GrowthBounds.DataGChain
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.GramBoundOfRestrictionOfProj
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.DerivativeKeepsSpaceHolds
public import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.OmegaInjectiveHolds
public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.FinalLL
public import Formalism.GrowthSums.LemmaATwoFactList
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.FormalDegreeBessel.StatementBF
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet

@[expose] public section

namespace Bl.general_b_fact_left_bis_form

theorem goal1 :
    ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module O V] [inst_4 : _root_.Module (Formalism.MainNotions.G.KK O) V]
      [IsScalarTower O (Formalism.MainNotions.G.KK O) V] (M : Submodule O V),
      ∀ y ∈ Submodule.span (Formalism.MainNotions.G.KK O) (M : Set V), ∃ (s : O), s ≠ 0 ∧ s • y ∈ M  := by
  intro O _ _ V _ _ _ _ M y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    have e : (s * t) • (x + z) = t • (s • x) + s • (t • z) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm t s]
    rw [e]
    exact M.add_mem (M.smul_mem t hsx) (M.smul_mem s htz)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors O) a
    refine ⟨(d : O) * s, mul_ne_zero (nonZeroDivisors.ne_zero d.2) hs, ?_⟩
    have e : ((d : O) * s) • (a • x) = n • (s • x) := by
      rw [mul_comm, mul_smul, ← algebraMap_smul (Formalism.MainNotions.G.KK O) (d : O) (a • x), smul_smul,
        mul_comm (algebraMap O (Formalism.MainNotions.G.KK O) (d : O)) a]
      simp only at hnd
      rw [hnd, algebraMap_smul]
      exact smul_comm s n x
    rw [e]
    exact M.smul_mem n hsx

end Bl.general_b_fact_left_bis_form
