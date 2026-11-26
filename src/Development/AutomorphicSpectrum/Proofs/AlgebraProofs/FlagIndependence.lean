module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PairNumberPullback
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSegreFlagClosureCut
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSegreFlagCutDivisorX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSegreFlagCutLiesOverX

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModel
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModel
namespace GlobalTheory.CompanionTheory.CommAlg.SegreFlag

open GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.AutoClose

theorem segreFlagClosureCut : SegreFlagClosureCut.Statement :=
  SegreFlagClosureCut.proof GlobalTheory.T.cut_effective_divisor
    (PairNumberExpansionIndependence.proof GlobalTheory.T.vertical_divisors_commute)
    NumbersDVR_SegreFlagClosureModel
    (SegreFlagCutSection.proof NumbersDVR_SegreFlagClosureModel
      SegreFlagCutForms.proof SegreFlagCutDivisor.closed segre_flag_degree_zero_holds)
    (SegreFlagCutContraction.proof NumbersDVR_SegreFlagClosureModel
      (SegreFlagCutProjection.proof SegreFlagCutLiesOver.closed NumbersDVR_SegreFlagProjSpecialDim))

end GlobalTheory.CompanionTheory.CommAlg.SegreFlag
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsHeckeCorrespondenceOnIntegralShimuraModelStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel : GroundTheory.Heights₂.Heights.NumbersDVR.SegreFlagClosureCut.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut | exact GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut | (intros; apply GlobalTheory.CompanionTheory.CommAlg.SegreFlag.segreFlagClosureCut <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence
namespace GlobalTheory.CompanionTheory.CommAlg.FlagIndependence

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  have hPE := PairNumberExpansionIndependence.proof
    GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute
  have hCM : GenericProjClosureModel.Statement :=
    GenericProjClosureModel.proof TwistedDualGensExist.proof
      (GenericProjClosureDim.proof DvrConeDimTrdeg.proof
        (PairBundleTrdeg.proof AdjoinTrdegAdd.proof PairConeLinesIndep.proof PairConeAlg.proof))
      (GenericProjClosureDivisor.proof TwistedDualGensExpress.proof)
  have hFM : SegreFlagClosureModel.Statement :=
    SegreFlagClosureModel.proof (SegreFlagClosureTrdeg.proof SegreFlagConeAlg.proof)
  have hSP := SegreFlagClosurePullback.proof GlobalTheory.T.pair_number_pullback hPE hFM
    PairNumberRelabel.proof VerticalDivisorJoinPullback.proof SegreFlagClosureBirational.proof
  have hSCN := SegreClosureNumber.proof hPE hFM
    GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel hSP
  exact FlagIndependence.proof hPE (HsymmPairFlagIndependence.proof hPE hCM hSCN)
    SymmetricSpanHsymm.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagIndependence
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependenceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_independence : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | exact GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main | (intros; apply GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main <;> assumption)
end
