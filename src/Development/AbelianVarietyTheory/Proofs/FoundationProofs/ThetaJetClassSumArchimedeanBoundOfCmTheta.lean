module

public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaJetClassSumArchimedeanBoundOfCmTheta
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchTop

theorem archSt_of_inp : (∀ D, Inp D) → ArchSt := by
  intro hI
  obtain ⟨C, hC, h⟩ := GlobalTheory.ArchNorm.norm_meanInf_posLog_le
  refine ⟨C, hC, ?_⟩
  intro D cc δ t0 Q hc ht hQ K _ _ _ σ ι N B L P P' zA zA' hN hB h1 hL hd hs hn i
  exact ⟨h D (hI D) cc δ t0 Q hc ht hQ K σ N B L (P i) (zA i) hN hB h1 hL hd (hs i).1 (hn i).1,
    h D (hI D) cc δ t0 Q hc ht hQ K σ N B L (P' i) (zA' i) hN hB h1 hL hd (hs i).2 (hn i).2⟩

end GlobalTheory.ArchTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaJetClassSumArchimedeanBoundOfCmThetaStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaJetClassSum_archimedeanBound_of_cmTheta : (∀ D, Inp D) → ArchSt := by
  first | exact @GlobalTheory.ArchTop.archSt_of_inp | exact GlobalTheory.ArchTop.archSt_of_inp | (intros; apply GlobalTheory.ArchTop.archSt_of_inp <;> assumption)
end
