module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedGraphBihomog

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneous
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem graph_bihomog : GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.Statement :=
  GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualStackedGraphBihomogeneousStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_stacked_graph_bihomogeneous : GroundTheory.Heights₂.Heights.DualStackedGraphBihomog.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog | exact GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.graph_bihomog <;> assumption)
end
