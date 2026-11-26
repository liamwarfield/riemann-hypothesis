module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredient
namespace GlobalTheory.CompanionTheory.Glob

theorem inductionContragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k :=
  GlobalTheory.SmGL.IndDual.inductionContragredient

end GlobalTheory.CompanionTheory.Glob
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionContragredientStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolic_induction_contragredient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.InductionContragredient k := by
  first | exact @GlobalTheory.CompanionTheory.Glob.inductionContragredient | exact GlobalTheory.CompanionTheory.Glob.inductionContragredient | (intros; apply GlobalTheory.CompanionTheory.Glob.inductionContragredient <;> assumption)
end
