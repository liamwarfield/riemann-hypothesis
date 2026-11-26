module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NilpotentVolumeOne.LinearIndependentFrameWithNormal

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepGramH
noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.Volumes Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

def StepCM : Prop := ∀ {D : D7} (X : HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig

def StepHerm : Prop := ∀ {D : D7} (X : HidaSetting D), IsHermND X.B.I.cm.sig X.B.I.J

def StepGramH : Prop := ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
  (∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) j i) =
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) i j) →
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u))).det ≠ 0

end MassDataVolumesW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem stepCM : StepCM := by
  intro D X
  exact ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩

theorem stepHerm : StepHerm := by
  intro D X
  exact ⟨fun i j => congrFun (congrFun X.B.I.J_herm i) j, X.B.I.J_det⟩

end MassDataVolumesW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepFrameStd
noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

def StepFrameStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
  ∃ T : X.B.I.F, (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T

theorem stepGramH_of (h : StepFrameStd) : StepGramH := by
  unfold StepGramH
  intro D X u hT1
  obtain ⟨T, hT⟩ := h X u
  exact PI.VolNzeroOne.W.det_gram_tupH_ne_zero X.B.I.cm.sig X.B.I.J (frameOf X u) T hT hT1

end MassDataVolumesW
end
end
