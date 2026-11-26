module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.FrameReduction
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.MeasureIsomorphismAtInfinity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GenericityConstantDoubleCosets

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitRow
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.Assemble
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SplitRowOf
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace PI.SRW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem splitRow_of (hc : CoreStep) (ha : AaStep) (ht : TrStep) : PI.SplitRow.SplitRow := by
  intro D u F0 Λ hΛ
  obtain ⟨hg, hF, hX⟩ := hΛ
  exact hc _ _ _ _ _ F0 Λ ⟨hg.1.toIsLattice, hF.2.1, hF.2.2.1.1, hF.2.2.2.2,
    hX.trans (Formalism.L2.SG.Saturated.latSpan_aaS D F0).symm,
    fun a => (ha D a).1, fun a => (ha D a).2, ht D⟩

end PI.SRW
end

namespace PI.SRW

theorem splitRow_of_iso (hi : IsoStep) : PI.SplitRow.SplitRow :=
  splitRow_of (coreStep_of frame_reduction hi assembly_reduction) adjoint_action_reduction trace_reduction

end PI.SRW
end

theorem split_row_iso : PI.SplitRow.SplitRow := PI.SRW.splitRow_of_iso PI.SRW.measure_isomorphism_at_infinity
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_function_const (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : Formalism.L2.SG.TermDef.TermFun D u u' :=
  PI.TermAttrConst.UnitaryGroupMassFormula.termFun_of PI.TermAttrConst.UnitaryGroupMassFormula.genericity_constant_double_cosets D u u'
end
