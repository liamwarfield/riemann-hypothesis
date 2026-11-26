module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorStatus
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgStatus
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedStatus
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJInt
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFixJ
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModInertKur

@[expose] public section

namespace Formalism.L2.Th1.CM

theorem cm1 : JInvariantIntegrality := ReciprocityTheory.ChartRestriction.L1.cm1
theorem cm4 : CM4 := ReciprocityTheory.ChartRestriction.L1.cm4
theorem cm3 : CM3 := ReciprocityTheory.ChartRestriction.L1.cmIntegralityThree
theorem cm2 [h : Fact CM2] : CM2 := h.out

end Formalism.L2.Th1.CM
