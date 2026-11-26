module

public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.InverseEndoIntegralHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveFormalFirstLevelHolds
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several

@[expose] public section

section -- merged from Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.ConstantCoeffCMulSqSum
noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace PairedSquareConstantCoefficients

section Alg

variable {K : Type} [Field K]

theorem inBlock_mul {ι B : Type} (k : B) (f g : MvPowerSeries ι K) :
    inBlock k (f * g) = inBlock k f * inBlock k g := by
  simp only [HurwitzJetIntegrality.inBlock_eq_rename, map_mul]

theorem tensor_four_mul {ι : Type} (f g : MvPowerSeries ι K) : tens4 (f * g) = tens4 f * tens4 g := by
  unfold tens4
  simp only [inBlock_mul, Finset.prod_mul_distrib]

variable [CharZero K]

theorem inBlock_mvExp {ι B : Type} [Finite ι] (k : B) {f : MvPowerSeries ι K}
    (hf : MvPowerSeries.constantCoeff f = 0) : inBlock k (mvExp f) = mvExp (inBlock k f) := by
  unfold inBlock
  exact mvSubst_mvExp hf
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => MvPowerSeries.constantCoeff_X _)

end Alg

end PairedSquareConstantCoefficients

open PairedSquareConstantCoefficients

end Formalism.L2.Th1.G
end
end

namespace Formalism.L2.Th1.G

theorem jetsInNorm : JetsInNorm := jets_in_norm_holds
theorem jetsRing : JetsRing := jets_ring_holds
theorem jetsExp : JetsExp := jets_exp_holds
theorem jetsFourth : JetsFourth := jets_fourth_holds
theorem intDJets : IntDJets := integral_dist_jets_holds

theorem invEndInt : InvEndInt := inverse_endo_integral_holds
theorem adjUnitNorm : AdjUnitNorm := adjoint_unit_norm_holds
theorem ramifiedShape : RamifiedShape := ramified_shape_holds
theorem curveNegNorm : CurveNegNorm := curve_neg_norm_holds
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := curve_formal_first_level_holds
theorem curveRamified : CurveRamified := CurveRamified_of_shape ramifiedShape adjUnitNorm invEndInt

theorem eigenSplit : EigenSplit := eigen_split_holds
theorem shapeCong : ShapeCong := shape_congruence_holds
theorem shapeOrth : ShapeOrth := shape_orthogonal_holds

end Formalism.L2.Th1.G
