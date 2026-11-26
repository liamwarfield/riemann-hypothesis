module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.DoubleCosetDecomposition
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselIntegralConvergenceOfGrowth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.SchurH
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.BeBesselOf

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.SchurDecayBounds.NormIdFixM
namespace PI.WBL.NIS

theorem measSideP : MeasSideP := by
  intro k r z u Wp _ _ _ π μW μN hz hT hπ hW hN
  exact Formalism.MainNotions.MeasFS.measF_side hz hT hπ hW hN

theorem normIdSm_of_growth (hGS : Formalism.FourierDecayAlt.ThreeDimData.GrowthS) (hGG : Formalism.FourierDecayAlt.ThreeDimData.GrowthG) : Formalism.FourierDecayAlt.ThreeDimData.NormIdSm :=
  normIdSm_of hGS hGG measSideP

end PI.WBL.NIS
end

namespace Formalism.FourierDecayAlt.P

theorem bessel_convergence : Formalism.FourierDecayAlt.ThreeDimData.BeConv := bessel_integral_convergence_of_growth growth_spherical_bound

theorem norm_identity_smooth : Formalism.FourierDecayAlt.ThreeDimData.NormIdSm :=
  PI.WBL.NIS.normIdSm_of_growth growth_spherical_bound growth_group_bound

theorem schur_hermitian : Formalism.FourierDecayAlt.ThreeDimData.SchurH := PI.WBL.NIS.schurH

theorem bessel_function_bound : Formalism.FourierDecayAlt.ThreeDimData.BeBessel := PI.WBL.S5.beBessel_of growth_spherical_bound

theorem psi_constant : Formalism.FourierDecayAlt.ThreeDimData.PsiConst := PI.WBL.S5.psiConst

end Formalism.FourierDecayAlt.P
