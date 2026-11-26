module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GammaFamilyCommuteGenerators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EqZeroOfIdealCompact
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussSumModulusOfLattice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GaussIndexIndependentOfChoice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PadicChangeOfVariables
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragedVectorChoices
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AveragedKernelSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdicNeighbourhood
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SubmoduleMultiplication
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoBlockPoint
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KernelScalingBack
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HenselRootsBounded
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HessianScalingIntegrals
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermSumLattices

@[expose] public section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6

theorem gauss_hessian_index_exists : Formalism.FourierDecayAlt.A6.GaussHess :=
  gauss_hessian_index_of_parts
    gauss_sum_modulus_of_lattice
    gauss_index_independent_of_choice
    phase_hessian_determinant
    modulus_positive_multiplicative
    volume_scaling_identity

theorem padic_stationary_phase : Formalism.FourierDecayAlt.A6.StationaryPhase :=
  stationaryPhaseOfSteps
    nonStationary morseLemma integral_field_refinement
    modulus_positive_multiplicative rootsFinite compactOpenChoice
    orthogonal_lattice_properties modulusLocallyConstant
    oscillatory_integral_invariant volume_scaling_identity
    rootsSeparated smallModules admissible_gauss_sum_small
    lattice_family_finite

theorem germ_expansion_matrix_function : Formalism.FourierDecayAlt.A6.GermPhi :=
  germExpansionOfTestFunction
    orbital_integral_change_of_variables
    padic_stationary_phase
    oscillatory_integral_invariant
    modulus_positive_multiplicative

theorem germ_expansion_with_head : Formalism.FourierDecayAlt.A6.Germ :=
  germExpansionOfSteps head_reduction_lemma germ_expansion_matrix_function

theorem germ_kernel_expansion : Formalism.FourierDecayAlt.A6.GermKernel :=
  germExpansionKernelOfSteps
    germ_expansion_with_head kernel_as_coset_sum
    integral_points_finite rootsFinite

theorem germ_identity_bis : Formalism.FourierDecayAlt.A6.GermIdentity :=
  germIdentityOfSteps
    gauss_hessian_index_exists germ_kernel_expansion gramKernelHermitian
    second_vanishing_off_ring modulus_positive_multiplicative rootsFinite
    shiftUnit_statement shiftSmall_statement rootCutStable rootCorrection
    square_near_unit phase_difference_estimate phase_locally_constant
    modulusLocallyConstant integral_lattice_refinement_identity
    padic_change_of_variables crossTermsVanish

theorem theta_omega_bound : Formalism.FourierDecayAlt.A6.ThOm :=
  thetaOnDomainOfSteps
    germ_identity_bis averaged_vector_choices_exist phase_locally_constant
    gramKernelHermitian modulusLocallyConstant compactOpenChoice
    lattice_family_finite shiftUnit_statement smallUnits
    gram_equality_of_vectors averaged_vector_norm_bound cut_posSemidef
    heads_distinct_determinant_orthogonal head_size_add_block
    modulus_positive_multiplicative kernel_gram_property
    kernel_block_diagonal_by_modulus gramRealisation averageBound
    parsevalGroup_statement annihilatorCharacters
    orthogonal_lattice_properties characterMean
    truncated_average_norm_formula thetaAverageLower
    averaged_kernel_periodic_psd averaged_kernel_parseval

theorem lattice_average_induction : Formalism.FourierDecayAlt.A5.ThetaExistsStep :=
  thetaExistsStepOfSteps
    theta_omega_bound finite_family_truncation_module
    added_block_kernel_support head_size_one_in_GL rootStableExhaustion
    lattice_family_finite posSemidefEntryBound posSemidefClosed
    boundedSubsequence

theorem lattice_average_lemma_full : Formalism.FourierDecayAlt.A5.LemmaA :=
  lattice_average_lemma_from_parts
    second_gram_and_vanishing first_kernel_parseval
    first_theta_kernel_equality first_theta_equals_first_kernel
    lattice_average_induction zero_kernel_all_ones
    added_block_kernel_support added_block_kernel_block_diagonal

end Formalism.FourierDecayAlt.P
