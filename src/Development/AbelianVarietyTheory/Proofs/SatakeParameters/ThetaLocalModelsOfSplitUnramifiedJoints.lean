module

public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ValIntN
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesIndependentAwayFromPlaceOverP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesAllStepsLtM
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLawAndFixedCoordinateStabiliserLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFrames
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonempty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointSiteChainComparedCarriesAdmittedSystem
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesStepZero
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesStepZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepZero

theorem del_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPos hL
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPos hL 0 (by have := GlobalTheory.TwU.m_eq t μ; omega)

end GlobalTheory.TwV.StepZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesStepZeroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_frameValues_step_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → S.Del 0) := by
  first | exact @GlobalTheory.TwV.StepZero.del_zero | exact GlobalTheory.TwV.StepZero.del_zero | (intros; apply GlobalTheory.TwV.StepZero.del_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesPositiveSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesPositiveSteps
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV.StepDel

theorem del_of_pos : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP hPo hL j _ hj
  exact GlobalTheory.T.kernelSite_frameValues_all_steps_lt_m S hD hP hPo hL j hj

end GlobalTheory.TwV.StepDel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteFrameValuesPositiveStepsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_frameValues_positive_steps : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ j, 1 ≤ j → j < D.R.m → S.Del j) := by
  first | exact @GlobalTheory.TwV.StepDel.del_of_pos | exact GlobalTheory.TwV.StepDel.del_of_pos | (intros; apply GlobalTheory.TwV.StepDel.del_of_pos <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesScalarPowIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPair
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealNormOneAndCharUnitarySmul
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealNormOneAndCharUnitarySmul
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.DetIdealUnitary

theorem determinantIdeal_normOne_and_char_unitary_smul : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∧ ∀ e : Matrix (Fin N) (Fin N) D.host.E, e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e L)) = (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  letI := fun D : D7 => D.host.cmStar
  intro D χ hχ N L hN hsd
  refine ⟨Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.relative_determinant_norm_one D N _ _ hN (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hsd, ?_⟩
  intro e he
  have hu : e ∈ Matrix.unitaryGroup (Fin N) D.host.E := Matrix.mem_unitaryGroup_iff.2 he
  have h := GlobalTheory.Mem.NatEqui.chi_smulLat hχ (L := L) hsd ⟨e, hu⟩
  rw [Finset.prod_inv_distrib] at h
  exact h

end GlobalTheory.DetIdealUnitary
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeterminantIdealNormOneAndCharUnitarySmulStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (N : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → IsSDLat D.host.E N L → TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ∧ ∀ e : Matrix (Fin N) (Fin N) D.host.E, e * star e = 1 → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (SDLat.smulLat e L)) = (∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ e.det)⁻¹ * χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) := by
  first | exact @GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul | exact GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul | (intros; apply GlobalTheory.DetIdealUnitary.determinantIdeal_normOne_and_char_unitary_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPair
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.KerInert.ScalM (qbar_zpow_mem lamC_mul_mem lamC_inv_mem lamC_zpow_mem)

noncomputable section

namespace GlobalTheory.TwV.Xc


set_option maxHeartbeats 4000000 in
theorem scal_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, -, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  obtain ⟨hp5, -, hIn, -, -, -, hχ, -, -⟩ := S.curve
  have hp2 : D.what₂.places.resChar w ≠ 2 := by omega
  intro j hj L0 hL0 La' hLa'
  have hj' : j < D.R.m := hmm ▸ hj
  have hL0lat : ((sysS H X std).Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat _ S.hfin j L0 hL0
  obtain ⟨hAdm, -, -, -, -, -, -, -⟩ := hPair j hj L0 La' hL0lat hLa'
  obtain ⟨hN, hN', hsd, hsd'⟩ := hAdm
  obtain ⟨ha, -, hu⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN hsd).1
  obtain ⟨ha', -, hu'⟩ := chi_alg_unit_inert D _ S.lam t.χ hχ hp2 hIn _ (GlobalTheory.T.determinantIdeal_normOne_char_unitary_smul D t.χ hχ _ _ hN' hsd').1
  obtain ⟨hU0, hord0⟩ := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS j hj'.le L0 hL0lat
  obtain ⟨hU1, hord1⟩ := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS (j + 1) hj' La' hLa'
  have hfill := GlobalTheory.T.systemWeights_eq_shifted_character_exponents S hD hS j hj' La'.1
  have hm1 := S.law.mu_alg j hj' _ hU1
  have hm0 := S.law.mu_alg j hj' _ hU0
  have hn1 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU1
  have hn0 := GlobalTheory.T.norm_lambdaCharacter_normOne_idele_eq_p_pow S hD hS hPos j hj' hfill _ hU0

  have hcf : Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La') ∈ TaylorLogMetric.Qbar := by
    unfold Base.chiFac
    exact TaylorLogMetric.Qbar.mul_mem (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _)
  have hcfn : ‖TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La'))‖ = 1 := by
    unfold Base.chiFac
    rw [lamC_mul_mem S.lam (qbar_zpow_mem ha _) (qbar_zpow_mem ha' _), lamC_zpow_mem S.lam ha,
      lamC_zpow_mem S.lam ha', norm_mul, norm_zpow, norm_zpow, hu, hu', one_zpow, one_zpow, mul_one]
  have hmr : S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hm1 (TaylorLogMetric.Qbar.inv_mem hm0)
  refine ⟨?_, ?_⟩
  · unfold KG.scalG
    exact TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
      (qbar_zpow_mem ha' _)
  have hexp : TaylorLogMetric.lamC S.lam (KG.scalG (J.fd std) t.χ S.muT j L0 La') =
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
        (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
        TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)) := by
    unfold KG.scalG
    rw [lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _))
        (qbar_zpow_mem ha' _),
      lamC_mul_mem S.lam (TaylorLogMetric.Qbar.mul_mem hmr (TaylorLogMetric.Qbar.inv_mem hcf)) (qbar_zpow_mem ha _),
      lamC_mul_mem S.lam hmr (TaylorLogMetric.Qbar.inv_mem hcf), lamC_inv_mem S.lam hcf, lamC_zpow_mem S.lam ha, lamC_zpow_mem S.lam ha']
  have hp0 : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact_mod_cast (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hB' : ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
      TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ = 1 := by
    rw [lamC_mul_mem S.lam hm1 (TaylorLogMetric.Qbar.inv_mem hm0), lamC_inv_mem S.lam hm0, norm_mul, norm_mul, norm_inv, norm_zpow,
      hn1, hn0, ← zpow_neg, ← mul_assoc, ← zpow_add₀ hp0, ← zpow_add₀ hp0]
    convert zpow_zero (‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w])‖) using 2
    simp only [hord1, hord0, KG.expG, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun v _ => by ring
  rw [hexp]
  calc ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
        (TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹) *
          (TaylorLogMetric.lamC S.lam (Base.chiFac t.χ _ _ ((J.fd std).kerN j L0) ((J.fd std).kerN (j + 1) La')))⁻¹ *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j L0))) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          TaylorLogMetric.lamC S.lam (t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN (j + 1) La'))) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))‖
      = ‖((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ KG.expG (sysS H X std) j L0 La' *
          TaylorLogMetric.lamC S.lam (S.muT (j + 1) ((J.fd std).dt (j + 1) La') * (S.muT (j + 1) ((J.fd std).dt j L0))⁻¹)‖ := by
        rw [← mul_assoc, ← mul_assoc, ← mul_assoc, norm_mul, norm_mul, norm_mul, norm_inv, norm_zpow, norm_zpow, hcfn, hu, hu',
          one_zpow, one_zpow, inv_one, mul_one, mul_one, mul_one]
    _ = 1 := hB'
    _ ≤ 1 := le_rfl

end GlobalTheory.TwV.Xc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPairStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Scal) := by
  first | exact @GlobalTheory.TwV.Xc.scal_of_pos_pair | exact GlobalTheory.TwV.Xc.scal_of_pos_pair | (intros; apply GlobalTheory.TwV.Xc.scal_of_pos_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesScalarPowIntegral
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem scal_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hd
  exact GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair S hd ⟨J.alg0, J.alg⟩ (pos_at_site S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hd)

end GlobalTheory.TwV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesScalarPowIntegralStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_seriesScalar_pow_integral : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  first | exact @GlobalTheory.TwV.scal_at_site | exact GlobalTheory.TwV.scal_at_site | (intros; apply GlobalTheory.TwV.scal_at_site <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleJointDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroPointMemDoubleCosetClassRep
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroPointMemDoubleCosetClassRep
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), ∃ κ : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.U, (J.pt std 0 (Nat.zero_le _) La).1 = ratA D.host.F γ * ((J.St 0 (Nat.zero_le _)).y (clsAt X H 0 La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La hLa
  obtain ⟨-, hA⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La
  have hb := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa
  obtain ⟨hγ, κ, hκ⟩ := pt00 J.one La.1 La.2 _ hb _ hA
  have hc : clsAt X H 0 La.1 La.2 = J.e0 (levelZeroClass J.one La.1 La.2) := J.cls0 La.1 La.2 hLa

  obtain ⟨κ', hκ'⟩ := (J.y0 (levelZeroClass J.one La.1 La.2)).imp fun _ h => h.1
  have hU := (J.lev0 (J.chart std 0 (Nat.zero_le _) La)).2.2.1
  have hm : κ'.1⁻¹ * κ.1 ∈ (J.Gd.forms u).cls0.lev.U := Subgroup.mul_mem _ (Subgroup.inv_mem _ κ'.2) κ.2
  refine ⟨rationalElementZero J.one La.1 La.2, hγ, ⟨κ'.1⁻¹ * κ.1, by rw [hU]; exact hm⟩, ?_⟩
  rw [hc, hκ', hκ]
  show _ = _ * _ * (κ'.1⁻¹ * κ.1)
  simp only [mul_assoc, mul_inv_cancel_left]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroPointMemDoubleCosetClassRepStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_point_mem_doubleCoset_classRep : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)), ∃ κ : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.U, (J.pt std 0 (Nat.zero_le _) La).1 = ratA D.host.F γ * ((J.St 0 (Nat.zero_le _)).y (clsAt X H 0 La.1 La.2)).1 * κ.1 := by
  first | exact @GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul | exact GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul | (intros; apply GlobalTheory.TwV.Joint.pt_zero_eq_rat_mul_rep_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroKernelLatticeEqPointKernelLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroKernelLatticeEqPointKernelLattice
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.kerN_zero_eq_latK_pt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), HEq ((J.fd std).kerN 0 La) (latK D.sp (gramN D 0 (Nat.zero_le _)) J.a (J.pt std 0 (Nat.zero_le _) La).1 ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J La
  obtain ⟨⟨hr, hx⟩, -⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La
  have hre := GlobalTheory.reindex_rename_point_det_latK D.sp (lev0At J.Gd u w hg).A.rk.symm (gramN D 0 (Nat.zero_le _)) J.a
    (Classical.epsilon fun x => (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (lev0At J.Gd u w hg).Lb
  have hpt : (J.pt std 0 (Nat.zero_le _) La).1 = (Classical.epsilon fun x => (lev0At J.Gd u w hg).A.IsPt La.1 (basesAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om 0 La.2) x ∧
        x ∈ Formalism.UG.UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := by
    rw [hx]
    exact hre.1
  have hLb : ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb = (lev0At J.Gd u w hg).Lb := (J.lev0 _).1
  rw [hpt, hLb]
  exact hre.2.2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroKernelLatticeEqPointKernelLatticeStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_kernelLattice_eq_pointKernelLattice : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (La : (sysS H X std).Lt 0), HEq ((J.fd std).kerN 0 La) (latK D.sp (gramN D 0 (Nat.zero_le _)) J.a (J.pt std 0 (Nat.zero_le _) La).1 ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) La)).lev.Lb) := by
  first | exact @GlobalTheory.kerN_zero_eq_latK_pt | exact GlobalTheory.kerN_zero_eq_latK_pt | (intros; apply GlobalTheory.kerN_zero_eq_latK_pt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepKernelLatticeEqPointKernelLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepKernelLatticeEqPointKernelLattice
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.TwV.KerSucc

theorem latK_of_renamed {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N n : ℕ} (h : N = n) (hr : n = N) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb Lb₁ : Submodule (𝓞 E) (Fin N → E))
    (J' : Matrix (Fin n) (Fin n) E) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))) (Lb' : Submodule (𝓞 E) (Fin n → E))
    (hJ : J' = J.reindex (finCongr h) (finCongr h)) (hy : x = Formalism.L2.PairingIndexBounds.F.reGL (finCongr hr) y)
    (hLb : Lb' = Lb.map ((reE (E := E) h).toLinearMap.restrictScalars (𝓞 E))) (h₁ : Lb₁ = Lb) :
    HEq ((latK sp J' a y Lb').map ((reE (E := E) (rfl : n = n)).toLinearMap.restrictScalars (𝓞 E))) (latK sp J a x Lb₁) := by
  have h1 := (GlobalTheory.reindex_rename_point_det_latK sp hr J' a y Lb').1
  have h3 := (GlobalTheory.reindex_rename_point_det_latK sp h J a x Lb).2.2
  have hy' : y = Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) x := by rw [hy]; exact h1.symm
  rw [hJ, hLb, h₁, hy']
  exact h3

section Unfold

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  {n0 : ℕ} (A0 : LocAt D.host.F D.host.E n0 (D.gat u w h)) (J0 : Matrix (Fin n0) (Fin n0) D.host.E)
  (Lb0 : Submodule (𝓞 D.host.E) (Fin n0 → D.host.E))
  (Uloc0 : ∀ v : HeightOneSpectrum (𝓞 D.host.F), Subgroup (GL (Fin n0) (D.host.E ⊗[D.host.F] v.adicCompletion D.host.F)))

theorem gram_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).J (i + 1) La =
      (Formalism.L2.Forms.gramN D (i + 1) hi).reindex (finCongr hr) (finCongr hr) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).J = _
  rw [chAt, dite_eq_left hi]

theorem base_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1))
    (hr : D.R.N (i + 1) = ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1) :
    (cpAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0).Lb (i + 1) La =
      ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb.map
        ((reE (E := D.host.E) hr).toLinearMap.restrictScalars (𝓞 D.host.E)) := by
  show (chAt Ch std vp unif eO eO_spec dG dG_spec om I A0 J0 Lb0 Uloc0 (i + 1) La).Lb = _
  rw [chAt, dite_eq_left hi]

end Unfold

end GlobalTheory.TwV.KerSucc

theorem GlobalTheory.TwV.Joint.kerN_succ_heq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → HEq ((J.fd std).kerN (j + 1) La) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La).1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  obtain ⟨hr, hx⟩ := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).1
  have hLb := (GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa).2.1
  have hJ : (J.cp std).J (j + 1) La = (gramN D (j + 1) hj).reindex (finCongr hr.symm) (finCongr hr.symm) :=
    GlobalTheory.TwV.KerSucc.gram_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  have hL : (J.cp std).Lb (j + 1) La = ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev.Lb.map
      ((reE (E := D.host.E) hr.symm).toLinearMap.restrictScalars (𝓞 D.host.E)) :=
    GlobalTheory.TwV.KerSucc.base_succ _ _ _ _ _ _ _ _ _ I _ _ _ _ j hj La hr.symm
  exact GlobalTheory.TwV.KerSucc.latK_of_renamed D.sp hr.symm hr _ J.a _ _ _ _ _ _ hJ hx hL hLb
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepKernelLatticeEqPointKernelLatticeStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.succStep_kernelLattice_eq_pointKernelLattice : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → HEq ((J.fd std).kerN (j + 1) La) (latK D.sp (gramN D (j + 1) hj) J.a (J.pt std (j + 1) hj La).1 ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.Lb) := by
  first | exact @GlobalTheory.TwV.Joint.kerN_succ_heq | exact GlobalTheory.TwV.Joint.kerN_succ_heq | (intros; apply GlobalTheory.TwV.Joint.kerN_succ_heq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepPointMemDoubleCosetClassRep
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepPointMemDoubleCosetClassRep
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.TwV.Joint.pt_succ_coset : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj), ∃ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La hLa
  have hb := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J (j + 1) La hLa
  obtain ⟨-, -, hU, -, hy⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).2
  obtain ⟨hc, κ, hγ, e⟩ := kaAt_pt H j hj ((I.at' j hj).st.eC.symm La.1).1 ((I.at' j hj).st.eC.symm La.1).2 La.2 _
    (fun v => hb v) (J.pt std (j + 1) hj La) hp
  have ea : (I.at' j hj).st.eC ⟨((I.at' j hj).st.eC.symm La.1).1, ((I.at' j hj).st.eC.symm La.1).2⟩ = La.1 :=
    Equiv.apply_symm_apply _ _
  have hc' : (I.at' j hj).st.chOf (clsOf (S := (I.at' j hj).st) (H.core j hj) La.1 La.2) = ((I.at' j hj).st.eC.symm La.1).1 := by
    rw [ea] at hc; exact hc
  refine ⟨_, hγ, ⟨κ.1, (SetLike.ext_iff.1 hU κ.1).2 κ.2⟩, ?_⟩
  rw [hy hc']
  have e2 : ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc⟩ =
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y ⟨_, hc'⟩ :=
    congrArg _ (Subtype.ext (congrArg (fun a => clsOf (S := (I.at' j hj).st) (H.core j hj) a La.2) ea))
  rw [← e2]
  exact e
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SuccStepPointMemDoubleCosetClassRepStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.succStep_point_mem_doubleCoset_classRep : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D (j + 1) hj), ∃ κ : ((J.St (j + 1) hj).K (J.chart std (j + 1) hj La)).lev.U, (J.pt std (j + 1) hj La).1 = ratA D.host.F γ * ((J.St (j + 1) hj).y (clsAt X H (j + 1) La.1 La.2)).1 * κ.1 := by
  first | exact @GlobalTheory.TwV.Joint.pt_succ_coset | exact GlobalTheory.TwV.Joint.pt_succ_coset | (intros; apply GlobalTheory.TwV.Joint.pt_succ_coset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDetEqAdelicPointDet
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDetEqAdelicPointDet
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


set_option maxHeartbeats 2000000 in
theorem joint_dt_eq_det_of_isPt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) x, J.IsPt std j hj La x → (J.fd std).dt j La = Matrix.GeneralLinearGroup.det x.1 := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j hj La x hx
  obtain ⟨hr, hx⟩ := hx
  have h1 : (J.fd std).dt j La = Matrix.GeneralLinearGroup.det ((J.cp std).y j La) := rfl
  rw [h1, hx]
  exact ((reindex_rename_point_det_latK D.sp hr 0 0 ((J.cp std).y j La) ⊥).2.1).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleDetEqAdelicPointDetStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) x, J.IsPt std j hj La x → (J.fd std).dt j La = Matrix.GeneralLinearGroup.det x.1 := by
  first | exact @GlobalTheory.joint_dt_eq_det_of_isPt | exact GlobalTheory.joint_dt_eq_det_of_isPt | (intros; apply GlobalTheory.joint_dt_eq_det_of_isPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleJointDictionary
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.joint_dict : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  intro j hj La hLa
  cases j with
  | zero =>
    have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).1
    exact ⟨hp, GlobalTheory.T.stepZero_point_mem_doubleCoset_classRep t std J La hLa, GlobalTheory.T.stepZero_kernelLattice_eq_pointKernelLattice t std J La, GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det t std J 0 hj La _ hp⟩
  | succ j =>
    have hp := (GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La).1
    exact ⟨hp, GlobalTheory.T.succStep_point_mem_doubleCoset_classRep t std J j hj La hLa, GlobalTheory.T.succStep_kernelLattice_eq_pointKernelLattice t std J j hj La hLa, GlobalTheory.T.lattice_tuple_det_eq_adelic_point_det t std J (j + 1) hj La _ hp⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleJointDictionaryStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuple_joint_dictionary : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  first | exact @GlobalTheory.TwV.joint_dict | exact GlobalTheory.TwV.joint_dict | (intros; apply GlobalTheory.TwV.joint_dict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStep
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasesCarryWittLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdHNatsmulRight
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV

theorem star_eq_hostConj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  apply D.host.φ₀.injective
  exact (IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem stdH_adj (D : D7) {N N' : ℕ} (A : Matrix (Fin N') (Fin N) D.host.E) (x : Fin N → D.host.E)
    (y : Fin N' → D.host.E) :
    stdH D.host.E N x ((A.map D.host.conj)ᵀ *ᵥ y) = stdH D.host.E N' (A *ᵥ x) y := by
  unfold stdH
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [star_eq_hostConj, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply, map_sum,
    map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem stdH_natsmul_left (D : D7) {N : ℕ} (s : ℕ) (x y : Fin N → D.host.E) :
    stdH D.host.E N ((s : D.host.E) • x) y = (s : D.host.E) * stdH D.host.E N x y := by
  unfold stdH
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem stdH_natsmul_right (D : D7) {N : ℕ} (s : ℕ) (x y : Fin N → D.host.E) :
    stdH D.host.E N x ((s : D.host.E) • y) = (s : D.host.E) * stdH D.host.E N x y := by
  unfold stdH
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem adj_maps_sd : ∀ (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (A : Matrix (Fin N') (Fin N) D.host.E) (s : ℕ), IsSDLat D.host.E N L → IsSDLat D.host.E N' L' → (∀ x ∈ L, (s : D.host.E) • (A *ᵥ x) ∈ L') → ∀ y ∈ L', (s : D.host.E) • ((A.map D.host.conj)ᵀ *ᵥ y) ∈ L := by
  intro D N N' L L' A s hL hL' hA y hy
  refine (hL.2.2 _).2 fun x hx => ?_
  rw [stdH_natsmul_right, stdH_adj, ← stdH_natsmul_left]
  exact (hL'.2.2 y).1 hy _ (hA x hx)

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocBasisMaps
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.YYMaps

section Glob

variable (D : D7) {p : ℕ} {N N' : ℕ}

theorem natsmul_mem {V : Type*} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
    (L : Submodule (𝓞 D.host.E) V) (s : ℕ) {y : V} (hy : y ∈ L) : (s : D.host.E) • y ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hy s

theorem homL_maps {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D L L') : ∀ x ∈ L, A *ᵥ x ∈ L' := by
  induction hA using Submodule.span_induction with
  | mem A hA => exact hA
  | zero => intro x _; simp
  | add A B _ _ hA hB => intro x hx; rw [Matrix.add_mulVec]; exact L'.add_mem (hA x hx) (hB x hx)
  | smul c A _ hA => intro x hx; rw [Matrix.smul_mulVec]; exact L'.smul_mem c (hA x hx)

theorem yy_maps
    (hA0 : ∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧
      (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {B : Matrix (Fin N') (Fin N) D.host.E}
    (hB : B ∈ TaylorLogMetric.YYl D L L') :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (B *ᵥ x) ∈ L' := by
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    obtain ⟨s, hs, t, ht⟩ := hA0 a ha
    refine ⟨s, hs, fun x hx => ?_⟩
    have e : (s : D.host.E) • ((a • A) *ᵥ x) = t • (A *ᵥ x) := by
      rw [Matrix.smul_mulVec, smul_smul, ← ht, algebraMap_smul]
    rw [e]
    exact L'.smul_mem t (homL_maps D hA x hx)
  | zero => exact ⟨1, Nat.coprime_one_left p, fun x _ => by simp⟩
  | add B C _ _ hB hC =>
    obtain ⟨s, hs, hB⟩ := hB
    obtain ⟨t, ht, hC⟩ := hC
    refine ⟨s * t, Nat.Coprime.mul_left hs ht, fun x hx => ?_⟩
    have e : ((s * t : ℕ) : D.host.E) • ((B + C) *ᵥ x) =
        (t : D.host.E) • ((s : D.host.E) • (B *ᵥ x)) + (s : D.host.E) • ((t : D.host.E) • (C *ᵥ x)) := by
      rw [Matrix.add_mulVec, smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (t : D.host.E) (s : D.host.E)]
    rw [e]
    exact L'.add_mem (natsmul_mem D L' t (hB x hx)) (natsmul_mem D L' s (hC x hx))
  | smul c B _ hB =>
    obtain ⟨s, hs, hB⟩ := hB
    refine ⟨s, hs, fun x hx => ?_⟩
    rw [Matrix.smul_mulVec, smul_comm]
    exact L'.smul_mem c (hB x hx)

end Glob

theorem locBasis_maps : ∀ (D : D7) (p : ℕ), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → ∀ {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), TaylorLogMetric.LocBasis D p (TaylorLogMetric.YYl D L L') b → ∀ i, ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (b i *ᵥ x) ∈ L' := by
  intro D p hA0 N N' L L' r b hb i
  obtain ⟨s, hs, hsb⟩ := hb.2.1 i
  obtain ⟨t, ht, h⟩ := yy_maps D hA0 hsb
  refine ⟨t * s, Nat.Coprime.mul_left ht hs, fun x hx => ?_⟩
  have := h x hx
  rwa [Matrix.smul_mulVec, smul_smul, ← Nat.cast_mul] at this

end GlobalTheory.TwV.YYMaps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLocSpOfNatCastSmulMem
noncomputable section

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

theorem mem_locSp_of_natCast_smul_mem {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N' : ℕ} (L' : Submodule (𝓞 E) (Fin N' → E)) (z : Fin N' → E) (s : ℕ) (hs : IsUnit (s : W))
    (hz : (s : E) • z ∈ L') : (fun k => ρ (z k)) ∈ locSp W ρ L' := by
  obtain ⟨u, hu'⟩ := hs
  have hmem : (fun k => ρ (((s : E) • z) k)) ∈ locSp W ρ L' := Submodule.subset_span ⟨_, hz, rfl⟩
  have e : (fun k => ρ (z k)) = ((↑u⁻¹ : W)) • (fun k => ρ (((s : E) • z) k)) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Algebra.smul_def]
    rw [← mul_assoc, ← map_natCast (algebraMap W K) s, ← hu', ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ hmem

theorem locSp_maps_of_unit_smul {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E))
    (A : Matrix (Fin N') (Fin N) E) (s : ℕ) (hs : IsUnit (s : W)) (hA : ∀ x ∈ L, (s : E) • (A *ᵥ x) ∈ L') :
    ∀ z ∈ locSp W ρ L, (A.map ρ) *ᵥ z ∈ locSp W ρ L' := by
  intro w hw
  have h : locSp W ρ L ≤ (locSp W ρ L').comap (((A.map ρ).mulVecLin).restrictScalars W) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    show (A.map ρ) *ᵥ (fun k => ρ (x k)) ∈ locSp W ρ L'
    have e : (A.map ρ) *ᵥ (fun k => ρ (x k)) = fun k => ρ ((A *ᵥ x) k) := by
      funext k
      exact (RingHom.map_mulVec ρ A x k).symm
    rw [e]
    exact mem_locSp_of_natCast_smul_mem W K ρ L' _ s hs (hA x hx)
  exact h hw

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasesCarryWittLattices
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FrameLat

theorem colSpan_mul' (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (M g : Matrix (Fin k) (Fin k) K) :
    Formalism.MainNotions.G.colSpan R (M * g) = (Formalism.MainNotions.G.colSpan R g).map ((M.mulVecLin).restrictScalars R) := by
  unfold Formalism.MainNotions.G.colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

theorem latMap_pair' (D : D7) {p : ℕ} (R : Type) {K : Type} [CommRing R] [Field K] [Algebra R K] (ρ : D.host.E →+* K)
    (hu : ∀ s : ℕ, Nat.Coprime s p → IsUnit (s : R)) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin N') (Fin N') K)
    (hG : Formalism.MainNotions.G.colSpan R G = locSp R ρ L) (hG' : Formalism.MainNotions.G.colSpan R G' = locSp R ρ L')
    (B : Matrix (Fin N') (Fin N) D.host.E) (hB : ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ L, (s : D.host.E) • (B *ᵥ x) ∈ L')
    (hL : Formalism.BasicNotions.IsSDLat D.host.E N L) (hL' : Formalism.BasicNotions.IsSDLat D.host.E N' L') :
    (∀ c, (B.map ρ) *ᵥ (fun x => G x c) ∈ Formalism.MainNotions.G.colSpan R G') ∧
    (∀ c, (B.map (fun y => ρ (D.host.conj y)))ᵀ *ᵥ (fun x => G' x c) ∈ Formalism.MainNotions.G.colSpan R G) := by
  obtain ⟨s, hs, hB'⟩ := hB
  constructor
  · intro c
    rw [hG']
    refine locSp_maps_of_unit_smul R K ρ L L' B s (hu s hs) hB' _ ?_
    rw [← hG]
    exact Submodule.subset_span ⟨c, rfl⟩
  · intro c
    have e : (B.map (fun y => ρ (D.host.conj y)))ᵀ = ((B.map D.host.conj)ᵀ).map ρ := by
      ext a b
      rfl
    rw [e, hG]
    refine locSp_maps_of_unit_smul R K ρ L' L _ s (hu s hs) (adj_maps_sd D L L' B s hL hL' hB') _ ?_
    rw [← hG']
    exact Submodule.subset_span ⟨c, rfl⟩

end GlobalTheory.TwV.FrameLat


open GlobalTheory.TwV.FrameLat in
theorem GlobalTheory.TwV.frameLatMapLt_of_ties : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∧ ∀ v, locSp (X.G.P.W v) (ρ v) (fd.kerN j La) = (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)) ∧ locSp (X.G.P.W v) (ρ v) (fd.kerN (j + 1) La') = (X.latAt v (j + 1) La'.2).map (((fd.frM (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))) → Lt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ := by
  intro p _ X _ hfin D fd ρ hA hT
  intro j hj L0 hL0 La' hLa' φ r b hb _ i v
  have hL0' : (X.Pj j).IsLatTup L0.2 := Formalism.L2.G.Pend.repOf_lat X.Lv hfin j L0 hL0
  obtain ⟨hAd, hK⟩ := hT j hj L0 La' hL0' hLa'
  obtain ⟨hK1, hK2⟩ := hK v
  refine latMap_pair' D (X.G.P.W v) (ρ v) (natCast_isUnit_localRing X v) (Formalism.L2.KerInert.RepFrame.Gm X fd.frM φ v)
    (Formalism.L2.KerInert.RepFrame.Gp X fd.frM φ v) ?_ ?_ (b i)
    (GlobalTheory.TwV.YYMaps.locBasis_maps D p hA _ _ b hb i) hAd.2.2.1 hAd.2.2.2
  · rw [hK1]
    unfold Formalism.L2.KerInert.RepFrame.Gm
    rw [colSpan_mul', ← φ.hg v]
  · rw [hK2]
    unfold Formalism.L2.KerInert.RepFrame.Gp
    rw [colSpan_mul', ← φ.hg' v]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrthonormalLocalBasesCarryWittLatticesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormal_local_bases_carry_witt_lattices : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7) (fd : FData X D) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), (∀ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E), ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) → (∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → TaylorLogMetric.admitted D _ _ (fd.kerN j La) (fd.kerN (j + 1) La') ∧ ∀ v, locSp (X.G.P.W v) (ρ v) (fd.kerN j La) = (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)) ∧ locSp (X.G.P.W v) (ρ v) (fd.kerN (j + 1) La') = (X.latAt v (j + 1) La'.2).map (((fd.frM (j + 1) La' v).mulVecLin).restrictScalars (X.G.P.W v))) → Lt.FrameLatMapLt X fd.frM hfin D (fun j La _ => fd.kerN j La) (fun j _ La' => fd.kerN (j + 1) La') ρ := by
  first | exact @GlobalTheory.TwV.frameLatMapLt_of_ties | exact GlobalTheory.TwV.frameLatMapLt_of_ties | (intros; apply GlobalTheory.TwV.frameLatMapLt_of_ties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimes
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SitePrime


set_option maxHeartbeats 2000000 in
theorem resChar_not_mem_S : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), D.what₂.places.resChar w ∉ (t.O u μ).S := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ _ J hmem
  obtain ⟨-, -, -, hg'⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨-, -, -, -, -, hT'⟩ := id hg
  rw [t.O_S u μ] at hmem
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hmem
  rcases hmem with h | (h | h) | h
  · exact hT' (h ▸ dvd_rfl)
  · exact hg' 0 h
  · exact hg' 1 h
  · exact J.away h

end GlobalTheory.TwV.SitePrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SiteResidueCharNotMemBadPrimesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.site_residue_char_not_mem_bad_primes : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), D.what₂.places.resChar w ∉ (t.O u μ).S := by
  first | exact @GlobalTheory.TwV.SitePrime.resChar_not_mem_S | exact GlobalTheory.TwV.SitePrime.resChar_not_mem_S | (intros; apply GlobalTheory.TwV.SitePrime.resChar_not_mem_S <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LamPosGOfLamPos
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem lamPosG_of_lamPos : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E.toCEmb pos lam ρ → RepFrame.LamPosG X E D pos lam ρ := by
  intro p _ X _ E D pos lam ρ h v s x
  change TaylorLogMetric.lamC lam (TaylorLogMetric.embT D (pos ⟨v, s⟩) x) = _
  rw [h v s x]
  rfl

end GlobalTheory.TwU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem kernelSite_seriesData_below_lastStep : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S _hD hP hPos hSc
  refine ⟨?_, ?_, ?_, hSc, J.rho std, ?_, ?_, ?_⟩
  · intro j hj L0 hL0 La' hLa'
    exact (hP j hj L0 La' (repOf_lat _ _ j L0 hL0) hLa').1
  · obtain ⟨hpos, hS⟩ := GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors t std J
    exact ⟨hpos, fun hd => GlobalTheory.T.site_residue_char_not_mem_bad_primes t std J (hS _ Fact.out hd)⟩
  · exact ⟨(t.O u μ).S, GlobalTheory.T.site_residue_char_not_mem_bad_primes t std J, fun j _ L0 _ La' _ y => GlobalTheory.T.intOff_xi0_of_joint t std J S j L0 La' y⟩
  · exact GlobalTheory.TwU.lamPosG_of_lamPos _ S.E D _ _ _ hPos
  · exact fun j La v => GlobalTheory.isUnit_det_frameMatrix_ofCharts _ _ _ j La v
  · refine GlobalTheory.T.orthonormal_local_bases_carry_witt_lattices _ S.hfin D (J.fd std) (J.rho std) (halfDiffInv_integral_at_split D _ _ hg) ?_
    intro j hj La La' h1 h2
    have q := hP j hj La La' h1 h2
    exact ⟨q.1, fun v => ⟨(q.2.2.2.2.2.2.2 v).2.2.1, (q.2.2.2.2.2.2.2 v).2.2.2⟩⟩

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesDataBelowLastStepStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allSites_k1_of_dict_pair_pos_scal : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Scal → S.K1) := by
  first | exact @GlobalTheory.TwV.kernelSite_seriesData_below_lastStep | exact GlobalTheory.TwV.kernelSite_seriesData_below_lastStep | (intros; apply GlobalTheory.TwV.kernelSite_seriesData_below_lastStep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdAtServed
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU

theorem std_at_served : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D), LatTied hT X Y → 2 * rG L.sc ≤ D.R.k → ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (D.gat u w hg).P.m (Y.Fl u w hg).t (Y.Fl u w hg).mm (Y.Fl u w hg).c (D.gat u w hg).P.r ((Y.Fl u w hg).TT v) ((Y.Fl u w hg).a v) ((Y.Fl u w hg).b v) ((D.gat u w hg).P.lam0 v) ((Y.Fl u w hg).w v) := by
  intro D u w hg L hT X Y hLT hk v
  obtain ⟨hmm, -, -, hr, -⟩ := hLT u w hg
  have hS := (D.gat u w hg).P.setting v
  have hgk := hT.gat_k u w hg
  have hrG : 1 ≤ rG L.sc := Nat.succ_le_succ (Nat.zero_le _)
  have hm2 := D.R.two_le_m
  refine ⟨hg.1, hg.2.1, hS.two_le, hS.even, ?_, ?_, ?_, (Y.Fl u w hg).base v, (D.gat u w hg).P.dom v, ?_, ?_⟩
  · rw [hr]; split_ifs <;> omega
  · rw [hr, hgk]; split_ifs <;> omega
  · rw [hmm]; omega
  · exact fun s => ⟨le_trans (le_max_left _ _) ((Y.Fl u w hg).w_ge v s),
      le_trans (le_max_right _ _) ((Y.Fl u w hg).w_ge v s)⟩
  · exact fun s l hl _ => (Y.Fl u w hg).w_mono v s l hl

end GlobalTheory.TwU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointSiteChainComparedCarriesAdmittedSystem
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.TwV


set_option maxHeartbeats 4000000 in
private theorem admissible_at_each_site : Lt.AdmAtEnt2 → AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => DV.Used D μ → OrbitPlaces.Stab0 D → admitted D (sysS H X std) S.Y) := by
  intro hA D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hU hS0
  have hDict := GlobalTheory.T.latticeTuple_joint_dictionary t std J
  have hPair := GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hDict
  have hPos := GlobalTheory.T.site_place_induces_position_embeddings S
  have hMove := GlobalTheory.T.kernelSite_arithmeticGroup_moves_frames S hDict
  have hAway := GlobalTheory.T.kernelSite_series_independent_away_from_place_over_p S hDict
  have hScal := GlobalTheory.T.kernelSite_seriesScalar_pow_integral S hDict
  have hK1 := GlobalTheory.T.allSites_k1_of_dict_pair_pos_scal S hDict hPair hPos hScal
  obtain ⟨hLaw, hLawIn, hXi⟩ := GlobalTheory.T.kernelSite_law_and_fixedCoordinateStabiliserLaw S hPair hPos hMove hAway
  obtain ⟨ι, hι⟩ := GlobalTheory.ThLoc.place_extends_to_iso _ S.lam
  haveI := Lt.fracAt Gl u w hg
  have key := hA D L hT Gi Gl Kc Dx cX ex t u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (kaAt X H hT) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg))
    (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)))
    (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT))
    (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le)
    S.E S.hfin S.hst S.g S.hLT
    (hT.gat_pos u w hg) ex.tw I (Formalism.L2.PairingIndexBounds.F.lev0At J.Gd u w hg) J.a ∅ t.cc t.δ t.B t.χ S.lam (GlobalTheory.TwU.ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT
  have k2 := key S.curve hK1 hXi hLawIn
  refine k2 ⟨ι.toRingHom, Formalism.L2.KerInert.SecondKernelProjection.rdJ I X.onCh ι.toRingHom, Formalism.L2.KerInert.SecondKernelSeries.srOf S.Y, fun j hj => ⟨J.sharp j hj, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := tieStab_kaAtAny X H hT (chainAt H hT) (chainMu_cmp_K _) std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y hU hS0 j hj.le
    rw [kaAtAny_cls] at h1
    rw [kaAt_cls]
    exact h1
  · refine Formalism.L2.KerInert.SecondKernelProjection.series_reading_entries D L hT Gi Gl Kc Dx cX ex u μ w hg (Gl.Fl u w hg) Lv (chainAt H hT) (labAt X H) I H Formalism.L2.G.RelativeIndexFlags.blockRationality_holds hT (chainMu_cmp_K _) X.onCh std (vpOf (D.gat u w hg)) (vpOf_irreducible (D.gat u w hg)) (eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0))) (Lt.dGT D u (D.what₂.places.resChar w)) (Lt.dGT_spec (kaAt X H hT)) (fun v => omOf (D.what₂.places.resChar w) ((D.gat u w hg).P.n' v) (std v).even (std v).two_le) S.Y ι.toRingHom ?_ j
    intro r
    have hz : D.what₂.embLL r ∈ algebraicClosure ℚ ℂ := by
      rw [mem_algebraicClosure_iff]
      exact (Algebra.IsAlgebraic.isAlgebraic r).algHom D.what₂.embLL.toRatAlgHom
    show ι (D.what₂.embLL r) = S.E.iK (ex.cmp.embW u w hg r)
    rw [S.hK r hz, ← hι]
  · exact Formalism.L2.KerInert.SecondKernelSeries.series_compatibility_of (D.what₂.places.resChar w) _ S.Y j
  · have hD : S.Del j := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        exact GlobalTheory.T.kernelSite_frameValues_step_zero S hDict hPair hPos hLaw
      · exact GlobalTheory.T.kernelSite_frameValues_positive_steps S hDict hPair hPos hLaw j hpos hj
    obtain ⟨cK, hn, hd⟩ := hD ι.toRingHom (fun z => hι z)
    refine ⟨cK, ?_, ?_, ?_, hd⟩
    · show ‖cK‖ ≤ 1
      rw [hn]
    · show ‖cK⁻¹‖ ≤ 1
      rw [norm_inv, hn, inv_one]
    · intro h
      rw [h, norm_zero] at hn
      exact zero_ne_one hn

theorem site_cmpLite_siteAdm : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}, Joint t H X → DV.Used D μ → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg (chainAt H hT) ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) Lv (chainAt H hT) := by
  intro hAdm hCur D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X J hU hS hk
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨hg.1⟩
  refine ⟨⟨(kaAt X H hT).cmp, (kaAt X H hT).cmp_zero, (kaAt X H hT).cmp_K, (kaAt X H hT).rat, (kaAt X H hT).val⟩, ?_⟩
  have std : Lt.StdAtW D Gl u w hg := GlobalTheory.TwU.std_at_served D u w hg L hT Gi Gl J.tied hk
  obtain ⟨S⟩ := GlobalTheory.T.jointData_at_p_and_adelicDatum_nonempty hCur t std J
  have hA : admitted D (sysS H X std) S.Y := admissible_at_each_site hAdm S hU hS
  refine ⟨inferInstance, std, vpOf (D.gat u w hg), vpOf_irreducible (D.gat u w hg),
    eOOf (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    eOOf_spec (D.gat u w hg) (p_ne_zero_of_place (D.gat u w hg) (Gl.vOf u w hg 0)),
    Lt.dGT D u (D.what₂.places.resChar w), Lt.dGT_spec (kaAt X H hT), _, S.Y, hA, Lt.dGT_zero _ _ _, fun j => ?_⟩
  unfold Lt.dGT
  split_ifs <;> simp

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointSiteChainComparedCarriesAdmittedSystemStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointSite_chain_compared_carries_admittedSystem : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}, Joint t H X → DV.Used D μ → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg (chainAt H hT) ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) Lv (chainAt H hT) := by
  first | exact @GlobalTheory.TwV.site_cmpLite_siteAdm | exact GlobalTheory.TwV.site_cmpLite_siteAdm | (intros; apply GlobalTheory.TwV.site_cmpLite_siteAdm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLocalModelsOfSplitUnramifiedJoints
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem modelsOK_of_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  intro hA hC D L hT Gi Gl Kc Dx cX ex t hJ h0 hS hk
  classical
  refine ⟨h0, fun μ u w hg => if h : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ then
      ⟨Classical.choose (hJ μ h.1 u w hg h.2),
        chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ h.1 u w hg h.2)))) hT⟩
    else ⟨Gl.Lv u w hg, Gl.Ch u w hg⟩, ?_⟩
  intro μ hU u w hg hq
  have hP : DV.Used D μ ∧ D.what₂.places.resChar w ∉ Dx.Qp μ := ⟨hU, hq⟩
  dsimp only
  have key : ∀ x : (Σ Lv : Levels (Gl.Fl u w hg), Chain Lv),
      x = ⟨_, chainAt (Classical.choose (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2)))) hT⟩ →
      GlobalTheory.TwU.CmpLite D ex.cmp ex.tw u μ w hg x.2 ∧ GlobalTheory.TwU.SiteAdm D u w hg (Gl.Fl u w hg) x.1 x.2 := by
    rintro x rfl
    exact GlobalTheory.T.jointSite_chain_compared_carries_admittedSystem hA hC t
      (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hJ μ hP.1 u w hg hP.2))))).some
      hU hS hk
  exact key _ (dif_pos hP)

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLocalModelsOfSplitUnramifiedJointsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLocalModels_of_splitUnramified_joints : Lt.AdmAtEnt2 → Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex), (∀ μ, DV.Used D μ → JointsAt t μ) → (∀ u, ex.tw.e0 u D.what₂.mu0 = ex.tw.eMu0 u 0 (Nat.zero_le _)) → OrbitPlaces.Stab0 D → 2 * rG L.sc ≤ D.R.k → GlobalTheory.TwU.ModelsOK D Gl ex.cmp Dx ex.tw := by
  first | exact @GlobalTheory.TwV.modelsOK_of_joints | exact GlobalTheory.TwV.modelsOK_of_joints | (intros; apply GlobalTheory.TwV.modelsOK_of_joints <;> assumption)
end
