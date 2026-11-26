module

public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.TiedNum
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpBig
public import CompanionTheory.AutomorphicTheory.CompactTopologicalForms.NormalFormTopDomination
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.WeylGroupActions.UpdateEqUMinus
public import CompanionTheory.AutomorphicTheory.SchurLimitBounds.ZuckermanDuality.LimBdFpm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothAtBuiltPlace
public import CompanionTheory.AutomorphicTheory.BesselWaveGrids.WaveInputsOfHypothesesGlobal
public import CompanionTheory.AutomorphicTheory.RankOneTori.FrameBesselBoundOfLargeConstants
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckDualTThrS
namespace CompanionTheory.Zuck

theorem zuckT_thrS : CompanionTheory.LimBd.Main.ZuckT fun _ ε => ReciprocityTheory.ChartRestriction.DS.G2.thrS ε := by
  intro n ε μ H _ _ _ σ hμ hσ h hg hlt
  obtain ⟨X, -⟩ := ReciprocityTheory.ChartRestriction.DS.G2.zuckerman_tensor_exists n ε μ H σ hμ hσ h hg hlt
  exact ⟨X⟩

theorem zuckDualT_thrS : CompanionTheory.LimBd.Main.ZuckDualT fun _ ε => ReciprocityTheory.ChartRestriction.DS.G2.thrS ε := by
  intro n ε μ H _ _ _ σ hμ hσ h hg hlt
  obtain ⟨X, -⟩ := ReciprocityTheory.ChartRestriction.DS.G2.zuckerman_dual_tensor_exists n ε μ H σ hμ hσ h hg hlt
  exact ⟨X⟩

end CompanionTheory.Zuck
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.WeightedBoundRotatedUniformOfHypsG
section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.WeightedBoundRotatedUniformOfCubicThreshold
section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.EndpointDifferentTypesThreshold
section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.SmoothCoefficientBessel
namespace CompanionTheory.WaveGrid.Coef

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity Formalism.QuantumDeterminants MeasureTheory

theorem global_regularity_jacobi : GRegJ :=
  gRegJ_of nilpotent_derivative unitary_capelli_holds group_equations_post_holds smooth_of_coefficients_holds
    (gRegScalar_of group_chart_holds chart_equations_holds classical_to_weak_solution elliptic_regularity_weighted JfS.symbol_nilpotent_holds lie_stabilizer_splitting)

theorem smooth_coefficient_bessel : SmoothKB := by
  intro P Wp Wq _ _ _ _ _ _ p f A hA hCk hCC heig
  have hThr : JF.TransportedAlt P.k P.r A (2 * P.r + P.k + 1) := hA _ (by
    unfold CompanionTheory.JfS.NN
    nlinarith [Nat.zero_le (2 * P.r * (2 * P.r + P.k + 1) * (2 * P.r + P.k + 1))])
  have hF := Gr.jf_mem_FFlM p.T.base A (2 * P.r + P.k + 1) f hThr (hCC _)
  obtain ⟨_, _, _, _, _, hTy, hTy'⟩ := p.hP
  refine global_regularity_jacobi P.k P.r Wp Wq p.T.base _ _ (B.JF p.T.base f) hTy hTy' hF fun Y => ?_
  obtain ⟨c, hc⟩ := heig Y
  refine ⟨c, fun g hg => ?_⟩
  have hgG : g ∈ B.GV P.k P.r := hg.1
  have hCkn : B.CkOn ((2 * P.r + P.k + 1 : ℕ) : ℕ∞) (B.GV P.k P.r) f := B5.ckOn_mono le_top hCk
  rw [casimir_under_jacquet_integral P.k P.r Wp Wq p.T.base A (2 * P.r + P.k + 1) f (Y : ℂ) le_rfl hThr (hCC _) _ hg]
  have hint : ∀ᵐ q ∂p.T.base.μSS,
      JF.xiP p.T.base q • Q.CV P.k P.r (Y : ℂ) (B.rho p.T.base q f) g =
        c • (JF.xiP p.T.base q • B.rho p.T.base q f g) := by
    filter_upwards [B7.ae_inSS p.T.base] with q hq
    rw [capelli_rho_commute P.k P.r _ _ p.T.base (Y : ℂ) f q hq hCkn _ hgG]
    have hs := B7.sgs_mem p.T.base hq hgG
    simp only [B.rho]
    rw [hc _ hs, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_comm]
  rw [integral_congr_ae hint, integral_smul]
  rfl

end CompanionTheory.WaveGrid.Coef
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.LimStepsOf
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq CompanionTheory.LimBd.Main

theorem limSteps_of (hI : PI.DSInfCharCap.DSInfCharCap) : LimSteps :=
  ⟨generating_function_polynomial, span_powers, CompanionTheory.CapEig.capelli_coefficient_smooth, CompanionTheory.CapEig.capelli_coefficient_continuity,
    CompanionTheory.CapEig.coefEig_of_infChar hI, phase_zero_alt, beta_at_infinity_zero⟩

end CompanionTheory.WaveGrid
end

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBPEq
open CompanionTheory.LimBd.Main (ZuckT ZuckDualT zuckT_of_zuck zuckDualT_of_zuckDual)

theorem asymptotic_different_types : AsmDiff := by
  intro Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := CutBP.CompactFormNormalFormDomination.thmBpAt_top Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA _
  exact h Wp Wq P p f b Λ A₀ p₀ χ nn Y K N hb hΛ hΛb hT hp₀ hK hKN hχ hnn hCb hf hfA

theorem asymptotic_equal_types : AsmEq := by
  intro Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨C₄, c₃, Cc, Cc', Cc'', h⟩ := CutBPEq.CompactFormNormalFormDomination.thmBpAt_eqR_top Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, Cc', Cc'', ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnp hnm hDp hDm hf
    hfA _ _
  exact h P Wp Wq p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnp hnm hDp hDm hf hfA

end CompanionTheory.WaveGrid
end

section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.WeightedUniformRotatedOfExpansion
section -- merged from CompanionTheory.AutomorphicTheory.BesselWaveGrids.NormalizedMeasureScaling
noncomputable section

namespace CompanionTheory.WaveGrid.Ties

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.L2.SG.Pf.BesselExpansion Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open scoped ENNReal

section energy

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {k r : ℕ}

theorem norm_JF_eq (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (d : Fin (r + 1) → ℂ)
    (hd : ∀ a, d a ≠ 0) {γ γ' : B.Mat k r} (hγ : γ ∈ B.GV k r) (hγ' : γ' ∈ B.GV k r)
    (hZ : Zhat k r Bs.z Bs.z' γ = D.ptMatN (PBJ.bigPt d) (r + 1))
    (hZ' : Zhat k r Bs.z Bs.z' γ' = D.ptMatN (PBJ.bigPt d) (r + 1)) (hpos : 0 < Gf k r Bs.z Bs.z' γ) :
    ‖B.hsVec (B.JF Bs F γ)‖ = ‖B.hsVec (B.JF Bs F γ')‖ := by
  have hl : D.IsLocPt (PBJ.bigPt d) (r + 1) := PBJ.Dens.isLocPt_bigPt d hd
  have hpos' : 0 < Gf k r Bs.z Bs.z' γ' := by
    rw [← ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ', ptG_spec k r _ _ (PBJ.bigPt d) _ hl hZ]
    exact hpos
  obtain ⟨s, hs, s', hs', hγs⟩ := fibre_orbit_description k r Bs.z Bs.z'
    ⟨Bs.k_pos, Dx2.VV.std_vector_z Bs, Dx2.VV.std_vector_z_prime Bs⟩ _ hγ _ hγ' hpos (hZ.trans hZ'.symm)
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z Bs) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Dx2.VV.std_vector_z_prime Bs) hs'
  have hlaw := Dx2.VV.orbJ_pt Bs (PBJ.bigPt d) hl hγ hZ hpos hhA hnA hfA hhB hnB hfB F
  rw [← hγs] at hlaw
  have hw : (hl.2 ▸ D.ptPerm (PBJ.bigPt d) : Equiv.Perm (Fin (r + 1))) = 1 :=
    PBM.cast_perm_eq_one _ _ (PBM.ptPerm_bigPt d hd)
  obtain ⟨hmono, hnz⟩ := Dx2.VV.ptMatN_monoP' (PBJ.bigPt d) (r + 1) hl.2 hl.1
  rw [hw] at hmono hlaw
  rw [PBM.orbJ_one_eq Bs hγ' hpos' hnz (hZ'.trans hmono) F, PBM.orbJ_one_eq Bs hγ hpos hnz (hZ.trans hmono) F] at hlaw
  rw [← hlaw, CutBP.hsVec_norm_CinL Bs hhA hhB]

theorem normSq_sec (hk : 2 ≤ k) (Bs : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hsec : IsSection k r Bs.z Bs.z' μsec) :
    B.normSq Bs F = jNormSq k r (Tz k r Bs.z) (Tz k r Bs.z')
      fun q => Real.sqrt (hsNormSq (B.JF Bs F (bigCell k r q.1 (μsec q.2)))) := by
  unfold B.normSq jNormSq
  refine lintegral_congr fun q => ?_
  by_cases hw0 : bcWeight k r (Tz k r Bs.z) (Tz k r Bs.z') q = 0
  · rw [hw0, zero_mul, zero_mul]
  obtain ⟨hc, hζ⟩ := Formalism.MainNotions.S.Pv.LemmaJ.bcWeight_ne hk hw0
  have hζ0 : q.2 ≠ 0 := by
    intro h
    rw [h, map_zero] at hζ
    exact absurd (mul_pos Bs.T_pos Bs.T'_pos) (not_lt.2 hζ.le)
  obtain ⟨d, hd1, hd2⟩ : ∃ d : Fin (r + 1) → ℂ, (fun i : Fin r => d i.castSucc) = q.1 ∧ d (Fin.last r) = q.2 :=
    ⟨Fin.snoc q.1 q.2, by funext i; simp, by simp⟩
  have hd : ∀ a, d a ≠ 0 := fun a => by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [hd2]; exact hζ0
    · rw [congrFun hd1 i]; exact hc i
  have hZ := PBM.zhat_bigCell_pt Bs d (by rw [hd2]; exact hζ)
  have hZ' := PBM.zhat_bigCell_pt { Bs with μsec := μsec, sec := hsec } d (by rw [hd2]; exact hζ)
  rw [hd1, hd2] at hZ hZ'
  have e := norm_JF_eq Bs F d hd (bigCellMem k r _ _ hc (Bs.sec.2 _ hζ).1) (bigCellMem k r _ _ hc (hsec.2 _ hζ).1) hZ hZ'
    (Formalism.MainNotions.S.Pv.LemmaJ.Gf_big Bs.z_mem Bs.z'_mem Bs.sec q.1 hc q.2 hζ)
  congr 2
  rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_nonneg _), Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_eq]
  change ‖B.hsVec (B.JF Bs F (bigCell k r q.1 (Bs.μsec q.2)))‖ ^ 2 = _
  rw [e, PiLp.norm_sq_eq_of_L2]
  rfl

end energy

theorem energy_identity : EnergyTie := by
  intro k r L f μsec u u' p _ hc _ _ htie _ _ hsec
  obtain ⟨hz, hz', hπ, hπ', hW, hN, hW'⟩ := htie
  have e : TBB.jN2 p f = jNorm2 L f μsec := by
    refine (GlobalTheory.T.jN2_eq_normSq_base (parOfL L u u') L.Wp L.Wq p f).trans ?_
    have h := normSq_sec (k := k) (r := r) p.hl.2.2 p.T.base f μsec (by
      have e1 : (p.T.base.z : Fin (2 * r + k + 1) → ℂ) = L.z := hz
      have e2 : (p.T.base.z' : Fin (2 * r + k + 1) → ℂ) = L.z' := hz'
      exact e1 ▸ e2 ▸ hsec)
    refine h.trans ?_
    unfold jNorm2 LocBessel.J B.JF
    rw [hc]
    simp only [hz, hz', hπ, hπ', hW, hN, hW']
  rw [e]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact one_le_pow₀ (by linarith [Real.pi_gt_three])

section scale

variable {k r : ℕ}

@[reducible] def withN (L : LocBessel k r) (κ : ℝ≥0∞) : LocBessel k r := { L with κN := κ }

theorem pairMeas_smul (L : LocBessel k r) (κ s : ℝ≥0∞) (h : L.μN = s • (withN L κ).μN) :
    pairMeas L = (s * s) • pairMeas (withN L κ) := by
  have i1 : SFinite (withN L κ).μN := Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _
  have i2 : SigmaFinite L.μW := L.hμW.1.1
  have i3 : SigmaFinite L.μW' := L.hμW'.1.1
  unfold pairMeas
  rw [h]
  change (L.μW.prod (s • (withN L κ).μN)).prod (L.μW'.prod (s • (withN L κ).μN)) =
    (s * s) • (L.μW.prod (withN L κ).μN).prod (L.μW'.prod (withN L κ).μN)
  rw [Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_right, Measure.prod_smul_left, smul_smul]

theorem orbSq_le (L : LocBessel k r) (κ s : ℝ≥0∞) (hs0 : s ≠ 0) (hs : s ≠ ⊤)
    (h : pairMeas L = s • pairMeas (withN L κ)) (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) :
    orbSq L f γ ≤ ENNReal.ofReal (s.toReal ^ 2) * orbSq (withN L κ) f γ := by
  unfold orbSq
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hc => ?_
  have hq : IsOrbQuot (withN L κ) g μR (s⁻¹ • ν) := by
    intro φ hφ
    have e := hc.2.2.2 φ hφ
    rw [h, lintegral_smul_measure] at e
    rw [lintegral_smul_measure, ← e, smul_eq_mul, smul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hs0 hs, one_mul]
  have e : OrbInt L f g ν = ((s.toReal : ℝ) : ℂ) • OrbInt (withN L κ) f g (s⁻¹ • ν) := by
    have e1 : ν = s • (s⁻¹ • ν) := by rw [smul_smul, ENNReal.mul_inv_cancel hs0 hs, one_smul]
    unfold OrbInt
    conv_lhs => rw [e1, integral_smul_measure]
    rw [Complex.coe_smul]
    rfl
  rw [e, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' le_rfl ?_
  exact le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le (s⁻¹ • ν) (le_iSup_of_le ⟨hc.1, hc.2.1, hc.2.2.1, hq⟩ le_rfl)))

theorem jNorm2_eq (L : LocBessel k r) (κ s : ℝ≥0∞) (h : pairMeas L = s • pairMeas (withN L κ))
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    jNorm2 L f μsec = ENNReal.ofReal (s.toReal ^ 2) * jNorm2 (withN L κ) f μsec := by
  have hJ : ∀ g, L.J f g = ((s.toReal : ℝ) : ℂ) • (withN L κ).J f g := fun g => by
    change ∫ x, besselIntg L f g x ∂(pairMeas L) = _ • ∫ x, besselIntg L f g x ∂(pairMeas (withN L κ))
    rw [h, integral_smul_measure, Complex.coe_smul]
  rw [Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, Formalism.MainNotions.BesselShellMomentBounds.jNorm2_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun q => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold Formalism.MainNotions.BesselShellMomentBounds.dens
  rw [hJ, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change _ = _ * (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * _)
  ring

end scale

end CompanionTheory.WaveGrid.Ties
end
end

noncomputable section

namespace CompanionTheory.WaveGrid.WGlue

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.BesselShellMomentBounds Formalism.MainNotions.TheoremBConstants
  Formalism.MainNotions.BigCellDensity Formalism.L2.SG.Pf.BesselExpansion
open CompanionTheory.WaveGrid CompanionTheory.WaveGrid.Tied
open scoped ENNReal

def WIneq {k r : ℕ} (L : LocBessel k r) (f : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (γ : Point ℂ (r + 1)) (w K : ℝ) : Prop :=
  ENNReal.ofReal (w * ptWeight k r (Tz k r L.z) (Tz k r L.z') γ) * orbSq L f γ ≤ ENNReal.ofReal K * jNorm2 L f μsec

def WLoc1 (D : D7) (Ch Cg Ca C : ℝ) (N : LocBessel D.R.k D.R.rS → Prop) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ), N L → LocOk D Ch Cg L L.lam ka b 1 →
    AllGaps L.lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4) → IsKFinCoefH L.σ f → IsSection D.R.k D.R.rS L.z L.z' μsec →
    ∀ (l : Fin (D.R.rS + 1)) (a : ℕ), (a : ℝ) ≤ Ca * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 → ∀ γ : Point ℂ (D.R.rS + 1),
      Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 →
      WIneq L f μsec γ (‖Dpt γ l‖ ^ (2 * a)) (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) *
        max 1 (1 / Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ) ^ (40 * (D.R.rS + 1) ^ 2))

set_option maxHeartbeats 1600000 in
theorem wLoc1N_of (hW : ∀ Cb, WEnd.WBp Cb) {Cgc : ℝ} (hCC : CoefCC1 Cgc) (Ch Ca : ℝ) :
    ∃ C Cg₀ : ℝ, 0 ≤ C ∧ ∀ Cg, Cg₀ ≤ Cg → ∀ D : D7,
      WLoc1 D Ch Cg Ca C fun L => L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS := by
  obtain ⟨Cb, hPl⟩ := TypeHC.exists_place
  obtain ⟨C₅, Cg₁, hC5, H⟩ := hW Cb (2 * |Ch|) Ca (by positivity)
  refine ⟨C₅ + 8, max (max Cg₁ Cgc) 1000, by linarith, ?_⟩
  intro Cg hCg D L f μsec ka b hμN hL hg4 hf hsec l a ha γ hG
  have g1 : Cg₁ ≤ Cg := le_trans (le_max_of_le_left (le_max_left _ _)) hCg
  have g2 : Cgc ≤ Cg := le_trans (le_max_of_le_left (le_max_right _ _)) hCg
  have g3 : 1000 ≤ Cg := le_trans (le_max_right _ _) hCg
  unfold WIneq
  by_cases h0 : orbSq L f γ = 0
  · simp [h0]
  obtain ⟨hk1, hε, hc, hN0, hNt, hStd, hT1, hT1'⟩ := hL
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk1 hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  obtain ⟨hlam, hI, hI', hka, hka1, -, -, -, hTle, hTle', hlamb, hub, hub', -, hgap, ⟨bv, hbv, hshape⟩, hcut⟩ := hStd
  have hk2 : 2 ≤ D.R.k := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hε' : L.ε = PI.BesselPeriodGGP.eps48 D.R.k D.R.rS := by
    rw [hε]
    funext i
    simp [PI.BesselPeriodGGP.eps48, epsSH, epsS]
  clear hε
  rw [one_pow, mul_one] at hT1 hT1'
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hcStd : L.c = cStd := by rw [hc]; exact Formalism.MainNotions.OnePlaceEstimates.cOfDpsi_one
  have hInCC := hCC D.R.k D.R.rS L f hk1 hf (Formalism.L2.SG.Pf.BesselExpansion.gap_mono hgap
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right g2 (by positivity)) (by positivity)))
  have hok := GapSizes.gapOK_of D.R.k D.R.rS hk1 Cg g3
  rw [mul_assoc] at hgap hok
  have hu := GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW (z := L.z) (u := L.u) (π := L.π) L.hπ
  have hu' := GlobalTheory.BesselMapCompare.isHCParam_of_isHCTypeW (z := L.z') (u := L.u') (π := L.π') L.hπ'
  have hTy := hypType_of hk1 hlam hu hI hub
  have hTy' := hypType_of hk1 hlam hu' hI' hub'
  obtain ⟨hcl, hnd⟩ := shape_of hk1 hlam hu hI hshape
  have hPOK : (parOfL L (lamN L.u) (lamN L.u')).OK :=
    Inhab.ok_diff (parOfL L (lamN L.u) (lamN L.u')) hk1 L.hz.2 L.hz'.2 L.lam b hlam hTy hTy'
  have hplace : Formalism.FourierDecayAlt.Q.IsPlace (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π L.π' :=
    ⟨hPOK, L.hz.1, L.hz'.1, rfl, rfl, TypeHC.isType_of_hc L.hz.1 L.hz.2 L.hπ (lamN_succ L.u),
      TypeHC.isType_of_hc L.hz'.1 L.hz'.2 L.hπ' (lamN_succ L.u')⟩
  have hW := Formalism.MainNotions.BridgeLemma₃.hu_haarUp.1 D.R.k D.R.rS L.z L.μW L.hz.1 L.hz.2 L.hμW.1
  have hW' := Formalism.MainNotions.BridgeLemma₃.hu_haarUp.1 D.R.k D.R.rS L.z' L.μW' L.hz'.1 L.hz'.2 L.hμW'.1
  have hfK : Formalism.FourierDecayAlt.P.CutBP.KFinDSCoef (PI.BesselPeriodGGP.eps48 D.R.k D.R.rS) L.lam f := by
    obtain ⟨Pm, Qm, h1, h2, h3⟩ := hf
    exact ⟨L.Hs, _, _, _, L.σ, Pm, Qm, L.hlam, hε' ▸ L.hσ, h1, h2, fun g _ => h3 g⟩
  have hr2 : 36 * ((D.R.rS : ℝ) + 1) ^ 2 ≤ Cg * ((D.R.rS : ℝ) + 1) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hr1 : 1 ≤ ((D.R.rS : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg D.R.rS : (0 : ℝ) ≤ D.R.rS)]
  obtain ⟨pl, ⟨hz, hz', hπ, hπ', hμW, hμN', hμW'⟩, hcase⟩ :
      ∃ pl : Formalism.FourierDecayAlt.KB.Pl (parOfL L (lamN L.u) (lamN L.u')) L.Wp L.Wq, PlTie L pl ∧
        ((30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6 ≤ |lamN L.u pl.l0 - lamN L.u' pl.l0| ∧
          Formalism.FourierDecayAlt.KB.InDDplus2 _ pl.l0 pl.T.base Cb pl.Θ) ∨
        (lamN L.u = lamN L.u' ∧ ∃ l, 1 ≤ l ∧ l < D.R.k ∧
          2 * (30 * ((D.R.rS : ℝ) + 1) ^ 2 + 6) + 1 ≤ lamN L.u l - lamN L.u (l + 1))) := by
    rcases hcut with ⟨huu, i, hi, hposition, -⟩ | ⟨-, x, y, ⟨i, x', y', -, hxy, hIcc, hx, hy, -⟩, hlen⟩
    · obtain ⟨p, -, e1, e2, e3, e4, e5, e6, e7, -⟩ := hPl L.Wp L.Wq (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π
        L.π' L.μW L.μW' 1 hplace hk2 le_rfl hk1 hW L.hμW.2 hW' L.hμW'.2
      refine ⟨p, ⟨e1, e2, e3, e4, e5, e6.trans hμN.symm, e7⟩, Or.inr ⟨congrArg lamN huu, i + 1, by omega, hi, ?_⟩⟩
      rw [lamN_succ L.u ⟨i, by omega⟩, lamN_succ L.u ⟨i + 1, hi⟩]
      linarith only [hposition, hr1, hr2]
    · obtain ⟨p, e0, e1, e2, e3, e4, e5, e6, e7, hDD⟩ := hPl L.Wp L.Wq (parOfL L (lamN L.u) (lamN L.u')) L.z L.z' L.π
        L.π' L.μW L.μW' (i + 1) hplace hk2 (by omega) i.isLt hW L.hμW.2 hW' L.hμW'.2
      refine ⟨p, ⟨e1, e2, e3, e4, e5, e6.trans hμN.symm, e7⟩, Or.inl ⟨?_, hDD⟩⟩
      rw [e0, lamN_succ L.u i, lamN_succ L.u' i]
      have hxy0 : x ≤ y := by linarith only [hlen, hr1, hr2]
      have h1 : x ∈ Set.Icc x' y' := hIcc ▸ ⟨le_rfl, hxy0⟩
      have h2 : y ∈ Set.Icc x' y' := hIcc ▸ ⟨hxy0, le_rfl⟩
      have h3 := max_sub_min_eq_abs (-L.u i) (-L.u' i)
      rw [show -L.u' i - -L.u i = L.u i - L.u' i by ring] at h3
      linarith only [h1.1, h2.2, hx, hy, h3, hlen, hr1, hr2]
  obtain ⟨g, hg⟩ := exists_relrep L f γ h0
  have hG0 := GPoint_nonneg_of_rep L γ g hg.1
  have hGpos : 0 < Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := lt_of_le_of_ne hG0 (Ne.symm hG)
  have hloc := isLocPt_swap γ
  have hTT : Formalism.FourierDecayAlt.TBB.TTp pl = Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' := by
    unfold Formalism.FourierDecayAlt.TBB.TTp; rw [hz, hz']; rfl
  have hGeq : Formalism.FourierDecayAlt.TBB.Gp pl (γ.1.map Prod.swap) = Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := by
    unfold Formalism.FourierDecayAlt.TBB.Gp; rw [hTT]; exact ptG_eq_GPoint _ _ γ
  have hB := H Cg g1 (parOfL L (lamN L.u) (lamN L.u')) L.Wp L.Wq pl f L.lam b bv l (Nat.le_of_lt_succ l.isLt) a hfK
    hTy hTy' hcl hnd hlamb hbv (fun s s' h => gap_of_lt hlam hg4 h) (hε' ▸ hgap) hok hT1 hT1'
    (scaled_le D.R.rS hb1 hka hka1 hTle) (scaled_le D.R.rS hb1 hka hka1 hTle') hcase ha _ hloc (by rw [hGeq]; exact hGpos)
  have hm : MomL.mnr (Nat.le_of_lt_succ l.isLt) (γ.1.map Prod.swap) = Dpt γ l := by
    unfold MomL.mnr Dpt leadMinor
    rw [ptMatN_swap]
  have hwt := weightTie D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ hk1
  have hn0 : 0 ≤ ptWeight D.R.k D.R.rS (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := by
    unfold ptWeight
    exact ptWeightFrom_nonneg _ _ _ _ _ 0 (fun b hb => (γ.2.1 b hb).2) (by rw [Nat.zero_add]; exact γ.2.2)
      (fun t ht => last_ok_of_G _ _ _ hG0 t ht)
  have hnPt : 0 ≤ Formalism.FourierDecayAlt.TBB.nPt D.R.k D.R.rS (Formalism.FourierDecayAlt.TBB.TTp pl) (γ.1.map Prod.swap) := by
    rw [hTT, ← hwt]; exact hn0
  have hEw : Formalism.FourierDecayAlt.TBB.Ew pl (fun _ => 1) f (D.R.rS + 1) [] (γ.1.map Prod.swap) =
      Formalism.FourierDecayAlt.TBB.nPt D.R.k D.R.rS (Formalism.FourierDecayAlt.TBB.TTp pl) (γ.1.map Prod.swap) *
        (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV pl.T.base pl.ν' pl.m₀ f (γ.1.map Prod.swap))
          (Formalism.FourierDecayAlt.D.vecV pl.T.base pl.ν' pl.m₀ f (γ.1.map Prod.swap))).re := ew_top pl f (γ.1.map Prod.swap) hloc hnPt
  rw [hTT, ← hwt] at hEw
  have hX := tieTopXk D.R.k D.R.rS hk1 L pl.T.base pl.ν' pl.m₀ hcStd hN0 hNt hz hz' hπ hπ' hμW hμN' hμW' pl.hF f γ
    hf hInCC hGpos ⟨g, hg⟩
  have hJ := Ties.energy_identity D.R.k D.R.rS L f μsec _ _ pl hk1 hcStd hN0 hNt ⟨hz, hz', hπ, hπ', hμW, hμN', hμW'⟩ hf hInCC
    hsec
  have hπb : Real.pi ^ (2 * (2 * D.R.rS + 2) ^ 2) ≤ b ^ (4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) := by
    have h1 : Real.pi ≤ b ^ 2 := by nlinarith [Real.pi_lt_four]
    refine (pow_le_pow_left₀ Real.pi_pos.le h1 _).trans ?_
    rw [← pow_mul, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
    have h2 : ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 ≤ ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + 2)) (by norm_num)
    push_cast at h2 ⊢
    linarith
  have hpc : Real.pi ^ (2 * Formalism.MainNotions.BigCellDensity.pc D.R.rS (γ.1.map Prod.snd)) ≤ Real.pi ^ (2 * (2 * D.R.rS + 2) ^ 2) := by
    refine pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) ?_
    have := pc_le D.R.rS (γ.1.map Prod.snd)
    nlinarith
  change ENNReal.ofReal (‖MomL.mnr (Nat.le_of_lt_succ l.isLt : (l : ℕ) ≤ D.R.rS) _‖ ^ (2 * a) * Formalism.FourierDecayAlt.TBB.Ew pl _ f (D.R.rS + 1) [] _) ≤
    ENNReal.ofReal (b ^ (C₅ * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) * max 1 (1 / Formalism.FourierDecayAlt.TBB.Gp pl _) ^ (40 * (D.R.rS + 1) ^ 2)) *
      Formalism.FourierDecayAlt.TBB.jN2 pl f at hB
  rw [hm, hGeq] at hB
  rw [hEw] at hB
  rw [hX, ← ENNReal.ofReal_mul (mul_nonneg (by positivity) hn0), mul_left_comm, ENNReal.ofReal_mul (by positivity),
    mul_assoc]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal (hpc.trans hπb))
    (hB.trans (mul_le_mul' le_rfl (hJ.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hπb) le_rfl))))).trans (le_of_eq ?_)
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [show (C₅ + 8) * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 = 4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 + C₅ * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 +
    4 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5 by ring, Real.rpow_add hb0, Real.rpow_add hb0]
  ring

theorem wLoc1_of_N {D : D7} {Ch Cg Ca C : ℝ}
    (H : WLoc1 D Ch Cg Ca C fun L => L.μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS) : WLoc1 D Ch Cg Ca C fun _ => True := by
  intro L f μsec ka b _ hok hg hf hsec l a ha γ hγ
  obtain ⟨c, hc0, hc1, hc⟩ := Formalism.MainNotions.BridgeLemma₃.hu_eq_smul (Formalism.FourierDecayAlt.P.unipotent_radical_closed D.R.k D.R.rS)
    (Formalism.FourierDecayAlt.P.nilpotent_measure_is_haar D.R.k D.R.rS) (Formalism.MainNotions.BridgeCSB.haarLieN D.R.k D.R.rS 1 one_ne_zero ENNReal.one_ne_top)
  have hsm : ∀ κ : ℝ≥0∞, haarLie (Nset D.R.k D.R.rS) κ = κ • haarLie (Nset D.R.k D.R.rS) 1 := fun κ => by
    simp [haarLie]
  have h1 : (Ties.withN L c⁻¹).μN = Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS := by
    change haarLie _ c⁻¹ = _
    rw [hsm, hc, smul_smul, ENNReal.inv_mul_cancel hc0 hc1, one_smul]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hok
  have h2 : L.μN = (L.κN * c) • (Ties.withN L c⁻¹).μN := by
    rw [h1, ← smul_smul, ← hc]
    exact hsm _
  have hs0 : L.κN * c ≠ 0 := mul_ne_zero a4.ne' hc0
  have hs1 : L.κN * c ≠ ⊤ := ENNReal.mul_ne_top a5 hc1
  have h3 := Ties.pairMeas_smul L c⁻¹ _ h2
  have hB := H (Ties.withN L c⁻¹) f μsec ka b h1
    ⟨a1, a2, a3, ENNReal.inv_pos.2 hc1, ENNReal.inv_ne_top.2 hc0, a6⟩ hg hf hsec l a ha γ hγ
  unfold WIneq at hB ⊢
  rw [Ties.jNorm2_eq L c⁻¹ _ h3 f μsec]
  calc _ ≤ _ * (_ * orbSq (Ties.withN L c⁻¹) f γ) :=
        mul_le_mul' le_rfl (Ties.orbSq_le L c⁻¹ _ (mul_ne_zero hs0 hs0) (ENNReal.mul_ne_top hs1 hs1) h3 f γ)
    _ = _ * (_ * orbSq (Ties.withN L c⁻¹) f γ) := mul_left_comm _ _ _
    _ ≤ _ * (_ * jNorm2 (Ties.withN L c⁻¹) f μsec) := mul_le_mul' le_rfl hB
    _ = _ := mul_left_comm _ _ _

theorem dpt_le {r : ℕ} {ka B : ℝ} (hka : 0 < ka) (h1 : ka ≤ B) (h2 : ka⁻¹ ≤ B) (hB : 1 ≤ B) (γ : Point ℂ (r + 1))
    (l : Fin (r + 1)) : ‖Dpt γ l‖ ≤ B ^ (2 * r + 2) ^ 2 *
      ‖Dpt (Formalism.MainNotions.FrameBoundFromBesselTorus.ptTr ka⁻¹ (ka ^ r) (inv_pos.2 hka) (pow_pos hka _) γ) l‖ := by
  unfold Dpt
  rw [Formalism.MainNotions.FrameBoundFromBesselTorus.leadMinor_ptTr, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
  refine le_mul_of_one_le_left (norm_nonneg _) ?_
  have key : ∀ a : ℕ, 1 ≤ B ^ (4 * r) * Formalism.MainNotions.FrameBoundFromBesselTorus.tF r ka⁻¹ (ka ^ r) a ^ 2 := fun a => by
    unfold Formalism.MainNotions.FrameBoundFromBesselTorus.tF
    have e1 : 1 ≤ B * ka := by
      have := mul_le_mul_of_nonneg_right h2 hka.le
      rwa [inv_mul_cancel₀ hka.ne'] at this
    have e2 : 1 ≤ B * ka⁻¹ := by
      have := mul_le_mul_of_nonneg_right h1 (inv_pos.2 hka).le
      rwa [mul_inv_cancel₀ hka.ne'] at this
    have e3 : 1 ≤ B ^ r * ka⁻¹ ^ (r - a) :=
      (one_le_pow₀ e2 (n := r - a)).trans (by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (Nat.sub_le _ _)) (by positivity))
    have e4 : 1 ≤ (B * ka) ^ r * (B ^ r * ka⁻¹ ^ (r - a)) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ e1) e3
    calc (1 : ℝ) ≤ ((B * ka) ^ r * (B ^ r * ka⁻¹ ^ (r - a))) ^ 2 := one_le_pow₀ e4
      _ = _ := by ring
  set S := Finset.univ.filter fun a : Fin (r + 1) => a.val < l.val + 1
  have hc : S.card ≤ r + 1 := (Finset.card_filter_le _ _).trans (by simp)
  have h3 : 1 ≤ ∏ a ∈ S, B ^ (4 * r) * Formalism.MainNotions.FrameBoundFromBesselTorus.tF r ka⁻¹ (ka ^ r) a ^ 2 :=
    le_trans (by simp) (Finset.prod_le_prod₀ (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) fun a _ => key a)
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul] at h3
  refine h3.trans (mul_le_mul (pow_le_pow_right₀ hB ?_) (le_abs_self _)
    (Finset.prod_nonneg fun _ _ => sq_nonneg _) (by positivity))
  nlinarith

theorem w_in_frame {D : D7} {Ch Cg Cgf Ca C : ℝ} (hFr : FrameBesselBound D Cgf 2) (H : WLoc1 D Ch Cg Ca C fun _ => True)
    (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
    (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (ka b : ℝ) (hL : LocOk D Ch Cg L L.lam ka b ka)
    (hg4 : AllGaps L.lam (Cg * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 4)) (hgap : GapFr D Cgf L.ε L.lam) (hB1 : 1 ≤ b ^ Ch)
    (hf : IsKFinCoefH L.σ f) (hsec : IsSection D.R.k D.R.rS L.z L.z' μsec) (l : Fin (D.R.rS + 1)) (a : ℕ)
    (ha : (a : ℝ) ≤ Ca * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3) (γ : Point ℂ (D.R.rS + 1))
    (hG : Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0) :
    WIneq L f μsec γ (‖Dpt γ l‖ ^ (2 * a)) (((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) * (FrC D 2 ka *
      (b ^ (C * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 5) * max 1 (1 / (GsC D ka * Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ)) ^
        (40 * (D.R.rS + 1) ^ 2)))) := by
  obtain ⟨hk, hε, hc, hκ0, hκt, hStd, hT1, hT1'⟩ := hL
  have hka : 0 < ka := hStd.2.2.2.1
  have hτ : 0 < ka ^ D.R.rS := pow_pos hka _
  obtain ⟨L₁, f₁, e1, e2, e3, e4, e5, e6, e7, e8, e9, hf₁, hrest⟩ :=
    hFr L f ka ka⁻¹ (ka ^ D.R.rS) hka (inv_pos.2 hka) hτ hc hκ0 hκt hε hgap hf
  obtain ⟨μsec₁, hsec₁, K₁, hK₁, hJ₁, hpt⟩ := hrest μsec hsec
  obtain ⟨γ₁, hγ₁, hG₁, -, hle⟩ := hpt γ hG
  have hγe : γ₁ = Formalism.MainNotions.FrameBoundFromBesselTorus.ptTr ka⁻¹ (ka ^ D.R.rS) (inv_pos.2 hka) hτ γ := Subtype.ext hγ₁
  have hsq : (ka ^ D.R.rS) ^ 2 = ka ^ (2 * D.R.rS) := by rw [← pow_mul, mul_comm]
  have hinv : ka ^ (2 * D.R.rS) * (1 / ka) ^ (2 * D.R.rS) = 1 := by
    rw [← mul_pow, mul_one_div, div_self hka.ne', one_pow]
  have hone : (ka / ka) ^ (2 * D.R.rS) = 1 := by rw [div_self hka.ne', one_pow]
  have hL₁ : LocOk D Ch Cg L₁ L₁.lam ka b 1 := by
    refine ⟨hk, e1.trans hε, ?_, e6, e7, ?_, ?_, ?_⟩
    · rw [e5, inv_mul_cancel₀ hka.ne']
    · rw [e1, e2, e3, e4, e8, e9, hsq]
      have a1 : ka ^ (2 * D.R.rS) * Tz D.R.k D.R.rS L.z * (1 / ka) ^ (2 * D.R.rS) =
          Tz D.R.k D.R.rS L.z * (ka / ka) ^ (2 * D.R.rS) := by
        rw [hone, mul_one, mul_right_comm, hinv, one_mul]
      have a2 : ka ^ (2 * D.R.rS) * Tz D.R.k D.R.rS L.z' * (1 / ka) ^ (2 * D.R.rS) =
          Tz D.R.k D.R.rS L.z' * (ka / ka) ^ (2 * D.R.rS) := by
        rw [hone, mul_one, mul_right_comm, hinv, one_mul]
      rw [a1, a2]
      exact hStd
    · rw [e8, hsq, one_pow, mul_one, mul_comm]; exact hT1
    · rw [e9, hsq, one_pow, mul_one, mul_comm]; exact hT1'
  have hG₁0 : Gpt (Tz D.R.k D.R.rS L₁.z) (Tz D.R.k D.R.rS L₁.z') γ₁ ≠ 0 := by
    rw [hG₁]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero hka.ne')) (pow_ne_zero _ hτ.ne')) hG
  have hB := H L₁ f₁ μsec₁ ka b trivial hL₁ (e2 ▸ hg4) hf₁ hsec₁ l a ha γ₁ hG₁0
  unfold WIneq at hB ⊢
  rw [hG₁, hJ₁, ENNReal.ofReal_mul (by positivity), mul_assoc] at hB
  have hD : ‖Dpt γ l‖ ^ (2 * a) ≤ ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) * ‖Dpt γ₁ l‖ ^ (2 * a) := by
    rw [← mul_pow, hγe]
    exact pow_le_pow_left₀ (norm_nonneg _) (dpt_le hka hStd.2.2.2.2.1 hStd.2.2.2.2.2.1 hB1 γ l) _
  have hK0 : ENNReal.ofReal K₁ ≠ 0 := (ENNReal.ofReal_pos.2 hK₁).ne'
  have hF0 : 0 ≤ FrC D 2 ka := FrC_nonneg D 2 ka hka
  have hX0 : (0 : ℝ) ≤ ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) := by positivity
  rw [← ENNReal.mul_le_mul_iff_right hK0 ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by positivity), mul_assoc,
    mul_left_comm]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hD) hle).trans ?_
  rw [ENNReal.ofReal_mul hX0, mul_assoc, mul_left_comm (ENNReal.ofReal (‖Dpt γ₁ l‖ ^ (2 * a)))]
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl hB)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hX0, ENNReal.ofReal_mul hF0]
  unfold FrC GsC
  ring

theorem weight_le {ι : Type} [Fintype ι] [Nonempty ι] (s x : ι → ℝ) (N : ι → ℕ) (σ : ℝ) (hσ : 1 ≤ σ)
    (hs0 : ∀ l, 0 ≤ s l) (hs : ∀ l, s l ≤ σ) :
    ∃ (l : ι) (a : ℕ), a ≤ 2 * ∑ l, N l ∧ (∏ l, (1 + s l * x l ^ 2) ^ N l) ^ 2 ≤ (2 * σ) ^ (2 * ∑ l, N l) * x l ^ (2 * a) := by
  obtain ⟨l, -, hl⟩ := Finset.exists_max_image Finset.univ (fun l => x l ^ 2) Finset.univ_nonempty
  have key : ∀ M : ℝ, 1 ≤ M → x l ^ 2 ≤ M → (∏ i, (1 + s i * x i ^ 2) ^ N i) ^ 2 ≤ (2 * σ * M) ^ (2 * ∑ i, N i) := by
    intro M hM hx
    rw [mul_comm 2 (∑ i, N i), pow_mul, ← Finset.prod_pow_eq_pow_sum]
    have hn : ∀ i, 0 ≤ 1 + s i * x i ^ 2 := fun i => add_nonneg zero_le_one (mul_nonneg (hs0 i) (sq_nonneg _))
    refine pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => pow_nonneg (hn i) _)
      (Finset.prod_le_prod₀ (fun i _ => pow_nonneg (hn i) _) fun i _ => pow_le_pow_left₀ (hn i) ?_ _) 2
    have h1 : s i * x i ^ 2 ≤ σ * M := mul_le_mul (hs i) ((hl i (Finset.mem_univ _)).trans hx) (sq_nonneg _) (by linarith)
    have h2 : 1 ≤ σ * M := one_le_mul_of_one_le_of_one_le hσ hM
    linarith
  rcases le_total (x l ^ 2) 1 with h | h
  · exact ⟨l, 0, Nat.zero_le _, by simpa using key 1 le_rfl h⟩
  · refine ⟨l, _, le_rfl, (key _ h le_rfl).trans (le_of_eq ?_)⟩
    rw [mul_pow (2 * σ), ← pow_mul]


set_option maxHeartbeats 1600000 in
theorem weighted_uniform_rotated_of_expansion_alt_alt (hW : ∀ Cb, WEnd.WBp Cb) {Cgc Cgf : ℝ} (hCC : CoefCC1 Cgc)
    (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform := by
  intro Aw Ch hAw
  obtain ⟨C, Cg₀, hC, H⟩ := wLoc1N_of hW hCC Ch (2 * (1 + Aw + 10))
  refine ⟨((4 + |Ch|) * (2 * (1 + Aw + 10)) + |Ch| * (4 * (1 + Aw + 10)) + 4 * |Ch| + C + (3 + 3 * |Ch|) * 10) + 6,
    max (max Cg₀ Cgf) 2, fun Cg hCg0 D => ?_⟩
  have g1 : Cg₀ ≤ Cg := le_trans (le_max_of_le_left (le_max_left _ _)) hCg0
  have g2 : Cgf ≤ Cg := le_trans (le_max_of_le_left (le_max_right _ _)) hCg0
  have hCg : 2 ≤ Cg := le_trans (le_max_right _ _) hCg0
  have hFr := Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D)
  have H1 := wLoc1_of_N (H Cg g1 D)
  refine Formalism.MainNotions.RotatedPoints.weighted_bound_rotated_of_one_place (A := AQ D 10) hCg ?_
  intro T T' b X hP γ hγ v
  set A := AQ D 10 with hAd
  set p : ℝ := Aw * ((D.R.rS : ℝ) + 1) ^ 2 with hpd
  have hp : 0 ≤ p := by positivity
  by_cases hO : orbSq (X.L v) (X.f v) (Pv.Frames.turnPt (ptLoc D v γ)) = 0
  · rw [hO, mul_zero]; exact bot_le
  have hL := X.hL v
  obtain ⟨hk, -, -, -, -, hStd, -, -⟩ := id hL
  have hb2 : 2 ≤ b := by
    have h1 := b_ge_of_StdHyp0 hk hStd.to0
    have h2 : (1 : ℝ) ≤ ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 7 :=
      one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + D.R.k + 1))
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hka : 0 < kaRe D := hStd.2.2.2.1
  have hk1 : kaRe D ≤ b ^ Ch := hStd.2.2.2.2.1
  have hk2 : (kaRe D)⁻¹ ≤ b ^ Ch := hStd.2.2.2.2.2.1
  set xG : ℝ := Complex.normSq (plEmb D v (leadMinorK (ptMat γ) (D.R.rS + 1) le_rfl)) -
    (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) with hxGd
  have hxG : plEmb D v (Gglob D T T' γ) = (xG : ℂ) := plEmb_Gglob D T T' v γ
  have hxG0 : xG ≠ 0 := by
    intro h0
    have : plEmb D v (Gglob D T T' γ) = 0 := by rw [hxG, h0]; simp
    exact hγ.2.1 ((map_eq_zero (plEmb D v)).1 this)
  have habs : absV D v (Gglob D T T' γ) = |xG| := by
    unfold absV; rw [hxG, Complex.norm_real, Real.norm_eq_abs]
  have hGreal : Gpt (T : ℝ) (T' : ℝ) (ptLoc D v γ) = ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 * xG :=
    GPoint_loc D T T' v γ
  have ha4 : 0 < ((∏ i : Fin D.R.rS, alf D i) ^ 2) ^ 2 := by
    have := Finset.prod_pos (s := Finset.univ) (fun (i : Fin D.R.rS) _ => alf_pos D i)
    positivity
  have hGne : Gpt (Tz D.R.k D.R.rS (X.L v).z) (Tz D.R.k D.R.rS (X.L v).z') (Pv.Frames.turnPt (ptLoc D v γ)) ≠ 0 := by
    rw [Pv.Frames.GPoint_turnPt, (X.hT v).1, (X.hT v).2, hGreal]
    exact mul_ne_zero ha4.ne' hxG0
  obtain ⟨g, hg⟩ := exists_rep_of_orbSq _ _ _ hO
  have hGnn := GPoint_nonneg_of_rep _ _ g hg
  rw [Pv.Frames.GPoint_turnPt, (X.hT v).1, (X.hT v).2] at hGnn
  have hxGnn : 0 ≤ xG := by
    rw [hGreal] at hGnn
    exact nonneg_of_mul_nonneg_right hGnn ha4
  have hGd : absV D v (Gglob D T T' γ) ≤ dLoc D v γ := by
    rw [habs, abs_of_nonneg hxGnn]
    unfold dLoc absV
    rw [← Complex.normSq_eq_norm_sq]
    have : 0 ≤ (T : ℝ) * (T' : ℝ) * Complex.normSq (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _))) := by
      have := Complex.normSq_nonneg (plEmb D v (leadMinorK (ptMat γ) D.R.rS (Nat.le_succ _)))
      positivity
    linarith
  have hn0 : 0 ≤ nLoc D T T' v γ := by
    unfold nLoc ptWeight
    exact ptWeightFrom_nonneg _ _ _ _ _ 0 (fun b hb => ((ptLoc D v γ).2.1 b hb).2)
      (by rw [Nat.zero_add]; exact (ptLoc D v γ).2.2)
      (fun t ht => last_ok_of_G _ _ _ hGnn t ht)
  have hb0 : 0 < b := by linarith
  have hCh : 0 ≤ Ch := ch_nonneg hCg ⟨X.hL v, X.hnear v, X.hcoef v, X.hsec v, X.hT v⟩
  rw [abs_of_nonneg hCh]
  have hlam := lam_eq_of_dist0 D X v
  have hgF : GapFr D Cgf (X.L v).ε (X.L v).lam := by
    rw [hlam]
    exact Formalism.L2.SG.Pf.BesselExpansion.gap_mono hStd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right g2 (by positivity)) (by positivity))
  set M : ℝ := ((2 * D.R.rS + 2 : ℕ) : ℝ) with hM
  have hM1 : 1 ≤ M := by rw [hM]; exact_mod_cast (by omega : 1 ≤ 2 * D.R.rS + 2)
  have hσ1 : 1 ≤ b ^ ((3 + Ch) * M ^ 2) := Real.one_le_rpow hb1 (by positivity)
  obtain ⟨l, a, ha, hwt⟩ := weight_le (sQ D) (fun l => ‖Dpt (ptLoc D v γ) l‖) (Formalism.MainNotions.TheoremBConstants.NQ D A p) _ hσ1 (sQ_nonneg D)
    fun l => alfProd_inv_le_b D Ch b hCh hb2 hka hk2 _ (by omega)
  simp only [Fl_eq] at hwt
  have hSN := sum_weighted_point_counts_le_cube D Aw 10 hAw (by norm_num)
  have hS2 : ((2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l : ℕ) : ℝ) ≤ 2 * (1 + Aw + 10) * M ^ 3 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    have : ((∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l : ℕ) : ℝ) ≤ (1 + Aw + 10) * M ^ 3 := hSN
    linarith only [this]
  have ha' : (a : ℝ) ≤ 2 * (1 + Aw + 10) * M ^ 3 := le_trans (by exact_mod_cast ha) hS2
  have hloc := w_in_frame hFr H1 (X.L v) (X.f v) (X.μsec v) (kaRe D) b (hlam ▸ hL) (hP v) hgF
    (Real.one_le_rpow hb1 hCh) (X.hcoef v) (X.hsec v) l a ha' (Pv.Frames.turnPt (ptLoc D v γ)) hGne
  unfold WIneq at hloc
  simp only [Dpt_norm_turnPt, Pv.Frames.ptWeight_turnPt, Pv.Frames.GPoint_turnPt] at hloc
  rw [(X.hT v).1, (X.hT v).2, hGreal] at hloc
  have hw := weights_le D T T' v γ A p hp hGd
  have h1 : wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p ≤
      (∏ l, Fl D v γ l ^ Formalism.MainNotions.TheoremBConstants.NQ D A p l) ^ 2 * nLoc D T T' v γ := by
    calc wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * nLoc D T T' v γ * WLoc D T T' v γ ^ p
        = (wLoc D v γ ^ 2 * (1 + dLoc D v γ) ^ A * WLoc D T T' v γ ^ p) * nLoc D T T' v γ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hw hn0
  have hY0 : 0 ≤ (2 * b ^ ((3 + Ch) * M ^ 2)) ^ (2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l) := by positivity
  have h2 := h1.trans ((mul_le_mul_of_nonneg_right hwt hn0).trans (le_of_eq (mul_assoc _ _ _)))
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal h2) le_rfl).trans ?_
  rw [ENNReal.ofReal_mul hY0, mul_assoc]
  refine (mul_le_mul' le_rfl hloc).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hY0]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hM25 : M ^ 2 ≤ M ^ 5 := pow_le_pow_right₀ hM1 (by norm_num)
  have hM45 : M ^ 4 ≤ M ^ 5 := pow_le_pow_right₀ hM1 (by norm_num)
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM1
  have n1 : (2 * b ^ ((3 + Ch) * M ^ 2)) ^ (2 * ∑ l, Formalism.MainNotions.TheoremBConstants.NQ D A p l) ≤ b ^ ((4 + Ch) * (2 * (1 + Aw + 10)) * M ^ 5) := by
    have e1 : 2 * b ^ ((3 + Ch) * M ^ 2) ≤ b ^ ((4 + Ch) * M ^ 2) := by
      rw [show (4 + Ch) * M ^ 2 = M ^ 2 + (3 + Ch) * M ^ 2 by ring, Real.rpow_add hb0]
      refine mul_le_mul_of_nonneg_right (hb2.trans ?_) (by positivity)
      simpa using bp_mono hb1 hM2
    refine (bp_pow hb0 e1 (by positivity) _).trans (bp_mono hb1 ?_)
    calc _ ≤ (4 + Ch) * M ^ 2 * (2 * (1 + Aw + 10) * M ^ 3) := mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = _ := by ring
  have n2 : ((b ^ Ch) ^ (2 * D.R.rS + 2) ^ 2) ^ (2 * a) ≤ b ^ (Ch * (4 * (1 + Aw + 10)) * M ^ 5) := by
    refine (bp_pow hb0 (bp_pow hb0 le_rfl (by positivity) _) (by positivity) _).trans (bp_mono hb1 ?_)
    rw [Nat.cast_pow, ← hM, Nat.cast_mul, Nat.cast_ofNat]
    calc _ ≤ Ch * M ^ 2 * (2 * (2 * (1 + Aw + 10) * M ^ 3)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have n3 : FrC D 2 (kaRe D) ≤ b ^ (4 * Ch * M ^ 5) :=
    (num_Fr D Ch 2 b (kaRe D) hCh (by norm_num) hb2 hka hk1 hk2).trans
      (bp_mono hb1 (by nlinarith [mul_le_mul_of_nonneg_left hM25 hCh]))
  have n4 := num_G D Ch 10 b hCh (by norm_num) hb2 hka hk1 hk2 A (AQ_ge D 10) xG hxG0
  rw [show 10 * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 = ((40 * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    show ((40 * (D.R.rS + 1) ^ 2 : ℕ) : ℝ) = 10 * M ^ 2 by rw [hM]; push_cast; ring] at n4
  have n5 : b ^ ((3 + 3 * Ch) * M ^ 2 * (10 * M ^ 2)) ≤ b ^ ((3 + 3 * Ch) * 10 * M ^ 5) :=
    bp_mono hb1 (by nlinarith [mul_le_mul_of_nonneg_left hM45 (show 0 ≤ (3 + 3 * Ch) * 10 by positivity)])
  have n6 := n4.trans (mul_le_mul_of_nonneg_right n5 (by positivity))
  have hF0 := FrC_nonneg D 2 (kaRe D) hka
  rw [habs, add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), add_mul _ _ (M ^ 5), Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_add hb0,
    Real.rpow_add hb0]
  calc _ ≤ b ^ ((4 + Ch) * (2 * (1 + Aw + 10)) * M ^ 5) * (b ^ (Ch * (4 * (1 + Aw + 10)) * M ^ 5) *
        (b ^ (4 * Ch * M ^ 5) * (b ^ (C * M ^ 5) * (b ^ ((3 + 3 * Ch) * 10 * M ^ 5) * max 1 (1 / |xG|) ^ A)))) := by
        gcongr
    _ = _ := by ring

end CompanionTheory.WaveGrid.WGlue
end
end

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.BasicNotions CompanionTheory.LimBd.Main

theorem uniqueness_global : WAt.UniqG := by
  intro k r ε lam hl h hg hh H _ _ _ σ hσ H' _ _ _ σ' hσ'
  refine ReciprocityTheory.ChartRestriction.DS.discrete_series_unique_large_gap k r ε lam hl h hg (lt_of_le_of_lt ?_ hh) H σ hσ H' σ' hσ'
  have h1 : (ReciprocityTheory.ChartRestriction.DS.pOf ε : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have h2 : (ReciprocityTheory.ChartRestriction.DS.qOf ε : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  have h3 := mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (2 * r + k + 1))) h2 (Nat.cast_nonneg _)
    (by positivity)
  linarith [show ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 = ((2 * r + k + 1 : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) *
    ((2 * r + k + 1 : ℕ) : ℝ) by ring]

theorem wave_bessel_period_threshold {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct : ℝ} (hCt : 0 ≤ Ct) (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3)
    (hZ : ZuckT t) (hZd : ZuckDualT t) (H : WEnd.In91) (Cb : ℝ) : WEnd.WBp Cb :=
  have hS := limSteps_of CompanionTheory.D.DSIC.discrete_series_infinitesimal_character
  have hK := CompanionTheory.D.gk.admitted.k_finite_smooth
  WEnd.wBp_of hCt ht hZ hZd hS (endDiffW_of asymptotic_different_types hS Coef.smooth_coefficient_bessel hK hZ hZd)
    (endEqW_of asymptotic_equal_types GlobalTheory.CompanionTheory.WignerShift.wigExists hS Coef.smooth_coefficient_bessel hK hZ hZd) hK H uniqueness_global Cb

theorem weighted_bound_rotated_uniform_of_cubic_threshold {t : ∀ n : ℕ, (Fin n → Bool) → ℝ} {Ct Cgf : ℝ} (hCt : 0 ≤ Ct)
    (ht : ∀ n ε, 1 ≤ n → t n ε ≤ Ct * (n : ℝ) ^ 3) (hZ : ZuckT t) (hZd : ZuckDualT t) (H : WEnd.In91)
    (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  WGlue.weighted_uniform_rotated_of_expansion_alt_alt (wave_bessel_period_threshold hCt ht hZ hZd H)
    (Tied.coefCC1_of hCt ht hZ CompanionTheory.D.gk.admitted.k_finite_smooth CompanionTheory.CapEig.capelli_coefficient_continuity) hOB

open ReciprocityTheory.ChartRestriction.DS in
theorem thrS_lt {n : ℕ} (ε : Fin n → Bool) (hn : 1 ≤ n) : G2.thrS ε + 1 < 43 * (n : ℝ) ^ 2 := by
  have hq : S7.q0 ε ≤ n := (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
  have hq' : (S7.q0 ε : ℝ) ≤ n := by exact_mod_cast hq
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt (2 * (S7.q0 ε : ℝ)) ≤ 2 * n := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [(Nat.cast_nonneg (S7.q0 ε) : (0 : ℝ) ≤ _)]
  have h1 : (n : ℝ) * (S7.q0 ε : ℝ) ≤ n * n := mul_le_mul_of_nonneg_left hq' (by positivity)
  unfold G2.thrS
  rcases max_cases (2 * (n : ℝ)) (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ))) with h2 | h2 <;>
    rw [h2.1] <;> nlinarith

theorem thrS_le (n : ℕ) (ε : Fin n → Bool) (hn : 1 ≤ n) : ReciprocityTheory.ChartRestriction.DS.G2.thrS ε ≤ 43 * (n : ℝ) ^ 3 := by
  have h1 := thrS_lt ε hn
  have h2 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ (by exact_mod_cast hn) (by norm_num)
  linarith

theorem uniform_bessel_rank_three_of_inputs {Cgf : ℝ} (H : WEnd.In91) (hOB : ∀ D : D7, Formalism.MainNotions.FrameBoundFromBesselTorus.OneBesselTor D Cgf) :
    Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  weighted_bound_rotated_uniform_of_cubic_threshold (by norm_num) thrS_le CompanionTheory.Zuck.zuckT_thrS CompanionTheory.Zuck.zuckDualT_thrS H hOB

end CompanionTheory.WaveGrid
end

namespace CompanionTheory.WaveGrid

theorem weighted_bound_rotated_uniform_of_hypsG (H : BranchingSupport.HypsG) : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  uniform_bessel_rank_three_of_inputs (WEnd.wave_inputs_of_hypotheses_global H) fun D => Formalism.MainStatements.RankOne.one_bessel_torus_bound D (le_refl 100)

end CompanionTheory.WaveGrid
end

namespace CompanionTheory.WaveGrid

theorem weighted_bound_rotated_uniform : Formalism.MainNotions.RotatedPoints.WeightedBoundRotatedUniform :=
  weighted_bound_rotated_uniform_of_hypsG (CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap)

end CompanionTheory.WaveGrid
