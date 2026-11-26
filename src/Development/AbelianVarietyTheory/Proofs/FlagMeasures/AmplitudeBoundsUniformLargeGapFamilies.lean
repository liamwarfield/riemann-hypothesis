module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeFoldrMax
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpectralStagePointRowPlacementTransfer
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SchurAlongFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKF0IffGapIn
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndDecInfAndKFinSmooth
namespace GlobalTheory.DecInputs

theorem decLow_and_decInf_and_kFinSmooth :
    Formalism.FourierDecayAlt.ThreeDimData.DecLow ∧ Formalism.FourierDecayAlt.ThreeDimData.DecInf ∧ PI.KFinSmooth :=
  ⟨GlobalTheory.DecTransport.decLow_holds, Formalism.L2.SG.BesselDiscreteSeries.decInf,
    Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.admitted.kFinSmooth'⟩

end GlobalTheory.DecInputs
end

section -- merged from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKFIff
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.NoPr

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.CellAmp

def AmpKF0 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

end GlobalTheory.NoPr

end
end

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace GlobalTheory.NoPr.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.ThreeDimData

theorem ampKF0_iff_gapIn : AmpKF0 ↔ GlobalTheory.GapIn.AmpKF0 := Iff.rfl


open Formalism.MainNotions.S.Pv.AmpDDPf in
theorem ampKF0_holds : AmpKF0 := by
  intro k r L h μG w0 l l' hOPKF γ μR νR ν hCD b hb hab' hpm v v' hv hv' ξ ξ'
  have hSchH := Formalism.FourierDecayAlt.P.schur_hermitian
  have hNI := Formalism.FourierDecayAlt.P.norm_inverse_bound
  have hGG := Formalism.FourierDecayAlt.P.growth_group_bound
  have hRS := Formalism.MainNotions.S.Pv.AmpDDPf.right_stabilizer_invariance
  have hIn := GlobalTheory.DecInputs.decLow_and_decInf_and_kFinSmooth
  obtain ⟨hOP, hK1, hK2⟩ := hOPKF
  obtain ⟨hgap, hOK, -, hw0, hμG, -, -⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
  have hw0K : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ :=
    hIn.2.2 k r L.ε L.lam L.Hs L.σ L.hlam hσ w0 hw0K
  obtain ⟨P, hP, hw⟩ := hw0
  have hnorm : ‖w0‖ = 1 := hw.1
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d :=
    Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2
  obtain ⟨C1, Ws1, -, hC1⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v hv
  obtain ⟨C2, Ws2, -, hC2⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v' hv'
  have e1 : (1 : ℝ) - Formalism.FourierDecayAlt.ThreeDimData.aOf r h = -(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) := by ring
  have hC1' : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤
      (C1 * (Ws1.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC1 w0 hw0s g hg
  have hC2' : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤
      (C2 * (Ws2.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC2 w0 hw0s g hg
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 := by linarith
  have hIG : Integrable (fun x : Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1))) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hK1 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v hv)
    (fun t ht => hK2 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v' hv') hC1' hC2' ξ ξ'

end GlobalTheory.NoPr.Model

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

open MeasureTheory NumberField Formalism.FourierDecayAlt Finset

namespace GlobalTheory.UnifPTGap

open Formalism.MainNotions.BridgeLemma

theorem tFrame_of_dsig (hM : Formalism.HermitianLatticesTheory.SiegelMassRatio) (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC)
    {eps : ℝ} (Fm : FamP eps) (h40 : 40 ≤ sCl Fm) {C0 Cg cb Cu cT CT : ℝ}
    (hR : PX.RanksF Fm C0 Cg cb Cu cT CT) : PX.TFrame Fm Cg cb Cu cT CT C0 := by
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := ⟨hDs⟩
  exact level_frame_of_sizes Fm Cg cb Cu cT CT C0 1 (by linarith)
    (level_formula_family Fm C0 Cg cb Cu cT CT (fun x i => mass_ratio_of_siegel_cm_unramified hM (Fm.D x i)) (mass_two_bound_family_holds Fm) hR)
    (Formalism.L2.SG.Pf.SzHypFam.localSplitExponents_of_forty_le_sCl Fm h40 C0 Cg cb Cu cT CT)

theorem uniformPT_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps),
    thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i =>
      VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  intro hM hH hBp Cg cb Cu cT CT C0 C1
  set Cβ : ℝ := max 2 (max Cu (max CT (1 / 8 + 2 * Cg))) with hCβ
  have hβ2 : 2 ≤ Cβ := le_max_left _ _
  have hu : Cu ≤ Cβ := (le_max_left _ _).trans (le_max_right _ _)
  have hT : CT ≤ Cβ * 1 := by rw [mul_one]; exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hg : 1 / 8 + 2 * Cg ≤ Cβ * 1 := by
    rw [mul_one]; exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  obtain ⟨Cb, Cg₀, hBP⟩ := (GlobalTheory.T.besselPointwiseBound_at_largeGaps hH hBp 1).imp fun _ h => h.imp fun _ h Cg hCg => (h Cg hCg).2.2
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.T.oneBessel_torusTranslates_largeGap hH
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.T.amplitude_eq_besselFunction_largeGaps hH Cg cb Cu cT CT C0 C1
  refine ⟨max (Ca + Cβ * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0), 1000, fun eps Fm _ hl hR Cn => ?_⟩
  obtain ⟨m₀, hA⟩ := hAmp Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  have hAmpF : OwnEv Fm fun C' Cl x i => Bridge.AmpIsBessel (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 Ca :=
    ⟨x0, fun x hx i => hA (Fm.D x i) (Fm.L x i) _ _ hl (hx0 x hx i).2.2.2.2.1 (hx0 x hx i).2.1
      (Fm.ties x i).cdScale_tie⟩
  obtain ⟨a', hFr⟩ := hFrm Cn
  have hStd := Formalism.MainNotions.BridgeLemma.stdHypS_of Fm Cg cb Cu cT CT C0 1 Cβ (by linarith) zero_le_one hβ2 hu hT hg
    (max Cg₀ a') (200 * Cn)
  have hTF := tFrame_of_dsig hM hH.2.2.2 Fm (by linarith) hR
  exact Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i H =>
    AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity _ _ _ _ _ _ _ _ _ _ Cn C1 Ca 1 Cf (max Cg₀ a') (200 * Cn) Cβ (max Cb 0) _ H.1.1
      (hFr _ (le_max_right _ _) _ (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus _ Cgf 2 le_rfl (hOB _)))
      H.1.2 H.2
      (OnePlaceEstimates.upper_bound_mono_constant _ one_pos (le_max_left _ _) (hBP _ (le_max_left _ _) _ Cn (200 * Cn) le_rfl))
      (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _)) ((hAmpF.and hStd).and hTF)

end GlobalTheory.UnifPTGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformAmplitudeBoundWideRangeLargeGapStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C) := by
  first | exact @GlobalTheory.UnifPTGap.uniformPT_gap | exact GlobalTheory.UnifPTGap.uniformPT_gap | (intros; apply GlobalTheory.UnifPTGap.uniformPT_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsAllAlongFamilyGap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section
open GlobalTheory.Amp

namespace GlobalTheory.GapUAmp

theorem abs_all_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.AbsAllParameters (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cn C) ∧ (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1) := by
  intro _ hH _ Cg cb Cu cT CT C0 A C1
  obtain ⟨CMo, hMo⟩ := GlobalTheory.T.majorantLength_moments_amplitudes_largeGap hH Cg cb Cu cT CT C0 C1 25
  obtain ⟨C₀, hAbs⟩ := GlobalTheory.Amp.AbsRange.abs_range Cg cb Cu cT CT C0 C1 CMo
  obtain ⟨m₁, hAbs'⟩ := hAbs (max C₀ 0) (le_max_left _ _)
  refine ⟨max C₀ 0, 1000, le_max_right _ _, ?_⟩
  intro eps Fm _ hCl _
  have key : ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i =>
      ABSr (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 (max C₀ 0) := by
    intro Cn
    obtain ⟨m₂, hM⟩ := hMo Cn
    obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max (max m₁ m₂) 1)
    refine ⟨x0, fun x hx i => ?_⟩
    obtain ⟨-, hm, -, -, hrd, -⟩ := hx0 x hx i
    have hm1 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := le_trans (le_max_right _ _) hm
    have hB : ∀ m₀, m₀ ≤ max (max m₁ m₂) 1 → Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
      fun m₀ h => ⟨hrd, by nlinarith, le_trans h hm⟩
    exact hAbs' Cn _ _ _ _ (hB _ (le_trans (le_max_left _ _) (le_max_left _ _)))
      (hM _ _ _ _ hCl (hB _ (le_trans (le_max_right _ _) (le_max_left _ _))))
  refine ⟨fun Cn => (key Cn).mono ?_, (key 0).mono ?_⟩
  · intro C' Cl x i h τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hHyp hD
    have h0 : HypZ (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
      unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
    exact (h h0 τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hD).2
  · intro C' Cl x i h τ w w' hTT θ hθ W hW S hS _ γ p hp θ' hθ' νR hR hHyp hD
    have h0 : HypZ (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
      unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
    exact (h h0 τ w w' hTT θ hθ W hW (lamD _ τ) (by simp [l1dist]) S hS γ p hp θ' hθ' νR hR hD).1

end GlobalTheory.GapUAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtDlAlongFamilyGap
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.FamDlGap

theorem ptDl_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  have hA : GlobalTheory.GapIn.AmpKF0 := GlobalTheory.NoPr.Model.ampKF0_iff_gapIn.mp GlobalTheory.NoPr.Model.ampKF0_holds
  have hCC : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
  obtain ⟨C, hC⟩ := GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps hH hA hCC Cg cb Cu cT CT C0 C1
  refine ⟨C, 1000, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max m₀ 1)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, hm1, -, -, hrd, -⟩ := hx0 x hx i
  have hmm : m₀ ≤ ((Fm.D x i).R.m : ℝ) := (le_max_left _ _).trans hm1
  have hm1' : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := (le_max_right _ _).trans hm1
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hmm⟩
  intro hH0
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hH0

end GlobalTheory.FamDlGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeNormDegreeAlongFamilyOfKFiniteIdentity
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.AmpFamGap

theorem cellConv : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence

theorem amplitudeNormDegree_along_family_of_kFiniteIdentity : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro hH hA Cg cb Cu cT CT C0 C1
  refine ⟨1000, fun eps Fm hC' hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := GlobalTheory.T.openCellAmplitudeNorm_eq_const_div_degree_largeGap hH hA cellConv Cg cb Cu cT CT C0 C1 Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i hZ => ?_⟩
  obtain ⟨-, hm0, -, -, hrd, -⟩ := hx0 x hx i
  have hm2 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := by
    have := (Fm.D x i).R.two_le_m
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.m)
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hm0⟩
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hZ

theorem amplitudeNormDegree_along_family_largeGaps : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ thr : ℝ,
    ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT →
      VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 := by
  intro _ hH _
  exact amplitudeNormDegree_along_family_of_kFiniteIdentity hH (GlobalTheory.T.amplitude_eq_kFiniteOrbitalIntegral_gap hH)

end GlobalTheory.AmpFamGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DegIAlongFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapNearPlaceParameterHalfNoncompactGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapNearPlaceParameterHalfNoncompactGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapNear

theorem gap_near : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  intro Cn
  refine ⟨max Cn 1000, fun D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm₀ τ lam' hl => ?_⟩
  have hdim := dimS_eq D.R
  have hrr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hmk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  have hnR : (D.R.r : ℝ) = 2 * D.R.rS + D.R.k + 1 := by rw [← hdim]; push_cast; ring
  have hmC : Cn ≤ (D.R.m : ℝ) := le_trans (le_max_left _ _) hm₀
  have hm1000 : (1000 : ℝ) ≤ D.R.m := le_trans (le_max_right _ _) hm₀
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.k ≤ D.R.r)
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : D.R.m ≤ D.R.r)
  have hr1000 : (1000 : ℝ) ≤ D.R.r := le_trans hm1000 hmr
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _

  have hsize : Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r ≤ (D.R.r : ℝ) ^ 19 / 2 := by
    have h1 : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
      have := mul_le_mul_of_nonneg_right hmC (show (0 : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 by positivity)
      linarith [show Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * (D.R.k * (D.R.m : ℝ) ^ 3) by ring,
        show (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = (D.R.m : ℝ) * (D.R.k * (D.R.m : ℝ) ^ 3) by ring]
    have h2 : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 5 := by
      have e : (D.R.m : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 = D.R.k * (D.R.m : ℝ) ^ 4 := by ring
      have e' : (D.R.r : ℝ) ^ 5 = D.R.r * (D.R.r : ℝ) ^ 4 := by ring
      rw [e, e']
      exact mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 4) (by positivity) (by positivity)
    have h3 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
    have h4 : (4 : ℝ) ≤ (D.R.r : ℝ) ^ 14 := le_trans (by norm_num) (le_trans hr1000 (le_self_pow₀ (by linarith) (by norm_num)))
    have h5 : 4 * (D.R.r : ℝ) ^ 5 ≤ (D.R.r : ℝ) ^ 19 := by
      have := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 5 by positivity)
      linarith [show (D.R.r : ℝ) ^ 5 * (D.R.r : ℝ) ^ 14 = (D.R.r : ℝ) ^ 19 by ring]
    linarith

  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hL : 1 ≤ large₂.sc.L := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hG0 := Formalism.MainNotions.BridgeLemma.szh_gap hZ.1 τ
  have hG : (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have hf' : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hf)
    have h5 : (1 : ℝ) ≤ Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_mul_of_one_le_of_one_le hf' hL)
    have h6 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity)
    have h7 : (D.R.r : ℝ) ^ 19 * (Cl * ((D.R.f : ℝ) ^ 5 * large₂.sc.L)) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by ring
    linarith
  refine ⟨fun a b hne => ?_, ?_⟩
  · have hab : a ≠ b := fun e => hne (e ▸ rfl)
    have g := hG0 a b hne
    change _ ≤ |lamD D τ a - lamD D τ b| at g
    have hpair : |lam' a - lamD D τ a| + |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ) := by
      unfold l1dist
      rw [← Finset.sum_pair (f := fun i => |lam' i - lamD D τ i|) hab]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => abs_nonneg _)
    have tri : |lamD D τ a - lamD D τ b| ≤ |lam' a - lam' b| + |lam' a - lamD D τ a| + |lam' b - lamD D τ b| := by
      rw [abs_le]
      constructor <;>
      linarith [le_abs_self (lam' a - lam' b), neg_abs_le (lam' a - lam' b), le_abs_self (lam' a - lamD D τ a),
        neg_abs_le (lam' a - lamD D τ a), le_abs_self (lam' b - lamD D τ b), neg_abs_le (lam' b - lamD D τ b)]
    linarith
  · have hok := (GlobalTheory.SizeNum.gapOK D.R.k D.R.rS D.R.r hnR (by omega) hr1000).1
    exact GlobalTheory.NumFam.gapOK_mono D.R.k D.R.rS (by linarith [show (0:ℝ) ≤ (D.R.r : ℝ) ^ 19 by positivity]) hok

end GlobalTheory.GapNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapNearPlaceParameterHalfNoncompactGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gap_near_placeParameter_half_noncompactGap : ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → 1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ), l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r → GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2) := by
  first | exact @GlobalTheory.GapNear.gap_near | exact GlobalTheory.GapNear.gap_near | (intros; apply GlobalTheory.GapNear.gap_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqHarishChandraRatioLargeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqHarishChandraRatioLargeGap
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.GapDegreeRatio

theorem deg_eq_of_goodS (hH : GlobalTheory.GapIn.Hyp) (D : D7) :
    ∃ c : ℝ, 0 < c ∧ ∀ (W : LocW D.R.k D.R.rS) (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ),
      GoodS D l A → GapAtLeast (epsSH D.R) l h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h →
      A.deg = c * Formalism.QuantumDeterminants.fdegHC l := by
  obtain ⟨c, hc, hF⟩ := hH.1.2.2.2.2.2.2 D.R.k D.R.rS (epsSH D.R) (Formalism.MainNotions.S.Inh.obj_cayleyU_rows D)
  set s : NNReal := D.s.cdScale _ (epsSH D.R) with hs
  have hs0 : 0 < s := D.s.cdScale_pos _ _
  have hs0' : (0 : ℝ) < s := by exact_mod_cast hs0
  refine ⟨c / s, div_pos hc hs0', fun W l A h hA hg hok => ?_⟩
  obtain ⟨hl, ⟨Q, hQ, hDS⟩, -, -, -, -, -, -, -, -, P, hP, hd⟩ := hA
  have hFQ : IsFdeg (Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q)) (c * Formalism.QuantumDeterminants.fdegHC l) :=
    hF l A.H (fun g => A.σ (Q⁻¹ * g * Q)) ⟨h, hg, hok⟩ hl hDS
  have hFQs : IsFdeg ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R)) (fun g => A.σ (Q⁻¹ * g * Q))
      (c * Formalism.QuantumDeterminants.fdegHC l / s) := by
    refine ⟨div_pos hFQ.1 hs0', fun v w v' w' => ⟨(hFQ.2 v w v' w').1.smul_measure ENNReal.coe_ne_top, ?_⟩⟩
    rw [integral_smul_measure, (hFQ.2 v w v' w').2, ENNReal.coe_toReal, Complex.real_smul]
    have hd0 : ((c * Formalism.QuantumDeterminants.fdegHC l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hFQ.1.ne'
    have hcc : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0'.ne'
    push_cast at hd0 ⊢
    field_simp
  have : Nontrivial A.H := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.1.2⟩
  have h1 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (P⁻¹ * g * P)) (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q = (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj ((s : ℝ≥0∞) • Formalism.REAL.muG (epsSH D.R))
    (fun g => A.σ (Q⁻¹ * g * Q)) (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 _ hFQs w hw
  rw [← h1, h2]
  ring

theorem deg_ratio : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  intro hH D W l l' A A' h hA hA' hg hg' hok
  obtain ⟨c, hc, hk⟩ := deg_eq_of_goodS hH D
  rw [hk W l A h hA hg hok, hk W l' A' h hA' hg' hok]
  exact mul_div_mul_left _ _ hc.ne'

end GlobalTheory.GapDegreeRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqHarishChandraRatioLargeGapStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap : GlobalTheory.GapIn.Hyp → ∀ (D : D7) (W : LocW D.R.k D.R.rS) (l l' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A A' : LocS W) (h : ℝ), GoodS D l A → GoodS D l' A' → GapAtLeast (epsSH D.R) l h → GapAtLeast (epsSH D.R) l' h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → A'.deg / A.deg = Formalism.QuantumDeterminants.fdegHC l' / Formalism.QuantumDeterminants.fdegHC l := by
  first | exact @GlobalTheory.GapDegreeRatio.deg_ratio | exact GlobalTheory.GapDegreeRatio.deg_ratio | (intros; apply GlobalTheory.GapDegreeRatio.deg_ratio <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.DegStepG

theorem vandLine (hH : GlobalTheory.GapIn.Hyp) (Cn m₀ : ℝ)
    (hnear : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 →
      1000 ≤ Cl → m₀ ≤ D.R.m → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
        l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r →
        Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) lam' ((D.R.r : ℝ) ^ 19 / 2) ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS ((D.R.r : ℝ) ^ 19 / 2))
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ) (hCl : 1000 ≤ Cl) (hm : m₀ ≤ D.R.m) :
    Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro hH0 τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hZ : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := hH0
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  obtain ⟨g1, gok⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ lam' h1
  obtain ⟨g2, _⟩ := hnear D large₂ C' Cl Cg cb Cu cT CT C0 hZ hCl hm τ _ h2
  exact GlobalTheory.T.formalDegree_ratio_eq_harishChandra_ratio_largeGap hH D W lam' (lam' + s • epsI I) A A' _ hA hA' g1 g2 gok

theorem degI_along_family : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS →
    ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm →
      PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ,
        OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.DegreeRatioUnitShiftBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  refine ⟨1, 1000, zero_le_one, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hnear⟩ := GlobalTheory.T.gap_near_placeParameter_half_noncompactGap Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm m₀
  refine ⟨x0, fun x hx i => ?_⟩
  exact Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
    (vandLine hH Cn m₀ hnear (Fm.D x i) (Fm.L x i) _ _ _ _ _ _ _ _ _ hCl (hx0 x hx i).2.1)

end GlobalTheory.DegStepG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TcritLowAlongFamilyGap
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AlongFamilyOfMassRatio
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Finset

namespace GlobalTheory.CritLevel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sq_le_two_pow (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

theorem sizes_low {D : D7} (L : SizeData₂ D) (h : SizesAt L) : L.sc.x ≤ D.R.k ∧ Real.sqrt L.sc.b ≤ L.sc.b' := by
  obtain ⟨-, -, hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hW, -⟩ := h
  have hx := L.sc.one_lt_alt
  have he := L.sc.eps_pos
  refine ⟨le_trans ?_ hK.1, le_trans hW ?_⟩
  · refine Real.self_le_rpow_of_one_le hx.le ?_
    unfold szTh
    linarith
  · have hn : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
      exact_mod_cast this
    refine div_le_self ?_ (one_le_mul_of_one_le_of_one_le hx.le hn)
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity

theorem err_le (D : D7) {δ : ℝ} (hδ : 0 < δ) (h : 8 / Real.log (1 + δ) ≤ D.R.k) :
    Real.exp ((D.R.f : ℝ) * (2 : ℝ) ^ ((3 : ℝ) - D.R.k)) - 1 ≤ δ := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hl : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (show D.R.f ≤ D.R.k from D.R.f_le_k)
  have h2 : (D.R.k : ℝ) ^ 2 ≤ 2 ^ D.R.k := by exact_mod_cast sq_le_two_pow D.R.k (by omega)
  have e2 : (2 : ℝ) ^ ((3 : ℝ) - D.R.k) = 8 / 2 ^ D.R.k := by
    rw [Real.rpow_sub two_pos, Real.rpow_natCast]; norm_num
  rw [sub_le_iff_le_add', ← Real.le_log_iff_exp_le (by linarith), e2]
  rw [div_le_iff₀ hl] at h
  calc (D.R.f : ℝ) * (8 / 2 ^ D.R.k) ≤ D.R.k * (8 / (D.R.k : ℝ) ^ 2) := by gcongr
    _ = 8 / D.R.k := by field_simp
    _ ≤ _ := by rw [div_le_iff₀ (by linarith)]; linarith

theorem form_of_ranks (D : D7) (hR : LocalBesselAndTopKernel.FamilyMidVolume D) (u : D.what₂.Word) (h3 : UnitaryVolumeMass.stLem3L0 D u) {C0 : ℝ}
    (hD : StandingNumericalData D C0) : UnitaryVolumeMass.FormAt D u := by
  intro F0 he hz what₂ hrows
  obtain ⟨-, -, -, -, -, -, -, -, hT, -⟩ := hD
  have hp := (D.mem u).A.T_prime
  have h3T : 3 ≤ (D.mem u).A.T := by
    have h1 := (hT u).2
    have h2 : 2 * 2 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (D.host.g_prime 0).two_le (D.host.g_prime 1).two_le
    have h4 : D.host.g 0 * D.host.g 1 ≤ (D.host.g 0 * D.host.g 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have h5 := hp.two_le
    by_contra h
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  have hst := GlobalTheory.Mass.StdMass.main D.host.E D.sp.cm.cmUnram D.R.k
  have h1 := (hR _ _ _ hst.1).1 hst.2.1 u
  have h2 := (h3 hp h3T (hT u).1 F0 he hz what₂ hrows).1
  have h4 : dimPi (hc := D.hcW) u = ∏ τ, vand (uS D u τ) / ∏ i ∈ range D.R.k, (i.factorial : ℝ) :=
    prod_congr rfl fun τ _ => (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D u τ)).2
  rw [h1, h2, h4]
  change _ * (Cnt.massU D.host.E D.R.k * (Tr D u ^ D.R.k - 1) ^ D.R.f) * _ =
    Cnt.massU D.host.E D.R.k * _ * _ * _
  ring

theorem along_family_of_massRatio (hM : ∀ D : D7, UnitaryVolumeMass.stMassRatio D) :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.FormalDegreeCompactDual → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) := by
  intro hE hF eps Fm Cg cb Cu cT CT C0 A hCl hR h3
  have hform : OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
      ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u := by
    obtain ⟨x0, h⟩ := hR
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i hH u => ?_⟩
    have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
    exact form_of_ranks _ (h x ((le_max_left _ _).trans hx) i ⟨hH.2.1, hH.1, hH.2.2⟩) u (h3 x hx1 i u) hH.2.1
  refine ⟨fun x i => ?_, ?_, ?_, hform.mono fun _ _ _ _ h u u' hH => h hH.1 u, ⟨0, fun x _ i _ w τ => ?_⟩, hform⟩
  · intro τ w H _ _ z π hπ
    obtain ⟨g, -, hg⟩ := hπ
    exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).1 H _ hg
  · refine AuxiliaryNormPrimes.family_temperature_product_asymptotic_of_bessel_bound Fm Cg cb Cu cT CT C0 ?_ fun δ hδ => ?_
    · obtain ⟨x0, h0⟩ := hR
      refine ⟨x0, fun x hx i hH => ?_⟩
      have h := h0 x hx i
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg0, -, hg1, -, -, -, -, hv, -⟩ := hH.2.1
      have hk : (5 : ℝ) ≤ (Fm.D x i).R.k := by
        have := (Fm.D x i).R.m_add_three_le_k
        have := (Fm.D x i).R.two_le_m
        exact_mod_cast (by omega : 5 ≤ (Fm.D x i).R.k)
      have hb : 1 ≤ (Fm.L x i).sc.b :=
        Real.one_le_exp (Real.rpow_nonneg (zero_le_one.trans (Fm.L x i).sc.one_lt_alt.le) _)
      have h1 : (4 : ℝ) ≤ (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 :=
        le_trans (by nlinarith) (le_self_pow₀ (by nlinarith) (by norm_num))
      exact ratio_ranks _ (hM _) (h hH) (lt_of_lt_of_le one_pos hv) (by exact_mod_cast h1.trans hg0)
        (by exact_mod_cast h1.trans hg1)
    · refine ⟨max (8 / Real.log (1 + δ)) (Fm.x1 + 1), fun x hx i _ => ?_⟩
      have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hx)
      have h1 := (sizes_low _ (Fm.sizes x hx1 i)).1
      rw [Fm.L_x x i hx1] at h1
      exact err_le _ hδ (((le_max_left _ _).trans hx).trans h1)
  · refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
    have h1 := sizes_low _ (Fm.sizes x (lt_of_lt_of_le (lt_add_one _) hx) i)
    exact tcrit_low _ _ _ _ _ _ _ _ _ _ hCl (vv_eq hE hF _ (Fm.ties x i)) h1.2 h1.1
  · exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS (Fm.D x i) w τ)).2

theorem along_family :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.FormalDegreeCompactDual → ∀ (eps : ℝ) (Fm : FamP eps) (Cg cb Cu cT CT C0 A : ℝ), 40 ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusMass.Conclusion3Family Fm → VanishingOnXAndXPlus.FamilyRowsExist Fm ∧ VanishingOnXAndXPlus.admF6 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF7 Fm Cg cb Cu cT CT C0 ∧ VanishingOnXAndXPlus.admF8 Fm Cg cb Cu cT CT C0 A ∧ VanishingOnXAndXPlus.FamilyWeylDimensionVandermondeQuotient Fm Cg cb Cu cT CT C0 ∧ (OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) :=
  along_family_of_massRatio fun D => by
    letI := D.host.cmStar
    exact fun j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho' =>
      GlobalTheory.T.siegel_massRatio_unimodular_definite D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'

end GlobalTheory.CritLevel
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.CritLevelGap

private theorem VV_eq_vand_lamSH_of_standingHypotheses (hDs : Formalism.L2.SG.Pf.SzHypFD.DsigHC) (D : D7) (large₂ : SizeData₂ D)
    (C' Cl Cg cb Cu cT CT : ℝ) (hT : Ties D) (hS : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) (hL : 1 ≤ Cl * large₂.sc.L)
    (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by

  have hanti : StrictAnti (lamSH D.R (D.hc τ)) := (GlobalTheory.Mem.Vol.lamSH_isHCParam D.R (D.hc τ)).1
  have hd : D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hDs D large₂ C' Cl Cg cb Cu cT CT hT hS hL τ
  have hN : 2 * D.R.rS + D.R.k + 1 = D.R.r := dimS_eq D.R
  have hpos : (0 : ℝ) < ∏ i ∈ Finset.range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [hd, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← hN]
  field_simp

theorem tcritLow_along_family_gap :
    Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 : ℝ, ∃ thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → VanishingOnXAndXPlusBranching.admF5 Fm Cg cb Cu cT CT C0 := by
  intro _ hH _ Cg cb Cu cT CT C0
  refine ⟨40, fun eps Fm _ hCl _ => ?_⟩
  unfold VanishingOnXAndXPlusBranching.admF5 OwnEv
  refine ⟨Fm.x1 + 1, fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by linarith
  obtain ⟨hxk, hb⟩ := GlobalTheory.CritLevel.sizes_low _ (Fm.sizes x hx1 i)
  have hL1 : 1 ≤ (Fm.L x i).sc.L := by
    show 1 ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps
    exact Real.one_le_rpow (Fm.L x i).sc.one_lt_alt.le (Fm.L x i).sc.eps_pos.le
  have hL : 1 ≤ sCl Fm * (Fm.L x i).sc.L := by nlinarith
  intro h0
  exact GlobalTheory.CritLevel.tcrit_low _ _ _ _ _ _ _ _ _ _ hCl
    (fun τ => VV_eq_vand_lamSH_of_standingHypotheses hH.2.2.2 _ _ _ _ _ _ _ _ _ (Fm.ties x i) h0.1 hL τ) hb hxk h0

end GlobalTheory.CritLevelGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpBoundsUniformOfInputs
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma

noncomputable section

namespace GlobalTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.S.Cnt Formalism.FourierDecayAlt
open scoped ENNReal

theorem ampConst_of_rd_le_b (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 CS C : ℝ)
    (hrd : D.host.rdE ≤ large₂.sc.b) (hC : CS + 1 + (1 + 2 * Cg) / 2 ≤ C) :
    VanishingOnXAndXPlusBranching.IntegralityFromMetric D large₂ C' Cl Cg cb Cu cT CT C0 C1 CS C := by
  unfold VanishingOnXAndXPlusBranching.IntegralityFromMetric
  intro hS hW
  unfold VanishingOnXAndXPlusBranching.adm11 UnitaryVolumeMass.stSchur at hS
  unfold VanishingOnXAndXPlusBranching.adm12 UnitaryVolumeMass.stWeyl at hW
  unfold VanishingOnXAndXPlusBranching.Conclusion1 UnitaryVolumeMass.stCONST
  intro hH0 τ w w' hTT θ hθ W hGW A hGS hdeg μsec hμ
  have hSch := hS hH0 τ w w' hTT θ hθ W hGW A hGS μsec hμ
  have hdimq : (Module.finrank ℂ W.Wq : ℝ) = vand (uS D w' τ) / superfactorial D.R.k :=
    hW τ w' W.Wq W.z' W.π' hGW.2.1
  have hF := superfactorial_pos D.R.k
  have hVu0 : 0 ≤ vand (uS D w' τ) := by
    have e : vand (uS D w' τ) = (Module.finrank ℂ W.Wq : ℝ) * superfactorial D.R.k := by
      rw [hdimq]; field_simp
    rw [e]; exact mul_nonneg (Nat.cast_nonneg _) hF.le
  rcases hVu0.lt_or_eq with hVu | hVu
  swap
  · have h0 : (Module.finrank ℂ W.Wq : ℝ) = 0 := by rw [hdimq, ← hVu, zero_div]
    have hM0 : MMv D w w' A μsec = 0 := by
      apply le_antisymm _ (by positivity)
      calc MMv D w w' A μsec ≤ _ := hSch
        _ = 0 := by rw [h0]; simp
    rw [hM0, mul_zero]
    positivity
  obtain ⟨hS0, -, -⟩ := hH0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg1, hg1b, hg2, hg2b, -, -, -, hv1, -⟩ := hS0
  have hk6 := rank_lower_bound D
  have hm := rank_eq_two_mul_add_two D
  have hn : D.R.r = D.R.k + 2 * D.R.rS + 1 := by unfold Formalism.BasicNotions.Ranks.r; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hb1 : 1 ≤ large₂.sc.b := one_le_scale_base_local large₂
  have hv : 0 < D.host.v := by linarith
  have hT : (3 : ℝ) ≤ Formalism.MainNotions.S.Tr D w := by unfold Formalism.MainNotions.S.Tr; exact_mod_cast hTT.2.2.1
  have hT' : (3 : ℝ) ≤ Formalism.MainNotions.S.Tr D w' := by unfold Formalism.MainNotions.S.Tr; exact_mod_cast hTT.2.2.2.1
  have hkb : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk1) hb1)
  have hgg1 : 1 ≤ gg D := by
    unfold gg; exact one_le_mul_of_one_le_of_one_le (hkb.trans hg1) (hkb.trans hg2)
  have hgpos : 0 < gg D := by linarith
  have hggb : gg D ≤ large₂.sc.b ^ (2 * Cg) := by
    unfold gg
    rw [show 2 * Cg = Cg + Cg by ring, Real.rpow_add (by linarith)]
    exact mul_le_mul hg1b hg2b (by linarith) (by positivity)
  have hL1 : 1 ≤ large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) (le_of_lt large₂.sc.eps_pos)
  have h2v : 2 * D.host.v = D.host.rdE := by simp only [Formalism.BasicNotions.Host.v]; ring
  have hV : Real.log (2 * D.host.v) ≤ large₂.sc.L / 1 := by
    rw [div_one, h2v]
    calc Real.log D.host.rdE ≤ Real.log large₂.sc.b := Real.log_le_log (by linarith) hrd
      _ = large₂.sc.L := Real.log_exp _
  have hnum := numerical_constant_clause_bound D.R.rS D.R.m hm large₂.sc.b large₂.sc.L (2 * D.host.v) (gg D) (Formalism.MainNotions.S.Tr D w)
    (Formalism.MainNotions.S.Tr D w') 1 Cg CS C rfl hL1 (by linarith) hV hgg1 hggb (by linarith) (by linarith)
    (by norm_num; linarith)
  have hmain := volume_constant_main_estimate D.R.k D.R.rS D.R.m D.R.r hm hn hk1 D.host.v (gg D) (Formalism.MainNotions.S.Tr D w)
    (Formalism.MainNotions.S.Tr D w') (Module.finrank ℂ W.Wp) (vand (uS D w' τ)) (D.dsig τ)
    (large₂.sc.b ^ (CS * (D.R.m : ℝ) ^ 2)) (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2)) hv hgpos (by linarith)
    (by linarith) (Nat.cast_nonneg _) hVu (D.dsig_pos τ) hnum (by positivity)
  have hmm1 : D.R.m - 1 = 2 * D.R.rS + 1 := by omega
  have hmm2 : D.R.m * (D.R.m - 1) / 2 = (D.R.rS + 1) * (2 * D.R.rS + 1) := by
    rw [hmm1, hm, show (2 * D.R.rS + 2) * (2 * D.R.rS + 1) = 2 * ((D.R.rS + 1) * (2 * D.R.rS + 1)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have ex1 : ((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 =
      (((D.R.m - 1) * D.R.k + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) := by
    rw [hmm2, hmm1, hm]; push_cast; ring
  have ex2 : (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 =
      ((D.R.k * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) := by
    rw [hmm2, hm]; push_cast; ring
  have eX : Formalism.MainNotions.S.Tcrit D w' τ = (Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v)
      (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ))) ^ ((1 : ℝ) / D.R.k) := by
    unfold Formalism.MainNotions.S.Tcrit Formalism.FourierDecayAlt.Sz.TcritPow
    rw [show D.host.ka = Real.pi / D.host.v from rfl, ex1, ex2, Real.rpow_neg (div_nonneg Real.pi_pos.le hv.le), Real.rpow_natCast, Real.rpow_natCast,
      h2v]
    rfl
  have hTP : 0 ≤ Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v)
      (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ)) := by
    unfold Formalism.FourierDecayAlt.Sz.TcritPow
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (inv_nonneg.2 (pow_nonneg (div_nonneg Real.pi_pos.le hv.le) _))
      (Real.rpow_nonneg (by linarith) _)) (pow_nonneg hgpos.le _))
      (mul_nonneg (D.dsig_pos τ).le (superfactorial_pos _).le)) hVu.le
  have hk0 : (D.R.k : ℝ) ≠ 0 := by exact_mod_cast (show D.R.k ≠ 0 by omega)
  have eT : Formalism.MainNotions.S.Tcrit D w' τ ^ D.R.k = Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v)
      (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ)) := by
    rw [eX, ← Real.rpow_natCast, ← Real.rpow_mul hTP, one_div, inv_mul_cancel₀ hk0, Real.rpow_one]
  have e1 : normalizedLocalScale D w = (Real.exp 1 * Real.pi * (gg D ^ D.R.m)⁻¹ /
      (Formalism.MainNotions.S.Tr D w * D.R.k * D.host.v)) ^ D.R.k := by
    unfold normalizedLocalScale
    rw [Real.rpow_neg (le_of_lt hgpos), Real.rpow_natCast]
  have eP : tvPr D τ w' ^ D.R.k = Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v)
      (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ)) / Formalism.MainNotions.S.Tr D w' ^ D.R.k := by
    unfold tvPr
    rw [div_pow, eT]
  have hnv : 0 ≤ normalizedLocalScale D w := by rw [e1]; positivity
  have key := hmain
  rw [← e1, ← eP, ← hdimq, ← hdeg] at key
  calc ENNReal.ofReal (normalizedLocalScale D w) * MMv D w w' A μsec
      ≤ ENNReal.ofReal (normalizedLocalScale D w) * _ := by gcongr
    _ = ENNReal.ofReal (normalizedLocalScale D w * _) := (ENNReal.ofReal_mul hnv).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal key

theorem ampConst_fam {eps : ℝ} (Fm : FamP eps) (Cg cb Cu cT CT C0 C1 CS : ℝ)
    (hS : OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 CS)
    (hW : VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm) :
    OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.Conclusion1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 (CS + Cg + 2) := by
  unfold OwnEv at hS ⊢
  obtain ⟨x0, hx0⟩ := hS
  obtain ⟨x1, hx1⟩ := family_sizes_eventually_large eps Fm 0
  refine ⟨max x0 x1, fun x hx i => ?_⟩
  have h1 := hx0 x (le_trans (le_max_left _ _) hx) i
  have h2 := (hx1 x (le_trans (le_max_right _ _) hx) i).2.2.2.2.1
  exact ampConst_of_rd_le_b (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 _ _ (CS + Cg + 2) h2
    (by linarith) h1 (hW x i)

theorem ampBounds_uniform_of_inputs :
    ∀ Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧
      ∀ (eps : ℝ) (Fm : FamP eps),
      (∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 CPT)) →
      (∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 CDl)) →
      VanishingOnXAndXPlusBranching.admF5 Fm Cg cb Cu cT CT C0 → VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 →
      (∀ Cn, (OwnEv Fm fun C' Cl x i => DegreeRatioUnitShiftBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant)) →
      (∀ Cn, (OwnEv Fm fun C' Cl x i => AbsAllParameters (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cn Ca)) →
      (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1) →
      (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 CS) →
      VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm → ∀ Cpr : ℝ, ∀ δ > 0,
      (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  intro Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa
  have hA6 : 0 ≤ 6 * Real.exp 1 * Real.pi * |A| := by positivity
  have hAA : 6 * Real.exp 1 * Real.pi * A ≤ 6 * Real.exp 1 * Real.pi * |A| :=
    mul_le_mul_of_nonneg_left (le_abs_self A) (by positivity)
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = max CPT 0 + max (CS + Cg + 2) 0 + 6 + Ca +
      6 * Real.exp 1 * Real.pi * |A| := ⟨_, rfl⟩
  obtain ⟨Ch, hChd⟩ : ∃ Ch : ℝ, Ch = max CDl 0 + 1 := ⟨_, rfl⟩
  have hm1 := le_max_right CPT 0
  have hm2 := le_max_right (CS + Cg + 2) 0
  have hm3 := le_max_left CDl 0
  have hm4 := le_max_right CDl 0
  have hC0 : 0 ≤ C := by linarith
  have hCL : max CPT 0 + max (CS + Cg + 2) 0 + 6 ≤ C := by linarith
  have hCaC : Ca ≤ C := by linarith
  have hC2 : 2 ≤ C := by linarith
  have hCA : 6 * Real.exp 1 * Real.pi * A ≤ C := by linarith
  have hCh0 : 0 ≤ Ch := by linarith
  have hChD : CDl ≤ Ch := by linarith
  have hChD1 : CDl + 1 ≤ Ch := by linarith
  refine ⟨C, 6 * C + C ^ 2 + C * Ch, Ch, hC0, hCh0, ?_⟩
  intro eps Fm h1 h2 h5 h9 hDeg hAbs h4c h11 h12 Cpr δ hδ
  have hCn0 : 0 ≤ max Cpr 0 := le_max_right _ _
  have hCpr : Cpr ≤ max Cpr 0 := le_max_left _ _
  have hCCh := mul_nonneg hC0 hCh0
  have hsq := sq_nonneg C
  have hP1 := ampConst_fam Fm Cg cb Cu cT CT C0 C1 CS h11 h12
  have h35 := family_third_fifth_items Fm Cg cb Cu cT CT C0 A C (6 * C + C ^ 2 + C * Ch) Ch hC0 hCh0
    (by linarith) (by linarith)
  unfold OwnEv at hP1 h35 h4c ⊢
  unfold VanishingOnXAndXPlusBranching.admF5 OwnEv at h5
  unfold VanishingOnXAndXPlusBranching.admF9 OwnEv at h9
  obtain ⟨a1, ha1⟩ := h1 (max Cpr 0)
  obtain ⟨a2, ha2⟩ := h2 (max Cpr 0)
  obtain ⟨a5, ha5⟩ := h5
  obtain ⟨a9, ha9⟩ := h9 (max Cpr 0)
  obtain ⟨aD, haD⟩ := hDeg (max Cpr 0)
  obtain ⟨aA, haA⟩ := hAbs (max Cpr 0)
  obtain ⟨ac, hac⟩ := h4c
  obtain ⟨aP, haP⟩ := hP1
  obtain ⟨a35, ha35⟩ := h35
  obtain ⟨a6, ha6⟩ := family_side_conditions_large Fm C δ hδ
  obtain ⟨a9s, ha9s⟩ := rank_power_le_scale_power Fm hilbertNinetyConstant hilbertNinetyConstant_pos
  refine ⟨|Fm.x1| + 1 + |a1| + |a2| + |a5| + |a9| + |aD| + |aA| + |ac| + |aP| + |a35| + |a6| + |a9s|,
    fun x hx i => ?_⟩
  have b1 := le_abs_self a1
  have b2 := le_abs_self a2
  have b5 := le_abs_self a5
  have b9 := le_abs_self a9
  have bD := le_abs_self aD
  have bA := le_abs_self aA
  have bc := le_abs_self ac
  have bP := le_abs_self aP
  have b35 := le_abs_self a35
  have b6 := le_abs_self a6
  have b9s := le_abs_self a9s
  have bx := le_abs_self Fm.x1
  have n1 := abs_nonneg a1
  have n2 := abs_nonneg a2
  have n5 := abs_nonneg a5
  have n9 := abs_nonneg a9
  have nD := abs_nonneg aD
  have nA := abs_nonneg aA
  have nc := abs_nonneg ac
  have nP := abs_nonneg aP
  have n35 := abs_nonneg a35
  have n6 := abs_nonneg a6
  have n9s := abs_nonneg a9s
  have nx := abs_nonneg Fm.x1
  have hx1 : Fm.x1 < x := by linarith
  have A1 := ha1 x (by linarith) i
  have A2 := ha2 x (by linarith) i
  have A5 := ha5 x (by linarith) i
  have A9 := ha9 x (by linarith) i
  have AD := haD x (by linarith) i
  have AA := haA x (by linarith) i
  have Ac := hac x (by linarith) i
  have AP := haP x (by linarith) i
  have A35 := ha35 x (by linarith) i
  have S6 := ha6 x (by linarith) hx1 i
  have S9 := ha9s x (by linarith) hx1 i
  apply VanishingOnXAndXPlus.eight_amplitude_bounds_of_source
  have Q1 := constant_bound_mono (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 C1 (CS + Cg + 2) C
    (by linarith [le_max_left (CS + Cg + 2) 0]) AP
  have Q2 := weightStatement_holds (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CPT
    (CS + Cg + 2) C hCn0 hCL A1 AP
  have Dec0 := abs_decay_of_all_parameters (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CDl hilbertNinetyConstant 0 Ca Ch
    hCn0 hCn0 hCa hilbertNinetyConstant_pos hCh0 hChD1 S9 A2 A9 AD AA
  have DecP := abs_decay_of_all_parameters (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CDl hilbertNinetyConstant Cpr Ca
    Ch hCn0 hCpr hCa hilbertNinetyConstant_pos hCh0 hChD1 S9 A2 A9 AD AA
  have Q4 := abs_bound_of_zero_decay (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 C Ch
    (abs_decay_mono_constants (Fm.D x i) (Fm.L x i) hCa hCaC le_rfl Dec0)
  have L2D := L2_decay_of_admissible (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CPT CDl
    (CS + Cg + 2) Cpr C Ch hCn0 hCpr hCL hCh0 hChD A1 A2 AP
  have Q6 := lossStatement_of_bounds (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 C C δ hC2 le_rfl S6.1 S6.2 hCA
    A5 Q2 Q4
  have Q7 := decayProp_of_l2AbsDecay (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 Cpr C C Ch δ hC2 le_rfl S6.1
    S6.2 hCA A5 L2D (abs_decay_mono_constants (Fm.D x i) (Fm.L x i) hCa hCaC le_rfl DecP)
  exact ⟨Q1, Q2, A35.1, Q4, Ac, A35.2, Q6, Q7⟩

end GlobalTheory

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundsUniformLargeGapFamilies
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.GapAmpUniform

theorem weyl_fam_gap : ∀ (eps : ℝ) (Fm : FamP eps), VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm := by
  intro eps Fm x i τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (GlobalTheory.CritLevel.isHCParam_uS (Fm.D x i) w τ)).1 H _ hg

theorem amplitude_bounds_uniform_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C C2 Ch thr : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cpr : ℝ, ∀ δ > 0, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  intro hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CPT, t1, hPT⟩ := GlobalTheory.T.uniform_amplitude_bound_wide_range_large_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨CDl, t2, hDl⟩ := GlobalTheory.FamDlGap.ptDl_along_family_gap hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨t3, h5⟩ := GlobalTheory.CritLevelGap.tcritLow_along_family_gap hM hH hB Cg cb Cu cT CT C0
  obtain ⟨t4, h9⟩ := GlobalTheory.AmpFamGap.amplitudeNormDegree_along_family_largeGaps hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨hilbertNinetyConstant, t5, hilbertNinetyConstant_pos, hDeg⟩ := GlobalTheory.DegStepG.degI_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨Ca, t6, hCa, hAC⟩ := GlobalTheory.GapUAmp.abs_all_along_family_gap hM hH hB Cg cb Cu cT CT C0 A C1
  obtain ⟨CS, t8, hS⟩ := GlobalTheory.GapAmp.schur_along_family hM hH hB Cg cb Cu cT CT C0 C1
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.ampBounds_uniform_of_inputs Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa
  refine ⟨C, C2, Ch, max t1 (max t2 (max t3 (max t4 (max t5 (max t6 t8))))), hC, hCh, ?_⟩
  intro eps Fm h1 h2 hR Cpr δ hδ
  exact H eps Fm
    (hPT eps Fm ((le_max_left _ _).trans h1) ((le_max_left _ _).trans h2) hR)
    (hDl eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h5 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (h9 eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hDeg eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).1
    (hAC eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR).2
    (hS eps Fm (by simp at h1 ⊢; tauto) (by simp at h2 ⊢; tauto) hR)
    (weyl_fam_gap eps Fm) Cpr δ hδ

end GlobalTheory.GapAmpUniform
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundsUniformLargeGapFamiliesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_bounds_uniform_large_gap_families : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C C2 Ch thr : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cpr : ℝ, ∀ δ > 0, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  first | exact @GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap | exact GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap | (intros; apply GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap <;> assumption)
end
