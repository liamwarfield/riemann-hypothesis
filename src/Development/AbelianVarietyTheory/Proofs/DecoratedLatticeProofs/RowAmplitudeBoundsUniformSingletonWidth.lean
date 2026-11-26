module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneBesselTorusTranslatesLargeGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPointwiseBoundAtLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeEqBesselFunctionLargeGaps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesCoefPointwiseBoundUnconditional
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormSqLeadMinorTurnP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpectralStagePointRowPlacementTransfer
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeFoldrMax
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SchurAlongFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqVandermondeRatioAlongLine
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqVandermondeRatioAlongLine
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DegLine

open Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem gap_near {N : ℕ} (ε : Fin N → Bool) (l ν : Fin N → ℝ) (G ρ : ℝ) (hg : GapAtLeast ε l G)
    (hν : l1dist ν l ≤ ρ) : GapAtLeast ε ν (G - 2 * ρ) := by
  intro a b hab
  have hco : ∀ j, |ν j - l j| ≤ ρ := fun j =>
    le_trans (Finset.single_le_sum (f := fun j => |ν j - l j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)) hν
  have h1 := hg a b hab
  have h2 := hco a
  have h3 := hco b
  have h4 : |l a - l b| ≤ |ν a - ν b| + |ν a - l a| + |ν b - l b| := by
    have e : l a - l b = (ν a - ν b) - (ν a - l a) + (ν b - l b) := by ring
    rw [e]
    exact le_trans (abs_add_le _ _) (by have := abs_sub (ν a - ν b) (ν a - l a); linarith)
  linarith

theorem gap_lamD (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) :
    GapAtLeast (epsSH D.R) (lamD D τ) (Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbnd, _, _, _, _, hstep, _, _, _, hCl⟩ := hH.1
  have hL := one_lt_scL large₂
  have hG0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have : 0 ≤ Cl := hCl.le
    have : 0 ≤ large₂.sc.L := by linarith
    positivity
  have hv : ∀ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l := fun l h1 h2 => (hH.2.1.1 τ l h1 h2).1
  have hm := D.R.two_le_m
  have hb1 : 0 ≤ bOne D τ 1 := by
    have h := (hbnd τ 1 le_rfl (by omega)).1
    exact le_trans (le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) (le_max_left _ _)) h
  have g := gapAtLeast_of τ _ hG0 hv hb1 (hstep τ)
  intro a b hab
  exact g (Fin.cast (dimS_eq D.R) a) (Fin.cast (dimS_eq D.R) b) hab

theorem deg_eq_fdegHC (D : D7) (ht : cdScaleTie D) {W : LocW D.R.k D.R.rS}
    (l : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (hA : GoodS D l A) (h : ℝ)
    (hg : GapAtLeast (epsSH D.R) l h) (hth : Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h) : A.deg = fdegHC l := by
  obtain ⟨P, hP, hd⟩ := hA.2.2.2.2.2.2.2.2.2.2
  obtain ⟨Q, ⟨hQ, -⟩, hDS⟩ := hA.2.1
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hQd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.1
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPd
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPd
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQd
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQd
  let u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ := ⟨Q * P⁻¹, P * Q⁻¹,
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc P⁻¹, hPP', Matrix.one_mul, hQQ],
    by rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q⁻¹, hQQ', Matrix.one_mul, hPP]⟩
  let a : Formalism.REAL.UJ (epsSH D.R) := ⟨u, GlobalTheory.FormalDegreeDatum.inUJ_of_cayley _ P Q _ hP.1 hP.2 hQ.2⟩
  have hsc := (GlobalTheory.Mem.Vol.cdScaleTie_iff D).1 ht
  obtain ⟨a1, b1, hab⟩ := Formalism.MainNotions.TheoremBConstants.epsSH_both D
  have ht1 : ∃ x, epsSH D.R x = true := by
    cases h1 : epsSH D.R a1
    · exact ⟨b1, by cases h2 : epsSH D.R b1 <;> simp_all⟩
    · exact ⟨a1, h1⟩
  have hf1 : ∃ x, epsSH D.R x = false := by
    cases h1 : epsSH D.R a1
    · exact ⟨a1, h1⟩
    · exact ⟨b1, by cases h2 : epsSH D.R b1 <;> simp_all⟩
  have hF := GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps D.cd D.s.cdScale hsc _ (epsSH D.R) l h hA.1 ht1 hf1 hg hth A.H
    (fun g => A.σ (Q⁻¹ * g * Q)) hDS
  haveI := hDS.2.1
  obtain ⟨w, hw⟩ := exists_ne (0 : A.H)
  have h2 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj _ (fun g => A.σ (P⁻¹ * g * P))
    (fun g => A.σ (Q⁻¹ * g * Q)) a (fun g => by
      have e : umat (a * g * a⁻¹) = Q * P⁻¹ * umat g * (P * Q⁻¹) := rfl
      have e2 : Q⁻¹ * (Q * P⁻¹ * umat g * (P * Q⁻¹)) * Q =
          (Q⁻¹ * Q) * (P⁻¹ * umat g * P) * (Q⁻¹ * Q) := by
        simp only [Matrix.mul_assoc]
      simp only [e, e2, hQQ', Matrix.one_mul, Matrix.mul_one]) hDS.2.2.1 A.deg hd w hw
  have h3 := GlobalTheory.FormalDegreeDatum.fdeg_of_conj _ (fun g => A.σ (Q⁻¹ * g * Q))
    (fun g => A.σ (Q⁻¹ * g * Q)) 1 (fun g => by simp) hDS.2.2.1 (fdegHC l) hF w hw
  exact h2.symm.trans h3

theorem deg_eq_near (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 Cn : ℝ} (hCl : 2 * |Cn| + 8 ≤ Cl)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (ht : cdScaleTie D) (τ : D.what₂.Tau) {W : LocW D.R.k D.R.rS}
    (ν : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (hν : l1dist ν (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r)
    (A : LocS W) (hA : GoodS D ν A) : A.deg = fdegHC ν := by
  refine deg_eq_fdegHC D ht ν A hA _ (gap_near _ _ _ _ _ (gap_lamD D large₂ hH τ) hν) ?_
  obtain ⟨_, _, hmf, _⟩ := hH.1
  have hL := one_lt_scL large₂
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr6 : (6 : ℝ) ≤ D.R.r := by
    have : 6 ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hthr := Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by rw [Formalism.MainNotions.BridgeLemma₂.deg_cast_r]; linarith)
  rw [Formalism.MainNotions.BridgeLemma₂.deg_cast_r] at hthr
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := le_trans (Nat.one_le_pow _ _ (by omega)) hmf
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ D.R.r := by linarith
  have h419 : (D.R.r : ℝ) ^ 4 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have h319 : (D.R.r : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 19 := pow_le_pow_right₀ hn1 (by norm_num)
  have h119 : (D.R.r : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by
    simpa using pow_le_pow_right₀ hn1 (show 1 ≤ 19 by norm_num)
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hfl : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 * large₂.sc.L := by nlinarith
  have hCl0 : 0 ≤ Cl * (D.R.r : ℝ) ^ 19 := mul_nonneg (by linarith [abs_nonneg Cn]) (by positivity)
  have e1 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have := mul_le_mul_of_nonneg_left hfl hCl0
    have e : Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) := by
      ring
    rw [e]; linarith
  have e2 : (2 * |Cn| + 8) * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 :=
    mul_le_mul_of_nonneg_right hCl (by positivity)
  have e3 : |Cn| * (D.R.r : ℝ) ^ 4 ≤ |Cn| * (D.R.r : ℝ) ^ 19 := mul_le_mul_of_nonneg_left h419 (abs_nonneg _)
  nlinarith

theorem deg_VandLine_of_gap : ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ),
    thr ≤ C' → thr ≤ Cl → Ties D → Formalism.MainNotions.BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  intro Cn
  refine ⟨2 * |Cn| + 8, fun D large₂ C' Cl Cg cb Cu cT CT C0 C1 _ hCl hT => ?_⟩
  intro hH τ w w' _ θ _ W _ lam' hl A hA I s hs A' hA'
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hkr : (D.R.k : ℝ) ≤ D.R.r := by
    have : D.R.k ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Formalism.BasicNotions.Ranks.r; omega
    exact_mod_cast this
  have hn : (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) ^ 4 := by
    calc (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.r : ℝ) * (D.R.r : ℝ) ^ 3 :=
          mul_le_mul hkr (pow_le_pow_left₀ (by positivity) hmr 3) (by positivity) (by positivity)
      _ = (D.R.r : ℝ) ^ 4 := by ring
  have hcard : (I.card : ℝ) ≤ D.R.r := by
    rw [← Formalism.MainNotions.BridgeLemma₂.deg_cast_r]
    have : I.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ I
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hl' : Cn * D.R.k * (D.R.m : ℝ) ^ 3 ≤ |Cn| * (D.R.r : ℝ) ^ 4 := by
    have e : Cn * D.R.k * (D.R.m : ℝ) ^ 3 = Cn * ((D.R.k : ℝ) * (D.R.m : ℝ) ^ 3) := by ring
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self Cn) (by positivity))
      (mul_le_mul_of_nonneg_left hn (abs_nonneg _))
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have h1 : l1dist lam' (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r := by linarith
  have h2 : l1dist (lam' + s • epsI I) (lamD D τ) ≤ |Cn| * (D.R.r : ℝ) ^ 4 + D.R.r :=
    le_trans (Formalism.MainNotions.BridgeLemma.l1_distance_sign_step _ _ s hs I) (by linarith)
  rw [deg_eq_near D large₂ hCl hH hT.cdScale_tie τ lam' h1 A hA,
    deg_eq_near D large₂ hCl hH hT.cdScale_tie τ _ h2 A' hA']

end GlobalTheory.DegLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeRatioEqVandermondeRatioAlongLineStatement
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDegree_ratio_eq_vandermonde_ratio_along_line : ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → BridgeLemma₂.deg_VandLine D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 := by
  first | exact @GlobalTheory.DegLine.deg_VandLine_of_gap | exact GlobalTheory.DegLine.deg_VandLine_of_gap | (intros; apply GlobalTheory.DegLine.deg_VandLine_of_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpleThetaWideRangeLargeConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpleThetaWideRangeLargeConstants
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

theorem ptWide_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hDB : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  have hBp : BpJoin.ThmBpDS := GlobalTheory.discreteSeriesCoef_pointwiseBound
  obtain ⟨Cgf, hOB⟩ := GlobalTheory.AmpTKGapOne.oneBesselTor_of_gapHyp hDB
  obtain ⟨Cf, hCf, hFrm⟩ := GlobalTheory.FrameTurn.frameChange_of_frames 1 Cgf 2 zero_le_one (by norm_num)
  obtain ⟨Cb, Cg₀, hB⟩ := GlobalTheory.bp_forms_of_gapIn_thmBpDS hDB hBp 1
  obtain ⟨Ca, hCa, hAmp⟩ := GlobalTheory.AmpBesselGap.ampIsBessel hDB Cg cb Cu cT CT C0 1
  refine ⟨max (Ca + max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) * (Cf + max Cb 0 + Cf * max Cb 0)) (max Cb 0),
    fun Cn => ?_⟩
  obtain ⟨m₀, hm₀⟩ := hAmp Cn
  obtain ⟨Cs₀, hCs₀⟩ := hFrm Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ (max (128 * |max Cg₀ Cs₀|) (200 * |Cn|)))
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hTies hTF => ?_⟩
  intro hH
  obtain ⟨h1000, -, hM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH.1
  have hβ2 : (2 : ℝ) ≤ max (max 2 Cu) (max CT (1 / 8 + 2 * Cg)) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hStd : Bridge.StdOfHyp D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|)
      (max (max 2 Cu) (max CT (1 / 8 + 2 * Cg))) :=
    stdOfHyp_rec D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cg₀ Cs₀) (200 * |Cn|) _ (by linarith) zero_le_one hβ2
      (le_trans (le_max_right _ _) (le_max_left _ _))
      (by rw [mul_one]; exact le_trans (le_max_left _ _) (le_max_right _ _))
      (by rw [mul_one]; exact le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM)
      (by
        rw [abs_of_nonneg (by positivity)]
        exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM)
  have h47 : OnePlaceEstimates.UniformityTheoremBPrime D 1 Cn (max Cg₀ Cs₀) (200 * |Cn|) (max Cb 0) :=
    OnePlaceEstimates.upper_bound_mono_constant D zero_lt_one (le_max_left _ _)
      ((hB (max Cg₀ Cs₀) (le_max_left _ _)).2.2 D Cn (200 * |Cn|)
        (mul_le_mul_of_nonneg_left (le_abs_self Cn) (by norm_num)))
  have hFr : Bridge.FrameChange D 1 (max Cg₀ Cs₀) Cn Cf :=
    hCs₀ (max Cg₀ Cs₀) (le_max_right _ _) D (Formalism.MainNotions.OnePlaceExpansion.frame_bound_of_bessel_torus D Cgf 2 le_rfl (hOB D))
  exact AuxiliaryNormPrimes.plancherelBoundOneParameter_of_uniformity D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 Ca 1 Cf (max Cg₀ Cs₀) (200 * |Cn|) _ (max Cb 0) _
    (hm₀ D large₂ C' Cl h1000 hrd (le_trans (le_max_left _ _) hM) hTies.cdScale_tie) hFr hStd (fun _ => hTF) h47
    (by linarith) (le_max_right _ _) hCa hCf (le_max_left _ _) (le_max_right _ _) hH

end GlobalTheory.Core.Deg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmpleThetaWideRangeLargeConstantsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampleTheta_wideRange_large_constants : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → Formalism.L2.SG.RowsConc.TFrameAt D → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  first | exact @GlobalTheory.Core.Deg.ptWide_at_record_gap | exact GlobalTheory.Core.Deg.ptWide_at_record_gap | (intros; apply GlobalTheory.Core.Deg.ptWide_at_record_gap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtDlAtRecord
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreDlGap

theorem ptDl_at_record : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 C := by
  intro Cg cb Cu cT CT C0
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨C, hC⟩ :=
    GlobalTheory.CellMinorLineGap.minor_line hH (GlobalTheory.AmpOrbGap.ampKF hH) GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 1
  refine ⟨C, fun Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ 1)
  refine ⟨thr, fun D large₂ C' Cl h1 h2 hT => ?_⟩
  intro hH0
  obtain ⟨hCl, -, hMm, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT h1 h2 hH0.1
  have hmm : m₀ ≤ (D.R.m : ℝ) := (le_max_left _ _).trans hMm
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := (le_max_right _ _).trans hMm
  have hbig : GlobalTheory.Amp.Big D large₂ Cl m₀ := ⟨hrd, by nlinarith, hmm⟩
  exact hm D large₂ C' Cl hCl hbig hT.cdScale_tie hH0

end GlobalTheory.CoreDlGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsAllAtRecordGap
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AbsRangeConstantsFirst
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.AbsRange
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsRangeUniform

theorem abs_range_constants_first : ∀ Cg cb Cu cT CT C1 CMo : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ Cn : ℝ,
    ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl C0 : ℝ), Big D large₂ Cl m₀ → MomIn D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 25 CMo →
      ABSr D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro Cg cb Cu cT CT C1 CMo
  refine ⟨8 * |C1| + 2 * |Cg| + 46 + 24 * max CMo 0 + 8 * Real.pi * Real.exp 1, fun C hC => ⟨4, ?_⟩⟩
  intro Cn D large₂ C' Cl C0 hBig hMom hZ τ w w' hTT θ hθ W hW lam' hlam S hS γ p hp θ' hθ' νR hνR hDr
  obtain ⟨hrd, -, hm4⟩ := hBig
  have hm4' : 4 ≤ D.R.m := by exact_mod_cast hm4
  obtain ⟨-, -, hb, hm, -, -, -, hk, hv, -, hka, hvb, hg, hgb, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hrd hZ
  have hb2 : 2 ≤ large₂.sc.b := by linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hv0 : 0 < D.host.v := by linarith
  have hg0 : 0 < gg D := by linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ.1
  have hθ'0 : 0 < θ' := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hθ'.1
  have hpi := Real.pi_pos
  have hka0 : 0 < D.host.ka := by rw [hka]; positivity
  have hr : 1 ≤ D.R.rS := by omega
  have hk' : 2 * D.R.rS + 6 ≤ D.R.k := by
    have : D.R.m * 2 ≤ D.R.m ^ 4 := by
      rw [show D.R.m ^ 4 = D.R.m * D.R.m ^ 3 by ring]
      exact Nat.mul_le_mul_left _ (le_trans (by norm_num) (Nat.pow_le_pow_left hm4' 3))
    omega
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.majorantMomentBound_both_sides D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 CMo hm4' hMom hZ τ w w' hTT θ hθ W hW
    lam' hlam S hS
  obtain ⟨-, -, hμN, hS1, hS2⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W lam' S hθ0 hv0 hTT hW hS
  rw [hμN] at hS1 hS2
  have hDr' : Dr D.R.k D.R.rS W.z W.z' γ = ‖DminN W.z W.z' γ D.R.rS‖ := by
    unfold Dr DminN; rw [dite_eq_left (by omega)]
  have hTF : TwoFl D.R.k D.R.rS W.z W.z' γ :=
    ⟨hS1.1, hS2.1, hS1.2.1, hS2.2.1, hp.1, hp.2.2, by rw [hDr']; exact norm_ne_zero_iff.2 hDr⟩
  obtain ⟨hends, -, -, -, hD0, -⟩ := GlobalTheory.T.cellPoint_blockEnds_leadingMinors D W.z W.z' γ p hS1.1 hS2.1 hS1.2.1 hS2.2.1 hp
  set De : ℝ := ((ptBlockEnds p).map fun l => max 1 ‖DminN W.z W.z' γ l‖⁻¹).foldr max 1 with hDe
  have hDe1 : 1 ≤ De := one_le_foldr_max _
  have hOK : DeOK D.R.k D.R.rS W.z W.z' γ De := by
    refine ⟨hDe1, fun l _ hl => ?_⟩
    have e : Dmin D.R.k D.R.rS W.z W.z' γ l = DminN W.z W.z' γ l.val := by
      unfold DminN; rw [dite_eq_left l.2]
    rw [e] at hl ⊢
    rcases Nat.eq_zero_or_pos l.val with h0 | h0
    · rw [h0, hD0]; simpa using hDe1
    · exact le_trans (le_max_right 1 _)
        (le_foldr_max _ _ (List.mem_map.2 ⟨l.val, (hends l.val h0).1 hl, rfl⟩))
  obtain ⟨p', μR, hroot, hquot⟩ := hνR
  obtain ⟨hN, hnorm⟩ := GlobalTheory.T.rootMeasure_eq_normalFormRootMeasure D W.z W.z' p' γ μR θ' hTF hroot hθ'0.le (by positivity)
  have hM0 : 0 ≤ max CMo 0 := le_max_right _ _
  have hH : 1 ≤ large₂.sc.b ^ (max CMo 0 * D.R.m) := Real.one_le_rpow (by linarith) (by positivity)
  obtain ⟨hint, hbd⟩ := GlobalTheory.T.amplitude_absolutelyConvergent_operatorNorm_le D.R.k D.R.rS W.z W.z' W.π W.π' _ _ W.μG W.μW W.μW' W.νS W.νS' _ νR S.Φ S.Φ' γ
    S.cN _ _ _ De hr hk' (by positivity) (by positivity) hH hS1 hS2 hM1 hM2 hTF hOK hnorm hquot
  refine ⟨hint, le_trans hbd ?_⟩
  rw [hDr']
  have hmr : (D.R.m : ℝ) = 2 * D.R.rS + 2 := by exact_mod_cast hm
  have hr' : (1 : ℝ) ≤ D.R.rS := by exact_mod_cast hr
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg Cg
  have a3 : 0 ≤ 8 * Real.pi * Real.exp 1 := by positivity
  refine absBd_le D.R.rS D.R.k large₂.sc.b D.host.v _ (8 * |C1| + 2 * |Cg| + 2) De _ C (max CMo 0) D.R.m hr hmr hb.le hv0
    hM0 hDe1 (norm_nonneg _) ?_ (by linarith) (by linarith) (by linarith)
  refine le_trans (ratio_le D.R.rS D.R.k _ (D.R.rS * (D.R.k - 2 - D.R.rS)) large₂.sc.b D.host.v (gg D) θ θ' D.host.ka _ Cg
    hb2 hv hvb hg hgb hka hθ0 hθ.2 hθ'.1 hN (Nat.mul_le_mul_left _ (by omega))) ?_
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
  have r3 : (D.R.rS : ℝ) ≤ (D.R.rS : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
  have r23 : (D.R.rS : ℝ) ^ 2 ≤ (D.R.rS : ℝ) ^ 3 := pow_le_pow_right₀ hr' (by norm_num)
  have m0 : (1 : ℝ) ≤ D.R.m := by linarith
  have b1 : (D.R.m : ℝ) ^ 2 ≤ 4 * (D.R.m * (D.R.rS : ℝ) ^ 3) := by
    have : (D.R.m : ℝ) ≤ 4 * (D.R.rS : ℝ) ^ 3 := by linarith
    nlinarith
  have b2 : (D.R.rS : ℝ) ^ 2 ≤ D.R.m * (D.R.rS : ℝ) ^ 3 := by nlinarith
  have c1 : C1 * (D.R.m : ℝ) ^ 2 ≤ |C1| * (4 * (D.R.m * (D.R.rS : ℝ) ^ 3)) :=
    mul_le_mul (le_abs_self _) b1 (by positivity) a1
  have c2 : Cg * (D.R.rS : ℝ) ^ 2 ≤ |Cg| * (D.R.m * (D.R.rS : ℝ) ^ 3) :=
    mul_le_mul (le_abs_self _) b2 (by positivity) a2
  nlinarith

end GlobalTheory.Amp.AbsRangeUniform
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.BridgeLemma

namespace GlobalTheory.AbsRecGap

theorem abs_all_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Formalism.MainNotions.BridgeLemma.AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cn C := by
  intro Cg cb Cu cT CT C0
  have hG : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨CMo, hMo⟩ := GlobalTheory.AmpMomentsGap.amplitude_moments_gap hG Cg cb Cu cT CT C0 1 25
  obtain ⟨C₀, hAbs⟩ := GlobalTheory.Amp.AbsRangeUniform.abs_range_constants_first Cg cb Cu cT CT 1 CMo
  obtain ⟨m₁, hAbs'⟩ := hAbs (max C₀ 0) (le_max_left _ _)
  refine ⟨max C₀ 0, le_max_right _ _, fun Cn => ?_⟩
  obtain ⟨m₂, hM⟩ := hMo Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max (max m₁ m₂) 1000)
  refine ⟨thr, ?_⟩
  intro D large₂ C' Cl hC' hCl τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hHyp hD
  have h0 : GlobalTheory.Amp.HypZ D large₂ C' Cl Cg cb Cu cT CT C0 := by
    unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
  obtain ⟨h1000, -, hm, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl h0.1
  have hm1000 : (1000 : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) hm
  have hB : ∀ m₀, m₀ ≤ max (max m₁ m₂) 1000 → GlobalTheory.Amp.Big D large₂ Cl m₀ :=
    fun m₀ h => ⟨hrd, by nlinarith, le_trans h hm⟩
  exact (hAbs' Cn D large₂ C' Cl C0 (hB _ (le_trans (le_max_left _ _) (le_max_left _ _)))
    (hM D large₂ C' Cl h1000 (hB _ (le_trans (le_max_right _ _) (le_max_left _ _))))
    h0 τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hD).2

end GlobalTheory.AbsRecGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealPlaceAmplitudeNormLeConstDivFormalDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealPlaceAmplitudeNormLeConstDivFormalDegree
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.BridgeLemma

namespace GlobalTheory.AmpRec

theorem exists_threshold_adm9_of_ties : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ),
    thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 := by
  intro Cg cb Cu cT CT C0 Cn
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨m₀, hm⟩ := GlobalTheory.Amp.OpenCellNormGap.norm_eq_const_div_deg_gap hH (GlobalTheory.AmpOrbGap.ampKF hH)
    GlobalTheory.CellMaj.cellConv Cg cb Cu cT CT C0 1 Cn
  obtain ⟨thr, hthr⟩ := GlobalTheory.Core.Deg.elementary_size_bounds_of_size_hypotheses (max m₀ 1)
  refine ⟨thr, fun D large₂ C' Cl hC' hCl hT => ?_⟩
  intro hH0
  obtain ⟨h1000, -, hmM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hmm : m₀ ≤ (D.R.m : ℝ) := (le_max_left _ _).trans hmM
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := (le_max_right _ _).trans hmM
  have hbig : GlobalTheory.Amp.Big D large₂ Cl m₀ := ⟨hrd, by nlinarith, hmm⟩
  exact hm D large₂ C' Cl h1000 hbig hT.cdScale_tie hH0

end GlobalTheory.AmpRec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealPlaceAmplitudeNormLeConstDivFormalDegreeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceAmplitude_norm_le_const_div_formalDegree : ∀ Cg cb Cu cT CT C0 : ℝ, ∀ Cn : ℝ, ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 Cn 1 := by
  first | exact @GlobalTheory.AmpRec.exists_threshold_adm9_of_ties | exact GlobalTheory.AmpRec.exists_threshold_adm9_of_ties | (intros; apply GlobalTheory.AmpRec.exists_threshold_adm9_of_ties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurAtRecordGap
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeSchurBoundUniformConstants
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeSchurBoundUniformConstants
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp

open SchurBound

theorem schurSt_of_big_tie_uniform : ∀ Cg cb Cu cT CT C1 : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl C0 : ℝ), Big D large₂ Cl m₀ → cdScaleTie D → BSch D large₂ C' Cl Cg cb Cu cT CT C0 → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 → SchurSt D large₂ C' Cl Cg cb Cu cT CT C0 C1 C := by
  intro Cg cb Cu cT CT C1
  refine ⟨2 * |CT| + 2 * C1, fun C hC => ⟨0, ?_⟩⟩
  intro D large₂ C' Cl C0 hBig htie hB hL hZ τ w w' hTT θ hθ W hW A hA μsec hsec
  obtain ⟨-, -, hb, hm, hr, -, -, hk, hv, -, -, -, -, -, -, -, hTb, -, -⟩ :=
    GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps D large₂ C' Cl Cg cb Cu cT CT C0 hBig.1 hZ
  have hb1 : 1 ≤ large₂.sc.b := by linarith [Real.add_one_le_exp 1]
  have hθ0 : 0 < θ := lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hθ.1
  have hv0 : 0 < D.host.v := by linarith
  have hm1 : 1 ≤ D.R.m := by omega
  have hk1 : 1 ≤ D.R.k := le_trans (Nat.one_le_pow _ _ hm1) hk
  have hT : 0 < Tr D w := by unfold Tr; exact_mod_cast hTT.1.pos
  have hT' : 0 < Tr D w' := by unfold Tr; exact_mod_cast hTT.2.1.pos
  obtain ⟨hU, hI, -, hS, hS'⟩ := GlobalTheory.T.local_data_both_amplitude_sides D τ w w' θ W _ A hθ0 hv0 hTT hW hA
  obtain ⟨hM, hM', hDec⟩ := hL hZ τ w w' θ W hTT hW A hA
  have hBS := hB hZ τ w w' θ W hW A hA hT
  have hBS' := hB hZ τ w' w θ (swapW W) (goodW_swap hW) (swapS A) (goodS_swap hA) hT'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, -, -, s13, s14, s15⟩ := hS
  obtain ⟨t1, t2, t3, t4, t5, -, t7, t8, -, t10, -, -, t13, -, t15⟩ := hS'
  obtain ⟨-, -, -, -, hz, hz', -, -, -, -, -, hN, -, -⟩ := hW
  obtain ⟨-, -, a3, a4, a5, a6, -, -, -, -, P, hP, hdeg⟩ := hA
  obtain ⟨c, hc, hdens, -⟩ := GlobalTheory.T.exists_unique_haarDensity_at_identity _ (GG D.R.k D.R.rS) W.μG (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group _ _) s6
  have hSch := GlobalTheory.T.besselModel_schur_of_formalDegree_density D.R.k D.R.rS A.σ (epsSH D.R) D.cd _ P A.deg c W.μG (htie _ _) hP hdeg hc s6 hdens
  have hd : 0 < A.deg := hdeg.1
  set κ : ℝ := (2 * D.host.v) ^ (-((D.R.rS : ℝ) * D.R.k)) * θ with hκ
  have hκ0 : 0 < κ := mul_pos (Real.rpow_pos_of_pos (by linarith) _) hθ0
  obtain ⟨hmeas, hdis⟩ := GlobalTheory.T.besselDoubleCosetMeasure_bigCell_eq D.R.k D.R.rS W.z W.z' μsec W.μG W.μW W.μW' c κ hk1 s1 t1 s2 t2 hsec hc hκ0
    s6 hdens s7 s8 t7 t8
  have hN' : haarLie (Nset D.R.k D.R.rS) (ENNReal.ofReal κ) = W.μN := hN.symm
  rw [hN'] at hdis
  have hnv : ‖A.v0‖ ≠ 0 := norm_ne_zero_iff.2 a6
  have hstd : StdSm A.σ (((‖A.v0‖ : ℝ) : ℂ)⁻¹ • A.v0) (2 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 5) W.μG
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1))) := by
    refine ⟨⟨hk1, hU, hI, ?_, s6, hSch, le_rfl, hDec.mono (DD_smul_le _ _ _), inferInstance⟩, smooth_smul _ _ _ a5⟩
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hnv]
  unfold psiS at hM hM' a3 a4
  rw [psi_eq_psiGen] at hM hM' a3 a4
  have hQ := GlobalTheory.T.lintegral_hilbertSchmidtNormSq_besselAmplitude_le D.R.k D.R.rS A.σ A.v0 _ _ A.cN W.μG _ _ W.νS W.νS' _ W.z W.z' _ _ W.π W.π' A.B A.B' a6 hstd
    ⟨⟨s1, s2, s4, GlobalTheory.T.isHaarOn_besselSubgroup_prod_map _ _ _ _ _ s1 s2 s7 s9, inferInstance⟩, s5, s3⟩
    ⟨⟨t1, t2, t4, GlobalTheory.T.isHaarOn_besselSubgroup_prod_map _ _ _ _ _ t1 t2 t7 s9, inferInstance⟩, t5, t3⟩
    s10 t10 hM hM' a3 a4 s14 s15 t15 hBS hBS' hdis
  have hFm := GlobalTheory.T.measurable_hsNormSq_amplitude_besselUnitary D.R.k D.R.rS W.μG A.cN A.Φ A.Φ' s6 s13 t13
  have hvk := volUn_pos D.R.k
  have hvk1 := volUn_pos (D.R.k - 1)
  have hvn := volUn_pos (2 * D.R.rS + D.R.k + 1)
  set a : ℝ := c * 2 ^ (D.R.rS + 1) * volUn D.R.k ^ 2 / volUn (D.R.k - 1) /
    (Tz D.R.k D.R.rS W.z * Tz D.R.k D.R.rS W.z') ^ D.R.k / κ ^ 2 with ha
  have ha0 : 0 < a := by positivity
  have hcell := lintegral_cell volume _ (measurable_bcWeight D.R.k D.R.rS _ _) (bcWeight_nonneg _ _ _ _) _ _ _ a ha0 hmeas
    (measure_mono_null (t := (Greg D.R.k D.R.rS W.z W.z')ᶜ) (fun x hx h => hx (Greg_subset W.z W.z' h)) hdis.2.1) hFm
  have hMM : ENNReal.ofReal a * MMv D w w' A μsec ≤ ENNReal.ofReal ((Module.finrank ℂ W.Wp : ℝ) * Module.finrank ℂ W.Wq /
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1)))) := by
    refine le_trans (le_of_eq ?_) hQ
    unfold MMv
    rw [← hz, ← hz']
    exact hcell.symm
  have hMM2 : MMv D w w' A μsec ≤ ENNReal.ofReal (((Module.finrank ℂ W.Wp : ℝ) * Module.finrank ℂ W.Wq /
      (A.deg / (c * volUn (2 * D.R.rS + D.R.k + 1)))) / a) := by
    rw [ENNReal.ofReal_div_of_pos ha0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using ha0)) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact hMM
  refine hMM2.trans (ENNReal.ofReal_le_ofReal ?_)
  have hf := factor_le large₂.sc.b D.R.m (Tr D w) (Tr D w') θ CT C1 C D.R.rS hb1 (by exact_mod_cast hm1) hT hT' hθ0
    (hTb w) (hTb w') hθ.2 hC
  have hκ2 : κ ^ 2 = θ ^ 2 / (2 * D.host.v) ^ (2 * D.R.rS * D.R.k) := by
    rw [hκ, Real.rpow_neg (by linarith), ← Nat.cast_mul, Real.rpow_natCast, mul_assoc 2, mul_comm 2 (D.R.rS * D.R.k),
      pow_mul _ _ 2]
    field_simp
  have hpow : (Tr D w * Tr D w') ^ D.R.k = (Tr D w * Tr D w') ^ (D.R.k - 1) * (Tr D w * Tr D w') := by
    rw [← pow_succ, Nat.sub_add_cancel hk1]
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hf ?_)
  · rw [ha, hz, hz', hκ2, hpow, hr]
    field_simp
  · have := volUn_pos D.R.r
    positivity

end GlobalTheory.Amp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeSchurBoundUniformConstantsStatement
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeSchurBound_uniform_constants : ∀ Cg cb Cu cT CT C1 : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl C0 : ℝ), Big D large₂ Cl m₀ → cdScaleTie D → BSch D large₂ C' Cl Cg cb Cu cT CT C0 → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 → SchurSt D large₂ C' Cl Cg cb Cu cT CT C0 C1 C := by
  first | exact @GlobalTheory.Amp.schurSt_of_big_tie_uniform | exact GlobalTheory.Amp.schurSt_of_big_tie_uniform | (intros; apply GlobalTheory.Amp.schurSt_of_big_tie_uniform <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Amp

theorem schur_at_record_gap : ∀ Cg cb Cu cT CT C0 : ℝ, ∃ C thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), thr ≤ C' → thr ≤ Cl → Ties D → VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 C := by
  intro Cg cb Cu cT CT C0
  have hH : GlobalTheory.GapIn.Hyp := GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.uniqGap_and_besselOfW.1
  obtain ⟨C₀, hC⟩ := GlobalTheory.T.amplitudeSchurBound_uniform_constants Cg cb Cu cT CT 1
  obtain ⟨m₀, hm⟩ := hC C₀ le_rfl
  obtain ⟨m₁, hL⟩ := GlobalTheory.T.amplitudeMultOneDecay_of_largeGapHypotheses hH Cg cb Cu cT CT C0
  obtain ⟨thr, hthr⟩ := GlobalTheory.T.size_bounds_of_standingHypotheses (max (max m₀ m₁) 1)
  refine ⟨C₀, thr, fun D large₂ C' Cl h1 h2 hT => ?_⟩
  intro hZ
  obtain ⟨h1000, -, hmM, -, hrd, -⟩ := hthr D large₂ C' Cl Cg cb Cu cT CT h1 h2 hZ.1
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := le_trans (le_max_right _ _) hmM
  have hCm : 1 ≤ Cl * (D.R.m : ℝ) := by nlinarith
  have hBig : ∀ m' : ℝ, m' ≤ max (max m₀ m₁) 1 → Big D large₂ Cl m' :=
    fun m' hm' => ⟨hrd, hCm, le_trans hm' hmM⟩
  exact hm D large₂ C' Cl C0 (hBig m₀ (le_trans (le_max_left _ _) (le_max_left _ _))) hT.cdScale_tie
    (GlobalTheory.GapAmp.bessel_schur_gap hH D large₂ C' Cl Cg cb Cu cT CT C0 h1000)
    (hL D large₂ C' Cl (hBig m₁ (le_trans (le_max_right _ _) (le_max_left _ _)))) hZ

end GlobalTheory.Amp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeBoundsAtParametersOfAdmittedBoundsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeBoundsAtParamsOfAdmittedBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg

noncomputable section

namespace GlobalTheory

theorem ampAt_record_of_inputs :
    ∀ Cg CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl cb Cu cT CT C0 : ℝ), thr ≤ C' → thr ≤ Cl → 1 ≤ large₂.CGam →
      VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CPT →
      VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CDl →
      VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 →
      VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 →
      DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 hilbertNinetyConstant →
      AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 (max Cpr 0) Ca →
      VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 CS → VanishingOnXAndXPlusBranching.adm12 D →
      AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ := by
  intro Cg CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa0
  set Cc : ℝ := CS + Cg + 2 with hCc
  set K : ℝ := max CPT 0 + max Cc 0 + 6 with hK
  set Ch : ℝ := max (max CDl 0) (max (CDl + 1) 0) with hChd
  set Cm : ℝ := max (max K Ca) 2 with hCm
  set C : ℝ := max Cm (6 * Real.exp 1 * Real.pi * 1) with hCd
  set C2 : ℝ := max (6 * C) (C ^ 2 + C * Ch) with hC2
  have m1 : K ≤ Cm := le_trans (le_max_left _ _) (le_max_left _ _)
  have m2 : Ca ≤ Cm := le_trans (le_max_right _ _) (le_max_left _ _)
  have m3 : 2 ≤ Cm := le_max_right _ _
  have n1 : Cm ≤ C := le_max_left _ _
  have n4 : 6 * Real.exp 1 * Real.pi * 1 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by linarith
  have hChA : max (CDl + 1) 0 ≤ Ch := le_max_right _ _
  have hCh0 : 0 ≤ Ch := le_trans (le_max_right _ _) hChA
  have hChD : CDl ≤ Ch := le_trans (le_max_left _ _) (le_max_left _ _)
  have h62 : 6 * C ≤ C2 := le_max_left _ _
  have h22 : C ^ 2 + C * Ch ≤ C2 := le_max_right _ _
  refine ⟨C, C2, Ch, hC0, hCh0, fun Cpr δ hδ => ?_⟩
  obtain ⟨thr0, hthr0⟩ := GlobalTheory.T.size_bounds_of_standingHypotheses (max (max (C + 6 * C * Ch) C) (max (1 / δ) hilbertNinetyConstant))
  refine ⟨thr0, fun D large₂ C' Cl cb Cu cT CT C0 hC' hCl hG hA1 hA2 hA5 hA9 hDeg hAbs hA11 hA12 => ?_⟩
  by_cases hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0
  swap
  · refine ⟨?_, ?_, ?_⟩
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro w w' zs zs' γs ps _ hH
      exact absurd hH.1 hH0
    · intro τ w w' hTT θ hθ W hW S hS hdeg γ p hRel θ' hθ' νR hνR hH
      exact absurd hH.1 hH0
  obtain ⟨h1000, -, hMm, hMk, -, -, hrb, hm2k, -⟩ := hthr0 D large₂ C' Cl Cg cb Cu cT CT hC' hCl hH0.1
  have hM1 : C + 6 * C * Ch ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMm
  have hMC : C ≤ (D.R.k : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMk
  have hMd : 1 / δ ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMm
  have hM9 : hilbertNinetyConstant ≤ (D.R.m : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMm
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hb : 1 ≤ large₂.sc.b := one_le_b large₂

  have hS3 : VanishingOnXAndXPlusBranching.TowerRallisLemma D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch := by
    refine heightStatement_of_bounds D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 h62 ?_
    nlinarith
  have hS5 : VanishingOnXAndXPlusBranching.GGFromIrreducibility D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch :=
    product_clause_at_record D large₂ C' Cl Cg cb Cu cT CT C0 1 C C2 Ch hC0 hCh0 (by linarith) h22

  have hCl1 : 1 / Cl ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have p1 : VanishingOnXAndXPlusBranching.Conclusion1 D large₂ C' Cl Cg cb Cu cT CT C0 1 Cc :=
    constant_clause_schur_weyl D large₂ C' Cl Cg cb Cu cT CT C0 1 CS Cc (by rw [hCc]; linarith) hA11 hA12

  have hn : (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := by
    calc (D.R.r : ℝ) ^ (hilbertNinetyConstant * (D.R.m : ℝ)) ≤ large₂.sc.b ^ (hilbertNinetyConstant * (D.R.m : ℝ)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hrb (mul_nonneg hilbertNinetyConstant_pos hm0)
      _ ≤ large₂.sc.b ^ (2 * (D.R.m : ℝ) ^ 2) := Real.rpow_le_rpow_of_exponent_le hb (by nlinarith)
  have hmr : (D.R.m : ℝ) = 2 * (D.R.rS : ℝ) + 2 := by exact_mod_cast rank_eq_two_mul_add_two D
  have hr0 : (0 : ℝ) ≤ D.R.rS := Nat.cast_nonneg _
  have hδk : (D.R.rS : ℝ) + 2 ≤ δ * D.R.k := by
    have hmpos : (0 : ℝ) < D.R.m := by rw [hmr]; positivity
    have e1 : 1 ≤ δ * (D.R.m : ℝ) := by
      rw [div_le_iff₀ hδ] at hMd; linarith
    have e3 : (D.R.m : ℝ) ≤ δ * (D.R.m : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right e1 hmpos.le
      nlinarith
    have e4 : δ * (D.R.m : ℝ) ^ 2 ≤ δ * D.R.k := mul_le_mul_of_nonneg_left hm2k hδ.le
    linarith

  have r1 : HilbertSchmidtBoundWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    L2_decay_of_admissible D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CPT CDl Cc Cpr Cm Ch (le_max_right _ _) (le_max_left _ _)
      m1 hCh0 hChD hA1 hA2 p1
  have r2 : AbsWithSizeDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm Ch :=
    abs_decay_mono_constants D large₂ hCa0 m2 hChA
      (abs_decay_of_all_parameters D large₂ C' Cl Cg cb Cu cT CT C0 1 (max Cpr 0) 1 CDl hilbertNinetyConstant Cpr Ca (max (CDl + 1) 0) (le_max_right _ _)
        (le_max_left _ _) hCa0 hilbertNinetyConstant_pos (le_max_right _ _) (le_max_left _ _) hn hA2 hA9 hDeg hAbs)
  have q7 : VanishingOnXAndXPlusBranching.division_rows_rational_lattice D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr C Ch δ :=
    decayProp_of_l2AbsDecay D large₂ C' Cl Cg cb Cu cT CT C0 1 1 Cpr Cm C Ch δ m3 n1 hMC hδk n4 hA5 r1 r2
  exact ⟨hS3, hS5, q7⟩

end GlobalTheory

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma GlobalTheory.Core.Deg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampAt_of_admitted_bounds : ∀ Cg CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ Cpr δ : ℝ, 0 < δ → ∃ thr : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl cb Cu cT CT C0 : ℝ), thr ≤ C' → thr ≤ Cl → 1 ≤ large₂.CGam → VanishingOnXAndXPlusBranching.adm1 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CPT → VanishingOnXAndXPlusBranching.adm2 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 CDl → VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 → VanishingOnXAndXPlusBranching.adm9 D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 → DegreeRatioUnitShiftBound D large₂ C' Cl Cg cb Cu cT CT C0 (max Cpr 0) 1 hilbertNinetyConstant → AbsAllParameters D large₂ C' Cl Cg cb Cu cT CT C0 1 1 (max Cpr 0) Ca → VanishingOnXAndXPlusBranching.adm11 D large₂ C' Cl Cg cb Cu cT CT C0 1 CS → VanishingOnXAndXPlusBranching.adm12 D → AmpAt D large₂ C' Cl Cg cb Cu cT CT C0 Cpr C C2 Ch δ := by
  first | exact @GlobalTheory.ampAt_record_of_inputs | exact GlobalTheory.ampAt_record_of_inputs | (intros; apply GlobalTheory.ampAt_record_of_inputs <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidth
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpRecordGap

theorem isHCParam_u (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (fun i => ((P.u i : ℚ) : ℝ)) := by
  have hk := R.m_add_three_le_k
  obtain ⟨c, hc⟩ := R.k_even
  have step : ∀ (i : ℕ) (h : i + 1 < R.k), P.u ⟨i + 1, h⟩ < P.u ⟨i, by omega⟩ := fun i h =>
    lt_trans (P.v_gt_u ⟨i, by omega⟩) (P.u_gt_v ⟨i, by omega⟩)
  refine ⟨?_, fun a => ?_⟩
  · have key : ∀ (d i : ℕ) (h : i + d + 1 < R.k), P.u ⟨i + d + 1, h⟩ < P.u ⟨i, by omega⟩ := by
      intro d
      induction d with
      | zero => intro i h; exact step i h
      | succ d ih => intro i h; exact lt_trans (step (i + d + 1) h) (ih i (by omega))
    intro i j hij
    have hlt : i.val < j.val := hij
    have := key (j.val - i.val - 1) i.val (by omega)
    have e : P.u ⟨i.val + (j.val - i.val - 1) + 1, by omega⟩ = P.u j := congrArg P.u (Fin.ext (by simp; omega))
    rw [e] at this
    beta_reduce
    exact_mod_cast this
  · obtain ⟨z, hz⟩ := P.u_half a
    refine ⟨z - c + 1, ?_⟩
    simp only
    rw [hz, hc]; push_cast; ring

theorem isHCParam_uS (D : D7) (w : D.what₂.Word) (τ : D.what₂.Tau) : Formalism.QuantumDeterminants.IsHCParam (uS D w τ) :=
  isHCParam_u D.R (D.hcW w τ)

theorem weyl_at (D : D7) : VanishingOnXAndXPlusBranching.adm12 D := by
  intro τ w H _ _ z π hπ
  obtain ⟨g, -, hg⟩ := hπ
  exact (GlobalTheory.WeylDimU.weyl_dimension _ _ (isHCParam_uS D w τ)).1 H _ hg

theorem ampOn_singleton : ∀ c : ℝ, AmpOn {c} := by
  intro c Cg cb Cu cT CT hcb _
  obtain ⟨CPT, hPT⟩ := GlobalTheory.T.ampleTheta_wideRange_large_constants Cg cb Cu cT CT c
  obtain ⟨CDl, hDl⟩ := GlobalTheory.CoreDlGap.ptDl_at_record Cg cb Cu cT CT c
  obtain ⟨Ca, hCa, hAbs⟩ := GlobalTheory.AbsRecGap.abs_all_at_record_gap Cg cb Cu cT CT c
  obtain ⟨CS, tS, hS⟩ := GlobalTheory.Amp.schur_at_record_gap Cg cb Cu cT CT c
  obtain ⟨tL, hL⟩ := GlobalTheory.T.exists_threshold_criticalLevel_lower_bound cb Cu hcb
  obtain ⟨tV, hV⟩ := GlobalTheory.T.normalizedFormalDegree_eq_vandermonde_of_sizes
  obtain ⟨C, C2, Ch, hC, hCh, H⟩ := GlobalTheory.T.ampAt_of_admitted_bounds Cg CPT CDl 1 Ca CS zero_le_one hCa
  refine ⟨C, C2, Ch, hC, hCh, fun Cpr δ hδ => ?_⟩
  obtain ⟨t0, H0⟩ := H Cpr δ hδ
  obtain ⟨t1, h1⟩ := hPT (max Cpr 0)
  obtain ⟨t2, h2⟩ := hDl (max Cpr 0)
  obtain ⟨t3, h3⟩ := GlobalTheory.T.realPlaceAmplitude_norm_le_const_div_formalDegree Cg cb Cu cT CT c (max Cpr 0)
  obtain ⟨t4, h4⟩ := hAbs (max Cpr 0)
  obtain ⟨t5, h5⟩ := GlobalTheory.T.formalDegree_ratio_eq_vandermonde_ratio_along_line (max Cpr 0)
  refine ⟨max t0 (max t1 (max t2 (max t3 (max t4 (max tS (max tL (max tV t5))))))),
    fun C0 hC0 C' Cl hC' hCl D large₂ hG hT _ hTF => ?_⟩
  obtain rfl : C0 = c := hC0
  simp only [max_le_iff] at hC' hCl
  obtain ⟨a0, a1, a2, a3, a4, aS, -, aV, a5⟩ := hC'
  obtain ⟨b0, b1, b2, b3, b4, bS, bL, bV, b5⟩ := hCl
  have hLow : VanishingOnXAndXPlusBranching.adm5 D large₂ C' Cl Cg cb Cu cT CT C0 := fun h0 =>
    hL D large₂ C' Cl Cg cT CT C0 bL
      (hV D large₂ C' Cl Cg cb Cu cT CT aV bV hT h0.1 (GlobalTheory.T.dataNW_of_standingNumericalData D C0 h0.2.2 h0.2.1)) h0
  exact H0 D large₂ C' Cl cb Cu cT CT C0 a0 b0 hG
    (h1 D large₂ C' Cl a1 b1 hT hTF)
    (h2 D large₂ C' Cl a2 b2 hT)
    hLow
    (h3 D large₂ C' Cl a3 b3 hT)
    (Formalism.MainNotions.BridgeLemma₂.degree_ratio_one_of_vandermonde _ _ _ _ _ _ _ _ _ _ _ _
      (h5 D large₂ C' Cl Cg cb Cu cT CT C0 1 a5 b5 hT))
    (h4 D large₂ C' Cl a4 b4)
    (hS D large₂ C' Cl aS bS hT)
    (weyl_at D)

end GlobalTheory.AmpRecordGap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowAmplitudeBoundsUniformSingletonWidthStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowAmplitudeBoundsUniform_singleton_width : ∀ c : ℝ, AmpOn {c} := by
  first | exact @GlobalTheory.AmpRecordGap.ampOn_singleton | exact GlobalTheory.AmpRecordGap.ampOn_singleton | (intros; apply GlobalTheory.AmpRecordGap.ampOn_singleton <;> assumption)
end
