module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DoubleCosetBesselBoundOfBesselUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopsTies
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PairAmpConstWd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypOf
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.DegIUp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchurG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneTwo
public import Formalism.LocalToGlobal.SiegelLatticeTheory.InfCharDSGOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CentralCharacters.QuasiDeterminantConjInv
public import Formalism.SharpRestriction.CuspSpanNormBounds.KFinOfLowUnitH

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.MainNotions.BridgeCS3dBOW

open Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem orbit_data {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hσ : PI.UpqRep.IsDSHpk k r ε lam σ) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    (hWh : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hNh : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hGh : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    {W : Mx k r → Wp} (hWc : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hWeq : PI.BesselPeriodGGP.IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    {x0 : Mx k r} (hx0 : x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))
    (hI : Integrable (fun y : Formalism.QuantumDeterminants.Mt k r =>
      PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of y) • W (x0 * Matrix.of y)) μG)
    (hR : PI.BesselPeriodGGP.rconv μG (PI.BesselPeriodGGP.eFun μG σ w0) W x0 = W x0) (η : Wp) :
    ∃ Φ : Formalism.QuantumDeterminants.Mt k r → ℂ, Measurable Φ ∧ Integrable Φ μG ∧ ∫ g, Φ g ∂μG = ⟪η, W x0⟫_ℂ ∧
      ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
        ∀ᵐ p ∂(μW.prod μN), Φ (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
          ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) *
            ⟪beInt z c π σ (σ (Matrix.of x) w0) (σ x0 w0) p η, W (Matrix.of x)⟫_ℂ := by
  classical
  have := hWh.1; have := hNh.1; have := hGh.1
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0
  obtain ⟨hxi, hxx, hxx'⟩ := uh_inv hx0
  set U : Set (Formalism.QuantumDeterminants.Mt k r) := {g | Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
  have hUm : MeasurableSet U := (isClosed_UH.preimage hof).measurableSet
  let Φ : Formalism.QuantumDeterminants.Mt k r → ℂ := fun g =>
    ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g) • W (Matrix.of g)⟫_ℂ
  let Φ' : Formalism.QuantumDeterminants.Mt k r → ℂ := U.piecewise Φ (fun _ => 0)
  have hΦc : ContinuousOn Φ U := by
    have hm : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U :=
      (continuous_const.matrix_mul hof).continuousOn
    have hmaps : Set.MapsTo (fun g : Formalism.QuantumDeterminants.Mt k r => x0⁻¹ * (Matrix.of g : Mx k r)) U
        (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := fun g hg => DDSmoothness.uh_mul hxi hg
    have he : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r =>
        PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * Matrix.of g)) U := by
      unfold PI.BesselPeriodGGP.eFun
      exact continuousOn_const.mul (continuous_star.comp_continuousOn
        (continuousOn_const.inner (hcs.comp hm hmaps)))
    have hWc' : ContinuousOn (fun g : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of g)) U :=
      hWc.comp hof.continuousOn (fun g hg => hg)
    exact continuousOn_const.inner (he.smul hWc')
  have hΦm : Measurable Φ' := hΦc.measurable_piecewise continuousOn_const hUm
  have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) x0) := continuous_const.matrix_mul hof
    exact this.measurable
  have htrans : (fun g : Formalism.QuantumDeterminants.Mt k r =>
      ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) =ᵐ[μG]
      Φ' ∘ Formalism.QuantumDeterminants.lmulM x0 := by
    filter_upwards [hGae] with g hg
    have hxg : x0 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hx0 hg
    have hmem : Formalism.QuantumDeterminants.lmulM x0 g ∈ U := hxg
    simp only [Function.comp, Φ', Set.piecewise, hmem, ite_true, Φ]
    show _ = ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (x0 * Matrix.of g)) • W (x0 * Matrix.of g)⟫_ℂ
    rw [← Matrix.mul_assoc, hxx', Matrix.one_mul]
  have hmapEq : μG.map (Formalism.QuantumDeterminants.lmulM x0) = μG := hGh.2.2.2 x0 hx0
  have h1 : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
      ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) μG :=
    (innerSL ℂ η).integrable_comp hI
  have hΦint : Integrable Φ' μG := by
    have h2 : Integrable (Φ' ∘ Formalism.QuantumDeterminants.lmulM x0) μG := h1.congr htrans
    rw [← integrable_map_measure hΦm.aestronglyMeasurable hlm.aemeasurable, hmapEq] at h2
    exact h2
  refine ⟨Φ', hΦm, hΦint, ?_, ?_⟩
  · have e1 : ⟪η, W x0⟫_ℂ = ∫ g, ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ ∂μG := by
      conv_lhs => rw [← hR]
      unfold PI.BesselPeriodGGP.rconv
      rw [integral_inner hI η]
    rw [e1, integral_congr_ae htrans]
    show ∫ g, Φ' g ∂μG = ∫ a, Φ' (Formalism.QuantumDeterminants.lmulM x0 a) ∂μG
    rw [← integral_map hlm.aemeasurable hΦm.aestronglyMeasurable, hmapEq]
  · intro x hx
    filter_upwards [hPae] with p hp
    set u' := σ (Matrix.of x) w0 with hu'
    set v' := σ x0 w0 with hv'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      DDSmoothness.uh_mul hs hx
    have hmem : mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x ∈ U := hsx
    simp only [Φ', Set.piecewise, hmem, ite_true, Φ]
    show ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) •
        W (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)⟫_ℂ = _
    rw [hWeq _ hp.1 _ hp.2 _ hx]
    have hdet : IsUnit x0.det := Matrix.isUnit_det_of_right_inverse hxx
    have eσ : σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0 =
        σ x0⁻¹ (σ (Matrix.of p.1 * Matrix.of p.2) u') := by
      rw [Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hxi hsx, Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hσ hs hx]; rfl
    have eA : ⟪w0, σ (x0⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)) w0⟫_ℂ =
        ⟪v', σ (Matrix.of p.1 * Matrix.of p.2) u'⟫_ℂ := by
      rw [eσ, sigma_inner hσ hxi, Matrix.nonsing_inv_nonsing_inv x0 hdet]
    unfold PI.BesselPeriodGGP.eFun beInt
    rw [eA, inner_smul_right, inner_smul_right, piW_inner hT hπ hp.1, smul_apply,
      inner_smul_left]
    simp only [map_mul, Complex.star_def, Complex.conj_conj]
    ring

theorem g_int {σ : Mx k r → (H →L[ℂ] H)} {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {l : H → Wp} {u' v' : H}
    (hI : Integrable (beInt z c π σ u' v') (μW.prod μN))
    (hE : ∫ p, beInt z c π σ u' v' p ∂(μW.prod μN) = (innerSL ℂ (l v')).smulRight (l u')) (η w : Wp) :
    Integrable (fun p => ⟪w, beInt z c π σ u' v' p η⟫_ℂ) (μW.prod μN) ∧
      ∫ p, ⟪w, beInt z c π σ u' v' p η⟫_ℂ ∂(μW.prod μN) = ⟪l v', η⟫_ℂ * ⟪w, l u'⟫_ℂ := by
  have hf : Integrable (fun p => beInt z c π σ u' v' p η) (μW.prod μN) :=
    (ContinuousLinearMap.apply ℂ Wp η).integrable_comp hI
  refine ⟨(innerSL ℂ w).integrable_comp hf, ?_⟩
  rw [integral_inner hf w, ← ContinuousLinearMap.integral_apply hI η, hE, ContinuousLinearMap.smulRight_apply,
    inner_smul_right]
  rfl

theorem bow_core [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hS : Side k r ε lam h σ w0 z c u π μW μN μG νq) (l : H → Wp)
    (hl : ∀ u' ∈ DDsp σ w0, ∀ v' ∈ DDsp σ w0, Integrable (beInt z c π σ u' v') (μW.prod μN) ∧
      ∫ p, beInt z c π σ u' v' p ∂(μW.prod μN) = (innerSL ℂ (l v')).smulRight (l u'))
    {W : Mx k r → Wp} (hWc : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)))
    (hWeq : PI.BesselPeriodGGP.IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    (hRe : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun y : Formalism.QuantumDeterminants.Mt k r =>
        PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of y) • W (x * Matrix.of y)) μG ∧
      PI.BesselPeriodGGP.rconv μG (PI.BesselPeriodGGP.eFun μG σ w0) W x = W x) :
    ∃ κ : ℂ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = κ • l (σ x w0) := by
  classical
  obtain ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩ := hS
  have := hWh.1; have := hNh.1; have := hGh.1
  obtain ⟨hS0, hSc⟩ := DDSmoothness.muSof_facts hWh hNh
  have hνae := DDSmoothness.ae_UH_of_quot hGh.2.2.1 hS0 hSc hq
  have memDD : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ DDsp σ w0 :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hsf : SFinite (muSof μW μN) := by unfold muSof; infer_instance
  have hpm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
    have h3 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := h1.matrix_mul h2
    exact h3.measurable
  have comb : ∀ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x1 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ η0 η1 : Wp,
      ∀ b0 b1 : ℂ, (starRingEnd ℂ) b0 * ⟪l (σ x0 w0), η0⟫_ℂ = (starRingEnd ℂ) b1 * ⟪l (σ x1 w0), η1⟫_ℂ →
      b0 * ⟪η0, W x0⟫_ℂ = b1 * ⟪η1, W x1⟫_ℂ := by
    intro x0 hx0 x1 hx1 η0 η1 b0 b1 hb
    obtain ⟨Φ0, hm0, hi0, he0, ho0⟩ :=
      orbit_data hσ hT hπ hWh hNh hGh hWc hWeq hx0 (hRe x0 hx0).1 (hRe x0 hx0).2 η0
    obtain ⟨Φ1, hm1, hi1, he1, ho1⟩ :=
      orbit_data hσ hT hπ hWh hNh hGh hWc hWeq hx1 (hRe x1 hx1).1 (hRe x1 hx1).2 η1
    let F : Formalism.QuantumDeterminants.Mt k r → ℂ := fun g => b0 * Φ0 g - b1 * Φ1 g
    have hFm : Measurable F := (measurable_const.mul hm0).sub (measurable_const.mul hm1)
    have hFi : Integrable F μG := (hi0.const_mul b0).sub (hi1.const_mul b1)
    have hF0 : ∫ g, F g ∂μG = 0 := by
      refine quot_zero hq F hFm hFi ?_
      filter_upwards [hνae] with x hx
      have hFm' : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => F (mulMt s x)) :=
        hFm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))
      unfold muSof
      rw [integral_map hpm.aemeasurable hFm'.aestronglyMeasurable]
      obtain ⟨hI0, hE0⟩ := hl (σ (Matrix.of x) w0) (memDD _ hx) (σ x0 w0) (memDD _ hx0)
      obtain ⟨hI1, hE1⟩ := hl (σ (Matrix.of x) w0) (memDD _ hx) (σ x1 w0) (memDD _ hx1)
      obtain ⟨hg0, e0⟩ := g_int hI0 hE0 η0 (W (Matrix.of x))
      obtain ⟨hg1, e1⟩ := g_int hI1 hE1 η1 (W (Matrix.of x))
      have hval : ∀ᵐ p ∂(μW.prod μN), F (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
          ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) * (starRingEnd ℂ)
            ((starRingEnd ℂ) b0 * ⟪W (Matrix.of x), beInt z c π σ (σ (Matrix.of x) w0) (σ x0 w0) p η0⟫_ℂ -
            (starRingEnd ℂ) b1 * ⟪W (Matrix.of x), beInt z c π σ (σ (Matrix.of x) w0) (σ x1 w0) p η1⟫_ℂ) := by
        filter_upwards [ho0 x hx, ho1 x hx] with p h0p h1p
        show b0 * Φ0 _ - b1 * Φ1 _ = _
        rw [h0p, h1p, ← inner_conj_symm (beInt z c π σ (σ (Matrix.of x) w0) (σ x0 w0) p η0) (W (Matrix.of x)),
          ← inner_conj_symm (beInt z c π σ (σ (Matrix.of x) w0) (σ x1 w0) p η1) (W (Matrix.of x))]
        simp only [map_sub, map_mul, Complex.conj_conj]
        ring
      rw [integral_congr_ae hval, integral_const_mul, integral_conj,
        integral_sub (hg0.const_mul _) (hg1.const_mul _), integral_const_mul, integral_const_mul, e0, e1]
      have hE : (starRingEnd ℂ) b0 * (⟪l (σ x0 w0), η0⟫_ℂ * ⟪W (Matrix.of x), l (σ (Matrix.of x) w0)⟫_ℂ) -
          (starRingEnd ℂ) b1 * (⟪l (σ x1 w0), η1⟫_ℂ * ⟪W (Matrix.of x), l (σ (Matrix.of x) w0)⟫_ℂ) = 0 := by
        linear_combination ⟪W (Matrix.of x), l (σ (Matrix.of x) w0)⟫_ℂ * hb
      rw [hE, map_zero, mul_zero]
    have hsplit : ∫ g, F g ∂μG = b0 * ∫ g, Φ0 g ∂μG - b1 * ∫ g, Φ1 g ∂μG := by
      show ∫ g, (b0 * Φ0 g - b1 * Φ1 g) ∂μG = _
      rw [integral_sub (hi0.const_mul b0) (hi1.const_mul b1), integral_const_mul, integral_const_mul]
    rw [hsplit, he0, he1] at hF0
    exact sub_eq_zero.mp hF0
  by_cases hzero : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), l (σ x w0) = 0
  · refine ⟨0, fun x0 hx0 => ?_⟩
    rw [zero_smul]
    apply ext_inner_left ℂ
    intro η
    rw [inner_zero_right]
    have := comb x0 hx0 x0 hx0 η 0 1 0 (by rw [hzero x0 hx0]; simp)
    simpa using this
  · push Not at hzero
    obtain ⟨x1, hx1, hl1⟩ := hzero
    have hy : ⟪l (σ x1 w0), l (σ x1 w0)⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hl1
    refine ⟨⟪l (σ x1 w0), W x1⟫_ℂ / ⟪l (σ x1 w0), l (σ x1 w0)⟫_ℂ, fun x0 hx0 => ?_⟩
    apply ext_inner_left ℂ
    intro η
    rw [inner_smul_right]
    have hc := comb x0 hx0 x1 hx1 η (l (σ x1 w0)) ⟪l (σ x1 w0), l (σ x1 w0)⟫_ℂ ⟪η, l (σ x0 w0)⟫_ℂ
      (by rw [inner_conj_symm, inner_conj_symm]; ring)
    rw [div_mul_eq_mul_div, eq_div_iff hy]
    linear_combination hc


variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] in
theorem besselOfW_of_local_decomposition (hDI : Formalism.FourierDecayAlt.ThreeDimData.DecInf) (hJ : PI.BesselMapUniq.BesselMapUniq) :
    Formalism.L2.SG.LocWSOf.BesselOfW := by
  intro k r z c u lam ε h H _ _ _ σ hlam hσ hgap hok hz hT hc Vp _ _ _ π hπ w hw μG μW μN ν hG hW hN hq W hWc hWeq
    hRe hne hfin
  have : CompleteSpace Vp := FiniteDimensional.completeSpace ℂ Vp
  have hS : Side k r ε lam h σ w z c u π μW μN μG ν := ⟨hlam, hσ, hgap, hok, hw, hz, hT, hc, hπ, hW, hN, hG, hq⟩
  obtain ⟨l, hlB, hla, -⟩ := Formalism.FourierDecayAlt.P.discrete_series_form_one (Formalism.MainNotions.BridgeCS3dClosed.inputs_of hDI hJ)
    k r ε lam h H σ w Vp z c u π μW μN μG ν hS
  obtain ⟨κ, hκ⟩ := bow_core hS l hla hWc hWeq hRe
  exact ⟨fun v => κ • l v, (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mpr (DDSmoothness.bessel_smul hlB κ), hκ⟩


end Formalism.MainNotions.BridgeCS3dBOW
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCountHolds
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

theorem FibreCount_holds {D : D7} {X : HidaSetting D} (Y : Full X) : Formalism.L2.SG.LoopTieOf.FibreCount Y :=
  fibreCount_of (Formalism.L2.SG.Pf.Act.rowFree_of (fun u' => Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK)
    Formalism.L2.SG.Pf.iotaRepC_holds)

end Formalism.L2.SG.Pf.FibreCounting
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstHolds
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

theorem AmpFibreConst_holds {D : D7} {X : HidaSetting D} (Y : Full X) : Formalism.L2.SG.LoopTieOf.AmpFibreConst Y :=
  ampFibreConst_of Formalism.L2.SG.Pf.ratPt_holds Formalism.L2.SG.Closed.ChiTrivialC_holds Y

end Formalism.L2.SG.Pf.FibreCounting
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GammaFixedOfHypotheses
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1e

variable {D : D7} {X : HidaSetting D}

theorem gamma_one_eq_prod (Y : Full X) (u u' : D.what₂.Word) :
    (Y.tO u u').Gam1 = ∏ v, ((Fintype.card (GL (Fin D.R.k) (Y.TR.Fq v)) : ℝ) /
      (Formalism.L2.SG.GGMirabolic.cardU (Y.TR.Fq v) D.R.k : ℝ)) := by
  have h1 : Formalism.L2.SG.GGMirabolic.gamProd Y.TR.psi0 (1 : Iof Y.TR) =
      ((∏ v, ((Fintype.card (GL (Fin D.R.k) (Y.TR.Fq v)) : ℝ) /
        (Formalism.L2.SG.GGMirabolic.cardU (Y.TR.Fq v) D.R.k : ℝ)) : ℝ) : ℂ) := by
    simp only [Formalism.L2.SG.GGMirabolic.gamProd, Pi.one_apply, Formalism.L2.SG.GGMirabolic.gam_one]
    push_cast
    rfl
  show (Formalism.L2.SG.GGMirabolic.gamProd Y.TR.psi0 (1 : Iof Y.TR)).re = _
  rw [h1, Complex.ofReal_re]

theorem card_gl_div_unipotent (K : Type) [Field K] [Fintype K] (k : ℕ) :
    (Fintype.card (GL (Fin k) K) : ℝ) / (Formalism.L2.SG.GGMirabolic.cardU K k : ℝ) =
      ∏ i ∈ Finset.Icc 1 k, ((Fintype.card K : ℝ) ^ i - 1) := by
  have hU : Formalism.L2.SG.GGMirabolic.cardU K k = Nat.card (Formalism.DoubleCosetMeasures.upUniG K k) := by
    unfold Formalism.L2.SG.GGMirabolic.cardU
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    show Formalism.L2.SG.GGMirabolic.IsUni k x ↔ Formalism.DoubleCosetMeasures.IsUpUni (x : Matrix (Fin k) (Fin k) K)
    constructor
    · intro h
      refine ⟨?_, h.1⟩
      intro i j hij
      exact h.2 i j hij
    · intro h
      refine ⟨h.2, ?_⟩
      intro i j hij
      exact h.1 hij
  have hG := Formalism.FourierDecayAlt.P.gamma_factor_product K k
  have hq : 1 ≤ Fintype.card K := Fintype.card_pos
  have hpos : 0 < Nat.card (Formalism.DoubleCosetMeasures.upUniG K k) := Nat.card_pos
  rw [hU, ← Nat.card_eq_fintype_card, hG, Nat.cast_mul, mul_div_cancel_left₀ _ (by exact_mod_cast hpos.ne'),
    Nat.cast_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one]

theorem GamPin_of_split (Y : Full X) (h0 : Formalism.MainNotions.S.SplitsE D (D.host.g 0)) (h1 : Formalism.MainNotions.S.SplitsE D (D.host.g 1)) :
    GamPin Y := by
  intro u u'
  rw [gamma_one_eq_prod, Formalism.MainNotions.BridgeLemma.gaG_eq D h0 h1]
  simp_rw [card_gl_div_unipotent]
  rw [Formalism.L2.SG.Pf.SatGram.prod_two (fun v => Fintype.card (Y.TR.Fq v)) (D.host.g 0) (D.host.g 1) D.host.g_ne
    (fun v => Y.TR.card_q v) (fun n : ℕ => ∏ i ∈ Finset.Icc 1 D.R.k, ((n : ℝ) ^ i - 1)),
    Formalism.L2.SG.Pf.typed_count_holds X Y.TR 0, Formalism.L2.SG.Pf.typed_count_holds X Y.TR 1,
    Formalism.L2.SG.KappaOffDiagonal.PgLe.finrank_F]

theorem GamPin_of_data (Y : Full X) {C0 : ℝ} (h : StandingNumericalData D C0) : GamPin Y :=
  GamPin_of_split Y h.2.2.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.2.2.1

theorem gammaFixed_of_hypotheses (Y : Full X) {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (h : Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) : GamPin Y :=
  GamPin_of_data Y h.2.1

end ZsC1e

end Formalism.L2.SG.LoopTieOf
end
end

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf Formalism.L2.SG.LoopsCut
  Formalism.L2.SG.LoopsFinal Formalism.L2.SG.LoopsEv Formalism.FourierDecayAlt

namespace Formalism.L2.SG.LoopsTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure ConcAt0 (D : D7) (T : TermTie D) where
  X : HidaSetting D
  Y : Full X
  hF : FinX Y
  hI : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF)
  jt : JtPin hF hI T
  wr : WRowPin hF hI T
  fc : FibreCount Y

section TransportedAlt

theorem loop_evaluation_threshold_zero (hLC : PN.LoopCores) (hSub : PB.SubFamily) (hS : Formalism.HermitianLatticesTheory.SiegelMassRatio)
    (Cg cb Cw cT CT C0 A C₀ : ℝ) :
    ∃ C'₀ Cl₀ : ℝ, ∀ {eps : ℝ} (Fm : FamP eps) (C1 : ℝ) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
      (Yt : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
        LoopTie (Fm.D x i) (Fm.L x i) (At x hx i) u u' C1)
      (Cc : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcAt0 (Fm.D x i) (At x hx i)),
      (∀ C : ℝ, C₀ ≤ C → OwnEv Fm fun C' Cl x i => ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
        Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A →
          Formalism.MainNotions.BridgeLemma.RowsND (At x hx i) (Yt x hx i u u') C ∧ Formalism.MainNotions.BridgeLemma.RowsDeg (At x hx i) (Yt x hx i u u') C ∧
            Formalism.MainNotions.BridgeLemma.RowsOne (At x hx i) (Yt x hx i u u') C) →
      (OwnEv Fm fun C' Cl x i =>
        Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cw cT CT C0 → ∀ u, UnitaryVolumeMass.FormAt (Fm.D x i) u) →
      OwnEv Fm fun C' Cl x i => C'₀ ≤ C' → Cl₀ ≤ Cl →
        ∀ (hx : Fm.x1 < x) (u u' : (Fm.D x i).what₂.Word),
          Cnt.Hyp (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cw cT CT C0 A → ConcTie (Cc x hx i).X (Cc x hx i).Y →
          ((Cc x hx i).Y.tO u u').AbsConv →
          ((Cc x hx i).Y.tO u u').RowBig (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') ∧
          ((Cc x hx i).Y.tO u u').RowNotScalar (epsL (Fm.D x i)) (ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
  obtain ⟨C₃, _, HX⟩ := xiSizesC_of hS Cg cb Cw cT CT C0 A
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max C₀ C₃) (max CT 1) := ⟨_, rfl⟩
  have hCC₀ : C₀ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_left _ _)
  have hCC₃ : C₃ ≤ C := by rw [hCdef]; exact le_max_of_le_left (le_max_right _ _)
  have hCT : CT ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_left _ _)
  have hC : 1 ≤ C := by rw [hCdef]; exact le_max_of_le_right (le_max_right _ _)
  obtain ⟨K₀, hJ⟩ := Formalism.L2.SG.RowsOther.rowLoops_of_input hLC hSub C hC
  obtain ⟨a3, b3, HX'⟩ := HX C hCC₃
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : ℝ, A₀ = max 1 C0 := ⟨_, rfl⟩
  have hA₀1 : 1 ≤ A₀ := by rw [hA₀]; exact le_max_left _ _
  refine ⟨max a3 K₀, max b3 (max 4 (3 + 6 * Real.log (3 * A₀))), ?_⟩
  intro eps Fm C1 At Yt Cc HR hFo
  refine (OwnEv.and (HR C hCC₀) hFo).mono ?_
  rintro C' Cl x i ⟨H1, H2⟩ hC' hCl hx u u' hH hT hA
  have ha3 : a3 ≤ C' := le_trans (le_max_left _ _) hC'
  have hK₀ : K₀ ≤ C' := le_trans (le_max_right _ _) hC'
  have hb3 : b3 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hCl4 : 4 ≤ Cl := le_trans (le_max_of_le_right (le_max_left _ _)) hCl
  have hClA : 3 + 6 * Real.log (3 * A₀) ≤ Cl := le_trans (le_max_of_le_right (le_max_right _ _)) hCl
  obtain ⟨hn, hd, h1⟩ := H1 hx u u' hH
  have hFo' := H2 hH.1 u
  have hGP : GamPin (Cc x hx i).Y := gammaFixed_of_hypotheses (Cc x hx i).Y hH.1
  have hXiH := HX' C' Cl ha3 hb3 (Fm.D x i) (Fm.L x i) u u' hH
  have hP := params_at hH.1 (Cc x hx i).X u hCl4 hCT hC hK₀
  have hb := Formalism.MainNotions.BridgeLemma.d_two_le_b (Fm.D x i) (Fm.L x i)
  have hb0 : (0 : ℝ) < (Fm.L x i).sc.b := by linarith
  have hk0 : (0 : ℝ) < (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < (Fm.D x i).R.k)
  have hg : 0 < ((Cc x hx i).X.B.g : ℝ) := by
    have h5 : (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 ≤ ((Cc x hx i).X.B.g : ℝ) := hP.2.2.2.2.1
    have h8 : 0 < (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 := by positivity
    linarith
  have hv : 0 ≤ (Fm.D x i).host.v := by linarith [hP.2.2.2.2.2.2.1]
  have hC0' : (0 : ℝ) ≤ C := by linarith
  have hGam : 0 ≤ GamS (Fm.D x i) (Fm.L x i) := by unfold GamS; exact (Real.exp_pos _).le
  have HS : ∀ s, 2 ≤ s → s ≤ (Fm.D x i).R.k →
      ClassLe ((Cc x hx i).Y.tO u u') (bigS ((Cc x hx i).Y.tO u u') s)
        (A₀ * rowS C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f s (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
          (Fm.D x i).host.v (GamS (Fm.D x i) (Fm.L x i)) (Formalism.MainNotions.BridgeLemma.XiB (Fm.D x i) (Fm.L x i) u C) *
          ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    intro s h2 hk
    have hX0 := xi_nonneg hXiH s h2 hk
    rw [hA₀]
    exact rowsSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      hH C hn hd s h2 hk (ndRow_nonneg hC0' hb0 hg hv hGam hX0) (degRow_nonneg hC0' hb0 hg hv hGam hX0)
  have H1' : ClassLe ((Cc x hx i).Y.tO u u') (((Cc x hx i).Y.tO u u').nsc ((Cc x hx i).Y.tO u u').genSet)
      (A₀ * oneT C (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f (Fm.L x i).sc.b ((Cc x hx i).X.B.g : ℝ)
        (GamS (Fm.D x i) (Fm.L x i)) * ddC (Cc x hx i).X (Cc x hx i).Y u u') := by
    rw [hA₀]
    exact oneSC_at (At x hx i) (Cc x hx i).jt (Cc x hx i).wr (Cc x hx i).fc hGP (Yt x hx i u u') hFo' hT
      C0 C hC0' h1
  obtain ⟨Al, NT', Gam, Xi, hAl, hP', hX', h6, hAmp⟩ :=
    loopsAmp_at hH hT hA hC hCT hK₀ hA₀1 hCl4 hClA hXiH HS H1'
  exact hJ _ _ _ _ _ ((Cc x hx i).Y.tO u u') (Fm.D x i).R.k (Fm.D x i).R.rS (Fm.D x i).R.f Al (Fm.L x i).sc.b
    ((Cc x hx i).X.B.g : ℝ) (Fm.D x i).host.v NT' Gam Xi (ddC (Cc x hx i).X (Cc x hx i).Y u u')
    hAl hP' hX' h6 (dd_nonneg hT u u') hA
    (Formalism.L2.SG.RowsOther.loopsInput_of_amp _ hA.2.2.le _ _ _ _ _ _ _ _ _ _ _ hAmp)

end TransportedAlt

section Fam5

variable {eps : ℝ} (Fm : FamP eps) (C1 : ℝ)
  (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, HidaSetting (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Full (X x hx i))
  (hF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), FinX (Y x hx i))
  (hI : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), SIso (Fm.D x i).s (Formalism.L2.SG.PackageTie2.sOf (hF x hx i)))
  (hCT : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ConcTie (X x hx i) (Y x hx i))


end Fam5

end Formalism.L2.SG.LoopsTies
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.FourierDecayAlt Finset

namespace Formalism.L2.SG.Pf.SzHypFD

variable {D : D7}

def DsigHC : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ), Ties D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → 1 ≤ Cl * large₂.sc.L →
    ∀ τ : D.what₂.Tau, D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ))

theorem dsig_eq [hF : Fact DsigHC] {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := hF.out D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem vv_eq_vand {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) : VV D τ = vand (lamSH D.R (D.hc τ)) := by
  have hanti := Formalism.MainNotions.BridgeLemma.szh_anti hH τ
  have hSF : (0 : ℝ) < ∏ i ∈ range (2 * D.R.rS + D.R.k + 1), (i.factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i
  unfold VV
  rw [dsig_eq hT hH hCL τ, Formalism.MainNotions.BridgeLemma.szh_fdegHC _ hanti, ← dimS_eq]
  field_simp


variable [Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC] in
theorem fdl_of_ties {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hT : Ties D) (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (τ : D.what₂.Tau) :
    Sz.FormalDegreeLower (Formalism.MainNotions.BridgeLemma.cfgOf D τ) (1 / 2) (VV D τ) := by
  unfold Sz.FormalDegreeLower
  rw [Formalism.MainNotions.BridgeLemma.Vand_lam D τ, vv_eq_vand hT hH hCL τ]
  have h0 : 0 ≤ vand (lamSH D.R (D.hc τ)) := Formalism.MainNotions.BridgeLemma.szh_vand_nonneg _ (Formalism.MainNotions.BridgeLemma.szh_anti hH τ)
  linarith

end Formalism.L2.SG.Pf.SzHypFD
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbClosed
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.GapOfHypotheses
noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDD

theorem arith (N m s h Cl M AS AG : ℝ) (hN : 6 ≤ N) (hm2 : 2 ≤ m) (hmN : m ≤ N) (hs1 : 1 ≤ s) (hsm : s ≤ m)
    (hCl : 1000 ≤ Cl) (hh : 8 * Cl * N ^ 19 ≤ h) (hM : M ≤ m ^ 2 / 2) (_hM0 : 0 ≤ M) (hAS : AS ≤ 2 * N ^ 3)
    (hAS0 : 0 ≤ AS) (hAG : AG ≤ 4 * N ^ 3) (hAG0 : 0 ≤ AG) :
    120 * N ^ 3 ≤ h ∧ 2 * M * (AS + AG) + AG + 3 ≤ h / (8 * s) ∧
      9 * (m / 2) * N ^ 2 + 3 * AG + 3 ≤ h / (8 * s) ∧
      10 * (m / 2) ^ 2 * (AS + AG) + 2 * AG + 4 ≤ h / (8 * s) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hs0 : (0 : ℝ) < s := by linarith
  have hsN : s ≤ N := le_trans hsm hmN
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have h35 : N ^ 3 ≤ N ^ 5 := pow_le_pow_right₀ hN1 (by norm_num)
  have h319 : N ^ 3 ≤ N ^ 19 := pow_le_pow_right₀ hN1 (by norm_num)
  have h619 : N ^ 6 ≤ N ^ 19 := pow_le_pow_right₀ hN1 (by norm_num)
  have h15 : (1 : ℝ) ≤ N ^ 5 := one_le_pow₀ hN1
  have h19 : (0 : ℝ) ≤ N ^ 19 := pow_nonneg hN0 19
  have hClN : 1000 * N ^ 19 ≤ Cl * N ^ 19 := mul_le_mul_of_nonneg_right hCl h19
  have hmm : m ^ 2 ≤ N ^ 2 := by nlinarith
  have hMb : M ≤ N ^ 2 / 2 := by linarith
  have hA : AS + AG ≤ 6 * N ^ 3 := by linarith
  have hA0 : 0 ≤ AS + AG := by linarith
  have key : ∀ X : ℝ, X ≤ 30 * N ^ 5 → X ≤ h / (8 * s) := by
    intro X hX
    rw [le_div_iff₀ (by linarith)]
    have q1 : X * (8 * s) ≤ 30 * N ^ 5 * (8 * s) := mul_le_mul_of_nonneg_right hX (by linarith)
    have q2 : 30 * N ^ 5 * (8 * s) ≤ 30 * N ^ 5 * (8 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have q3 : 30 * N ^ 5 * (8 * N) = 240 * N ^ 6 := by ring
    linarith
  refine ⟨by linarith, key _ ?_, key _ ?_, key _ ?_⟩
  · have q : M * (AS + AG) ≤ N ^ 2 / 2 * (6 * N ^ 3) := mul_le_mul hMb hA hA0 (by positivity)
    have e : N ^ 2 / 2 * (6 * N ^ 3) = 3 * N ^ 5 := by ring
    linarith
  · have q : m * N ^ 2 ≤ N * N ^ 2 := mul_le_mul_of_nonneg_right hmN (by positivity)
    have e : N * N ^ 2 = N ^ 3 := by ring
    linarith
  · have hm4 : (m / 2) ^ 2 ≤ N ^ 2 / 4 := by nlinarith
    have q : (m / 2) ^ 2 * (AS + AG) ≤ N ^ 2 / 4 * (6 * N ^ 3) := mul_le_mul hm4 hA hA0 (by positivity)
    have e : N ^ 2 / 4 * (6 * N ^ 3) = 3 / 2 * N ^ 5 := by ring
    linarith

theorem gap_of_hypotheses (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) (hCl : 1000 ≤ Cl) (hCn : Cn ≤ Cl) :
    GapOfHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ lam' hdist
  obtain ⟨hS0, -, -⟩ := hH
  have hg := Formalism.MainNotions.BridgeLemma.szh_gap hS0 τ
  have hkL := Formalism.MainNotions.BridgeLemma.szh_k_le hS0 (by linarith) τ

  have hm2 := D.R.two_le_m
  have hkm := D.R.m_add_three_le_k
  have hrS : 2 * D.R.rS + 2 = D.R.m := Ranks.rS_two D.R
  have hr : D.R.r = 2 * D.R.rS + D.R.k + 1 := by unfold Ranks.r; omega
  set N : ℝ := (D.R.r : ℝ) with hNdef
  set m : ℝ := (D.R.m : ℝ) with hmdef
  set kk : ℝ := (D.R.k : ℝ) with hkdef
  have hNr : N = kk + m - 1 := by
    rw [hNdef, hkdef, hmdef]; unfold Ranks.r; push_cast [show 1 ≤ D.R.k + D.R.m by omega]; ring
  have hm2' : (2 : ℝ) ≤ m := by rw [hmdef]; exact_mod_cast hm2
  have hk5 : m + 3 ≤ kk := by rw [hmdef, hkdef]; exact_mod_cast hkm
  have hN6 : (6 : ℝ) ≤ N := by linarith
  have hmN : m ≤ N := by linarith
  have hkN : kk ≤ N := by linarith

  have hf : (2 : ℝ) ≤ (D.R.f : ℝ) := by
    have : 2 ≤ D.R.f := by
      unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hL : (1 / 2 : ℝ) ≤ large₂.sc.L := by
    by_contra hc
    push Not at hc
    have h1 : Real.exp (2 * large₂.sc.L) < Real.exp 1 := Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    linarith

  set h0 : ℝ := Cl * N ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L with hh0
  have hf5 : (32 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := by
    have : (2 : ℝ) ^ 5 ≤ (D.R.f : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) hf 5
    norm_num at this; linarith
  have hN19 : (0 : ℝ) ≤ N ^ 19 := by positivity
  have hClN : (0 : ℝ) ≤ Cl * N ^ 19 := by positivity
  have hh0big : 16 * (Cl * N ^ 19) ≤ h0 := by
    have e1 : Cl * N ^ 19 * 32 ≤ Cl * N ^ 19 * (D.R.f : ℝ) ^ 5 :=
      mul_le_mul_of_nonneg_left hf5 (by positivity)
    have e2 : Cl * N ^ 19 * (D.R.f : ℝ) ^ 5 * (1 / 2) ≤ h0 :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    nlinarith

  have hkm3 : kk * m ^ 3 ≤ N ^ 19 := by
    have a1 : kk * m ^ 3 ≤ N * N ^ 3 :=
      mul_le_mul hkN (pow_le_pow_left₀ (by linarith) hmN 3) (by positivity) (by linarith)
    have a2 : N * N ^ 3 = N ^ 4 := by ring
    have a3 : N ^ 4 ≤ N ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
    linarith
  have hpert : 4 * (Cn * kk * m ^ 3) ≤ h0 / 2 := by
    have hkm0 : 0 ≤ kk * m ^ 3 := by positivity
    have b1 : Cn * kk * m ^ 3 ≤ Cl * N ^ 19 := by
      rcases le_total Cn 0 with hc | hc
      · have : Cn * (kk * m ^ 3) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hkm0
        have : (0 : ℝ) ≤ Cl * N ^ 19 := by positivity
        nlinarith
      · have : Cn * (kk * m ^ 3) ≤ Cl * N ^ 19 := mul_le_mul hCn hkm3 hkm0 (by linarith)
        nlinarith
    linarith
  refine ⟨h0 / 2, ?_, ?_, ?_⟩
  ·
    intro a b hab
    have h1 := hg a b hab
    have da : |lam' a - lamD D τ a| ≤ l1dist lam' (lamD D τ) := by
      unfold l1dist
      exact Finset.single_le_sum (f := fun i => |lam' i - lamD D τ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ a)
    have db : |lam' b - lamD D τ b| ≤ l1dist lam' (lamD D τ) := by
      unfold l1dist
      exact Finset.single_le_sum (f := fun i => |lam' i - lamD D τ i|) (fun i _ => abs_nonneg _) (Finset.mem_univ b)
    have hlam : lamD D τ = lamSH D.R (D.hc τ) := rfl
    rw [hlam] at da db
    have tri : |lamSH D.R (D.hc τ) a - lamSH D.R (D.hc τ) b| ≤
        |lam' a - lam' b| + |lam' a - lamSH D.R (D.hc τ) a| + |lam' b - lamSH D.R (D.hc τ) b| := by
      have := abs_sub_le (lamSH D.R (D.hc τ) a) (lam' a) (lamSH D.R (D.hc τ) b)
      have h2 := abs_sub_le (lam' a) (lam' b) (lamSH D.R (D.hc τ) b)
      rw [abs_sub_comm (lamSH D.R (D.hc τ) a) (lam' a)] at this
      linarith
    have hd2 : l1dist lam' (lamD D τ) ≤ Cn * kk * m ^ 3 := by rw [hkdef, hmdef]; exact hdist
    rw [hlam] at hd2
    have : h0 ≤ |lamSH D.R (D.hc τ) a - lamSH D.R (D.hc τ) b| := h1
    linarith
  ·
    have hk1 : 1 ≤ D.R.k := by omega
    obtain ⟨cM, cM0, cS, cS0, cG, cG0⟩ := Formalism.MainNotions.NearParameterGap.consts D.R.k D.R.rS hk1
    have eN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = N := by rw [hNdef, hr]
    have eM : (2 * (D.R.rS : ℝ) + 2) = m := by rw [hmdef, ← hrS]; push_cast; ring
    have eN' : 2 * (D.R.rS : ℝ) + D.R.k + 1 = N := by rw [← eN]; push_cast; ring
    rw [eM] at cM
    rw [eN'] at cS cG
    have hsq : Real.sqrt (2 * ((D.R.rS : ℝ) + 1)) = Real.sqrt m := by rw [← eM]; ring_nf
    have hs1 : (1 : ℝ) ≤ Real.sqrt m := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hsm : Real.sqrt m ≤ m := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hh8 : 8 * Cl * N ^ 19 ≤ h0 / 2 := by
      rw [show 8 * Cl * N ^ 19 = 8 * (Cl * N ^ 19) by ring]; linarith
    obtain ⟨g1, g2, g3, -⟩ := arith N m (Real.sqrt m) (h0 / 2) Cl (Formalism.FourierDecayAlt.ThreeDimData.Mexp D.R.rS) (Formalism.FourierDecayAlt.ThreeDimData.AS D.R.k D.R.rS)
      (Formalism.FourierDecayAlt.ThreeDimData.AG D.R.k D.R.rS) hN6 hm2' hmN hs1 hsm hCl hh8 cM cM0 cS cS0 cG cG0
    unfold Formalism.FourierDecayAlt.ThreeDimData.GapOK Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [hsq, eN]
    have hrS1 : 9 * ((D.R.rS : ℝ) + 1) = 9 * (m / 2) := by rw [← eM]; ring
    refine ⟨hk1, g1, g2, ?_⟩
    rw [hrS1]; exact g3
  ·
    have hk1 : 1 ≤ D.R.k := by omega
    obtain ⟨cM, cM0, cS, cS0, cG, cG0⟩ := Formalism.MainNotions.NearParameterGap.consts D.R.k D.R.rS hk1
    have eN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = N := by rw [hNdef, hr]
    have eM : (2 * (D.R.rS : ℝ) + 2) = m := by rw [hmdef, ← hrS]; push_cast; ring
    have eN' : 2 * (D.R.rS : ℝ) + D.R.k + 1 = N := by rw [← eN]; push_cast; ring
    rw [eM] at cM
    rw [eN'] at cS cG
    have hsq : Real.sqrt (2 * ((D.R.rS : ℝ) + 1)) = Real.sqrt m := by rw [← eM]; ring_nf
    have hs1 : (1 : ℝ) ≤ Real.sqrt m := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
    have hsm : Real.sqrt m ≤ m := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hh8 : 8 * Cl * N ^ 19 ≤ h0 / 2 := by
      rw [show 8 * Cl * N ^ 19 = 8 * (Cl * N ^ 19) by ring]; linarith
    obtain ⟨-, -, -, g4⟩ := arith N m (Real.sqrt m) (h0 / 2) Cl (Formalism.FourierDecayAlt.ThreeDimData.Mexp D.R.rS) (Formalism.FourierDecayAlt.ThreeDimData.AS D.R.k D.R.rS)
      (Formalism.FourierDecayAlt.ThreeDimData.AG D.R.k D.R.rS) hN6 hm2' hmN hs1 hsm hCl hh8 cM cM0 cS cS0 cG cG0
    unfold GapCell Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [hsq]
    have hrS1 : 10 * ((D.R.rS : ℝ) + 1) ^ 2 = 10 * (m / 2) ^ 2 := by rw [← eM]; ring
    rw [hrS1]; exact g4

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneThree
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem amplitude_orbital_integral : Formalism.MainNotions.S.Pv.AmpDD.AmpDDOfSteps := by
  intro hSchH hNI hGG _hDD hRS hIn k r L h μG w0 l l' hOP γ μR νR ν hCD b hb hab' hpm v hv v' hv' ξ ξ'
  obtain ⟨hgap, hOK, -, hw0, hμG, hl, hl'⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
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
  obtain ⟨C, hC⟩ := hIn.1 k r hOK.1 L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK.2.1 P hP w0 w0 hw.2 hw.2
  have hh : 0 ≤ h := le_trans (by positivity) hOK.2.1
  have ha : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := div_nonneg hh (by positivity)
  have hD : Formalism.MainNotions.InverseNormDecayBounds.DiagonalMatrixCoefficientPowerDecay L.σ w0 (Formalism.FourierDecayAlt.ThreeDimData.aOf r h) := ⟨C, fun g hg => hC g hg⟩
  have hw0DD : w0 ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp L.σ w0 := by
    have := Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 (Formalism.FourierDecayAlt.P.S3dx6.one_mem_uh (k := k) (r := r))
    rwa [(Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hσ).1, ContinuousLinearMap.one_apply] at this
  obtain ⟨C1, hC1⟩ := Formalism.MainNotions.InverseNormDecayBounds.decDD L.hσ ha hD w0 hw0DD v hv
  obtain ⟨C2, hC2⟩ := Formalism.MainNotions.InverseNormDecayBounds.decDD L.hσ ha hD w0 hw0DD v' hv'
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h := by linarith
  have hIG : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - Formalism.FourierDecayAlt.ThreeDimData.aOf r h)) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core L hμG hd hSch hNI hw1 l l' hl hl' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm hv hv' hC1 hC2 ξ ξ'

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

noncomputable section

namespace Formalism.L2.SG.AmpOrbClosed

open Formalism.BasicNotions Formalism.MainNotions.S



theorem ampDD_thm : Formalism.MainNotions.S.Pv.AmpDD.AmpDD :=
  Formalism.MainNotions.S.Pv.AmpDDPf.amplitude_orbital_integral Formalism.FourierDecayAlt.P.schur_hermitian Formalism.FourierDecayAlt.P.norm_inverse_bound
    Formalism.FourierDecayAlt.P.growth_group_bound Formalism.FourierDecayAlt.P.double_coset_decomposition Formalism.MainNotions.S.Pv.AmpDDPf.right_stabilizer_invariance



end Formalism.L2.SG.AmpOrbClosed
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTParNums
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built

theorem half_lt_int {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : a < b) : a + 1 / 2 ≤ b := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : z < n := by
    have : (z : ℚ) < n := by linarith
    exact_mod_cast this
  have : (z : ℚ) + 1 ≤ n := by exact_mod_cast this
  linarith

theorem int_lt_half {a b : ℚ} (ha : ∃ z : ℤ, a = z + 1 / 2) (hb : ∃ z : ℤ, b = z) (h : b < a) : b + 1 / 2 ≤ a := by
  obtain ⟨z, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have : n ≤ z := by
    have : (n : ℚ) < z + 1 := by linarith
    have : n < z + 1 := by exact_mod_cast this
    omega
  have : (n : ℚ) ≤ z := by exact_mod_cast this
  linarith

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Formalism.L2.SG.LocWSOf.Choice X θ)

end Formalism.L2.SG.Pf.CarrierT
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoefCap
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf

def CoefCapAll : Prop :=
  ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ) (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)))
    (hHC : ∀ w, Formalism.QuantumDeterminants.IsHCParam (X.B.lam w))
    (hgap : ∀ w, ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h),
    CoefCap (carrierInT X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c ν' m₀ Θ TP A₀)

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem coefCap_carrierInT [hF : Fact CoefCapAll] (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (hb : ∀ j, b j ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm (X.B.I.ε (tauE X e j))) (X.B.σ (tauE X e j)))
    (hHC : ∀ w, Formalism.QuantumDeterminants.IsHCParam (X.B.lam w))
    (hgap : ∀ w, ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (X.B.I.ε w) (X.B.lam w) h ∧ Formalism.MainNotions.GapDS.thrX (X.B.I.ε w) < h) :
    CoefCap (carrierInT X C u u' e he hv CA de de' l grid grid1 (fcT X C e u u' a b ξ ξ' cc) c ν' m₀ Θ TP A₀) :=
  hF.out X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀ hb hHC hgap

end Formalism.L2.SG.Pf.CarrierT
end
end
