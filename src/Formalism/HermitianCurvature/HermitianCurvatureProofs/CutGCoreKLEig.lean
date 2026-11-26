module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTKLineCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLEig
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLEigPf

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem alg {ι : Type} [Fintype ι] [DecidableEq ι] (Qs : ι → (Wq →L[ℂ] Wq)) (x : ι → ℂ → ℂ)
    (C : ℂ → (Wq →L[ℂ] Wq)) (E : Wq →L[ℂ] Wp)
    (hQQ : ∀ ρ σ, (Qs ρ).comp (Qs σ) = if ρ = σ then Qs ρ else 0) (hsum : ∑ ρ, Qs ρ = 1)
    (hsep : ∀ ρ σ, ρ ≠ σ → ∃ Y, x ρ Y ≠ x σ Y)
    (hid : ∀ Y, E.comp (∑ σ, x σ Y • Qs σ) = E.comp (C Y)) (ρ : ι) :
    E.comp (Qs ρ) = E ↔ ∀ (Y : ℂ) (v : Wq), E (C Y v) = x ρ Y • E v := by
  have hQv : ∀ ρ σ v, Qs ρ (Qs σ v) = if ρ = σ then Qs ρ v else 0 := by
    intro ρ σ v
    have h := congrArg (fun T : Wq →L[ℂ] Wq => T v) (hQQ ρ σ)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [h]
    split_ifs <;> simp
  have hEC : ∀ Y v, E (C Y v) = ∑ σ, x σ Y • E (Qs σ v) := by
    intro Y v
    have h := congrArg (fun T : Wq →L[ℂ] Wp => T v) (hid Y)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hEv : ∀ v, E v = ∑ σ, E (Qs σ v) := by
    intro v
    have h : (∑ σ, Qs σ) v = v := by rw [hsum, ContinuousLinearMap.one_apply]
    conv_lhs => rw [← h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [ContinuousLinearMap.sum_apply, map_sum]
  constructor
  · intro h Y v
    have hE : ∀ w, E (Qs ρ w) = E w := fun w => congrArg (fun T : Wq →L[ℂ] Wp => T w) h
    have hσ : ∀ σ, E (Qs σ v) = if ρ = σ then E v else 0 := by
      intro σ
      rw [← hE (Qs σ v), hQv]
      split_ifs
      · exact hE v
      · exact map_zero E
    rw [hEC]
    simp [hσ, Finset.sum_ite_eq]
  · intro h
    have h0 : ∀ σ, σ ≠ ρ → ∀ v, E (Qs σ v) = 0 := by
      intro σ hσ v
      obtain ⟨Y, hY⟩ := hsep ρ σ (Ne.symm hσ)
      have h1 := h Y (Qs σ v)
      rw [hEC] at h1
      have h2 : ∑ τ, x τ Y • E (Qs τ (Qs σ v)) = x σ Y • E (Qs σ v) := by
        simp only [hQv]
        rw [Finset.sum_eq_single σ]
        · simp
        · intro τ _ hτ
          simp [hτ]
        · simp
      rw [h2] at h1
      have h3 : (x σ Y - x ρ Y) • E (Qs σ v) = 0 := by rw [sub_smul, h1, sub_self]
      exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hY))
    ext v
    rw [ContinuousLinearMap.comp_apply, hEv v, Finset.sum_eq_single ρ]
    · intro σ _ hσ
      exact h0 σ hσ v
    · simp

end KLEigPf

open KLEigPf in
theorem lie_eigenvalue_holds : KLEig := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hE
  obtain ⟨hpl, hk, hcs, hL, -, -, hQ⟩ := id hH
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set c0 : Fin P.r → ℂ := fun _ => 1 with hc0def
  have hq : ((c0, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨fun _ => one_ne_zero, hζ'⟩
  set φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator (fun _ => E) with hφdef
  have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    refine ⟨?_, ?_, ?_⟩
    · exact contDiffOn_const.congr (fun q hq' => Set.indicator_of_mem hq' _)
    · intro q hq'
      rw [hφdef, Set.indicator_of_mem hq']
      have hst := hcs.2 q.2 ζ hq'.2 hζ'
      intro p hp
      exact hE p (hst ▸ hp)
    · intro q hq'
      exact Set.indicator_of_notMem hq' _
  have hbase : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨by omega, hz, hz', hT, hT', hcs.1, Bs.π_rep, Bs.π'_rep, Bs.π_cont, Bs.π'_cont⟩
  obtain ⟨Φ, hΦ, hΦr⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hbase φ hφ
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  have hval : Φ c0 g = E := by
    have h1 := congrFun hΦr (c0, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq, hφdef] at h1
    exact h1
  have hx : (c0, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' := Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hcs.1 hq
  set Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ⟨Φ, hΦ⟩ with hΦ'def
  let qq : MA.Qp P.r P.TT := ⟨(c0, ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩
  have hx1 : ∀ Y : ℂ, (d.x Y).1 = X.fn 5 * X.t Y 1 1 := by
    intro Y
    have h : d.x Y = d.L.GGi * X.QQ Y 1 1 := by
      rw [hQ]
      simp only [Q.NFData.QQ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_zero]
      rw [← mul_assoc, d.L.GGi_GG, one_mul]
    show Formalism.FourierDecayAlt.P5.Kfp.fstAlg _ (d.x Y) = _
    rw [h, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    rfl
  let C : ℂ → (Wq →L[ℂ] Wq) := fun Y =>
    LinearMap.toContinuousLinearMap (qdet (Qr.EB Bs.π' Fr) (Y + ((P.k : ℂ) - 2) / 2))
  have hid : ∀ Y, E.comp (∑ σ, M.xC P σ Y • Qρ σ) = E.comp (C Y) := by
    intro Y
    ext v
    have hk1 := hK.2.2.2 (fun σ => M.xC P σ Y) Φ' qq
    have hk2 := congrArg (fun L : Wq →L[ℂ] Wp => L v) hk1
    have hact := Formalism.FourierDecayAlt.P5.Kfp.diagonal_transfer_action X hz hz' Bs.π'_rep Bs.π'_cont hx Fr hFr Y Φ' v
    have hκx : (d.κ fun σ => M.xC P σ Y) = d.x Y := rfl
    rw [hκx, hx1 Y] at hk2
    change (((X.fn 5 * X.t Y 1 1) Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 g v =
      (Φ c0 g) ((∑ σ, M.xC P σ Y • Qρ σ) v) at hk2
    rw [hact, hval] at hk2
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hk2]
    show (Φ c0 g) _ = _
    rw [hval]
    rfl
  obtain ⟨Y₀, hY₀⟩ := Formalism.FourierDecayAlt.P5.Kfp.sep_real hOK
  have hsep : ∀ ρ σ : M.Ty P, ρ ≠ σ → ∃ Y, M.xC P ρ Y ≠ M.xC P σ Y :=
    fun ρ σ h => ⟨(Y₀ : ℂ), fun he => h (hY₀ he)⟩
  classical
  exact alg Qρ (fun σ Y => M.xC P σ Y) C E hK.1 hK.2.1 hsep hid ρ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNonvanishingFromL2
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

set_option maxHeartbeats 1600000

namespace Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

open Formalism.FourierDecayAlt.ThreeDimData

theorem bessel_nonvanishing_from_L2 : Formalism.FourierDecayAlt.ThreeDimData.More.BesselNonvanishingReduction := by
  classical
  intro hSch hNI hGS hGG hDD hBC hInp _ k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS W hWc hWeq
    hRe hpos hfin
  by_contra hcon
  push_neg at hcon
  obtain ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩ := hS
  have hS' : Side k r ε lam h σ w0 z c u π μW μN μG νq :=
    ⟨hlam, hσ, hgap, hGapOK, hw0, hz, hT, hc, hπ, hWh, hNh, hGh, hq⟩
  have := hWh.1; have := hNh.1; have := hGh.1
  have hsm := DDSmoothness.DD_smooth hInp.2.2.1 hlam hσ hw0
  have memDD : ∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ g w0 ∈ DDsp σ w0 :=
    fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hof : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) := continuous_id
  have hGae : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := ae_iff.mpr hGh.2.2.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hWh.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hNh.2.2.1
  have hPae : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)
  obtain ⟨hS0, hSc⟩ := DDSmoothness.muSof_facts hWh hNh
  have hνae := DDSmoothness.ae_UH_of_quot hGh.2.2.1 hS0 hSc hq
  have hBC' := hBC hInp k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS'
  have hcs := Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hσ w0

  have hW0 : ∀ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x0 = 0 := by
    intro x0 hx0
    obtain ⟨hI, hR⟩ := hRe x0 hx0
    rw [← hR]
    unfold PI.BesselPeriodGGP.rconv
    apply ext_inner_left ℂ
    intro η
    rw [inner_zero_right, ← integral_inner hI η]
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
      simp only [Function.comp, Φ', Set.piecewise, hmem, if_true, Φ]
      show _ = ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (x0⁻¹ * (x0 * Matrix.of g)) • W (x0 * Matrix.of g)⟫_ℂ
      rw [← Matrix.mul_assoc, hxx', Matrix.one_mul]
    have hmapEq : μG.map (Formalism.QuantumDeterminants.lmulM x0) = μG := hGh.2.2.2 x0 hx0
    have hΦint : Integrable Φ' μG := by
      have h1 : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
          ⟪η, PI.BesselPeriodGGP.eFun μG σ w0 (Matrix.of g) • W (x0 * Matrix.of g)⟫_ℂ) μG :=
        (innerSL ℂ η).integrable_comp hI
      have h2 : Integrable (Φ' ∘ Formalism.QuantumDeterminants.lmulM x0) μG := h1.congr htrans
      rw [← integrable_map_measure hΦm.aestronglyMeasurable hlm.aemeasurable, hmapEq] at h2
      exact h2
    rw [integral_congr_ae htrans]
    show ∫ a, Φ' (Formalism.QuantumDeterminants.lmulM x0 a) ∂μG = 0
    rw [← integral_map hlm.aemeasurable hΦm.aestronglyMeasurable, hmapEq]
    have : SFinite (muSof μW μN) := by unfold muSof; infer_instance
    refine quot_zero hq Φ' hΦm hΦint ?_
    filter_upwards [hνae] with x hx
    have hpm : Measurable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
      have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
      have h3 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
          (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := h1.matrix_mul h2
      exact h3.measurable
    have hFm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => Φ' (mulMt s x)) :=
      hΦm.comp (measurable_mulMt.comp (measurable_id.prodMk measurable_const))
    unfold muSof
    rw [integral_map hpm.aemeasurable hFm.aestronglyMeasurable]
    set u' := σ (Matrix.of x) w0 with hu'
    set v' := σ x0 w0 with hv'
    have hu'DD : u' ∈ DDsp σ w0 := memDD _ hx
    have hv'DD : v' ∈ DDsp σ w0 := memDD _ hx0
    have hI2 : Integrable (beInt z c π σ u' v') (μW.prod μN) := hBC'.1 u' (hsm _ hu'DD) v' (Or.inl hv'DD)
    have hval : ∀ᵐ p ∂(μW.prod μN), Φ' (mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x) =
        ((PI.BesselPeriodGGP.fdegH μG σ w0 : ℝ) : ℂ) * ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ := by
      filter_upwards [hPae] with p hp
      have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
      have hsx : Matrix.of p.1 * Matrix.of p.2 * Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
        DDSmoothness.uh_mul hs hx
      have hmem : mulMt (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) x ∈ U := hsx
      simp only [Φ', Set.piecewise, hmem, if_true, Φ]
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
      rw [eA, inner_smul_right, inner_smul_right, piW_inner hT hπ hp.1, ContinuousLinearMap.smul_apply,
        inner_smul_left]
      simp only [map_mul, Complex.star_def, Complex.conj_conj]
      ring
    rw [integral_congr_ae hval, integral_const_mul]
    have hf : Integrable (fun p => beInt z c π σ u' v' p η) (μW.prod μN) :=
      (ContinuousLinearMap.apply ℂ Wp η).integrable_comp hI2
    have hinner : ∫ p, ⟪beInt z c π σ u' v' p η, W (Matrix.of x)⟫_ℂ ∂(μW.prod μN) =
        ⟪be z c π σ μW μN u' v' η, W (Matrix.of x)⟫_ℂ := by
      have e2 : be z c π σ μW μN u' v' η = ∫ p, beInt z c π σ u' v' p η ∂(μW.prod μN) :=
        ContinuousLinearMap.integral_apply hI2 η
      rw [e2, ← inner_conj_symm, ← integral_inner hf (W (Matrix.of x)), ← integral_conj]
      congr 1
      funext p
      rw [inner_conj_symm]
    rw [hinner, hcon u' hu'DD v' hv'DD]
    simp

  have hl0 : PI.BesselPeriodGGP.l2SG νq W = 0 := by
    unfold PI.BesselPeriodGGP.l2SG
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hνae] with x hx
    rw [hW0 _ hx]; simp
  rw [hl0] at hpos
  exact lt_irrefl _ hpos

theorem bessel_nonzero_l2_reduction : Formalism.FourierDecayAlt.ThreeDimData.More.BesselNonvanishingReduction := bessel_nonvanishing_from_L2

end Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoCut
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut

open Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

section K

variable {Wp : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]

def Kset (k r : ℕ) (z b : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) : Set Wp :=
  {x | ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, b] Fr → ∀ w : ℂ, capRep k r π Fr w x = f w • x}

def K (k r : ℕ) (z b : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (f : ℂ → ℂ) : Submodule ℂ Wp :=
  Submodule.span ℂ (Kset k r z b π f)

end K

def FrameLoc : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), 2 ≤ k → inWb k r z → 0 < Tz k r z →
    ∀ a₀ : Fin (2 * r + k + 1) → ℂ, 0 < PRho.nrmW k r z a₀ →
      ∃ Fr : (Fin (2 * r + k + 1) → ℂ) → Fin (k - 1) → Fin (2 * r + k + 1) → ℂ,
        ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fr a₀ ∧ ∀ᶠ a in 𝓝 a₀, IsFrameOf k r [z, SSn.prWv k r z a] (Fr a)

def CapSmooth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r m : ℕ)
    (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)), Qr.IsRepW k r z π → ∀ w : ℂ,
    ∃ C : (Fin m → Fin (2 * r + k + 1) → ℂ) → (Wp →L[ℂ] Wp), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) C ∧
      ∀ Bs, IsFrameOf k r [z] Bs → ∀ v, C Bs v = capRep k r π Bs w v

def EigOrth : Prop :=
  ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (k r : ℕ)
    (z e : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → Qr.IsRepW k r z π →
    (∀ h ∈ UWset k r z, ∀ v, ‖π h v‖ = ‖v‖) →
    (∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [z, e] Fr) →
    ∀ (f g : ℂ → ℂ) (x y : Wp), x ∈ Kset k r z e π f → y ∈ Kset k r z e π g → (∃ w, f w ≠ g w) → inner ℂ x y = 0

def Lagrange : Prop :=
  EigOrth → ∀ (P : M.Par), P.OK → 2 ≤ P.k → ∃ (w : ℂ) (p : M.Ty P → Polynomial ℂ),
    ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      (z e : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp)),
      inWb P.k P.r z → 0 < Tz P.k P.r z → IsType P.k P.r z π P.u →
      inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 → herm (Hpk P.k P.r) e e = 1 →
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, IsFrameOf P.k P.r [z, e] Fr →
      ∀ C : Wp →L[ℂ] Wp, (∀ v, C v = capRep P.k P.r π Fr w v) →
      ∀ ρ : M.Ty P, Polynomial.aeval C (p ρ) =
        (K P.k P.r z e π (fun w' => M.xC P ρ (w' - ((P.k : ℂ) - 2) / 2))).starProjection

def Assembly : Prop := FrameLoc → CapSmooth → EigOrth → Lagrange → PRho.PRhoExists

theorem pRhoExists_of_cut (hA : Assembly) (hF : FrameLoc) (hC : CapSmooth) (hO : EigOrth) (hL : Lagrange) :
    PRho.PRhoExists :=
  hA hF hC hO hL

end Formalism.FourierDecayAlt.P.CutMP.JA.PRhoCut
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorEquivariance
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

open TLC in
theorem capelli_vector_equivariance : TL.CapVEquiv := by
  intro Wq _ _ _ k r z' π' B0 ν ν' h hk hz hT hπ hB0 hν hh hνν' w
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  set g := h⁻¹ with hgdef
  have hg : g ∈ UWset (n + 1) r z' := LieBracketMultiplication.uw_inv hh
  have hgU : g ∈ UH (Hpk (n + 1) r) := hg.1
  have hgL : g ∈ Glev (n + 1) r (Fin.last r) := Qx8.uw_glev _ hg
  have hν' : C6.sq2 ν' = 1 := by
    have h1 : herm (Hpk (n + 1) r) (∑ j, ν' j • B0 j) (∑ j, ν' j • B0 j) = 1 := by
      rw [hνν', Qx2.herm_uh hgU, hee]
    rw [HermitianFormSums.herm_comb hB0] at h1
    have : ∀ a, ν' a * star (ν' a) = ((Complex.normSq (ν' a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν' a)
    simp only [this] at h1
    rw [← Complex.ofReal_sum] at h1
    exact_mod_cast h1
  obtain ⟨Bs, hBs⟩ := exists_frame_two n r z' e hz hT he hez hee
  set Bs' : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ := fun a => g *ᵥ Bs a with hBs'def
  have hBs' : IsFrameOf (n + 1) r [z', ∑ j, ν' j • B0 j] Bs' := by
    refine ⟨fun a => Qx8.inWb_mulVec hgL (hBs.1 a), fun a b => ?_, fun a v hv => ?_⟩
    · rw [hBs'def, Qx2.herm_uh hgU]; exact hBs.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · have e1 := Qx2.herm_uh hgU (Bs a) v
        rw [hg.2.2] at e1
        rw [e1]; exact hBs.2.2 a _ (by simp)
      · rw [hνν', Qx2.herm_uh hgU]; exact hBs.2.2 a _ (by simp)
  have hF := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs ν (by omega) hz hT hπ hB0 hν hBs w
  have hF' := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs' ν' (by omega) hz hT hπ hB0 hν' hBs' w
  have hBs1 := HermitianFormSums.frame_sub hBs
  have hBs1' := HermitianFormSums.frame_sub hBs'
  have hq := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w
  have hq' := (frame_general_linear Wq (n + 1) r n z' π' Bs' hπ hBs1').2 w
  have hgi : g⁻¹ = h := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1)
  have hgh : g * h = 1 := LeftDerivativeCurves.uh_inv_mul hh.1
  have hhg : h * g = 1 := LeftDerivativeCurves.uh_mul_inv hh.1
  have hUUi : (π' g).comp (π' h) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hg _ hh, hgh, hπ.1.1]; rfl
  have hUiU : (π' h).comp (π' g) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hh _ hg, hhg, hπ.1.1]; rfl
  set U : Module.End ℂ Wq := (π' g : Wq →ₗ[ℂ] Wq) with hU
  set Ui : Module.End ℂ Wq := (π' h : Wq →ₗ[ℂ] Wq) with hUi
  have hUUi' : U * Ui = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUUi
    simpa [hU, hUi] using this
  have hUiU' : Ui * U = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hU, hUi] using this
  have hEB : ∀ a b, U * EB π' Bs a b * Ui = EB π' Bs' a b := by
    intro a b
    obtain ⟨hX1, hX2⟩ := QrD.frame_lie hBs1 a b
    obtain ⟨-, -, e1⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX1 g hg
    obtain ⟨-, -, e2⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX2 g hg
    obtain ⟨c1, c2⟩ := Qx8.hpart_conj Bs a b hgU
    unfold EB QrD.ecOp
    rw [c1, c2, e1, e2, hgi]
    apply LinearMap.ext; intro v
    simp [hU, hUi]
  let f : Module.End ℂ Wq →+* Module.End ℂ Wq :=
    { toFun := fun T => U * T * Ui
      map_one' := by simp only [mul_one, hUUi']
      map_mul' := fun S T => by
        show U * (S * T) * Ui = U * S * Ui * (U * T * Ui)
        calc U * (S * T) * Ui = U * S * (Ui * U) * T * Ui := by rw [hUiU']; noncomm_ring
          _ = U * S * Ui * (U * T * Ui) := by noncomm_ring
      map_zero' := by simp only [mul_zero, zero_mul]
      map_add' := fun S T => by noncomm_ring }
  have hf : ∀ v, f (algebraMap ℂ (Module.End ℂ Wq) v) = algebraMap ℂ (Module.End ℂ Wq) v := by
    intro v
    show U * algebraMap ℂ (Module.End ℂ Wq) v * Ui = _
    rw [← Algebra.commutes, mul_assoc, hUUi', mul_one]
  have hqd := QuantumMinorExpansion.map_qminor (EB π' Bs') f hf (EB π' Bs) (fun a b => hEB a b) id id w
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [hF', hF, hq', hq]
  unfold qdet
  rw [← hqd]
  show U (qminor (EB π' Bs) id id w (Ui (π' h⁻¹ v))) = π' h⁻¹ (qminor (EB π' Bs) id id w v)
  have : Ui (π' h⁻¹ v) = v := by
    rw [← hgdef]
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hUi] using this
  rw [this]
  rfl

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NotCdomRaiseOfLt
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace QrCap

theorem not_cdom_raise_of_lt {k : ℕ} {Λ : Fin k → ℝ} {a b : Fin k} (hab : a < b)
    (h : PI.UpqRep.CDom (PI.UpqRep.allPos k)
      (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) Λ) : False := by
  obtain ⟨c, hc, heq⟩ := h
  have hsing : ∀ p : Fin k, ∑ j : Fin k, ((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j = ((p : ℕ) : ℝ) := by
    intro p
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have e1 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (Λ - fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) j =
      ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by
    have hj : ∀ j : Fin k,
        (Λ - fun c => Λ c + (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) j =
          (Pi.single b (1 : ℝ) : Fin k → ℝ) j - (Pi.single a (1 : ℝ) : Fin k → ℝ) j := by
      intro j
      simp only [Pi.sub_apply, Pi.single_apply]
      ring
    simp only [hj, mul_sub, Finset.sum_sub_distrib, hsing]
  have e2 : ∑ j : Fin k, ((j : ℕ) : ℝ) *
      (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j ≤ 0 := by
    have hj : ∀ j : Fin k, ((j : ℕ) : ℝ) * (∑ p, ∑ q, (c p q : ℝ) • PI.UpqRep.root p q) j =
        ∑ p, ∑ q, (c p q : ℝ) * (((j : ℕ) : ℝ) * (Pi.single p (1 : ℝ) : Fin k → ℝ) j -
          ((j : ℕ) : ℝ) * (Pi.single q (1 : ℝ) : Fin k → ℝ) j) := by
      intro j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PI.UpqRep.root, Pi.sub_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      ring
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_comm]
    apply Finset.sum_nonpos
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_nonpos
    intro q _
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsing, hsing]
    by_cases h0 : c p q = 0
    · simp [h0]
    · have hpq : ((p : ℕ) : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast (hc p q h0).1
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hab' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  rw [heq] at e1
  linarith

theorem core {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} {g : Mx k r} {u : Fin k → ℝ}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hR : IsRepW k r z π) (hgU : g ∈ UH (Hpk k r))
    (hgfix : ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a))
    (s : ℂ) (hgz : g *ᵥ (s • bvec (wI k r (Fin.last k))) = z)
    (hK : PI.UpqRep.IsKTypeOf (PI.UpqRep.allPos k) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
      (PI.UpqRep.lowK (PI.UpqRep.allPos k) u) ⊤) (w : ℂ) (v : W) :
    qdet (EB π (fr k r g)) w v =
      cpol (fun j : Fin k => ((PI.UpqRep.lowK (PI.UpqRep.allPos k) u j : ℝ) : ℂ) - ((j : ℕ) : ℂ)) w • v := by
  set Bs := fr k r g with hBs
  have hB : IsFrameOf k r [z] Bs := fr_frame hgU hgfix s hgz
  set Λ := PI.UpqRep.lowK (PI.UpqRep.allPos k) u with hΛ
  set E := EB π Bs with hE
  have hgl : GlRel E := (frame_general_linear W k r k z π Bs hR hB).1
  set Ec : Fin k → (W →L[ℂ] W) := fun c => ecOp π (unitB (Hpk k r) Bs c c) with hEc
  have hEE : ∀ c x, E c c x = Ec c x := fun c x => rfl
  have hσ : ∀ θ : Fin k → ℝ, π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) =
      NormedSpace.exp (∑ c, ((θ c : ℂ) * Complex.I) • Ec c) := by
    intro θ
    rw [← torus hgU θ]
    exact op_torus hR hB θ
  obtain ⟨-, -, hirr, ⟨v₀, -, hv0, hwt⟩, hdom⟩ := hK

  have hdiag : ∀ c, E c c v₀ = (Λ c : ℂ) • v₀ := by
    intro c
    set A := hpart2 (Hpk k r) (unitB (Hpk k r) Bs c c) with hAdef
    have hA : InLieW k r z A := (QrD.frame_lie hB c c).2
    have hAe : A = (-Complex.I) • unitB (Hpk k r) Bs c c := hpart2_self Bs c
    have hf : (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • A)) v₀) =
        fun t : ℝ => Complex.exp (((-t * Λ c : ℝ) : ℂ) * Complex.I) • v₀ := by
      funext t
      set θ : Fin k → ℝ := fun c' => if c' = c then -t else 0 with hθ
      have h1 : (t : ℂ) • A = ∑ c', ((θ c' : ℂ) * Complex.I) • unitB (Hpk k r) Bs c' c' := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        rw [hAe, smul_smul]
        congr 1
        simp only [hθ, if_pos rfl]
        push_cast
        ring
      have hsθ : ∑ a, Λ a * θ a = -t * Λ c := by
        rw [Finset.sum_eq_single c (fun b _ hb => by simp [hθ, hb]) (fun h => absurd (Finset.mem_univ c) h)]
        simp only [hθ, if_pos rfl]
        ring
      rw [h1, torus hgU θ]
      refine (hwt θ (Dg_mem θ)).trans ?_
      rw [hsθ]
    have hd : dOp π A v₀ = (-(Λ c : ℂ) * Complex.I) • v₀ := by
      rw [← QrD.dRep_eq hR.1 hR.2 hA v₀]
      unfold dRep
      rw [hf]
      exact (deriv_cexp (Λ c) v₀).deriv
    rw [hEE]
    show ecOp π (unitB (Hpk k r) Bs c c) v₀ = _
    unfold ecOp
    rw [hpart1_self, SkewHermitianParts.dOp_zero, zero_add, _root_.smul_apply, hd, smul_smul]
    congr 1
    linear_combination (-(Λ c : ℂ)) * Complex.I_sq

  have hup : ∀ a b, a < b → E a b v₀ = 0 := by
    intro a b hab
    by_contra hne
    set x := E a b v₀ with hx
    have hxw : ∀ c, Ec c x = (((fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) c : ℝ) : ℂ) • x := by
      intro c
      rw [← hEE, hx, CommonEigenvectors.diag_move hgl c a b v₀, hdiag c, map_smul]
      by_cases hca : c = a <;> by_cases hcb : c = b
      · exact absurd (hca.symm.trans hcb) hab.ne
      · rw [if_pos hca, if_neg (fun h => hcb h.symm)]
        simp only [if_pos hca, if_neg hcb]
        push_cast
        module
      · rw [if_neg hca, if_pos hcb.symm]
        simp only [if_neg hca, if_pos hcb]
        push_cast
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm)]
        simp only [if_neg hca, if_neg hcb]
        push_cast
        module
    have hwx : PI.UpqRep.IsWtOn (PI.UpqRep.Kset (PI.UpqRep.allPos k)) (fun h => π (g * PI.UpqRep.blockW k r h * g⁻¹))
        (fun c => Λ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) x := by
      intro θ _
      show π (g * PI.UpqRep.blockW k r (Dg θ) * g⁻¹) x = _
      rw [hσ θ]
      exact exp_sum_eig Ec θ _ x hxw
    exact not_cdom_raise_of_lt hab (hdom _ x Submodule.mem_top hne hwx)

  have hHW : IsHW E (fun j => (Λ j : ℂ)) v₀ := ⟨hdiag, hup⟩
  set m : Fin k → ℂ := fun j => (Λ j : ℂ) - ((j : ℕ) : ℂ) with hm
  have hq0 : ∀ w', qdet E w' v₀ = cpol m w' • v₀ := by
    intro w'
    rw [quantumDetHighestWeight_holds W k E _ v₀ hgl hHW w']
    congr 1
    unfold cpol
    apply Finset.prod_congr rfl
    intro j _
    simp only [hm]
    ring
  have hmem : v₀ ∈ CapSp E m := mem_CapSp.2 hq0
  have hstab : Stab E (CapSp E m) := (capelli_stabilizer W k E m hgl).1
  have hirrE : ∀ S : Submodule ℂ W, Stab E S → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hU := lie_stabilizer W k r z π Bs hz hT hR hB S hS
    refine hirr S le_top ?_
    intro h hh y hy
    have hu : hᴴ * h = 1 := by
      have := Matrix.mem_unitaryGroup_iff'.1 hh.1
      rwa [Matrix.star_eq_conjTranspose] at this
    exact hU _ (emb_uw hgU hgfix s hgz hu) y hy
  have htop : CapSp E m = ⊤ := by
    rcases hirrE _ hstab with h | h
    · exfalso
      rw [h] at hmem
      exact hv0 ((Submodule.mem_bot ℂ).1 hmem)
    · exact h
  have hv : v ∈ CapSp E m := by
    rw [htop]
    exact Submodule.mem_top
  exact mem_CapSp.1 hv w

end QrCap

end Formalism.FourierDecayAlt.P
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqWigMapsValueECas
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.WigCas

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cas_comm {A : Type*} [Ring A] {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) (c d : Fin n) :
    Cas E * E c d = E c d * Cas E := by
  have expand : Cas E * E c d - E c d * Cas E = ∑ a, ∑ b, (E a b * ((if a = c then E b d else 0) -
      (if d = b then E c a else 0)) + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a) := by
    simp only [Cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [← hE b a c d, ← hE a b c d]
    noncomm_ring
  have hT1 : ∑ a, ∑ b, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have hT4 : ∑ a, ∑ b, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have hT2 : ∑ a, ∑ b, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    simp [mul_ite]
  have hT3 : ∑ a, ∑ b, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    simp [ite_mul]
  rw [← sub_eq_zero, expand]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hT1, hT2, hT3, hT4]
  abel

end Formalism.FourierDecayAlt.P.WigCas

end
end
