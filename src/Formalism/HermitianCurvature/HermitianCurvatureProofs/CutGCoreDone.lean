module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRMove
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopAct
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnReal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTSS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddDone

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnFinal
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

def GTConnOfLeaves : Prop := GTCLocal → GTCReal → GTCCurv → GTCHol → GTCAnnulus → GTConn

theorem gTConn_of_leaves : GTConnOfLeaves := fun hL hR hC hH hA =>
  gTConn_of_cut hL (gTCPhase_of_cut hR hC hH hA torus_parameter) gauge_transform_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefAn
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem reference_annulus_holds : GTCRefAn := by
  intro TT α c hTT hα hre R hR hR2
  have hpt : ∀ θ : ℝ, TT < Complex.normSq (circleMap 0 R θ) := by
    intro θ
    have h1 : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    rw [Complex.normSq_eq_norm_sq, h1]
    exact hR2
  have hcα : Continuous (fun θ : ℝ => α (circleMap 0 R θ)) :=
    hα.continuousOn.comp_continuous (continuous_circleMap 0 R) hpt
  have hd : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
    funext θ
    exact deriv_circleMap 0 R θ
  have hF : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) := by
    have h2 : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ) := by
      rw [hd]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact h2.smul hcα
  have key : ∀ θ : ℝ, Complex.imCLM (deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) = c := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, Complex.imCLM_apply]
    rw [← hre (circleMap 0 R θ) (hpt θ)]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  unfold circleIntegral
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hF.intervalIntegrable _ _)]
  simp only [key]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnAnn
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtBrReal
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NeZeroOfAn
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThShiftInt
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ImCircleIntegral
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThetaAtBasePointZero
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemHalfPlane
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.FderivDecomp
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtPrim
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasDerivAtTMul
open Set Filter Topology MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def prim (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) : ℝ := ∫ t in (0 : ℝ)..1, ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Set Filter Topology MeasureTheory intervalIntegral Metric

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def seg (w₀ x : ℂ) (t : ℝ) : ℂ := w₀ + (t : ℂ) * (x - w₀)

theorem seg_mem (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) {x : ℂ} (hx : x ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    seg w₀ x t ∈ S := by
  have h := hc.add_smul_sub_mem hw₀ hx ht
  simpa [seg, Complex.real_smul] using h

theorem seg_one (w₀ x : ℂ) : seg w₀ x 1 = x := by
  simp [seg]

theorem continuous_seg : Continuous fun p : ℂ × ℝ => seg w₀ p.1 p.2 := by
  unfold seg
  fun_prop

theorem hasDerivAt_seg (x : ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => seg w₀ x s) (x - w₀) t := by
  have h := ((hasDerivAt_id t).ofReal_comp.mul_const (x - w₀)).const_add w₀
  simpa [seg] using h

theorem hasFDerivAt_seg (x : ℂ) (t : ℝ) :
    HasFDerivAt (fun y : ℂ => seg w₀ y t) ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ) x := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const w₀).const_smul (t : ℂ)
  have h2 := h.const_add w₀
  have hf : (fun y : ℂ => seg w₀ y t) = fun y => w₀ + ((t : ℂ) • fun x => id x - w₀) y := by
    funext y
    simp [seg, smul_eq_mul]
  rw [hf]
  exact h2

theorem prim_eq (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) :
    prim ω w₀ w = ∫ t in (0 : ℝ)..1, ω (seg w₀ w t) (w - w₀) := rfl

theorem hasFDerivAt_prim (hS : IsOpen S) (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) (hω : ContDiffOn ℝ 1 ω S)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} (hw : w ∈ S) :
    HasFDerivAt (prim ω w₀) (ω w) w := by
  have hdiff : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p := fun p hp =>
    (((hω.differentiableOn one_ne_zero) p hp).differentiableAt (hS.mem_nhds hp)).hasFDerivAt
  have hcontω : ContinuousOn ω S := hω.continuousOn
  have hcontD : ContinuousOn (fderiv ℝ ω) S := hω.continuousOn_fderiv_of_isOpen hS le_rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS w hw
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hcb : closedBall w δ' ⊆ S := (closedBall_subset_ball (by linarith)).trans hball
  set K := (fun p : ℂ × ℝ => seg w₀ p.1 p.2) '' (closedBall w δ' ×ˢ Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := ((isCompact_closedBall w δ').prod isCompact_Icc).image continuous_seg
  have hKS : K ⊆ S := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact seg_mem hc hw₀ (hcb hx) ht
  have hmemK : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1, seg w₀ x t ∈ K := fun x hx t ht =>
    ⟨(x, t), ⟨hx, ht⟩, rfl⟩
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (hcontω.mono hKS)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (hcontD.mono hKS)
  set F' : ℂ → ℝ → (ℂ →L[ℝ] ℝ) := fun x t => ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)
    with hF'
  have hFd : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun y => ω (seg w₀ y t) (y - w₀)) (F' x t) x := by
    intro x hx t ht
    have hs := hmemK x hx t ht
    have hc1 : HasFDerivAt (fun y => ω (seg w₀ y t)) ((fderiv ℝ ω (seg w₀ x t)).comp ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ)) x :=
      (hdiff _ (hKS hs)).comp x (hasFDerivAt_seg x t)
    have hu : HasFDerivAt (fun y : ℂ => y - w₀) (ContinuousLinearMap.id ℝ ℂ) x := (hasFDerivAt_id x).sub_const w₀
    have h := hc1.clm_apply hu
    refine h.congr_fderiv ?_
    ext h'
    simp only [hF', ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply]
    rw [show ((t : ℂ) • h' : ℂ) = (t : ℝ) • h' from by rw [Complex.real_smul]; rfl, map_smul]
    simp
  have hseg_cont : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => seg w₀ x t) (Icc 0 1) := fun x _ =>
    (continuous_seg.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
  have hωseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontω.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hDseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => fderiv ℝ ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontD.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hF'cont : ∀ x ∈ closedBall w δ', ContinuousOn (F' x) (Icc 0 1) := by
    intro x hx
    refine (hωseg x hx).add (ContinuousOn.smul continuousOn_id ?_)
    exact ((ContinuousLinearMap.flipₗᵢ ℝ ℂ ℂ ℝ).continuous.comp_continuousOn (hDseg x hx)).clm_apply continuousOn_const
  have hIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hwc : w ∈ closedBall w δ' := mem_closedBall_self hδ'0.le
  have hLeib := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun y t => ω (seg w₀ y t) (y - w₀)) (F' := F') (x₀ := w) (a := 0) (b := 1)
    (bound := fun _ => M₁ + M₂ * (δ' + ‖w - w₀‖)) (s := ball w δ') (ball_mem_nhds w hδ'0) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · have hint : ∫ t in (0 : ℝ)..1, F' w t = ω w := by
      have hEq : EqOn (F' w) (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        simp only [hF']
        congr 2
        ext h'
        simp only [ContinuousLinearMap.flip_apply]
        exact hsym _ hs h' (w - w₀)
      rw [intervalIntegral.integral_congr hEq]
      have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s • ω (seg w₀ w s))
          (ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) t := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        have h1 := (hdiff _ hs).comp_hasDerivAt t (hasDerivAt_seg (w₀ := w₀) w t)
        have h2 := (hasDerivAt_id t).smul h1
        refine h2.congr_deriv ?_
        simp only [id, one_smul]
        abel
      have hcd : ContinuousOn (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        exact (hωseg w hwc).add (continuousOn_id.smul ((hDseg w hwc).clm_apply continuousOn_const))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcd.intervalIntegrable)]
      simp [seg_one]
    rw [← hint]
    exact hLeib
  · filter_upwards [ball_mem_nhds w hδ'0] with x hx
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    rw [hIoc]
    exact (((hωseg x hxc).clm_apply continuousOn_const).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hωseg w hwc).clm_apply continuousOn_const
  · rw [hIoc]
    exact ((hF'cont w hwc).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    have hs := hmemK x hxc t ht'
    have h1 : ‖ω (seg w₀ x t)‖ ≤ M₁ := hM₁ _ hs
    have h2 : ‖fderiv ℝ ω (seg w₀ x t)‖ ≤ M₂ := hM₂ _ hs
    have h3 : ‖x - w₀‖ ≤ δ' + ‖w - w₀‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x w w₀
      have hxw : ‖x - w‖ ≤ δ' := by rw [← dist_eq_norm]; exact mem_closedBall.mp hxc
      linarith
    have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) h2
    simp only [hF']
    calc ‖ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖
        ≤ ‖ω (seg w₀ x t)‖ + ‖t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ := norm_add_le _ _
      _ ≤ M₁ + M₂ * (δ' + ‖w - w₀‖) := by
        refine add_le_add h1 ?_
        rw [norm_smul]
        have hf : ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ M₂ * (δ' + ‖w - w₀‖) := by
          refine ((fderiv ℝ ω (seg w₀ x t)).flip.le_opNorm (x - w₀)).trans ?_
          rw [ContinuousLinearMap.opNorm_flip]
          exact mul_le_mul h2 h3 (norm_nonneg _) hM₂0
        have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2
        calc ‖t‖ * ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ 1 * (M₂ * (δ' + ‖w - w₀‖)) :=
              mul_le_mul ht1 hf (norm_nonneg _) zero_le_one
          _ = M₂ * (δ' + ‖w - w₀‖) := one_mul _
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    exact hFd x (ball_subset_closedBall hx) t (Ioc_subset_Icc_self ht)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

def wZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - I * fderiv ℝ f ζ I)

def wZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + I * fderiv ℝ f ζ I)

def Hh (TT : ℝ) : Set ℂ := {w | TT < Complex.normSq (Complex.exp w)}

theorem normSq_exp (w : ℂ) : Complex.normSq (Complex.exp w) = Real.exp w.re ^ 2 := by

  first
    | rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    | simp [Complex.normSq_eq_norm_sq, Complex.norm_exp]

theorem isOpen_Hh (TT : ℝ) : IsOpen (Hh TT) := isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)

theorem convex_Hh (TT : ℝ) : Convex ℝ (Hh TT) := by

  intro w1 h1 w2 h2 a b ha hb hab
  simp only [Hh, Set.mem_setOf_eq, normSq_exp] at h1 h2 ⊢
  have hre : (a • w1 + b • w2).re = a * w1.re + b * w2.re := by simp
  rw [hre]
  rcases le_total w1.re w2.re with h | h
  · calc TT < Real.exp w1.re ^ 2 := h1
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w1.re = b * (w2.re - w1.re) := by
          rw [show a = 1 - b by linarith]; ring
        have : w1.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg hb (sub_nonneg.2 h)]
        gcongr
  · calc TT < Real.exp w2.re ^ 2 := h2
      _ ≤ Real.exp (a * w1.re + b * w2.re) ^ 2 := by
        have e : a * w1.re + b * w2.re - w2.re = a * (w1.re - w2.re) := by
          rw [show b = 1 - a by linarith]; ring
        have : w2.re ≤ a * w1.re + b * w2.re := by nlinarith [mul_nonneg ha (sub_nonneg.2 h)]
        gcongr

def bet (α : ℂ → ℂ) (w : ℂ) : ℂ := α (Complex.exp w) * Complex.exp w

def omL : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (2 : ℝ) • (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ Complex.imCLM).comp (ContinuousLinearMap.mul ℝ ℂ)

theorem omL_apply (c v : ℂ) : omL c v = 2 * (c * v).im := by

  simp [omL]

def om (α : ℂ → ℂ) (w : ℂ) : ℂ →L[ℝ] ℝ := omL (bet α w)

theorem om_apply (α : ℂ → ℂ) (w v : ℂ) : om α w v = 2 * (bet α w * v).im := omL_apply _ _

theorem bet_periodic (α : ℂ → ℂ) (w : ℂ) (k : ℤ) : bet α (w + (k : ℂ) * (2 * Real.pi * I)) = bet α w := by

  simp only [bet, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def An (TT : ℝ) : Set ℂ := {ζ | TT < Complex.normSq ζ}

theorem isOpen_An (TT : ℝ) : IsOpen (An TT) :=
  isOpen_lt continuous_const Complex.continuous_normSq

theorem exp_mem_An {w : ℂ} (hw : w ∈ Hh TT) : Complex.exp w ∈ An TT := by
  exact hw

theorem hasFDerivAt_exp_real (w : ℂ) :
    HasFDerivAt Complex.exp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w)) w := by
  have h : HasFDerivAt Complex.exp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (Complex.exp w)).restrictScalars ℝ) w :=
    (Complex.hasDerivAt_exp w).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]

theorem hasFDerivAt_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (bet α)
      (α (Complex.exp w) • (ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w) +
        Complex.exp w • (fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w := by
  have he := hasFDerivAt_exp_real w
  have hmem : Complex.exp w ∈ An TT := exp_mem_An hw
  have hdα : DifferentiableAt ℝ α (Complex.exp w) :=
    (hα.contDiffAt ((isOpen_An TT).mem_nhds hmem)).differentiableAt
      (by first | simp | exact le_top)
  have hc : HasFDerivAt (fun z => α (Complex.exp z))
      ((fderiv ℝ α (Complex.exp w)).comp ((ContinuousLinearMap.mul ℝ ℂ) (Complex.exp w))) w :=
    hdα.hasFDerivAt.comp w he
  exact hc.mul he

theorem fderiv_bet_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (v : ℂ) :
    fderiv ℝ (bet α) w v = (α (Complex.exp w) * Complex.exp w + wZ α (Complex.exp w) * Complex.exp w ^ 2) * v +
      wZb α (Complex.exp w) * Complex.exp w * (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v := by
  rw [(hasFDerivAt_bet hα hw).fderiv]
  unfold wZ wZb
  obtain ⟨L, hL⟩ : ∃ L, L = fderiv ℝ α (Complex.exp w) := ⟨_, rfl⟩
  rw [← hL]
  have hL' : ∀ u : ℂ, 2 * L u = (u + (starRingEnd ℂ) u) * L 1 + Complex.I * ((starRingEnd ℂ) u - u) * L Complex.I := by
    intro u
    have hre : L u = (u.re : ℂ) * L 1 + (u.im : ℂ) * L Complex.I := by
      have hu : u.re • (1 : ℂ) + u.im • Complex.I = u := by
        rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
      conv_lhs => rw [← hu]
      rw [map_add (f := _), map_smul, map_smul, Complex.real_smul, Complex.real_smul]
    have h1 := Complex.add_conj u
    have h2 := Complex.sub_conj u
    push_cast at h1 h2
    rw [hre]
    linear_combination (-(L 1)) * h1 + (Complex.I * L Complex.I) * h2 +
      (2 * (u.im : ℂ) * L Complex.I) * Complex.I_sq
  have key := hL' (Complex.exp w * v)
  have hcj : (starRingEnd ℂ) (Complex.exp w * v) = (starRingEnd ℂ) (Complex.exp w) * (starRingEnd ℂ) v :=
    map_mul (starRingEnd ℂ) _ _
  rw [hcj] at key
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  linear_combination (Complex.exp w / 2) * key

theorem sym_alg (A b ζ h k : ℂ) (hb : b.re = 0) :
    ((A * h + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) h) * k).im =
      ((A * k + b * ζ * (starRingEnd ℂ) ζ * (starRingEnd ℂ) k) * h).im := by
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re, Complex.conj_re,
    Complex.conj_im, hb]
  ring

theorem contDiffOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bet α) (Hh TT) := by
  have he : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.exp (Hh TT) :=
    Complex.contDiff_exp.contDiffOn
  exact (hα.comp he (fun w hw => exp_mem_An hw)).mul he

theorem contDiffOn_om (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (om α) (Hh TT) :=
  omL.contDiff.comp_contDiffOn (contDiffOn_bet hα)

theorem fderiv_om_apply (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (h k : ℂ) :
    fderiv ℝ (om α) w h k = 2 * (fderiv ℝ (bet α) w h * k).im := by
  have hb := hasFDerivAt_bet hα hw
  have hom : HasFDerivAt (om α) (omL.comp (fderiv ℝ (bet α) w)) w :=
    omL.hasFDerivAt.comp w hb.differentiableAt.hasFDerivAt
  rw [hom.fderiv]
  simp [omL, two_smul, two_mul]

theorem om_sym (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) :
    ∀ p ∈ Hh TT, ∀ h k : ℂ, fderiv ℝ (om α) p h k = fderiv ℝ (om α) p k h := by
  intro p hp h k
  rw [fderiv_om_apply hα hp, fderiv_om_apply hα hp, fderiv_bet_apply hα hp, fderiv_bet_apply hα hp,
    sym_alg _ _ _ h k (hcurv _ (exp_mem_An hp))]

def x0 (TT : ℝ) : ℂ := (Real.log (TT + 1) : ℂ)

theorem base_point_mem_half_plane (hTT : 0 ≤ TT) : x0 TT ∈ Hh TT := by
  show TT < Complex.normSq (Complex.exp (x0 TT))
  unfold x0
  rw [← Complex.ofReal_exp, Complex.normSq_ofReal, Real.exp_log (by linarith)]
  nlinarith

def th (TT : ℝ) (α : ℂ → ℂ) (w : ℂ) : ℝ := prim (om α) (x0 TT) w

theorem hasFDerivAt_th (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    HasFDerivAt (th TT α) (om α w) w :=
  hasFDerivAt_prim (isOpen_Hh TT) (convex_Hh TT) (base_point_mem_half_plane hTT) ((contDiffOn_om hα).of_le (by simp))
    (om_sym hα hcurv) hw

theorem contDiffOn_th (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (Hh TT) := by
  have hHo : IsOpen (Hh TT) :=
    isOpen_lt continuous_const (Complex.continuous_normSq.comp Complex.continuous_exp)
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hHo]
  refine ⟨fun y hy => (hasFDerivAt_th hTT hα hcurv hy).differentiableAt.differentiableWithinAt, ?_⟩
  exact (contDiffOn_om hα).congr (fun y hy => (hasFDerivAt_th hTT hα hcurv hy).fderiv)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem theta_at_base_point_zero : th TT α (x0 TT) = 0 := by
  simp [th, prim_eq]

theorem exp_base_point_eq (hTT : 0 ≤ TT) : Complex.exp (x0 TT) = ((TT + 1 : ℝ) : ℂ) := by
  rw [x0, ← Complex.ofReal_exp, Real.exp_log (by linarith)]

theorem circleMap_eq (hTT : 0 ≤ TT) (θ : ℝ) : circleMap 0 (TT + 1) θ = Complex.exp (x0 TT + (θ : ℂ) * I) := by
  simp [circleMap, Complex.exp_add, exp_base_point_eq hTT]

theorem vert_mem (hTT : 0 ≤ TT) (θ : ℝ) : x0 TT + (θ : ℂ) * I ∈ Hh TT := by
  show TT < Complex.normSq (Complex.exp (x0 TT + (θ : ℂ) * I))
  rw [Complex.exp_add, exp_base_point_eq hTT, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I]
  nlinarith

theorem circleIntegral_eq (hTT : 0 ≤ TT) :
    circleIntegral α 0 (TT + 1) = ∫ θ in (0 : ℝ)..2 * Real.pi, I * bet α (x0 TT + (θ : ℂ) * I) := by
  unfold circleIntegral
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [deriv_circleMap, smul_eq_mul, circleMap_eq hTT θ, bet]
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem continuousOn_bet (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContinuousOn (bet α) (Hh TT) := by
  exact (contDiffOn_bet hα).continuousOn

theorem cont_vert (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    Continuous fun θ : ℝ => bet α (x0 TT + (θ : ℂ) * I) := by
  exact (continuousOn_bet hα).comp_continuous (by fun_prop) (vert_mem hTT)

theorem im_circleIntegral (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    (circleIntegral α 0 (TT + 1)).im = ∫ θ in (0 : ℝ)..2 * Real.pi, (bet α (x0 TT + (θ : ℂ) * I)).re := by
  have hint : IntervalIntegrable (fun θ : ℝ => I * bet α (x0 TT + (θ : ℂ) * I)) MeasureTheory.volume
      0 (2 * Real.pi) :=
    (continuous_const.mul (cont_vert hTT hα)).intervalIntegrable _ _
  rw [circleIntegral_eq hTT, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1
  funext θ
  simp [Complex.mul_im]

theorem th_top (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    th TT α (x0 TT + 2 * Real.pi * I) = 2 * (circleIntegral α 0 (TT + 1)).im := by
  rw [im_circleIntegral hTT hα]
  have hw : x0 TT + 2 * Real.pi * I - x0 TT = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
  have harg : ∀ t : ℝ, x0 TT + (t : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * I) =
      x0 TT + ((2 * Real.pi * t : ℝ) : ℂ) * I := by
    intro t; push_cast; ring
  have him : ∀ z : ℂ, (z * (((2 * Real.pi : ℝ) : ℂ) * I)).im = 2 * Real.pi * z.re := by
    intro z
    simp [Complex.mul_im, Complex.mul_re]
    ring
  simp only [th, prim, hw, om_apply, harg, him]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (f := fun θ : ℝ => (bet α (x0 TT + (θ : ℂ) * I)).re)
      (by positivity : (2 * Real.pi) ≠ 0)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  have hpi : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc (2 * Real.pi), hpi, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

theorem Hh_add_int {w : ℂ} (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by
  simp only [Hh, Set.mem_ofPred_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem Hh_add_one {w : ℂ} (hw : w ∈ Hh TT) : w + 2 * Real.pi * I ∈ Hh TT := by
  have := (Hh_add_int (TT := TT) (w := w) 1).2 hw
  simpa using this

theorem th_shift (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    th TT α (w + 2 * Real.pi * I) = th TT α w + 2 * (circleIntegral α 0 (TT + 1)).im := by
  have hc : ∀ z ∈ Hh TT, HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I) - th TT α z)
      (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    have h1 : HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I)) (om α (z + 2 * Real.pi * I)) z := by
      have := (hasFDerivAt_th hTT hα hcurv (Hh_add_one hz)).comp z
        ((hasFDerivAt_id z).add_const (2 * Real.pi * I))
      exact this
    have h2 := hasFDerivAt_th hTT hα hcurv hz
    have hom : om α (z + 2 * Real.pi * I) = om α z := by
      have := bet_periodic α z 1
      simp only [Int.cast_one, one_mul] at this
      simp only [om, this]
    have := h1.sub h2
    rwa [hom, sub_self] at this
  have hconst := (convex_Hh TT).is_const_of_fderivWithin_eq_zero
    (fun z hz => (hc z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hc z hz).hasFDerivWithinAt.fderivWithin ((isOpen_Hh TT).uniqueDiffWithinAt hz))
    (base_point_mem_half_plane hTT) hw
  rw [th_top hTT hα, theta_at_base_point_zero, sub_zero] at hconst
  linarith

theorem th_shift_int (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (k : ℤ) :
    ∀ w ∈ Hh TT, th TT α (w + (k : ℂ) * (2 * Real.pi * I)) = th TT α w + k * (2 * (circleIntegral α 0 (TT + 1)).im) := by
  intro w hw
  refine Int.induction_on k ?_ ?_ ?_
  · simp
  · intro n ih
    have hmem : w + ((n : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int (n : ℤ)).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + ((n : ℂ) + 1) * (2 * Real.pi * I) = w + (n : ℂ) * (2 * Real.pi * I) + 2 * Real.pi * I by ring,
      h1, ih]
    ring
  · intro n ih
    have hmem : w + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int _).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + (-(n : ℂ) - 1) * (2 * Real.pi * I) + 2 * Real.pi * I = w + -(n : ℂ) * (2 * Real.pi * I) by ring,
      ih] at h1
    linarith

theorem expI_th_eq (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n)
    {w w' : ℂ} (hw : w ∈ Hh TT) (hw' : w' ∈ Hh TT) (he : Complex.exp w = Complex.exp w') :
    Complex.exp (I * (th TT α w : ℂ)) = Complex.exp (I * (th TT α w' : ℂ)) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  obtain ⟨m, hm⟩ := hhol
  have h := th_shift_int hTT hα hcurv n w' hw'
  rw [← hn, hm] at h
  apply Complex.exp_eq_exp_iff_exists_int.2
  refine ⟨n * m, ?_⟩
  rw [h]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def uu (TT : ℝ) (α : ℂ → ℂ) (ζ : ℂ) : ℂ := Complex.exp (I * (th TT α (Complex.log ζ) : ℂ))

theorem ne_zero_of_An (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : ζ ≠ 0 := by
  rintro rfl
  simp [An] at hζ
  linarith

def br (s : Bool) (ζ : ℂ) : ℂ := if s then Complex.log ζ else Complex.log (-ζ) + Real.pi * I

def brD (s : Bool) : Set ℂ := if s then Complex.slitPlane else {ζ | -ζ ∈ Complex.slitPlane}

theorem isOpen_brD (s : Bool) : IsOpen (brD s) := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte]
    exact Complex.isOpen_slitPlane.preimage continuous_neg
  · simp only [brD, ↓reduceIte]
    exact Complex.isOpen_slitPlane

theorem exp_br (s : Bool) {ζ : ℂ} (hζ : ζ ≠ 0) : Complex.exp (br s ζ) = ζ := by
  cases s
  · simp only [br, Bool.false_eq_true, ↓reduceIte]
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hζ), Complex.exp_pi_mul_I]
    ring
  · simp only [br, ↓reduceIte]
    exact Complex.exp_log hζ

theorem exists_br {ζ : ℂ} (hζ : ζ ≠ 0) : ∃ s, ζ ∈ brD s := by
  by_cases h : ζ ∈ Complex.slitPlane
  · exact ⟨true, by simpa [brD] using h⟩
  · refine ⟨false, ?_⟩
    simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq]
    rw [Complex.mem_slitPlane_iff] at h ⊢
    push_neg at h
    left
    rcases h with ⟨h1, h2⟩
    have h3 : ζ.re ≠ 0 := fun h0 => hζ (Complex.ext (by simpa using h0) (by simpa using h2))
    have h4 : ζ.re < 0 := lt_of_le_of_ne h1 h3
    simp only [Complex.neg_re]
    linarith

theorem hasDerivAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : HasDerivAt (br s) ζ⁻¹ ζ := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq] at hs
    have e1 : br false = fun z : ℂ => Complex.log (-z) + Real.pi * I := by
      funext z
      simp [br]
    have h1 : HasDerivAt (fun z : ℂ => Complex.log (-z)) ((-ζ)⁻¹ * (-1)) ζ :=
      (Complex.hasDerivAt_log hs).comp ζ (hasDerivAt_neg ζ)
    have h2 := h1.add_const ((Real.pi : ℂ) * I)
    have e2 : (-ζ)⁻¹ * (-1) = ζ⁻¹ := by rw [inv_neg, neg_mul_neg, mul_one]
    rw [e2] at h2
    rw [e1]
    exact h2
  · simp only [brD, ↓reduceIte] at hs
    have e1 : br true = Complex.log := by
      funext z
      simp [br]
    rw [e1]
    exact Complex.hasDerivAt_log hs

theorem contDiffAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ := by
  have hd : DifferentiableOn ℂ (br s) (brD s) := fun z hz =>
    (hasDerivAt_br s hz).differentiableAt.differentiableWithinAt
  exact (hd.contDiffOn (isOpen_brD s)).contDiffAt ((isOpen_brD s).mem_nhds hs)

theorem br_mem_Hh (s : Bool) (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : br s ζ ∈ Hh TT := by
  show Complex.exp (br s ζ) ∈ An TT
  rw [exp_br s (ne_zero_of_An hTT hζ)]
  exact hζ

theorem uu_eq_br (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) (s : Bool) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    uu TT α ζ = Complex.exp (I * (th TT α (br s ζ) : ℂ)) := by
  unfold uu
  have h0 := ne_zero_of_An hTT hζ
  exact expI_th_eq hTT hα hcurv hhol (br_mem_Hh true hTT hζ) (br_mem_Hh s hTT hζ)
    (by rw [Complex.exp_log h0, exp_br s h0])

theorem norm_uu (ζ : ℂ) : ‖uu TT α ζ‖ = 1 := by
  rw [uu, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def ug (TT : ℝ) (α : ℂ → ℂ) (s : Bool) (z : ℂ) : ℂ := Complex.exp (I * (th TT α (br s z) : ℂ))

theorem hasFDerivAt_br_real (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) :
    HasFDerivAt (br s) ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹) ζ := by
  have h : HasFDerivAt (br s)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) ζ⁻¹).restrictScalars ℝ) ζ :=
    (hasDerivAt_br s hs).hasFDerivAt.restrictScalars ℝ
  convert h using 1
  refine ContinuousLinearMap.ext fun v => ?_
  simp [mul_comm]

theorem hasFDerivAt_ug (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s)
    (hζ : ζ ∈ An TT) :
    HasFDerivAt (ug TT α s)
      (((ContinuousLinearMap.mul ℝ ℂ) (ug TT α s ζ)).comp
        (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)))) ζ := by
  have h1 : HasFDerivAt (fun z => th TT α (br s z))
      ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹)) ζ :=
    (hasFDerivAt_th hTT hα hcurv (br_mem_Hh s hTT hζ)).comp ζ (hasFDerivAt_br_real s hs)
  have h2 : HasFDerivAt (fun z => ((th TT α (br s z) : ℝ) : ℂ))
      (Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹))) ζ :=
    Complex.ofRealCLM.hasFDerivAt.comp ζ h1
  have h3 : HasFDerivAt (fun z => I * ((th TT α (br s z) : ℝ) : ℂ))
      (I • Complex.ofRealCLM.comp ((om α (br s ζ)).comp ((ContinuousLinearMap.mul ℝ ℂ) ζ⁻¹))) ζ :=
    h2.const_smul I
  have h4 := h3.cexp
  show HasFDerivAt (fun z => Complex.exp (I * (th TT α (br s z) : ℂ))) _ ζ
  refine h4.congr_fderiv ?_
  ext v
  simp [ug]

theorem fderiv_uu_apply (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) (v : ℂ) :
    fderiv ℝ (uu TT α) ζ v = uu TT α ζ * (I * ((2 * (α ζ * v).im : ℝ) : ℂ)) := by
  have hne := ne_zero_of_An hTT hζ
  obtain ⟨s, hs⟩ := exists_br hne
  have hev : uu TT α =ᶠ[𝓝 ζ] ug TT α s := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hu : ug TT α s ζ = uu TT α ζ := (uu_eq_br hTT hα hcurv hhol s hζ).symm
  rw [hev.fderiv_eq, (hasFDerivAt_ug hTT hα hcurv s hs hζ).fderiv]
  have hb : α ζ * ζ * (ζ⁻¹ * v) = α ζ * v := by field_simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, om_apply, bet, exp_br s hne,
    smul_eq_mul, hu, hb]

theorem wZ_uu (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    wZ (uu TT α) ζ = uu TT α ζ * α ζ ∧ wZb (uu TT α) ζ = -(uu TT α ζ * (starRingEnd ℂ) (α ζ)) := by
  have h1 := fderiv_uu_apply hTT hα hcurv hhol hζ 1
  have h2 := fderiv_uu_apply hTT hα hcurv hhol hζ I
  have e1 : (1 / 2 : ℂ) * (I * ((2 * (α ζ * 1).im : ℝ) : ℂ) - I * (I * ((2 * (α ζ * I).im : ℝ) : ℂ)))
      = α ζ := by
    apply Complex.ext <;> simp
  have e2 : (1 / 2 : ℂ) * (I * ((2 * (α ζ * 1).im : ℝ) : ℂ) + I * (I * ((2 * (α ζ * I).im : ℝ) : ℂ)))
      = -(starRingEnd ℂ) (α ζ) := by
    apply Complex.ext <;> simp
  refine ⟨?_, ?_⟩
  · rw [wZ, h1, h2]
    linear_combination (uu TT α ζ) * e1
  · rw [wZb, h1, h2]
    linear_combination (uu TT α ζ) * e2

theorem contDiffOn_uu (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (uu TT α) (An TT) := by
  intro ζ hζ
  obtain ⟨s, hs⟩ := exists_br (ne_zero_of_An hTT hζ)
  have hev : uu TT α =ᶠ[𝓝 ζ] fun z => Complex.exp (I * (th TT α (br s z) : ℂ)) := by
    filter_upwards [(isOpen_An TT).mem_nhds hζ] with z hz
    exact uu_eq_br hTT hα hcurv hhol s hz
  have hth : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (th TT α) (br s ζ) :=
    (contDiffOn_th hTT hα hcurv).contDiffAt ((isOpen_Hh TT).mem_nhds (br_mem_Hh s hTT hζ))
  have hbr : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ :=
    (contDiffAt_br s hs).restrict_scalars ℝ
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ((th TT α (br s z) : ℝ) : ℂ)) ζ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp ζ (hth.comp ζ hbr)
  exact ((contDiffAt_const.mul h2).cexp.congr_of_eventuallyEq hev).contDiffWithinAt

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
end

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem annulus_condition_holds : GTCAnnulus := by
  intro TT α hTT hα hcurv hper
  have hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n :=
    hper (TT + 1) (by linarith) (by nlinarith [sq_nonneg (TT + 1 / 2)])
  have hcurv' : ∀ ζ : ℂ, TT < Complex.normSq ζ → (Ann.wZb α ζ).re = 0 := hcurv
  refine ⟨Ann.uu TT α, Ann.contDiffOn_uu hTT hα hcurv' hhol, fun ζ hζ => ?_⟩
  obtain ⟨h1, h2⟩ := Ann.wZ_uu hTT hα hcurv' hhol (ζ := ζ) hζ
  have hn : ‖Ann.uu TT α ζ‖ = 1 := Ann.norm_uu ζ
  have hs : star (Ann.uu TT α ζ) * Ann.uu TT α ζ = 1 := by
    calc star (Ann.uu TT α ζ) * Ann.uu TT α ζ
        = (starRingEnd ℂ) (Ann.uu TT α ζ) * Ann.uu TT α ζ := rfl
      _ = ((‖Ann.uu TT α ζ‖ : ℝ) : ℂ) ^ 2 := Complex.conj_mul' _
      _ = 1 := by rw [hn]; norm_num
  refine ⟨hn, ?_, ?_⟩
  · show star (Ann.uu TT α ζ) * Ann.wZ (Ann.uu TT α) ζ = α ζ
    rw [h1, ← mul_assoc, hs, one_mul]
  · show star (Ann.uu TT α ζ) * Ann.wZb (Ann.uu TT α) ζ = -star (α ζ)
    rw [h2, mul_neg, ← mul_assoc, hs, one_mul] <;> rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem gTCRefTrace_of_rotK (h : GTRRotK) : GTCRefTrace :=
  gTCRefTrace_of_cutK radial_gauge_move radial_gauge_constant_holds top_normal_form_of_curvature top_action_on_gauge_holds h radial_gauge_integrality_holds radial_gauge_transition_holds gauge_reality_holds

theorem gTCRef_of_rotK (h : GTRRotK) : GTCRef :=
  gTCRef_of_cut gauge_reality_holds curvature_identity_holds curvature_trace_holds (gTCRefTrace_of_rotK h) reference_annulus_holds

theorem gTConn_of_rotK (h : GTRRotK) : GTConn :=
  gTConn_of_leaves gauge_locality_holds gauge_reality_holds (gTCCurv_of_ref (gTCRef_of_rotK h)) (gTCHol_of_ref (gTCRef_of_rotK h)) annulus_condition_holds

theorem genTransfer_of_rotK (h : GTRRotK) : GenTransfer :=
  genTransfer_of_cut GT.gauge_function_holds gauge_kappa_holds (gTConn_of_rotK h) second_shift_gauge_holds

theorem gCore_of_rotK (h : GTRRotK) : GCore := gCore_of_genTransfer (genTransfer_of_rotK h)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_rotK (hJ : JfSmoothDS) (hR : Gauge.GC.GTRRotK) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_ssnRep hJ (Gauge.GC.genTransfer_of_rotK hR) h

end Formalism.FourierDecayAlt.P.CutMP
