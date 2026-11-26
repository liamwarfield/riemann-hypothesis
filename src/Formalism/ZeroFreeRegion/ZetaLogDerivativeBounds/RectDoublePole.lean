module

public import Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth

@[expose] public section

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RectDoublePole
open Complex

noncomputable section

namespace Formalism.ZF

theorem rdp_rectInt_eq_fx (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) :
    rectInt g x0 x1 y0 y1 = Formalism.FX.rectInt g x0 x1 y0 y1 := rfl

theorem rdp_rectInt_add (f1 f2 : ℂ → ℂ) (x0 x1 y0 y1 : ℝ)
    (hB1 : IntervalIntegrable (fun x : ℝ => f1 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hB2 : IntervalIntegrable (fun x : ℝ => f2 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hT1 : IntervalIntegrable (fun x : ℝ => f1 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hT2 : IntervalIntegrable (fun x : ℝ => f2 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hR1 : IntervalIntegrable (fun y : ℝ => f1 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hR2 : IntervalIntegrable (fun y : ℝ => f2 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hL1 : IntervalIntegrable (fun y : ℝ => f1 (x0 + y * I)) MeasureTheory.volume y0 y1)
    (hL2 : IntervalIntegrable (fun y : ℝ => f2 (x0 + y * I)) MeasureTheory.volume y0 y1) :
    rectInt (fun w => f1 w + f2 w) x0 x1 y0 y1 =
      rectInt f1 x0 x1 y0 y1 + rectInt f2 x0 x1 y0 y1 := by
  simp only [rectInt]
  rw [intervalIntegral.integral_add hB1 hB2, intervalIntegral.integral_add hT1 hT2,
    intervalIntegral.integral_add hR1 hR2, intervalIntegral.integral_add hL1 hL2]
  ring

theorem rdp_hasDerivAt_prim (a p w : ℂ) (hw : w ≠ p) :
    HasDerivAt (fun z => -a * (z - p)⁻¹) (a / (w - p) ^ 2) w := by
  have hwp : w - p ≠ 0 := sub_ne_zero.2 hw
  have h := (((hasDerivAt_id' w).sub_const p).inv hwp).const_mul (-a)
  convert h using 1
  all_goals first | rfl | ring | (field_simp; ring) | (simp; ring)

theorem rdp_horiz (a p : ℂ) (y x0 x1 : ℝ) (hy : y ≠ p.im) :
    ∫ x in x0..x1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x1 : ℂ) + y * I - p)⁻¹) - (-a * ((x0 : ℂ) + y * I - p)⁻¹) := by
  have hne : ∀ x : ℝ, (x : ℂ) + y * I ≠ p := by
    intro x h
    apply hy
    have := congrArg Complex.im h
    simpa using this
  have hder : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -a * ((t : ℂ) + y * I - p)⁻¹)
      (a / ((x : ℂ) + y * I - p) ^ 2) x := by
    intro x
    have hh : HasDerivAt (fun t : ℝ => (t : ℂ) + y * I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
    have h2 := (rdp_hasDerivAt_prim a p ((x : ℂ) + y * I) (hne x)).comp x hh
    simpa [Function.comp_def] using h2
  have hcont : Continuous (fun x : ℝ => a / ((x : ℂ) + y * I - p) ^ 2) := by
    refine Continuous.div₀ continuous_const (by fun_prop) (fun x => ?_)
    exact pow_ne_zero _ (sub_ne_zero.2 (hne x))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    (hcont.intervalIntegrable _ _)

theorem rdp_vert (a p : ℂ) (x y0 y1 : ℝ) (hx : x ≠ p.re) :
    I * ∫ y in y0..y1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x : ℂ) + y1 * I - p)⁻¹) - (-a * ((x : ℂ) + y0 * I - p)⁻¹) := by
  have hne : ∀ y : ℝ, (x : ℂ) + y * I ≠ p := by
    intro y h
    apply hx
    have := congrArg Complex.re h
    simpa using this
  have hder : ∀ y : ℝ, HasDerivAt (fun t : ℝ => -a * ((x : ℂ) + t * I - p)⁻¹)
      (I * (a / ((x : ℂ) + y * I - p) ^ 2)) y := by
    intro y
    have hh : HasDerivAt (fun t : ℝ => (x : ℂ) + t * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
    have h2 := (rdp_hasDerivAt_prim a p ((x : ℂ) + y * I) (hne y)).comp y hh
    simp only [Function.comp_def] at h2
    exact h2.congr_deriv (mul_comm _ _)
  have hcont : Continuous (fun y : ℝ => I * (a / ((x : ℂ) + y * I - p) ^ 2)) := by
    refine continuous_const.mul (Continuous.div₀ continuous_const (by fun_prop) (fun y => ?_))
    exact pow_ne_zero _ (sub_ne_zero.2 (hne y))
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hder y)
    (hcont.intervalIntegrable _ _)

theorem rdp_rectInt_double (a p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => a / (w - p) ^ 2) x0 x1 y0 y1 = 0 := by
  simp only [rectInt]
  rw [rdp_horiz a p y0 x0 x1 (ne_of_lt h3), rdp_horiz a p y1 x0 x1 (ne_of_gt h4),
    rdp_vert a p x1 y0 y1 (ne_of_gt h2), rdp_vert a p x0 y0 y1 (ne_of_lt h1)]
  ring

theorem rdp_seg (g G : ℂ → ℂ) (a b p : ℂ) (γ : ℝ → ℂ) (s t : ℝ) (hγ : Continuous γ)
    (hG : ContinuousOn (fun u => G (γ u)) (Set.uIcc s t)) (hP : ∀ u ∈ Set.uIcc s t, γ u ≠ p)
    (hg : ∀ w : ℂ, w ≠ p → g w = G w + a / (w - p) ^ 2 + b / (w - p)) :
    IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
    IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by
  have hD : ContinuousOn (fun u => a / (γ u - p) ^ 2) (Set.uIcc s t) := by
    refine ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun u hu => ?_)
    exact pow_ne_zero _ (sub_ne_zero.2 (hP u hu))
  have hS : ContinuousOn (fun u => G (γ u) + b / (γ u - p)) (Set.uIcc s t) := by
    refine hG.add (ContinuousOn.div₀ continuousOn_const (by fun_prop) (fun u hu => ?_))
    exact sub_ne_zero.2 (hP u hu)
  refine ⟨(hS.congr fun u hu => ?_).intervalIntegrable, hD.intervalIntegrable⟩
  rw [hg _ (hP u hu)]
  ring

theorem rectangle_double_pole : RectDoublePole := by
  intro g G a b p x0 x1 y0 y1 h1 h2 h3 h4 hU hg
  obtain ⟨U, hUo, hRU, hGU⟩ := hU
  have hGc : ContinuousOn G U := hGU.continuousOn
  have hx01 : x0 ≤ x1 := by linarith
  have hy01 : y0 ≤ y1 := by linarith

  have hmem : ∀ x y : ℝ, x ∈ Set.uIcc x0 x1 → y ∈ Set.uIcc y0 y1 → (x : ℂ) + y * I ∈ U := by
    intro x y hx hy
    apply hRU
    rw [Complex.mem_reProdIm]
    simp [hx, hy]
  have hseg : ∀ (γ : ℝ → ℂ) (s t : ℝ), Continuous γ → (∀ u ∈ Set.uIcc s t, γ u ∈ U) →
      (∀ u ∈ Set.uIcc s t, γ u ≠ p) →
      IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
      IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by
    intro γ s t hγ hγU hγp
    exact rdp_seg g G a b p γ s t hγ (hGc.comp hγ.continuousOn fun u hu => hγU u hu) hγp hg
  have hxl : x0 ∈ Set.uIcc x0 x1 := Set.left_mem_uIcc
  have hxr : x1 ∈ Set.uIcc x0 x1 := Set.right_mem_uIcc
  have hyl : y0 ∈ Set.uIcc y0 y1 := Set.left_mem_uIcc
  have hyr : y1 ∈ Set.uIcc y0 y1 := Set.right_mem_uIcc
  have hB := hseg (fun x : ℝ => (x : ℂ) + y0 * I) x0 x1 (by fun_prop)
    (fun u hu => hmem u y0 hu hyl)
    (fun u _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have hT := hseg (fun x : ℝ => (x : ℂ) + y1 * I) x0 x1 (by fun_prop)
    (fun u hu => hmem u y1 hu hyr)
    (fun u _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have hR := hseg (fun y : ℝ => (x1 : ℂ) + y * I) y0 y1 (by fun_prop)
    (fun u hu => hmem x1 u hxr hu)
    (fun u _ h => by have := congrArg Complex.re h; simp at this; linarith)
  have hL := hseg (fun y : ℝ => (x0 : ℂ) + y * I) y0 y1 (by fun_prop)
    (fun u hu => hmem x0 u hxl hu)
    (fun u _ h => by have := congrArg Complex.re h; simp at this; linarith)
  have hsplit : g = fun w => (g w - a / (w - p) ^ 2) + a / (w - p) ^ 2 := by
    funext w; ring
  rw [hsplit, rdp_rectInt_add _ _ x0 x1 y0 y1 hB.1 hB.2 hT.1 hT.2 hR.1 hR.2 hL.1 hL.2,
    rdp_rectInt_double a p x0 x1 y0 y1 h1 h2 h3 h4, add_zero, rdp_rectInt_eq_fx]
  have hres := Formalism.FX.rectangle_residue (fun w => g w - a / (w - p) ^ 2) G {p} (fun _ => b)
    x0 x1 y0 y1 (by linarith) (by linarith) (by simp [h1, h2, h3, h4]) ⟨U, hUo, hRU, hGU⟩
    (by
      intro w hw
      have hwp : w ≠ p := by simpa using hw
      simp only [Finset.sum_singleton]
      rw [hg w hwp]
      ring)
  simpa using hres

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRegionOf
section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LdrMid
section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LdrInvSubOneLe
open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma ldr_inv_sub_one_le {s : ℂ} (h : 1 ≤ |s.im|) : ‖1 / (s - 1)‖ ≤ 1 := by
  have h1 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, Complex.one_im, sub_zero] at h1
  rw [norm_div, norm_one, div_le_one (by linarith)]
  linarith

end Formalism.ZF
end
end

open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma ldr_mid {c₀ : ℝ}
    (hZ0 : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hc₀ : 0 < c₀) (hG : ZetaGrowth) (hI : ZetaInvBound) (hLL : LandauLocal) {σ t : ℝ}
    (hL : 24 ≤ Real.log (|t| + 2))
    (hσlo : 1 - (c₀ / 4) / Real.log (|t| + 2) ≤ σ) (hσlo' : 1 - 1 / Real.log (|t| + 2) ≤ σ)
    (hσhi : σ ≤ 1 + 1 / Real.log (|t| + 2)) :
    ‖deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I)
        + 1 / (((σ : ℂ) + t * I) - 1)‖
      ≤ (1441 + 60 / c₀) * Real.log (|t| + 2) ^ 2 := by
  set T := |t| with hTdef
  set L := Real.log (T + 2) with hLdef
  have hLpos : 0 < L := by linarith
  have hT0 : 0 ≤ T := abs_nonneg t
  have hLX : L ≤ T + 1 := by
    have := Real.log_le_sub_one_of_pos (show 0 < T + 2 by linarith)
    linarith
  have hT3 : 3 ≤ T := by linarith
  set u := 1 / L with hudef
  have hu : 0 < u := by positivity
  have hu24 : u ≤ 1 / 24 := one_div_le_one_div_of_le (by norm_num) hL
  have hLu : L * u = 1 := by rw [hudef]; field_simp
  set σ₀ := 1 + u with hσ₀def
  have hσ₀1 : 1 < σ₀ := by linarith
  have hσ₀2 : σ₀ ≤ 2 := by linarith
  have hσK : 2 / (σ₀ - 1) ≤ 20000 * (T + 2) := by
    have e : 2 / (σ₀ - 1) = 2 * L := by
      rw [show σ₀ - 1 = u by ring, hudef, div_div_eq_mul_div, div_one]
    rw [e]; linarith
  set z₀ : ℂ := (σ₀ : ℂ) + t * I with hz₀
  have hz0re : z₀.re = σ₀ := by simp [z₀]
  have hz0 : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by rw [hz0re]; exact hσ₀1)
  have hM := zfo_M_bound hG hI hσ₀1 hσ₀2 hσK hT3 hT3 (by linarith)
  have hM1 : 1 ≤ (T + 2) ^ 10 := one_le_pow₀ (by linarith)
  obtain ⟨Z, m, hZ, hm, hsum, hder⟩ :=
    hLL riemannZeta z₀ (1 / 2) ((T + 2) ^ 10) (by norm_num) hM1 (zfo_diff_ball hT3) hz0 hM
  have hlogM : Real.log ((T + 2) ^ 10) = 10 * L := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlogM] at hsum hder
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hsz : s - z₀ = ((σ - σ₀ : ℝ) : ℂ) := by
    simp only [s, z₀, Complex.ofReal_sub]; ring
  have hs_mem : s ∈ closedBall z₀ (1 / 2 / 6) := by
    rw [mem_closedBall, dist_eq_norm, hsz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have ht0 : t ≠ 0 := by
    intro h; rw [h, abs_zero] at hTdef; linarith
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.im h; rw [hsim, Complex.one_im] at this; exact ht0 this
  have hc4 : (c₀ / 4) / L ≤ c₀ / L := div_le_div_of_nonneg_right (by linarith) hLpos.le
  have hs_ne : riemannZeta s ≠ 0 := by
    apply hZ0 s hs1
    rw [hsre, hsim]; linarith
  have hD := hder s hs_mem hs_ne

  set δ := (c₀ / 4) / L with hδdef
  have hδ : 0 < δ := by positivity
  have hterm : ∀ ρ ∈ Z, ‖(m ρ : ℂ) / (s - ρ)‖ ≤ (m ρ : ℝ) / δ := by
    intro ρ hρ
    obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
    rw [mem_closedBall, dist_eq_norm] at hρb
    have him : |ρ.im - t| ≤ 1 / 6 := by
      have h1 : (ρ - z₀).im = ρ.im - t := by simp [z₀]
      rw [← h1]; exact (Complex.abs_im_le_norm _).trans (by linarith)
    have hρim : |ρ.im| ≤ T + 1 / 6 := by
      have := abs_sub_abs_le_abs_sub ρ.im t; linarith
    have hρim' : T - 1 / 6 ≤ |ρ.im| := by
      have := abs_sub_abs_le_abs_sub t ρ.im; rw [abs_sub_comm] at this; linarith
    have hρ1 : ρ ≠ 1 := by
      intro h; rw [h, Complex.one_im, abs_zero] at hρim'; linarith
    have hre : ρ.re < 1 - c₀ / Real.log (|ρ.im| + 2) := by
      by_contra hc; exact hZ0 ρ hρ1 (not_lt.mp hc) hρ0
    have hlogρ : Real.log (|ρ.im| + 2) ≤ 2 * L := by
      have e : 2 * L = Real.log ((T + 2) ^ 2) := by rw [Real.log_pow]; push_cast; ring
      rw [e]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have hlogρpos : 0 < Real.log (|ρ.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg ρ.im])
    have h2 : c₀ / (2 * L) ≤ c₀ / Real.log (|ρ.im| + 2) :=
      div_le_div_of_nonneg_left hc₀.le hlogρpos hlogρ
    have h3 : c₀ / (2 * L) = 2 * δ := by rw [hδdef]; field_simp; ring
    have hsρ : δ < (s - ρ).re := by rw [Complex.sub_re, hsre]; linarith
    have hn : δ < ‖s - ρ‖ := lt_of_lt_of_le hsρ (Complex.re_le_norm _)
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ hn.le
  have hSm : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ (60 / c₀) * L ^ 2 := by
    have h1 : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / δ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    have h2 : ∑ ρ ∈ Z, (m ρ : ℝ) / δ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ := by
      rw [← Finset.sum_div]; push_cast; rfl
    have hlog2 : (2 : ℝ) / 3 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hl2pos : 0 < Real.log 2 := by linarith
    have h3 : 10 * L / Real.log 2 ≤ 15 * L := by
      rw [div_le_iff₀ hl2pos]; nlinarith
    have h4 : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ ≤ 15 * L / δ :=
      div_le_div_of_nonneg_right (hsum.trans h3) hδ.le
    have h5 : 15 * L / δ = (60 / c₀) * L ^ 2 := by rw [hδdef]; field_simp; ring
    linarith
  have hinv : ‖1 / (s - 1)‖ ≤ 1 := ldr_inv_sub_one_le (by rw [hsim]; linarith)
  have hsplit : deriv riemannZeta s / riemannZeta s + 1 / (s - 1) =
      (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
        + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) + 1 / (s - 1) := by ring
  have hD' : (72 : ℝ) * (10 * L) / (1 / 2) = 1440 * L := by ring
  rw [hD'] at hD
  have htot : ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ 1440 * L + (60 / c₀) * L ^ 2 + 1 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (deriv riemannZeta s / riemannZeta s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
      (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ))
    linarith
  have hL1 : 1 ≤ L := by linarith
  have hLL2 : L ≤ L ^ 2 := by nlinarith
  nlinarith

end Formalism.ZF
end
end

open Complex

noncomputable section

namespace Formalism.ZF

theorem logDerivBoundInRegionOfBounds : LogDerivRegionOf := by
  intro hZF hLR hG hI hSH hLL
  obtain ⟨c₀, hc₀, hZ0⟩ := hZF
  obtain ⟨CR, hCR0, hCR⟩ := hLR
  obtain ⟨cS, CS, hcS, hCS⟩ := hSH (Real.exp 24)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set c := min (min (c₀ / 4) 1) (cS * Real.log 2) with hc
  have hcpos : 0 < c := lt_min (lt_min (by linarith) one_pos) (mul_pos hcS (by linarith))
  have hc1 : c ≤ c₀ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ cS * Real.log 2 := min_le_right _ _
  have hK1 : 0 ≤ 1441 + 60 / c₀ := by positivity
  have hK3 : 0 ≤ 4 * |CS| := by positivity
  refine ⟨c, (1441 + 60 / c₀) + (4 + 4 * CR) + 4 * |CS|, hcpos, ?_⟩
  intro s hs1 hreg
  have hs : s = (s.re : ℂ) + s.im * I := (Complex.re_add_im s).symm
  set σ := s.re with hσ
  set t := s.im with ht
  set L := Real.log (|t| + 2) with hL
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hLpos : 1 / 2 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hLsq : 1 / 4 ≤ L ^ 2 := by nlinarith
  by_cases hright : 1 + 1 / L < σ
  · have hinvpos : 0 < 1 / L := by positivity
    have hσ1 : 1 < σ := by linarith
    have h1 := hCR s hσ1
    have hnorm : σ - 1 ≤ ‖s - 1‖ := by
      have : (s - 1).re = σ - 1 := by simp [hσ]
      calc σ - 1 = (s - 1).re := this.symm
        _ ≤ |(s - 1).re| := le_abs_self _
        _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    have hσL : 1 / (σ - 1) ≤ L := by
      rw [div_le_iff₀ (by linarith)]
      have h := hright
      have : 1 / L < σ - 1 := by linarith
      rw [div_lt_iff₀ hL0] at this
      linarith
    have h2 : ‖1 / (s - 1)‖ ≤ L := by
      rw [norm_div, norm_one]
      calc 1 / ‖s - 1‖ ≤ 1 / (σ - 1) := one_div_le_one_div_of_le (by linarith) hnorm
        _ ≤ L := hσL
    calc ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖
        ≤ ‖deriv riemannZeta s / riemannZeta s‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ ≤ (1 / (σ - 1) + CR) + L := add_le_add h1 h2
      _ ≤ (4 + 4 * CR) * L ^ 2 := by nlinarith [mul_nonneg hCR0 (sq_nonneg L)]
      _ ≤ _ := by nlinarith [mul_nonneg hK1 (sq_nonneg L), mul_nonneg hK3 (sq_nonneg L)]
  · push_neg at hright
    by_cases hbig : 24 ≤ L
    · have hlo : 1 - (c₀ / 4) / L ≤ σ := by
        have : c / L ≤ (c₀ / 4) / L := by gcongr
        linarith
      have hlo' : 1 - 1 / L ≤ σ := by
        have : c / L ≤ 1 / L := by gcongr
        linarith
      have hm := Formalism.ZF.ldr_mid hZ0 hc₀ hG hI hLL (σ := σ) (t := t) hbig hlo hlo' hright
      rw [hs]
      calc _ ≤ (1441 + 60 / c₀) * L ^ 2 := hm
        _ ≤ _ := by nlinarith [mul_nonneg hK3 (sq_nonneg L), mul_nonneg hCR0 (sq_nonneg L)]
    · push_neg at hbig
      have htT : |t| ≤ Real.exp 24 := by
        have : |t| + 2 < Real.exp 24 := by
          rw [← Real.log_lt_iff_lt_exp (by positivity)]
          exact hbig
        linarith
      have hcL : c / L ≤ cS := by
        rw [div_le_iff₀ hL0]
        nlinarith
      have hinv : 1 / L ≤ 2 := by
        rw [div_le_iff₀ hL0]; linarith
      have hσ3 : σ ≤ 3 := by linarith
      have hb := hCS s hs1 htT (by linarith) hσ3
      calc _ ≤ CS := hb
        _ ≤ |CS| := le_abs_self _
        _ ≤ 4 * |CS| * L ^ 2 := by nlinarith [abs_nonneg CS]
        _ ≤ _ := by nlinarith [mul_nonneg hK1 (sq_nonneg L), mul_nonneg hCR0 (sq_nonneg L)]

end Formalism.ZF
end
end
