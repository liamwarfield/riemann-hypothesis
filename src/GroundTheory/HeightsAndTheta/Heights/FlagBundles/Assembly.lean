module

public import GroundTheory.PAdicHodge.PerfectoidField
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalHeightReduction
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreConstantClosedForm
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreIntegralInvariant
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyIntegral

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.StatementsZonalPairing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def ZonalKernelPairing.Statement : Prop :=
  ∀ F H : Polynomial ℝ,
    (1 / 4) * ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1, zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂ =
      -(1 / 2) * uniformMean F.eval * uniformMean H.eval -
        (1 / 4) * ∫ c in (-1 : ℝ)..1, centredPrimitive F c * centredPrimitive H c / (1 - c ^ 2)

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalBilinearFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

theorem ZonalBilinearFormula.proof (hB : ZonalHeightReduction.Statement)
    (hC : ZonalKernelPairing.Statement) : ZonalBilinearFormula.Statement := by
  refine ⟨fun F H => (hB F H).2.trans (hC F H), ?_⟩
  have h := (hB Polynomial.X Polynomial.X).2.trans (hC Polynomial.X Polynomial.X)
  simp only [Polynomial.eval_X] at h
  rw [h]
  have hm : uniformMean (fun x : ℝ => x) = 0 := by
    simp [uniformMean, integral_id]
  have hg : ∀ c : ℝ, centredPrimitive Polynomial.X c = (c ^ 2 - 1) / 2 := by
    intro c
    simp only [centredPrimitive, Polynomial.eval_X]
    rw [hm]
    simp only [sub_zero, integral_id]
    ring
  have hq : ∀ c : ℝ, centredPrimitive Polynomial.X c * centredPrimitive Polynomial.X c / (1 - c ^ 2)
      = (1 - c ^ 2) / 4 := by
    intro c
    rw [hg]
    rcases eq_or_ne (1 - c ^ 2) 0 with h0 | h0
    · have : c ^ 2 - 1 = 0 := by linarith
      rw [h0, this]; simp
    · field_simp
      ring
  rw [hm]
  simp only [hq]
  simp [intervalIntegral.integral_div, integral_pow]
  norm_num

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernelPairing
section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.ZonalPairingCalculus
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Polynomial MeasureTheory Set

noncomputable section

theorem exists_polynomial_antiderivative (p : ℝ[X]) : ∃ q : ℝ[X], derivative q = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [derivative_add, ha, hb]⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (a / (n + 1)), ?_⟩
    rw [derivative_monomial, Nat.add_sub_cancel]
    congr 1
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

theorem exists_centredPrimitive_poly (F : ℝ[X]) :
    ∃ G : ℝ[X], (∀ c, centredPrimitive F c = G.eval c) ∧
      derivative G = F - C (uniformMean F.eval) ∧ G.eval (-1) = 0 ∧ G.eval 1 = 0 := by
  obtain ⟨q, hq⟩ := exists_polynomial_antiderivative (F - C (uniformMean F.eval))
  have hprim : ∀ c, centredPrimitive F c = q.eval c - q.eval (-1) := by
    intro c
    unfold centredPrimitive
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
    · intro x _
      have := q.hasDerivAt x
      rwa [hq, eval_sub, eval_C] at this
    · exact (F.continuous.sub continuous_const).intervalIntegrable _ _
  refine ⟨q - C (q.eval (-1)), fun c => by rw [hprim]; simp, by simp [hq], by simp, ?_⟩
  have h1 := hprim 1
  unfold centredPrimitive at h1
  rw [intervalIntegral.integral_sub (F.continuous.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const] at h1
  simp only [eval_sub, eval_C]
  rw [← h1]
  unfold uniformMean
  simp only [smul_eq_mul]
  ring

theorem exists_eq_sq_sub_one_mul (G : ℝ[X]) (hm : G.eval (-1) = 0) (hp : G.eval 1 = 0) :
    ∃ w : ℝ[X], G = (X ^ 2 - C 1) * w := by
  have h1 : (X - C 1) * (G /ₘ (X - C 1)) = G := mul_divByMonic_eq_iff_isRoot.mpr hp
  have hq : (G /ₘ (X - C 1)).IsRoot (-1) := by
    have h := congrArg (eval (-1)) h1
    rw [eval_mul, hm, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  have h2 : (X - C (-1)) * ((G /ₘ (X - C 1)) /ₘ (X - C (-1))) = G /ₘ (X - C 1) :=
    mul_divByMonic_eq_iff_isRoot.mpr hq
  refine ⟨(G /ₘ (X - C 1)) /ₘ (X - C (-1)), ?_⟩
  conv_lhs => rw [← h1, ← h2]
  simp only [map_neg, map_one]
  ring

theorem zonalKernel_of_le {x y : ℝ} (hx : -1 < x) (hy : y < 1) (hyx : y ≤ x) :
    zonalKernel x y = (1 / 2) * Real.log (1 + x) + (1 / 2) * Real.log (1 - y) - Real.log 2 := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have h2 : (0 : ℝ) < 1 - y := by linarith
  unfold zonalKernel
  rw [max_eq_left hyx, min_eq_right hyx, Real.log_div (mul_pos h1 h2).ne' (by norm_num),
    Real.log_mul h1.ne' h2.ne']
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [this]
  ring

theorem zonalKernel_of_ge {x y : ℝ} (hx : x < 1) (hy : -1 < y) (hxy : x ≤ y) :
    zonalKernel x y = (1 / 2) * Real.log (1 + y) + (1 / 2) * Real.log (1 - x) - Real.log 2 := by
  have h1 : (0 : ℝ) < 1 + y := by linarith
  have h2 : (0 : ℝ) < 1 - x := by linarith
  unfold zonalKernel
  rw [max_eq_right hxy, min_eq_left hxy, Real.log_div (mul_pos h1 h2).ne' (by norm_num),
    Real.log_mul h1.ne' h2.ne']
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [this]
  ring

theorem continuousOn_zonalKernel_mul_eval {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (H : ℝ[X]) :
    ContinuousOn (fun y => zonalKernel x y * H.eval y) (Icc (-1) 1) := by
  apply ContinuousOn.mul _ H.continuous.continuousOn
  unfold zonalKernel
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.log (by fun_prop)
  intro y _
  have h1 : 0 < 1 + max x y := by linarith [le_max_left x y, hx.1]
  have h2 : 0 < 1 - min x y := by linarith [min_le_left x y, hx.2]
  exact (div_pos (mul_pos h1 h2) (by norm_num)).ne'

theorem integral_zonalKernel_mul_eval (H w ρ σ : ℝ[X]) (e : ℝ)
    (hw : derivative ((X ^ 2 - C 1) * w) = H - C e)
    (hρ : derivative ρ = -((X + C 1) * w)) (hσ : derivative σ = (C 1 - X) * w)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∫ y in (-1 : ℝ)..1, zonalKernel x y * H.eval y =
      -e + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hcont := continuousOn_zonalKernel_mul_eval ⟨hx1, hx2⟩ H
  have hint1 : IntervalIntegrable (fun y => zonalKernel x y * H.eval y) volume (-1) x :=
    (hcont.mono (by rw [uIcc_of_le hx1.le]; exact Icc_subset_Icc le_rfl hx2.le)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun y => zonalKernel x y * H.eval y) volume x 1 :=
    (hcont.mono (by rw [uIcc_of_le hx2.le]; exact Icc_subset_Icc hx1.le le_rfl)).intervalIntegrable
  set Γ : ℝ[X] := (X ^ 2 - C 1) * w with hΓ
  have hΓe : ∀ y, Γ.eval y = (y ^ 2 - 1) * w.eval y := fun y => by simp [hΓ]
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  have h1 : ∫ y in (-1 : ℝ)..x, zonalKernel x y * H.eval y =
      (((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - x)) *
          (Γ.eval x + e * (1 + x)) + (1 / 2) * (ρ.eval x - e * x - 2 * e * Real.log (1 - x))) -
      (((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - -1)) *
          (Γ.eval (-1) + e * (1 + -1)) +
        (1 / 2) * (ρ.eval (-1) - e * (-1) - 2 * e * Real.log (1 - -1))) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y =>
      ((1 / 2) * Real.log (1 + x) - Real.log 2 + (1 / 2) * Real.log (1 - y)) *
          (Γ.eval y + e * (1 + y)) + (1 / 2) * (ρ.eval y - e * y - 2 * e * Real.log (1 - y)))
      ?_ hint1
    intro y hy
    rw [uIcc_of_le hx1.le] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy3 : 0 < 1 - y := by linarith
    have hL : HasDerivAt (fun y => Real.log (1 - y)) (-1 / (1 - y)) y := by
      exact ((hasDerivAt_id y).const_sub 1).log hy3.ne'
    have hk : HasDerivAt (fun y => (1 / 2) * Real.log (1 + x) - Real.log 2 +
        (1 / 2) * Real.log (1 - y)) ((1 / 2) * (-1 / (1 - y))) y :=
      (hL.const_mul (1 / 2)).const_add _
    have hP : HasDerivAt (fun y => Γ.eval y + e * (1 + y)) (Γ.derivative.eval y + e * 1) y :=
      (Γ.hasDerivAt y).add (((hasDerivAt_id y).const_add 1).const_mul e)
    have hQ : HasDerivAt (fun y => (1 / 2) * (ρ.eval y - e * y - 2 * e * Real.log (1 - y)))
        ((1 / 2) * (ρ.derivative.eval y - e * 1 - 2 * e * (-1 / (1 - y)))) y :=
      (((ρ.hasDerivAt y).sub ((hasDerivAt_id y).const_mul e)).sub (hL.const_mul (2 * e))).const_mul
        (1 / 2)
    refine ((hk.mul hP).add hQ).congr_deriv ?_
    rw [zonalKernel_of_le hx1 (by linarith) hy2, hw, hρ]
    simp only [eval_sub, eval_neg, eval_mul, eval_add, eval_C, eval_X, hΓe]
    field_simp
    ring
  have h2 : ∫ y in x..1, zonalKernel x y * H.eval y =
      (-(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + 1)) *
          (-Γ.eval 1 + e * (1 - 1))) +
        (1 / 2) * (σ.eval 1 + 2 * e * Real.log (1 + 1) - e * 1)) -
      (-(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + x)) *
          (-Γ.eval x + e * (1 - x))) +
        (1 / 2) * (σ.eval x + 2 * e * Real.log (1 + x) - e * x)) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y =>
      -(((1 / 2) * Real.log (1 - x) - Real.log 2 + (1 / 2) * Real.log (1 + y)) *
          (-Γ.eval y + e * (1 - y))) + (1 / 2) * (σ.eval y + 2 * e * Real.log (1 + y) - e * y))
      ?_ hint2
    intro y hy
    rw [uIcc_of_le hx2.le] at hy
    obtain ⟨hy1, hy2⟩ := hy
    have hy3 : 0 < 1 + y := by linarith
    have hL : HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + y)) y := by
      exact ((hasDerivAt_id y).const_add 1).log hy3.ne'
    have hk : HasDerivAt (fun y => (1 / 2) * Real.log (1 - x) - Real.log 2 +
        (1 / 2) * Real.log (1 + y)) ((1 / 2) * (1 / (1 + y))) y :=
      (hL.const_mul (1 / 2)).const_add _
    have hP : HasDerivAt (fun y => -Γ.eval y + e * (1 - y)) (-Γ.derivative.eval y + e * (-1)) y :=
      (Γ.hasDerivAt y).neg.add (((hasDerivAt_id y).const_sub 1).const_mul e)
    have hQ : HasDerivAt (fun y => (1 / 2) * (σ.eval y + 2 * e * Real.log (1 + y) - e * y))
        ((1 / 2) * (σ.derivative.eval y + 2 * e * (1 / (1 + y)) - e * 1)) y :=
      (((σ.hasDerivAt y).add (hL.const_mul (2 * e))).sub ((hasDerivAt_id y).const_mul e)).const_mul
        (1 / 2)
    refine ((hk.mul hP).neg.add hQ).congr_deriv ?_
    rw [zonalKernel_of_ge hx2 (by linarith) hy1, hw, hσ]
    simp only [eval_sub, eval_mul, eval_C, eval_X, hΓe]
    field_simp
    ring
  rw [h1, h2]
  simp only [hΓe]
  norm_num
  ring

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Polynomial MeasureTheory Set

noncomputable section

theorem ZonalKernelPairing.proof : ZonalKernelPairing.Statement := by
  intro F H
  obtain ⟨GF, hGF, hdGF, hGFm, hGFp⟩ := exists_centredPrimitive_poly F
  obtain ⟨GH, hGH, hdGH, hGHm, hGHp⟩ := exists_centredPrimitive_poly H
  obtain ⟨w, hw⟩ := exists_eq_sq_sub_one_mul GH hGHm hGHp
  obtain ⟨ρ, hρ⟩ := exists_polynomial_antiderivative (-((X + C 1) * w))
  obtain ⟨σ, hσ⟩ := exists_polynomial_antiderivative ((C 1 - X) * w)
  set eF := uniformMean F.eval with heF
  set eH := uniformMean H.eval with heH
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    simp [ae_iff]
  have hinner : ∫ c₁ in (-1 : ℝ)..1, ∫ c₂ in (-1 : ℝ)..1,
        zonalKernel c₁ c₂ * F.eval c₁ * H.eval c₂ =
      ∫ x in (-1 : ℝ)..1,
        (-eH + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1)) * F.eval x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with x hx1 hxI
    rw [uIoc_of_le (by norm_num)] at hxI
    have hx : x ∈ Ioo (-1 : ℝ) 1 := ⟨hxI.1, lt_of_le_of_ne hxI.2 hx1⟩
    have hfun : (fun c₂ => zonalKernel x c₂ * F.eval x * H.eval c₂) =
        fun c₂ => F.eval x * (zonalKernel x c₂ * H.eval c₂) := by
      funext c₂
      ring
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_zonalKernel_mul_eval H w ρ σ eH (by rw [← hw, hdGH]) hρ hσ hx]
    ring
  have hrhs : ∫ c in (-1 : ℝ)..1, centredPrimitive F c * centredPrimitive H c / (1 - c ^ 2) =
      -∫ c in (-1 : ℝ)..1, GF.eval c * w.eval c := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with x hx1 hxI
    rw [uIoc_of_le (by norm_num)] at hxI
    have hxlt : x < 1 := lt_of_le_of_ne hxI.2 hx1
    have hpos : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos (sub_pos.2 hxlt) (show 0 < 1 + x by linarith [hxI.1])]
    rw [hGF, hGH, hw]
    simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_C]
    field_simp
    ring
  have hibp : ∫ x in (-1 : ℝ)..1,
        (-eH + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1)) * F.eval x =
      (-eH + (1 / 2) * (ρ.eval 1 - ρ.eval (-1) - σ.eval 1 + σ.eval 1)) * (GF.eval 1 + eF * (1 + 1)) -
        (-eH + (1 / 2) * (ρ.eval (-1) - ρ.eval (-1) - σ.eval (-1) + σ.eval 1)) *
          (GF.eval (-1) + eF * (1 + -1)) -
        ∫ x in (-1 : ℝ)..1, -w.eval x * (GF.eval x + eF * (1 + x)) := by
    have hu : ∀ x ∈ uIcc (-1 : ℝ) 1, HasDerivAt
        (fun x => -eH + (1 / 2) * (ρ.eval x - ρ.eval (-1) - σ.eval x + σ.eval 1)) (-w.eval x) x := by
      intro x _
      have h := ((((ρ.hasDerivAt x).sub_const (ρ.eval (-1))).sub (σ.hasDerivAt x)).add_const
        (σ.eval 1)).const_mul (1 / 2) |>.const_add (-eH)
      refine h.congr_deriv ?_
      rw [hρ, hσ]
      simp only [eval_neg, eval_mul, eval_add, eval_sub, eval_C, eval_X]
      ring
    have hv : ∀ x ∈ uIcc (-1 : ℝ) 1, HasDerivAt (fun x => GF.eval x + eF * (1 + x)) (F.eval x) x := by
      intro x _
      have h := (GF.hasDerivAt x).add (((hasDerivAt_id x).const_add 1).const_mul eF)
      refine h.congr_deriv ?_
      rw [hdGF]
      simp only [eval_sub, eval_C]
      ring
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((w.continuous.neg).intervalIntegrable _ _) (F.continuous.intervalIntegrable _ _)
  have hρint : ∫ x in (-1 : ℝ)..1, -((x + 1) * w.eval x) = ρ.eval 1 - ρ.eval (-1) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => ρ.eval x) ?_ ?_
    · intro x _
      refine (ρ.hasDerivAt x).congr_deriv ?_
      rw [hρ]
      simp
    · exact (((continuous_id.add continuous_const).mul w.continuous).neg).intervalIntegrable _ _
  have hsplit : ∫ x in (-1 : ℝ)..1, -w.eval x * (GF.eval x + eF * (1 + x)) =
      -(∫ x in (-1 : ℝ)..1, GF.eval x * w.eval x) + eF * ∫ x in (-1 : ℝ)..1, -((x + 1) * w.eval x) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg,
      ← intervalIntegral.integral_add]
    · congr 1
      funext x
      ring
    · exact ((GF.continuous.mul w.continuous).neg).intervalIntegrable _ _
    · exact (continuous_const.mul
        ((continuous_id.add continuous_const).mul w.continuous).neg).intervalIntegrable _ _
  rw [hinner, hrhs, hibp, hsplit, hρint, hGFm, hGFp]
  ring

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGKernelIdentity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial Finset

def kernelSum {S : Type*} [CommRing S] (a b : S) (k : ℕ) : S :=
  ∑ j ∈ range k, (a ^ (2 * j + 1) * b ^ (2 * k - 1 - 2 * j) - a ^ (2 * j) * b ^ (2 * k - 2 * j))

section kernelSum

variable {S : Type*} [CommRing S]

theorem kernelSum_zero (a b : S) : kernelSum a b 0 = 0 := by
  simp [kernelSum]

theorem kernelSum_succ (a b : S) (k : ℕ) :
    kernelSum a b (k + 1) =
      b ^ 2 * kernelSum a b k + (a ^ (2 * k + 1) * b - a ^ (2 * k) * b ^ 2) := by
  unfold kernelSum
  rw [sum_range_succ, mul_sum]
  congr 1
  · refine sum_congr rfl fun j hj => ?_
    have hj : j < k := mem_range.mp hj
    rw [show 2 * (k + 1) - 1 - 2 * j = (2 * k - 1 - 2 * j) + 2 by omega,
      show 2 * (k + 1) - 2 * j = (2 * k - 2 * j) + 2 by omega, pow_add, pow_add]
    ring
  · rw [show 2 * (k + 1) - 1 - 2 * k = 1 by omega, show 2 * (k + 1) - 2 * k = 2 by omega, pow_one]

theorem add_mul_kernelSum (a b : S) (k : ℕ) :
    (a + b) * kernelSum a b k = b * (a ^ (2 * k) - b ^ (2 * k)) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, show 2 * (k + 1) = 2 * k + 2 by ring]
    linear_combination b ^ 2 * ih

theorem map_kernelSum {T : Type*} [CommRing T] (φ : S →+* T) (a b : S) (k : ℕ) :
    φ (kernelSum a b k) = kernelSum (φ a) (φ b) k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [kernelSum, map_sum, map_sub, map_mul, map_pow]

theorem kernelSum_one_one (k : ℕ) : kernelSum (1 : S) 1 k = 0 := by
  simp [kernelSum]

theorem neg_one_pow_two_mul (k : ℕ) : (-1 : S) ^ (2 * k) = 1 := by
  rw [pow_mul]
  simp

theorem kernelSum_neg_one_neg_one (k : ℕ) : kernelSum (-1 : S) (-1) k = 0 := by
  induction k with
  | zero => exact kernelSum_zero _ _
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    ring

theorem kernelSum_one_neg_one (k : ℕ) : kernelSum (1 : S) (-1) k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih]
    push_cast
    ring

theorem kernelSum_neg_one_one (k : ℕ) : kernelSum (-1 : S) 1 k = -(2 * k : S) := by
  induction k with
  | zero => simp [kernelSum_zero]
  | succ k ih =>
    rw [kernelSum_succ, ih, pow_succ (-1 : S) (2 * k), neg_one_pow_two_mul]
    push_cast
    ring

end kernelSum

theorem gKernel_eq_kernelSum (R : Type*) [CommRing R] (k : ℕ) :
    gKernel R k = kernelSum (X 0 : MvPolynomial (Fin 2) R) (X 1) k := rfl

theorem eval_gKernel {R : Type*} [CommRing R] (k : ℕ) (a b : R) :
    eval ![a, b] (gKernel R k) = kernelSum a b k := by
  rw [gKernel_eq_kernelSum, map_kernelSum]
  simp

theorem gKernel_isHomogeneous (R : Type*) [CommRing R] (k : ℕ) :
    (gKernel R k).IsHomogeneous (2 * k) := by
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj : j < k := mem_range.mp hj
  refine IsHomogeneous.sub ?_ ?_
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j + 1)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 1 - 2 * j))
    rwa [show 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * k by omega] at h
  · have h := (isHomogeneous_X_pow (R := R) (0 : Fin 2) (2 * j)).mul
      (isHomogeneous_X_pow (R := R) (1 : Fin 2) (2 * k - 2 * j))
    rwa [show 2 * j + (2 * k - 2 * j) = 2 * k by omega] at h

theorem GKernelIdentity.proof : GKernelIdentity.Statement := by
  intro R _ k
  refine ⟨?_, gKernel_isHomogeneous R k, ?_, ?_, ?_, ?_, fun c => ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [gKernel_eq_kernelSum, add_mul_kernelSum]
  · rw [eval_gKernel, kernelSum_one_one]
  · rw [eval_gKernel, kernelSum_neg_one_neg_one]
  · rw [eval_gKernel, kernelSum_one_neg_one]
  · rw [eval_gKernel, kernelSum_neg_one_one]
  · have h := add_mul_kernelSum c (-1 : R) k
    rw [eval_gKernel, mul_comm]
    rw [neg_pow, pow_mul] at h
    rw [show c + -1 = c - 1 by ring] at h
    rw [h, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (-1 : R) c k
    rw [eval_gKernel, mul_comm, show c - 1 = -1 + c by ring, h, pow_mul, pow_mul]
    simp
    ring
  · have h := add_mul_kernelSum (1 : R) c k
    rw [eval_gKernel, mul_comm, h]
    simp
  · have h := add_mul_kernelSum c (1 : R) k
    rw [eval_gKernel, mul_comm, h]
    simp

end GroundTheory.Heights₂.Heights.FlagBundles
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGHatIdentity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial

noncomputable section

theorem pderiv_comm_two_variables (i j : Fin 2) (P : MvPolynomial (Fin 2) ℝ) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    simp only [pderiv_mul, map_add (f := _), hp, pderiv_X, Pi.single_apply]
    split_ifs <;> (try simp) <;> ring

theorem hasDerivAt_eval_fst (P : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    HasDerivAt (fun u => eval ![u, t] P) (eval ![s, t] (pderiv 0 P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const s a
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasDerivAt (fun u : ℝ => (![u, t] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 0 (X n))) s := by
      fin_cases n
      · simpa using hasDerivAt_id' s
      · simpa using hasDerivAt_const s t
    simp only [map_mul, eval_X, pderiv_mul, map_add (f := _)]
    exact hp.mul hX

theorem hasDerivAt_eval_snd (P : MvPolynomial (Fin 2) ℝ) (s t : ℝ) :
    HasDerivAt (fun u => eval ![s, u] P) (eval ![s, t] (pderiv 1 P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C, pderiv_C, map_zero]
    exact hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p n hp =>
    have hX : HasDerivAt (fun u : ℝ => (![s, u] : Fin 2 → ℝ) n) (eval ![s, t] (pderiv 1 (X n))) t := by
      fin_cases n
      · simpa using hasDerivAt_const t s
      · simpa using hasDerivAt_id' t
    simp only [map_mul, eval_X, pderiv_mul, map_add (f := _)]
    exact hp.mul hX

theorem continuous_eval_fst (P : MvPolynomial (Fin 2) ℝ) (t : ℝ) :
    Continuous fun u => eval ![u, t] P :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_fst P u t).continuousAt

theorem continuous_eval_snd (P : MvPolynomial (Fin 2) ℝ) (s : ℝ) :
    Continuous fun u => eval ![s, u] P :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_eval_snd P s u).continuousAt

theorem integral_eval_pderiv_fst (P : MvPolynomial (Fin 2) ℝ) (t a b : ℝ) :
    ∫ u in a..b, eval ![u, t] (pderiv 0 P) = eval ![b, t] P - eval ![a, t] P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_fst P u t)
    ((continuous_eval_fst _ t).intervalIntegrable a b)

theorem integral_eval_pderiv_snd (P : MvPolynomial (Fin 2) ℝ) (s a b : ℝ) :
    ∫ u in a..b, eval ![s, u] (pderiv 1 P) = eval ![s, b] P - eval ![s, a] P :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hasDerivAt_eval_snd P s u)
    ((continuous_eval_snd _ s).intervalIntegrable a b)

theorem gKernel_eval_diag (k : ℕ) (c : ℝ) : eval ![c, c] (gKernel ℝ k) = 0 := by
  unfold gKernel
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_sub, map_mul, map_pow, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' : j < k := Finset.mem_range.1 hj
  have h : 2 * j + 1 + (2 * k - 1 - 2 * j) = 2 * j + (2 * k - 2 * j) := by omega
  rw [← pow_add, ← pow_add, h, sub_self]

theorem GHatIdentity.proof (h0 : GKernelIdentity.Statement) : GHatIdentity.Statement := by
  intro k
  obtain ⟨-, -, h11, hmm, h1m, hm1, hc⟩ := h0 ℝ k
  set G := gKernel ℝ k with hGdef
  have hg : gMixed k = pderiv 0 (pderiv 1 G) := rfl
  have hg' : gMixed k = pderiv 1 (pderiv 0 G) := by rw [hg, pderiv_comm_two_variables]
  have hI1 : ∀ t : ℝ, ∫ x in (-1 : ℝ)..1, eval ![x, t] (gMixed k) =
      eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G) := fun t => by
    rw [hg]; exact integral_eval_pderiv_fst _ _ _ _
  have hI2 : ∀ s : ℝ, ∫ y in (-1 : ℝ)..1, eval ![s, y] (gMixed k) =
      eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G) := fun s => by
    rw [hg']; exact integral_eval_pderiv_snd _ _ _ _
  have hsq : squareMean (gMixed k) = k := by
    unfold squareMean
    simp only [hI2]
    rw [intervalIntegral.integral_sub ((continuous_eval_fst _ _).intervalIntegrable _ _)
      ((continuous_eval_fst _ _).intervalIntegrable _ _), integral_eval_pderiv_fst,
      integral_eval_pderiv_fst, h11, hmm, h1m, hm1]
    ring
  refine ⟨hsq, fun c => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hc c
  have hdiag := gKernel_eval_diag k c
  rw [← hGdef] at hdiag
  unfold doublyCentred
  simp only [hI1, hI2, hsq]
  have hin : ∀ s : ℝ, ∫ t in (-1 : ℝ)..c,
      (eval ![s, t] (gMixed k) - 1 / 2 * (eval ![1, t] (pderiv 1 G) - eval ![-1, t] (pderiv 1 G)) -
        1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) + (k : ℝ)) =
      (eval ![s, c] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) -
        1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) -
        (c + 1) * (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) := by
    intro s
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => eval ![s, t] (pderiv 0 G) - 1 / 2 * (eval ![1, t] G - eval ![-1, t] G) -
        (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k) * t)]
    · ring
    · intro t _
      have := ((hasDerivAt_eval_snd (pderiv 0 G) s t).sub
        (((hasDerivAt_eval_snd G 1 t).sub (hasDerivAt_eval_snd G (-1) t)).const_mul (1 / 2))).sub
        ((hasDerivAt_id t).const_mul
          (1 / 2 * (eval ![s, 1] (pderiv 0 G) - eval ![s, -1] (pderiv 0 G)) - k))
      convert this using 1
      · funext u; simp only [Pi.sub_apply, id]
      · rw [hg']; ring
    · exact (((continuous_eval_snd _ s).sub (continuous_const.mul
        ((continuous_eval_snd _ 1).sub (continuous_eval_snd _ (-1))))).sub
        continuous_const |>.add continuous_const).intervalIntegrable _ _
  simp only [hin]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => eval ![s, c] G - eval ![s, -1] G -
      1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G)) * s -
      (c + 1) * (1 / 2 * (eval ![s, 1] G - eval ![s, -1] G) - k * s))]
  · linear_combination (1 / 2 : ℝ) * e1 + (1 / 2 : ℝ) * e2 - (1 / 2 : ℝ) * e3 - (1 / 2 : ℝ) * e4 +
      hdiag + (1 + c) / 2 * h1m - c * hmm + (1 + c) / 2 * hm1
  · intro s _
    have := (((hasDerivAt_eval_fst G s c).sub (hasDerivAt_eval_fst G s (-1))).sub
      ((hasDerivAt_id s).const_mul
        (1 / 2 * ((eval ![1, c] G - eval ![1, -1] G) - (eval ![-1, c] G - eval ![-1, -1] G))))).sub
      ((((hasDerivAt_eval_fst G s 1).sub (hasDerivAt_eval_fst G s (-1))).const_mul (1 / 2)).sub
        ((hasDerivAt_id s).const_mul (k : ℝ)) |>.const_mul (c + 1))
    convert (preTransparency := .reducible) this using 1
    · funext u
      simp only [Pi.sub_apply, id]
    · ring
  · exact ((((continuous_eval_fst _ c).sub (continuous_eval_fst _ (-1))).sub continuous_const).sub
      (continuous_const.mul ((continuous_const.mul ((continuous_eval_fst _ 1).sub
        (continuous_eval_fst _ (-1)))).sub continuous_const))).intervalIntegrable _ _

end

end GroundTheory.Heights₂.Heights.FlagBundles
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open Real
open scoped InnerProductSpace

theorem norm_circleMap_sub_ofReal_sq (r φ : ℝ) :
    ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 = 1 + r ^ 2 - 2 * r * Real.cos φ := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [circleMap, Complex.exp_re, Complex.exp_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem ZonalKernel.proof : ZonalKernel.Statement := by
  intro c₁ h₁ c₂ h₂ hne
  obtain ⟨h₁l, h₁u⟩ := h₁
  obtain ⟨h₂l, h₂u⟩ := h₂
  have hs₁ : Real.sqrt (1 - c₁ ^ 2) ^ 2 = 1 - c₁ ^ 2 := Real.sq_sqrt (by nlinarith)
  have hs₂ : Real.sqrt (1 - c₂ ^ 2) ^ 2 = 1 - c₂ ^ 2 := Real.sq_sqrt (by nlinarith)
  set B := Real.sqrt (1 - c₁ ^ 2) * Real.sqrt (1 - c₂ ^ 2) with hBdef
  set A := 1 - c₁ * c₂ with hAdef
  set D := |c₁ - c₂| with hDdef
  have hD : 0 < D := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hA : 0 ≤ A := by nlinarith
  have hB : 0 ≤ B := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hABD : A ^ 2 = B ^ 2 + D ^ 2 := by
    rw [hBdef, mul_pow, hs₁, hs₂, hDdef, sq_abs]; ring
  have hAD : 0 < A + D := by linarith
  set r := B / (A + D) with hrdef
  have hr0 : 0 ≤ r := div_nonneg hB hAD.le
  have hBlt : B < A + D := by nlinarith
  have hr1 : r < 1 := (div_lt_one hAD).mpr hBlt
  have key : ∀ φ : ℝ, kernelL ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ =
      (1 / 2) * Real.log ((A + D) / 4) + Real.log ‖circleMap 0 1 φ - (r : ℂ)‖ := by
    intro φ
    have hinner : ⟪spherePoint c₁ 0, spherePoint c₂ φ⟫_ℝ = c₁ * c₂ + B * Real.cos φ := by
      simp [spherePoint, PiLp.inner_apply, Fin.sum_univ_three, hBdef]
      ring
    have hne0 : ‖circleMap 0 1 φ - (r : ℂ)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro h
      have := congrArg norm h
      rw [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
      norm_num at this
      linarith
    have hfac : (1 - (c₁ * c₂ + B * Real.cos φ)) / 2 =
        (A + D) / 4 * ‖circleMap 0 1 φ - (r : ℂ)‖ ^ 2 := by
      rw [norm_circleMap_sub_ofReal_sq, hrdef]
      field_simp
      linear_combination (2 : ℝ) * hABD
    rw [kernelL, hinner, hfac, Real.log_mul (by positivity) (pow_ne_zero 2 hne0), Real.log_pow]
    push_cast
    ring
  simp only [key]
  have hint : IntervalIntegrable (fun φ : ℝ => Real.log ‖circleMap 0 1 φ - (r : ℂ)‖)
      MeasureTheory.volume 0 (2 * π) := circleIntegrable_log_norm_sub_const (a := (r : ℂ)) (c := 0) 1
  rw [intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const]
  have havg := circleAverage_log_norm_sub_const₀ (a := (r : ℂ))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
  rw [circleAverage_def, smul_eq_mul] at havg
  have hpi : (2 * π) ≠ 0 := by positivity
  have hsum : A + D = (1 + max c₁ c₂) * (1 - min c₁ c₂) := by
    rcases le_total c₁ c₂ with h | h
    · rw [max_eq_right h, min_eq_left h, hDdef, abs_of_nonpos (by linarith), hAdef]; ring
    · rw [max_eq_left h, min_eq_right h, hDdef, abs_of_nonneg (by linarith), hAdef]; ring
  rw [zonalKernel, ← hsum, mul_add, havg, smul_eq_mul, sub_zero, ← mul_assoc, inv_mul_cancel₀ hpi]
  ring

end GroundTheory.Heights₂.Heights.FlagBundles
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

theorem GKernelIdentity.full : GKernelIdentity.Statement :=
  GKernelIdentity.proof

theorem ZonalKernel.full : ZonalKernel.Statement :=
  ZonalKernel.proof

theorem SphereLongitudeCoordinates.full : SphereLongitudeCoordinates.Statement :=
  SphereLongitudeCoordinates.proof

theorem ZonalHeightReduction.full : ZonalHeightReduction.Statement :=
  ZonalHeightReduction.proof SphereLongitudeCoordinates.full ZonalKernel.full

theorem ZonalKernelPairing.full : ZonalKernelPairing.Statement :=
  ZonalKernelPairing.proof

theorem ZonalBilinearFormula.full : ZonalBilinearFormula.Statement :=
  ZonalBilinearFormula.proof ZonalHeightReduction.full ZonalKernelPairing.full

theorem GHatIdentity.full : GHatIdentity.Statement :=
  GHatIdentity.proof GKernelIdentity.full

theorem FibreConstantClosedForm.full : FibreConstantClosedForm.Statement :=
  FibreConstantClosedForm.proof ZonalBilinearFormula.full GHatIdentity.full

theorem fibreConstant_eq (k : ℕ) :
    fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) :=
  FibreConstantClosedForm.full.1 k

theorem FibreIntegralInvariant.full : FibreIntegralInvariant.Statement :=
  FibreIntegralInvariant.proof FibreConstantClosedForm.full

end GroundTheory.Heights₂.Heights.FlagBundles
