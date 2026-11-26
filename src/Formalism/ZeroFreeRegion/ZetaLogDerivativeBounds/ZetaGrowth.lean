module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.RiemannZetaOneEqOneSubOfRePos

@[expose] public section

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth
open Complex Filter Topology

noncomputable section

namespace Formalism.ZF

open ComplexPowerDifferenceIntegral in
lemma norm_Dz_le {s : ℂ} (hs : 0 < s.re) :
    ‖Dz s‖ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
  set σ := s.re with hσ

  have hkey : ∀ x : ℝ, 1 ≤ x → σ * (x + 1) ^ (-σ - 1) ≤ x ^ (-σ) - (x + 1) ^ (-σ) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < x + 1 := by linarith
    have hA : 0 < (x + 1) ^ σ := Real.rpow_pos_of_pos hy0 σ
    have hB : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have hq : 0 < (x + 1) / x := div_pos hy0 hx0
    have hr : ((x + 1) / x) ^ σ = (x + 1) ^ σ / x ^ σ := Real.div_rpow hy0.le hx0.le σ
    have hlog : 1 / (x + 1) ≤ Real.log ((x + 1) / x) := by
      have := Real.one_sub_inv_le_log_of_pos hq
      have e : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
      linarith
    have hexp : 1 + σ / (x + 1) ≤ (x + 1) ^ σ / x ^ σ := by
      rw [← hr, Real.rpow_def_of_pos hq]
      have h1 := Real.add_one_le_exp (Real.log ((x + 1) / x) * σ)
      have h2 : σ / (x + 1) ≤ Real.log ((x + 1) / x) * σ := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_right hlog hs.le
      linarith
    rw [Real.rpow_sub_one hy0.ne', Real.rpow_neg hy0.le, Real.rpow_neg hx0.le]
    have e1 : σ * ((x + 1) ^ σ)⁻¹ / (x + 1) = σ / (x + 1) * ((x + 1) ^ σ)⁻¹ := by ring
    have e2 : (x ^ σ)⁻¹ - ((x + 1) ^ σ)⁻¹ = ((x + 1) ^ σ / x ^ σ - 1) * ((x + 1) ^ σ)⁻¹ := by
      field_simp
    rw [mul_div_assoc', e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hA.le)
  have hS : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), ((i : ℝ) + 1) ^ (-σ - 1)
      ≤ 1 + (1 - ((N : ℝ) + 1) ^ (-σ)) / σ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hk := hkey ((N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)])
      have hk' : ((N : ℝ) + 1 + 1) ^ (-σ - 1) ≤ (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        rw [le_div_iff₀ hs]
        linarith
      push_cast
      have e : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ + (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ
          = (1 - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        field_simp
        ring
      linarith
  have hT : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ := by
    intro n
    rcases n with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · refine (hS N).trans ?_
      have h0 : 0 ≤ ((N : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      have : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ := div_le_div_of_nonneg_right (by linarith) hs.le
      linarith
  have hC : 0 ≤ ‖s - 1‖ * ‖s‖ := by positivity
  show ‖∑' n, dz s n‖ ≤ _
  calc ‖∑' n, dz s n‖ ≤ ∑' n, ‖dz s n‖ := norm_tsum_le_tsum_norm (summable_norm_dz hs)
    _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := by
      refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun n => ?_
      calc ∑ i ∈ Finset.range n, ‖dz s i‖
          ≤ ∑ i ∈ Finset.range n, ‖s - 1‖ * ‖s‖ * ((i : ℝ) + 1) ^ (-σ - 1) :=
            Finset.sum_le_sum fun i _ => norm_dz_le hs i
        _ = ‖s - 1‖ * ‖s‖ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) := by
            rw [Finset.mul_sum]
        _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := mul_le_mul_of_nonneg_left (hT n) hC

theorem growthBound : ZetaGrowth := by
  intro s hs hs1
  have h1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    unfold riemannZeta₁ riemannZeta₀
    rw [if_neg hs1, mul_sub, mul_inv_cancel₀ (sub_ne_zero.2 hs1)]
    ring
  have hD := norm_Dz_le hs
  have hne : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hpos : 0 < ‖s - 1‖ := norm_pos_iff.2 hne
  have hz : riemannZeta s = (s - ComplexPowerDifferenceIntegral.Dz s) / (s - 1) := by
    rw [← ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hs, h1]
    field_simp
  rw [hz, norm_div, div_le_iff₀ hpos]
  have hs' : ‖s‖ ≤ ‖s - 1‖ + 1 := by simpa using norm_add_le (s - 1) 1
  calc ‖s - ComplexPowerDifferenceIntegral.Dz s‖ ≤ ‖s‖ + ‖ComplexPowerDifferenceIntegral.Dz s‖ := norm_sub_le _ _
    _ ≤ (‖s - 1‖ + 1) + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := add_le_add hs' hD
    _ = (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) * ‖s - 1‖ := by
        field_simp

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.IntegralEqIntervalIntegralAddCompl
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

theorem norm_sub_le_of_rectangle_identity (Sz R V0 V1 E a b : ℂ) (hS : Sz = (1 / (2 * Real.pi) : ℂ) * (V0 + E))
    (hrect : a - b + I * V0 - I * V1 = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Sz - R‖ ≤ ‖E‖ + ‖a‖ + ‖b‖ + ‖V1‖ := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h1 : (2 * Real.pi : ℂ) * (Sz - R) = (V0 - 2 * Real.pi * R) + E := by
    rw [hS]; field_simp; ring
  have h2 : I * (V0 - 2 * Real.pi * R) = -(a - b - I * V1) := by linear_combination hrect
  have h3 : ‖V0 - 2 * Real.pi * R‖ = ‖a - b - I * V1‖ := by
    have := congrArg norm h2
    rwa [norm_mul, Complex.norm_I, one_mul, norm_neg] at this
  have h4 : ‖(2 * Real.pi : ℂ) * (Sz - R)‖ = 2 * Real.pi * ‖Sz - R‖ := by
    rw [norm_mul]
    congr 1
    have : (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [← h4, h1]
  calc ‖V0 - 2 * Real.pi * R + E‖ ≤ ‖V0 - 2 * Real.pi * R‖ + ‖E‖ := norm_add_le _ _
    _ = ‖a - b - I * V1‖ + ‖E‖ := by rw [h3]
    _ ≤ (‖a‖ + ‖b‖ + ‖V1‖) + ‖E‖ := by
        gcongr
        calc ‖a - b - I * V1‖ ≤ ‖a - b‖ + ‖I * V1‖ := norm_sub_le _ _
          _ ≤ ‖a‖ + ‖b‖ + ‖V1‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]; gcongr; exact norm_sub_le _ _
    _ = ‖E‖ + ‖a‖ + ‖b‖ + ‖V1‖ := by ring

theorem integral_eq_intervalIntegral_add_compl (f : ℝ → ℂ) (hf : Integrable f) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t, f t = (∫ t in (-T)..T, f t) + ∫ t in (Set.Ioc (-T) T)ᶜ, f t := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_add_compl measurableSet_Ioc hf]

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormIntegralComplLe
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

theorem norm_integral_compl_le (f : ℝ → ℂ) (B T : ℝ) (hB : 0 ≤ B) (hT : 0 < T)
    (hf : ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ B / t ^ 2) :
    ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ 2 * Real.pi * B / T := by
  have hSm : MeasurableSet ((Set.Ioc (-T) T)ᶜ) := measurableSet_Ioc.compl
  have hg_int : Integrable (fun t : ℝ => 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_div hT.ne').const_mul _
  have hbound : ∀ t ∈ (Set.Ioc (-T) T)ᶜ, ‖f t‖ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ := by
    intro t ht
    have hTt : T ≤ |t| := by
      simp only [Set.mem_compl_iff, Set.mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have ht2 : T ^ 2 ≤ t ^ 2 := by
      have := pow_le_pow_left₀ hT.le hTt 2
      rwa [sq_abs] at this
    have htpos : 0 < t ^ 2 := lt_of_lt_of_le (by positivity) ht2
    calc ‖f t‖ ≤ B / t ^ 2 := hf t hTt
      _ ≤ 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ := by
        rw [show 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * B / (T ^ 2 + t ^ 2) by
          field_simp]
        rw [div_le_div_iff₀ htpos (by positivity)]
        nlinarith
  have h1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, f t‖ ≤ ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ :=
    norm_integral_le_of_norm_le hg_int.integrableOn (ae_restrict_of_forall_mem hSm hbound)
  have h2 : ∫ t in (Set.Ioc (-T) T)ᶜ, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ ≤
      ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ :=
    setIntegral_le_integral hg_int (Filter.Eventually.of_forall (fun t => by positivity))
  have h3 : ∫ t, 2 * B / T ^ 2 * (1 + (t / T) ^ 2)⁻¹ = 2 * Real.pi * B / T := by
    rw [integral_const_mul]
    have e := MeasureTheory.Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) T
    rw [e, integral_univ_inv_one_add_sq, abs_of_pos hT]
    field_simp
    ring
  linarith

theorem pow_three_mul_exp_le (c s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) :
    s ^ 3 * Real.exp (-(c * s / 4)) ≤ 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by
  have hs0 : 0 ≤ c * s / 8 := by positivity
  have hA : 0 < Real.exp (-(c / 8) * s) := Real.exp_pos _
  have hEA : Real.exp (c * s / 8) * Real.exp (-(c / 8) * s) = 1 := by
    rw [← Real.exp_add, show c * s / 8 + -(c / 8) * s = 0 by ring, Real.exp_zero]
  have hsq : Real.exp (-(c * s / 4)) = Real.exp (-(c / 8) * s) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfact : (c * s / 8) ^ 3 ≤ 6 * Real.exp (c * s / 8) := by
    have h := Real.pow_div_factorial_le_exp (c * s / 8) hs0 3
    norm_num [Nat.factorial] at h
    linarith
  have hkey : (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ≤ 6 := by
    nlinarith [mul_le_mul_of_nonneg_right hfact hA.le]
  have hs3 : s ^ 3 = (8 / c) ^ 3 * (c * s / 8) ^ 3 := by
    field_simp
  rw [hsq, hs3]
  have hk : 0 < (8 / c) ^ 3 := by positivity
  calc (8 / c) ^ 3 * (c * s / 8) ^ 3 * Real.exp (-(c / 8) * s) ^ 2
      = (8 / c) ^ 3 * ((c * s / 8) ^ 3 * Real.exp (-(c / 8) * s)) * Real.exp (-(c / 8) * s) := by ring
    _ ≤ (8 / c) ^ 3 * 6 * Real.exp (-(c / 8) * s) := by gcongr
    _ = 6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s) := by ring

theorem log_exp_add_two_bounds (c s : ℝ) (hc : 0 < c) (hs : 8 / c ≤ s) :
    1 ≤ Real.exp (c * s / 4) ∧ 1 ≤ Real.log (Real.exp (c * s / 4) + 2) ∧
      Real.log (Real.exp (c * s / 4) + 2) ≤ c * s / 2 := by
  have hcs : 8 ≤ c * s := by
    rw [div_le_iff₀ hc] at hs
    linarith
  have hE1 : 1 ≤ Real.exp (c * s / 4) := Real.one_le_exp (by linarith)
  have hE2 : Real.exp 2 ≤ Real.exp (c * s / 4) := Real.exp_le_exp.mpr (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨hE1, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  · rw [Real.log_le_iff_le_exp (by positivity)]
    have e : Real.exp (c * s / 2) = Real.exp (c * s / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    nlinarith

theorem exp_mul_rpow_le (y c L s : ℝ) (hy : 0 < y) (hℓ : Real.log y = s ^ 2) (hc : 0 < c)
    (hc2 : c ≤ 1 / 2) (hL : 0 < L) (hLs : L ≤ c * s / 2) (hs : 0 < s) :
    Real.exp (c * s / 4) * y ^ (1 - c / L) ≤ y * Real.exp (-(c * s / 4)) := by
  have hy' : y = Real.exp (s ^ 2) := by rw [← hℓ, Real.exp_log hy]
  rw [Real.rpow_def_of_pos hy, hℓ]
  conv_rhs => rw [hy']
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have key : c * s / 2 ≤ s ^ 2 * (c / L) := by
    rw [show s ^ 2 * (c / L) = (c * s ^ 2) / L by ring, le_div_iff₀ hL]
    have hcs : 0 < c * s := mul_pos hc hs
    have hL4 : L ≤ s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hL4 hcs.le]
  nlinarith [key]

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFactor
open Complex Set Filter Topology

noncomputable section

namespace Formalism.ZF

private theorem closedBall_mem_nhds_of_mem_closedBall_lt {z₀ z : ℂ} {r R₁ : ℝ} (hR : R₁ < r)
    (hz : z ∈ Metric.closedBall z₀ R₁) : Metric.closedBall z₀ r ∈ 𝓝 z :=
  Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hR hz))
    Metric.ball_subset_closedBall

private theorem natCast_analyticOrderNatAt_of_ne_top {f : ℂ → ℂ} {z : ℂ}
    (h : analyticOrderAt f z ≠ ⊤) : ((analyticOrderNatAt f z : ℕ) : ℕ∞) = analyticOrderAt f z :=
  ENat.natCast_toNat h

theorem exists_factorization_of_sum_order (z₀ : ℂ) (r R₁ : ℝ) (hR : R₁ < r) :
    ∀ N : ℕ, ∀ (f : ℂ → ℂ) (Z : Finset ℂ), DifferentiableOn ℂ f (Metric.closedBall z₀ r) →
      (∀ ρ ∈ Z, ρ ∈ Metric.closedBall z₀ R₁) →
      (∀ z ∈ Metric.closedBall z₀ R₁, f z = 0 → z ∈ Z) →
      (∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) →
      ∑ ρ ∈ Z, analyticOrderNatAt f ρ = N →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
        (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
        ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by
  classical
  intro N
  induction N with
  | zero =>
    intro f Z hf hZ hzero htop hsum
    have h0 : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = 0 := Finset.sum_eq_zero_iff.mp hsum
    refine ⟨f, hf, ?_, ?_⟩
    · intro z hz hfz
      have hzZ := hzero z hz hfz
      have han : AnalyticAt ℂ f z := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hz)
      have hord : analyticOrderAt f z = 0 := by
        rw [← natCast_analyticOrderNatAt_of_ne_top (htop z hzZ)]
        simp [h0 z hzZ]
      exact (han.analyticOrderAt_eq_zero.mp hord) hfz
    · intro z _
      rw [Finset.prod_eq_one (fun ρ hρ => by rw [h0 ρ hρ, pow_zero]), one_mul]
  | succ n ih =>
    intro f Z hf hZ hzero htop hsum
    obtain ⟨ρ₀, hρ₀Z, hρ₀⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact Nat.succ_ne_zero n)
    have hρ₀B := hZ ρ₀ hρ₀Z
    have hanρ₀ : AnalyticAt ℂ f ρ₀ := hf.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)
    have hfρ₀ : f ρ₀ = 0 := by
      by_contra hne
      apply hρ₀
      have h0 : analyticOrderAt f ρ₀ = 0 := hanρ₀.analyticOrderAt_eq_zero.mpr hne
      simp [analyticOrderNatAt, h0]
    obtain ⟨g, hg⟩ : ∃ g : ℂ → ℂ, g = dslope f ρ₀ := ⟨_, rfl⟩
    have hfg : ∀ z, f z = (z - ρ₀) * g z := by
      intro z
      have h := sub_smul_dslope f ρ₀ z
      rw [hfρ₀, sub_zero, smul_eq_mul, ← hg] at h
      exact h.symm
    have hgd : DifferentiableOn ℂ g (Metric.closedBall z₀ r) := by
      rw [hg]
      exact (Complex.differentiableOn_dslope (closedBall_mem_nhds_of_mem_closedBall_lt hR hρ₀B)).mpr hf
    have hfeq : f = (fun z : ℂ => z - ρ₀) * g := funext fun z => hfg z
    have key : ∀ ρ ∈ Z,
        analyticOrderAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderAt g ρ := by
      intro ρ hρ
      have hB := hZ ρ hρ
      have hga : AnalyticAt ℂ g ρ := hgd.analyticAt (closedBall_mem_nhds_of_mem_closedBall_lt hR hB)
      have hla : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ := analyticAt_id.sub analyticAt_const
      rw [hfeq, analyticOrderAt_mul hla hga]
      congr 1
      split_ifs with hρρ₀
      · rw [hρρ₀]
        have hl : AnalyticAt ℂ (fun z : ℂ => z - ρ₀) ρ₀ := analyticAt_id.sub analyticAt_const
        have h1 := (hl.analyticOrderAt_eq_natCast (n := 1)).mpr
          ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun z => by simp⟩
        simpa using h1
      · exact hla.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρρ₀)
    have keyN : ∀ ρ ∈ Z,
        analyticOrderNatAt f ρ = (if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ ∧
          analyticOrderAt g ρ ≠ ⊤ := by
      intro ρ hρ
      have hk := key ρ hρ
      have ht := htop ρ hρ
      have hgt : analyticOrderAt g ρ ≠ ⊤ := by
        intro h
        apply ht
        rw [hk, h]
        simp
      refine ⟨?_, hgt⟩
      have h1 : ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) =
          (((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ : ℕ) : ℕ∞) := by
        rw [natCast_analyticOrderNatAt_of_ne_top ht, hk, Nat.cast_add,
          natCast_analyticOrderNatAt_of_ne_top hgt]
        split_ifs <;> simp
      exact_mod_cast h1
    have hsumg : ∑ ρ ∈ Z, analyticOrderNatAt g ρ = n := by
      have hs : ∑ ρ ∈ Z, analyticOrderNatAt f ρ =
          ∑ ρ ∈ Z, ((if ρ = ρ₀ then 1 else 0) + analyticOrderNatAt g ρ) :=
        Finset.sum_congr rfl fun ρ hρ => (keyN ρ hρ).1
      rw [hs, Finset.sum_add_distrib] at hsum
      simp only [Finset.sum_ite_eq', hρ₀Z, if_true] at hsum
      omega
    have hzg : ∀ z ∈ Metric.closedBall z₀ R₁, g z = 0 → z ∈ Z :=
      fun z hz h0 => hzero z hz (by rw [hfg z, h0, mul_zero])
    obtain ⟨h, hhd, hh0, hhf⟩ := ih g Z hgd hZ hzg (fun ρ hρ => (keyN ρ hρ).2) hsumg
    refine ⟨h, hhd, hh0, fun z hz => ?_⟩
    have hone : ∏ ρ ∈ Z, (z - ρ) ^ (if ρ = ρ₀ then 1 else 0) = z - ρ₀ := by
      rw [Finset.prod_eq_single ρ₀ (fun b _ hb => by simp [hb]) (fun h => absurd hρ₀Z h)]
      simp
    have hprod : ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ =
        (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
      calc ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ
          = ∏ ρ ∈ Z, ((z - ρ) ^ (if ρ = ρ₀ then 1 else 0) * (z - ρ) ^ analyticOrderNatAt g ρ) :=
            Finset.prod_congr rfl fun ρ hρ => by rw [(keyN ρ hρ).1, pow_add]
        _ = (z - ρ₀) * ∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt g ρ := by
            rw [Finset.prod_mul_distrib, hone]
    rw [hfg z, hhf z hz, hprod, mul_assoc]

theorem zeroFactorization : ZeroFactor := by
  intro f z₀ r R₁ hR₁ hR hf hf0
  have hr : 0 < r := hR₁.trans hR
  have hU : AnalyticOnNhd ℂ f (Metric.ball z₀ r) :=
    (hf.mono Metric.ball_subset_closedBall).analyticOnNhd Metric.isOpen_ball
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hpre : IsPreconnected (Metric.ball z₀ r) := (convex_ball z₀ r).isPreconnected
  have hnotzero : ∀ x ∈ Metric.ball z₀ r, ¬ (∀ᶠ w in 𝓝 x, f w = 0) := by
    intro x hx hev
    have hEq := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hx hev
    exact hf0 (hEq hz₀)
  have hisol : ∀ x ∈ Metric.ball z₀ r, ∀ᶠ w in 𝓝[≠] x, f w ≠ 0 := fun x hx =>
    ((hU x hx).eventually_eq_zero_or_eventually_ne_zero).resolve_left (hnotzero x hx)
  have htop : ∀ x ∈ Metric.ball z₀ r, analyticOrderAt f x ≠ ⊤ := fun x hx h =>
    hnotzero x hx (analyticOrderAt_eq_top.mp h)
  have hSsub : Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0} ⊆ Metric.ball z₀ r :=
    fun x hx => Metric.closedBall_subset_ball hR hx.1
  have hScpt : IsCompact (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}) :=
    (isCompact_closedBall z₀ R₁).of_isClosed_subset
      ((hf.continuousOn.mono (Metric.closedBall_subset_closedBall hR.le)).preimage_isClosed_of_isClosed
        Metric.isClosed_closedBall isClosed_singleton)
      Set.inter_subset_left
  have hSdisc : DiscreteTopology (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0} : Set ℂ) := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    refine Filter.inf_principal_eq_bot.mpr ?_
    filter_upwards [hisol x (hSsub hx)] with w hw hwS
    exact hw hwS.2
  have hfin : (Metric.closedBall z₀ R₁ ∩ f ⁻¹' {0}).Finite := by
    exact hScpt.finite ⟨hSdisc⟩
  have hmem : ∀ ρ : ℂ, ρ ∈ hfin.toFinset ↔ (ρ ∈ Metric.closedBall z₀ R₁ ∧ f ρ = 0) := by
    intro ρ
    rw [Set.Finite.mem_toFinset]
    rfl
  obtain ⟨h, hhd, hh0, hhf⟩ := exists_factorization_of_sum_order z₀ r R₁ hR _ f hfin.toFinset hf
    (fun ρ hρ => ((hmem ρ).mp hρ).1) (fun z hz hfz => (hmem z).mpr ⟨hz, hfz⟩)
    (fun ρ hρ => htop ρ (Metric.closedBall_subset_ball hR ((hmem ρ).mp hρ).1)) rfl
  refine ⟨hfin.toFinset, analyticOrderNatAt f, h, hmem, ?_, hhd, hh0, hhf⟩
  intro ρ hρ
  obtain ⟨hB, hfρ⟩ := (hmem ρ).mp hρ
  have hball : ρ ∈ Metric.ball z₀ r := Metric.closedBall_subset_ball hR hB
  have hne : analyticOrderAt f ρ ≠ 0 := fun h0 =>
    ((hU ρ hball).analyticOrderAt_eq_zero.mp h0) hfρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hne
  rw [← natCast_analyticOrderNatAt_of_ne_top (htop ρ hball)]
  simp [h0]

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf
open Complex Filter Topology Metric

noncomputable section

namespace Formalism.ZF

private theorem hasDerivAt_sub_pow_of_sub_ne_zero (a z : ℂ) (n : ℕ) (h : z - a ≠ 0) :
    HasDerivAt (fun w => (w - a) ^ n) ((z - a) ^ n * ((n : ℂ) / (z - a))) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := by
    simpa using (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1) * 1) z :=
    (hasDerivAt_pow n (z - a)).comp z h1
  refine h2.congr_deriv ?_
  rcases n with _ | k
  · simp
  · rw [pow_succ, Nat.add_sub_cancel]
    have hinv : (z - a) * (z - a)⁻¹ = 1 := mul_inv_cancel₀ h
    linear_combination (-((z - a) ^ k * ((k + 1 : ℕ) : ℂ))) * hinv

private theorem hasDerivAt_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    HasDerivAt (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ)
      ((∏ ρ ∈ Z, (z - ρ) ^ m ρ) * ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) z := by
  classical
  revert hz
  induction Z using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.prod_empty, Finset.sum_empty, mul_zero]
    exact hasDerivAt_const z (1 : ℂ)
  | insert =>
    rename_i a s ha ih
    intro hz
    have hs : ∀ ρ ∈ s, z - ρ ≠ 0 := fun ρ hρ => hz ρ (Finset.mem_insert_of_mem hρ)
    have hza : z - a ≠ 0 := hz a (Finset.mem_insert_self a s)
    have hd := (hasDerivAt_sub_pow_of_sub_ne_zero a z (m a) hza).mul (ih hs)
    beta_reduce at hd
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    refine hd.congr_deriv ?_
    ring

lemma landauLocal_logDeriv_prod (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hz : ∀ ρ ∈ Z, z - ρ ≠ 0) :
    logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_apply, (hasDerivAt_prod_sub_pow Z m z hz).deriv]
  have hP : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hz ρ hρ)
  exact (div_eq_iff hP).mpr (mul_comm _ _)

private theorem pow_le_pow_left_of_nonneg_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact mul_le_mul ih hab ha (le_trans (pow_nonneg ha k) ih)

private theorem norm_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (w : ℂ) :
    ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖w - ρ‖ ^ m ρ := by
  simp only [norm_prod, norm_pow]

private theorem div_add_div_sub_eq_div (P S H D : ℂ) (hP : P ≠ 0) (hH : H ≠ 0) :
    (P * S * H + P * D) / (P * H) - S = D / H := by
  rw [sub_eq_iff_eq_add, div_eq_iff (mul_ne_zero hP hH)]
  have hHH : H⁻¹ * H = 1 := inv_mul_cancel₀ hH
  linear_combination (-(P * D)) * hHH

theorem localZeroExpansionOfFactorization : LandauLocalOf := by
  unfold LandauLocalOf LandauLocal
  intro hfac hlog f z₀ r M hr hM hf hf0 hbound
  classical
  have hr3 : 0 < r / 3 := by positivity
  obtain ⟨Z, m, h, hZ, hm, hh, hh0, hfeq⟩ := hfac f z₀ r (r / 3) hr3 (by linarith) hf hf0
  have hZball : ∀ ρ ∈ Z, ‖ρ - z₀‖ ≤ r / 3 := fun ρ hρ => by
    have := ((hZ ρ).1 hρ).1
    rwa [Metric.mem_closedBall, dist_eq_norm] at this
  have hZzero : ∀ ρ ∈ Z, f ρ = 0 := fun ρ hρ => ((hZ ρ).1 hρ).2
  have hz₀mem : z₀ ∈ Metric.closedBall z₀ r := Metric.mem_closedBall_self hr.le
  have hfz₀ := hfeq z₀ hz₀mem
  have hhz₀ : h z₀ ≠ 0 := by
    intro h0; apply hf0; rw [hfz₀, h0, mul_zero]
  have hPz₀le : ‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => pow_nonneg (norm_nonneg _) _) ?_
    intro ρ hρ
    have h1 : ‖z₀ - ρ‖ ≤ r / 3 := by rw [norm_sub_rev]; exact hZball ρ hρ
    exact pow_le_pow_left_of_nonneg_le (norm_nonneg _) h1 _
  have hPw : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ := by
    intro w hw
    rw [norm_prod_sub_pow, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => pow_nonneg (by linarith) _) ?_
    intro ρ hρ
    have h2 := hZball ρ hρ
    have h3 : ‖w - z₀‖ ≤ ‖w - ρ‖ + ‖ρ - z₀‖ := by
      have := norm_add_le (w - ρ) (ρ - z₀)
      rwa [sub_add_sub_cancel] at this
    have h1 : 2 * r / 3 ≤ ‖w - ρ‖ := by linarith
    exact pow_le_pow_left_of_nonneg_le (by linarith) h1 _
  have key_sphere : ∀ w : ℂ, ‖w - z₀‖ = r →
      (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ ≤ M * ‖h z₀‖ := by
    intro w hw
    have hwmem : w ∈ Metric.closedBall z₀ r :=
      Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hw.le)
    have e1 := hbound w hwmem
    rw [hfeq w hwmem, hfz₀, norm_mul, norm_mul] at e1
    have e2 := hPw w hw
    have hq : 0 < (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by positivity
    have e3 : (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) = (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
      rw [mul_div_assoc, mul_pow]
    have e4 : (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
        ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by
      calc (r / 3) ^ (∑ ρ ∈ Z, m ρ) * ((2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖)
          = (2 * r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h w‖ := by rw [e3]; ring
        _ ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ * ‖h w‖ := mul_le_mul_of_nonneg_right e2 (norm_nonneg _)
        _ ≤ M * (‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ * ‖h z₀‖) := e1
        _ ≤ M * ((r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h z₀‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            exact mul_le_mul_of_nonneg_right hPz₀le (norm_nonneg _)
        _ = (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by ring
    exact le_of_mul_le_mul_left e4 hq
  have hdc : DiffContOnCl ℂ h (Metric.ball z₀ r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ hr.ne']
    exact hh
  have hmax : ∀ z ∈ Metric.closedBall z₀ r,
      ‖h z‖ ≤ M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    intro z hz
    have hz' : z ∈ closure (Metric.ball z₀ r) := by rwa [closure_ball z₀ hr.ne']
    refine Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hdc ?_ hz'
    intro w hw
    rw [frontier_ball z₀ hr.ne', mem_sphere_iff_norm] at hw
    rw [le_div_iff₀ (by positivity), mul_comm (‖h w‖)]
    exact key_sphere w hw
  have h2N : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M := by
    have := hmax z₀ hz₀mem
    have hpos : 0 < ‖h z₀‖ := norm_pos_iff.mpr hhz₀
    rw [le_div_iff₀ (by positivity), mul_comm M] at this
    exact le_of_mul_le_mul_left this hpos
  have hsum : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos one_lt_two), ← Real.log_pow]
    exact Real.log_le_log (by positivity) h2N
  have h2N1 : (1 : ℝ) ≤ (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) := by
    simpa using pow_le_pow_left_of_nonneg_le (a := 1) (b := 2) zero_le_one one_le_two (∑ ρ ∈ Z, m ρ)
  have hhb : ∀ z ∈ Metric.closedBall z₀ (r / 3), ‖h z‖ ≤ M * ‖h z₀‖ := by
    intro z hz
    have hz' : z ∈ Metric.closedBall z₀ r := Metric.closedBall_subset_closedBall (by linarith) hz
    have h1 := hmax z hz'
    have h2 : M * ‖h z₀‖ / (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M * ‖h z₀‖ :=
      div_le_self (mul_nonneg (by linarith) (norm_nonneg _)) h2N1
    linarith
  have hlogb := hlog h z₀ (r / 3) M hr3 hM
    (hh.mono (Metric.closedBall_subset_closedBall (by linarith))) hh0 hhb
  refine ⟨Z, m, hZ, hm, hsum, ?_⟩
  intro z hz hfz
  have hzr : z ∈ Metric.ball z₀ r := by
    rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
  have hnhds : Metric.closedBall z₀ r ∈ 𝓝 z :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzr) Metric.ball_subset_closedBall
  have hev : f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w :=
    Filter.mem_of_superset hnhds (fun w hw => hfeq w hw)
  have hfeqz := hfeq z (Metric.ball_subset_closedBall hzr)
  have hPz : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, zero_mul]
  have hhz : h z ≠ 0 := by
    intro h0; apply hfz; rw [hfeqz, h0, mul_zero]
  have hzρ : ∀ ρ ∈ Z, z - ρ ≠ 0 := by
    intro ρ hρ h0; apply hfz; rw [sub_eq_zero.mp h0]; exact hZzero ρ hρ
  have hPd := hasDerivAt_prod_sub_pow Z m z hzρ
  have hhd : HasDerivAt h (deriv h z) z := (hh.differentiableAt hnhds).hasDerivAt
  have hd := (hPd.mul hhd).congr_of_eventuallyEq hev
  have hsplit : deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) = deriv h z / h z := by
    rw [hd.deriv, hfeqz]
    exact div_add_div_sub_eq_div _ _ _ _ hPz hhz
  rw [hsplit]
  have hz6 : z ∈ Metric.closedBall z₀ (r / 3 / 2) := by
    rw [Metric.mem_closedBall] at hz ⊢; linarith
  calc ‖deriv h z / h z‖ ≤ 24 * Real.log M / (r / 3) := hlogb z hz6
    _ = 72 * Real.log M / r := by rw [div_div_eq_mul_div]; ring

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight
section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormLogDerivLeLamF
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

def lamF (σ : ℝ) : ℝ := ∑' n, ‖term ↗Λ (σ : ℂ) n‖

lemma norm_logDeriv_le_lamF {s : ℂ} (hs : 1 < s.re) :
    ‖deriv riemannZeta s / riemannZeta s‖ ≤ lamF s.re := by
  have hL := LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  have hsum : Summable fun n => ‖term ↗Λ s n‖ := summable_norm_iff.2 (LSeriesSummable_vonMangoldt hs)
  have heq : (fun n => ‖term ↗Λ s n‖) = fun n => ‖term ↗Λ ((s.re : ℝ) : ℂ) n‖ := by
    funext n
    rw [norm_term_eq, norm_term_eq]
    simp
  calc ‖deriv riemannZeta s / riemannZeta s‖ = ‖L ↗Λ s‖ := by rw [hL, neg_div, norm_neg]
    _ ≤ ∑' n, ‖term ↗Λ s n‖ := norm_tsum_le_tsum_norm hsum
    _ = lamF s.re := by rw [heq]; rfl

lemma term_vonMangoldt_real (σ : ℝ) (n : ℕ) :
    term ↗Λ (σ : ℂ) n = ((‖term ↗Λ (σ : ℂ) n‖ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have h : term ↗Λ (σ : ℂ) n = ((Λ n / (n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
        Complex.ofReal_natCast]
    rw [h, Complex.norm_real, Real.norm_of_nonneg (div_nonneg vonMangoldt_nonneg (by positivity))]

lemma lamF_eq_norm {σ : ℝ} (hσ : 1 < σ) : lamF σ = ‖L ↗Λ (σ : ℂ)‖ := by
  have h : L ↗Λ (σ : ℂ) = ((lamF σ : ℝ) : ℂ) := by
    rw [LSeries, lamF, Complex.ofReal_tsum]
    exact tsum_congr fun n => term_vonMangoldt_real σ n
  rw [h, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ lamF σ from tsum_nonneg fun n => norm_nonneg _)]

lemma lamF_anti {σ τ : ℝ} (hσ : 1 < σ) (h : σ ≤ τ) : lamF τ ≤ lamF σ := by
  have hs : ∀ x : ℝ, 1 < x → Summable fun n => ‖term ↗Λ (x : ℂ) n‖ := fun x hx =>
    summable_norm_iff.2 (LSeriesSummable_vonMangoldt (by simpa using hx))
  unfold lamF
  refine Summable.tsum_le_tsum (fun n => ?_) (hs τ (by linarith)) (hs σ hσ)
  rw [norm_term_eq, norm_term_eq]
  split_ifs with hn
  · rfl
  · simp only [ofReal_re]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    exact div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_le_rpow_of_exponent_le hn1 h)

end Formalism.ZF
end
end

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

noncomputable section

namespace Formalism.ZF

theorem logDerivBoundRightHalfPlane : LogDerivRight := by
  obtain ⟨B, hB⟩ := log_deriv_riemannZeta_add_inv_sub_bounded.bound
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hB)
  refine ⟨max (max B 0) (lamF (1 + ε / 2)), le_max_of_le_left (le_max_right _ _),
    fun s hs => (norm_logDeriv_le_lamF hs).trans ?_⟩
  have hσ1 : 0 < s.re - 1 := sub_pos.mpr hs
  have hpos : 0 < 1 / (s.re - 1) := by positivity
  rcases lt_or_ge s.re (1 + ε / 2) with hlt | hge
  · have hreal : ‖((s.re : ℂ) - 1)‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg hσ1.le]
    have hd : dist (s.re : ℂ) 1 < ε := by
      rw [Complex.dist_eq, hreal]; linarith
    have hne : (s.re : ℂ) ∈ ({1}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one]; exact hs.ne'
    have hb := hball hd hne
    simp only [norm_one, mul_one] at hb
    have hL := LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (s.re : ℂ)) (by simpa using hs)
    rw [lamF_eq_norm hs, hL, neg_div, norm_neg]
    have htri : ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ)‖ ≤
        ‖deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) + ((s.re : ℂ) - 1)⁻¹‖ +
          ‖((s.re : ℂ) - 1)⁻¹‖ := by
      have := norm_sub_le (deriv riemannZeta (s.re : ℂ) / riemannZeta (s.re : ℂ) +
        ((s.re : ℂ) - 1)⁻¹) (((s.re : ℂ) - 1)⁻¹)
      simpa using this
    rw [norm_inv, hreal] at htri
    have : B ≤ max (max B 0) (lamF (1 + ε / 2)) :=
      le_max_of_le_left (le_max_left _ _)
    rw [one_div]
    linarith
  · have h1 : lamF s.re ≤ lamF (1 + ε / 2) := lamF_anti (by linarith) hge
    have : lamF (1 + ε / 2) ≤ max (max B 0) (lamF (1 + ε / 2)) := le_max_right _ _
    linarith

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoGrowthBall
open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zfo_ball_facts {σ τ : ℝ} {w : ℂ} (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) :
    |w.re - σ| ≤ 1 / 2 ∧ |w.im - τ| ≤ 1 / 2 ∧ ‖w‖ ≤ |σ| + |τ| + 1 / 2 := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre : (w - ((σ : ℂ) + τ * I)).re = w.re - σ := by simp
  have him : (w - ((σ : ℂ) + τ * I)).im = w.im - τ := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← hre]
    exact (Complex.abs_re_le_norm _).trans hw
  · rw [← him]
    exact (Complex.abs_im_le_norm _).trans hw
  · have hc : ‖(σ : ℂ) + τ * I‖ ≤ |σ| + |τ| := by
      refine (norm_add_le _ _).trans ?_
      simp [Complex.norm_real]
    calc ‖w‖ = ‖(w - ((σ : ℂ) + τ * I)) + ((σ : ℂ) + τ * I)‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - ((σ : ℂ) + τ * I)‖ + ‖(σ : ℂ) + τ * I‖ := norm_add_le _ _
      _ ≤ 1 / 2 + (|σ| + |τ|) := add_le_add hw hc
      _ = |σ| + |τ| + 1 / 2 := by ring

lemma zfo_ball_ne_one {σ τ : ℝ} (hτ : 3 ≤ |τ|) {w : ℂ}
    (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) : w ≠ 1 ∧ 5 / 2 ≤ |w.im| := by
  obtain ⟨-, him, -⟩ := zfo_ball_facts hw
  have h : 5 / 2 ≤ |w.im| := by
    have h' := abs_sub_abs_le_abs_sub τ w.im
    rw [abs_sub_comm] at h'
    linarith
  refine ⟨fun h1 => ?_, h⟩
  norm_num [h1] at h

lemma zfo_diff_ball {σ τ : ℝ} (hτ : 3 ≤ |τ|) :
    DifferentiableOn ℂ riemannZeta (closedBall ((σ : ℂ) + τ * I) (1 / 2)) := by
  intro w hw
  exact (differentiableAt_riemannZeta (zfo_ball_ne_one hτ hw).1).differentiableWithinAt

lemma zfo_growth_ball (hG : ZetaGrowth) {σ τ T : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (hτ : 3 ≤ |τ|)
    (hτT : |τ| ≤ 2 * T) {w : ℂ} (hw : w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2)) :
    ‖riemannZeta w‖ ≤ 6 * (T + 2) := by
  obtain ⟨hre, -, hn⟩ := zfo_ball_facts hw
  obtain ⟨hne, him2⟩ := zfo_ball_ne_one hτ hw
  have hre' : 1 / 2 < w.re := by
    have := (abs_le.mp hre).1
    linarith
  have h1 : 5 / 2 ≤ ‖w - 1‖ := by
    have h' : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at h'
    linarith
  have hinv1 : 1 / ‖w - 1‖ ≤ 2 / 5 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hinv2 : 1 / w.re ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hσabs : |σ| = σ := abs_of_pos (by linarith)
  have hnw : ‖w‖ ≤ 2 * T + 5 / 2 := by
    rw [hσabs] at hn
    linarith
  have hc0 : 0 ≤ 1 + 1 / w.re := by
    have : 0 < 1 / w.re := one_div_pos.mpr (by linarith)
    linarith
  have hprod : ‖w‖ * (1 + 1 / w.re) ≤ (2 * T + 5 / 2) * 3 :=
    mul_le_mul hnw (by linarith) hc0 (by linarith [abs_nonneg τ])
  have hg := hG w (by linarith) hne
  linarith

lemma zfo_M_bound (hG : ZetaGrowth) (hI : ZetaInvBound) {σ τ T : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hσK : 2 / (σ - 1) ≤ 20000 * (T + 2)) (hT : 3 ≤ T) (hτ : 3 ≤ |τ|) (hτT : |τ| ≤ 2 * T) :
    ∀ w ∈ closedBall ((σ : ℂ) + τ * I) (1 / 2),
      ‖riemannZeta w‖ ≤ (T + 2) ^ 10 * ‖riemannZeta ((σ : ℂ) + τ * I)‖ := by
  intro w hw
  have hzw := zfo_growth_ball hG hσ1 hσ2 hτ hτT hw
  set s : ℂ := (σ : ℂ) + τ * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hinv := hI s hs1
  rw [hsre] at hinv
  have hσ1' : 0 < σ - 1 := by linarith
  have hA : 0 < T + 2 := by linarith
  have ha0 : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs1)
  have h1 : 1 ≤ ‖riemannZeta s‖ * (σ / (σ - 1)) :=
    calc (1 : ℝ) = ‖riemannZeta s‖ * ‖riemannZeta s‖⁻¹ := (mul_inv_cancel₀ ha0.ne').symm
      _ ≤ ‖riemannZeta s‖ * (σ / (σ - 1)) := mul_le_mul_of_nonneg_left hinv ha0.le
  rw [mul_div_assoc', le_div_iff₀ hσ1'] at h1
  have h3 : σ - 1 ≤ 2 * ‖riemannZeta s‖ := by nlinarith
  have h4 : 2 ≤ 20000 * (T + 2) * (σ - 1) := by
    rwa [div_le_iff₀ hσ1'] at hσK
  have h5 : 1 ≤ 20000 * (T + 2) * ‖riemannZeta s‖ := by
    have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 10000 * (T + 2))
    nlinarith
  have h8 : (5 : ℝ) ^ 8 ≤ (T + 2) ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
  have h6 : 120000 * (T + 2) ^ 2 ≤ (T + 2) ^ 10 := by
    have e : (T + 2) ^ 10 = (T + 2) ^ 2 * (T + 2) ^ 8 := by ring
    have := mul_le_mul_of_nonneg_left h8 (sq_nonneg (T + 2))
    rw [e]
    norm_num at this ⊢
    nlinarith [sq_nonneg (T + 2)]
  calc ‖riemannZeta w‖ ≤ 6 * (T + 2) := hzw
    _ ≤ 6 * (T + 2) * (20000 * (T + 2) * ‖riemannZeta s‖) := le_mul_of_one_le_right (by linarith) h5
    _ = 120000 * (T + 2) ^ 2 * ‖riemannZeta s‖ := by ring
    _ ≤ (T + 2) ^ 10 * ‖riemannZeta s‖ := mul_le_mul_of_nonneg_right h6 ha0.le

end Formalism.ZF
end
end
