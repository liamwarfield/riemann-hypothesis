module

public import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.TrivReal

@[expose] public section

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ZetaNegReal
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma exponential_integral_nonneg_real {σ a : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) :
    ∃ r : ℝ, 0 ≤ r ∧ Formalism.ZF.ComplexPowerDifferenceIntegral.eint (σ : ℂ) a = (r : ℂ) := by
  refine ⟨∫ x in a..(a + 1), (x ^ (-σ) - (a + 1) ^ (-σ)), ?_, ?_⟩
  · apply intervalIntegral.integral_nonneg (by linarith)
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1 := Real.rpow_le_rpow_of_nonpos hx0 hx.2 (by linarith : -σ ≤ 0)
    linarith
  · unfold Formalism.ZF.ComplexPowerDifferenceIntegral.eint
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have hx0 : 0 ≤ x := le_trans ha.le hx.1
    simp only [Complex.ofReal_sub]
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ a + 1)]
    push_cast
    ring

theorem zeta_negative_real_axis : ZetaNegReal := by
  intro σ hσ0 hσ1
  have hre : 0 < (σ : ℂ).re := by simpa using hσ0
  have hz1 := Formalism.ZF.ComplexPowerDifferenceIntegral.riemannZetaOne_eq_one_sub_of_re_pos hre
  have hne : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hne' : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hζ := riemannZeta_eq_inv_sub_mul hne
  choose r hr0 hr using fun n : ℕ =>
    exponential_integral_nonneg_real (σ := σ) (a := (n : ℝ) + 1) hσ0.le (by positivity)
  have hdz : ∀ n : ℕ, Formalism.ZF.ComplexPowerDifferenceIntegral.dz (σ : ℂ) n = ((σ : ℂ) - 1) * ((r n : ℝ) : ℂ) := by
    intro n
    rw [← hr n]
    exact Formalism.ZF.ComplexPowerDifferenceIntegral.d_eq (by positivity) _
  have hsum : Summable r := by
    have hs := Formalism.ZF.ComplexPowerDifferenceIntegral.summable_norm_dz hre
    have hs' : Summable (fun n => ‖((σ : ℂ) - 1)‖⁻¹ * ‖Formalism.ZF.ComplexPowerDifferenceIntegral.dz (σ : ℂ) n‖) := hs.mul_left _
    refine hs'.congr (fun n => ?_)
    rw [hdz n, norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne'), one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
  have hDz : Formalism.ZF.ComplexPowerDifferenceIntegral.Dz (σ : ℂ) = ((σ : ℂ) - 1) * ((∑' n, r n : ℝ) : ℂ) := by
    unfold Formalism.ZF.ComplexPowerDifferenceIntegral.Dz
    simp_rw [hdz]
    rw [tsum_mul_left, Complex.ofReal_tsum]
  set R := ∑' n, r n with hRdef
  have hR0 : 0 ≤ R := tsum_nonneg hr0
  have hval : riemannZeta (σ : ℂ) = ((σ / (σ - 1) - R : ℝ) : ℂ) := by
    rw [hζ, hz1, hDz]
    have hσ1' : (σ - 1 : ℝ) ≠ 0 := by intro h; linarith
    push_cast
    field_simp
  rw [hval, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  have : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg hσ0 (by linarith)
  linarith

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
open Complex Finset

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma three_le_modulus_of_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 3 ≤ q := by
  by_contra h
  push_neg at h
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  interval_cases q
  all_goals
    apply hχ
    ext a
    have ha : a = 1 := by revert a; decide
    rw [ha]
    simp

lemma two_le_log_three_mul (q : ℕ) (hq : 3 ≤ q) : 2 ≤ Real.log (3 * q) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; try norm_num
  rw [Real.le_log_iff_exp_le (by positivity), e2]
  nlinarith

private lemma rpow_le_exp_three_halves_of_le_log (q : ℕ) (hq : 3 ≤ q) (x t : ℝ) (hx : 1 ≤ x) (hxq : x ≤ 3 * q)
    (ht : t ≤ 3 / (2 * Real.log (3 * q))) : x ^ t ≤ Real.exp (3 / 2) := by
  have hL : 2 ≤ Real.log (3 * q) := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlxL : Real.log x ≤ Real.log (3 * q) := Real.log_le_log hx0 hxq
  rw [Real.rpow_def_of_pos hx0]
  apply Real.exp_le_exp.2
  have h1 : Real.log x * t ≤ Real.log x * (3 / (2 * Real.log (3 * q))) := mul_le_mul_of_nonneg_left ht hlx
  have h2 : Real.log x * (3 / (2 * Real.log (3 * q))) ≤ Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) :=
    mul_le_mul_of_nonneg_right hlxL (by positivity)
  have h3 : Real.log (3 * q) * (3 / (2 * Real.log (3 * q))) = 3 / 2 := by field_simp; try ring
  linarith

lemma rpow_neg_le_exp_inv_near_one (q : ℕ) (hq : 3 ≤ q) (x : ℝ) (hx : 1 ≤ x) (hxq : x ≤ q) (r : ℝ)
    (hr : 1 - 3 / (2 * Real.log (3 * q)) ≤ r) :
    x ^ (-r) ≤ Real.exp (3 / 2) * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hqR : (0 : ℝ) ≤ q := by positivity
  have e : x ^ (-r) = x ^ (1 - r) * x⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx0]
    congr 1
    ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (rpow_le_exp_three_halves_of_le_log q hq x (1 - r) hx (by linarith) (by linarith))
    (inv_nonneg.2 hx0.le)

lemma partial_sum_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) :
    ‖∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (1 + Real.log (3 * q)) := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ n ∈ Icc 1 q, ‖χ (n : ZMod q) * (n : ℂ) ^ (-w)‖ ≤ Real.exp (3 / 2) * (n : ℝ)⁻¹ := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hn
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    have hχn : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hr := rpow_neg_le_exp_inv_near_one q hq n (by exact_mod_cast h1) (by exact_mod_cast h2) w.re hw
    calc ‖χ (n : ZMod q)‖ * (n : ℝ) ^ (-w.re) ≤ 1 * (Real.exp (3 / 2) * (n : ℝ)⁻¹) :=
          mul_le_mul hχn hr (by positivity) zero_le_one
      _ = _ := one_mul _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hH : ∑ n ∈ Icc 1 q, ((n : ℝ))⁻¹ = (harmonic q : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [hH]
  refine (harmonic_le_one_add_log q).trans ?_
  have : Real.log q ≤ Real.log (3 * q) := Real.log_le_log (by positivity) (by linarith)
  linarith

lemma lfunction_norm_le_near_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (w : ℂ)
    (hw : 1 - 3 / (2 * Real.log (3 * q)) ≤ w.re) (hw4 : 1 / 4 ≤ w.re) (hw2 : ‖w‖ ≤ 2) :
    ‖DirichletCharacter.LFunction χ w‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by
  have hq := three_le_modulus_of_ne_one χ hχ
  have hL := two_le_log_three_mul q hq
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hre0 : 0 < w.re := by linarith
  have hB : ∀ M, ‖Formalism.FX.LFunctionPartialSum.Ap χ M‖ ≤ (q : ℝ) + 1 := fun M => norm_character_sum_Icc_le χ hχ M
  have hpos : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  have hx1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith
  have hx3 : (q : ℝ) + 1 ≤ 3 * q := by linarith
  have hpow : ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re) ≤ Real.exp (3 / 2) := by
    have := rpow_le_exp_three_halves_of_le_log q hq ((q : ℝ) + 1) (1 - w.re) hx1 hx3 (by linarith)
    rwa [sub_eq_add_neg, Real.rpow_add hpos, Real.rpow_one] at this
  rw [Formalism.FX.LFunctionPartialSum.LFunction_eq_G (χ := χ) hχ hB hre0]
  unfold Formalism.FX.LFunctionPartialSum.G
  rw [← Summable.sum_add_tsum_nat_add (q + 1) (Formalism.FX.LFunctionPartialSum.summable_dterm (χ := χ) hB hre0),
    eq_sub_of_add_eq (Formalism.FX.LFunctionPartialSum.partial_identity (χ := χ) w q)]
  have h1 := partial_sum_norm_le_near_one χ hq w hw
  have h2 : ‖Formalism.FX.LFunctionPartialSum.Ap χ q * ((q : ℂ) + 1) ^ (-w)‖ ≤ Real.exp (3 / 2) := by
    rw [norm_mul]
    have e : ((q : ℂ) + 1) = ((q + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    push_cast
    calc ‖Formalism.FX.LFunctionPartialSum.Ap χ q‖ * ((q : ℝ) + 1) ^ (-w.re) ≤ ((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re) :=
          mul_le_mul_of_nonneg_right (hB q) (by positivity)
      _ ≤ _ := hpow
  have h3 : ‖∑' i, Formalism.FX.LFunctionPartialSum.dterm χ w (i + (q + 1))‖ ≤ 8 * Real.exp (3 / 2) := by
    refine (Formalism.FX.LFunctionPartialSum.norm_tail_le χ hB hre0 q).trans ?_
    have hw' : ‖w‖ / w.re ≤ 8 := by rw [div_le_iff₀ hre0]; linarith
    calc ((q : ℝ) + 1) * (‖w‖ / w.re) * ((q : ℝ) + 1) ^ (-w.re)
        = (‖w‖ / w.re) * (((q : ℝ) + 1) * ((q : ℝ) + 1) ^ (-w.re)) := by ring
      _ ≤ 8 * Real.exp (3 / 2) := mul_le_mul hw' hpow (by positivity) (by norm_num)
  have hsub := norm_sub_le (∑ n ∈ Icc 1 q, χ (n : ZMod q) * (n : ℂ) ^ (-w)) (Formalism.FX.LFunctionPartialSum.Ap χ q * ((q : ℂ) + 1) ^ (-w))
  refine (norm_add_le _ _).trans ?_
  have he := Real.exp_pos (3 / 2)
  have hk := mul_le_mul_of_nonneg_left (show 10 + Real.log (3 * q) ≤ 38 * Real.log (3 * q) by linarith) he.le
  nlinarith

theorem lfunction_deriv_near_one : LDerivNearOne := by
  refine ⟨76 * Real.exp (3 / 2), fun q _ χ hχ σ hσ1 hσ2 => ?_⟩
  have hq := three_le_modulus_of_ne_one χ hχ
  have hL := two_le_log_three_mul q hq
  have hLpos : 0 < Real.log (3 * q) := by linarith
  have hρ : 0 < 1 / (2 * Real.log (3 * q)) := by positivity
  have hd : DiffContOnCl ℂ (DirichletCharacter.LFunction χ) (Metric.ball (σ : ℂ) (1 / (2 * Real.log (3 * q)))) :=
    (DirichletCharacter.differentiable_LFunction hχ).diffContOnCl
  have hC : ∀ z ∈ Metric.sphere (σ : ℂ) (1 / (2 * Real.log (3 * q))),
      ‖DirichletCharacter.LFunction χ z‖ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hre : |(z - σ).re| ≤ 1 / (2 * Real.log (3 * q)) := by rw [← hz]; exact Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    have h1 : 1 / Real.log (3 * q) ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    have h2 : 1 / (2 * Real.log (3 * q)) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; linarith
    have e3 : 3 / (2 * Real.log (3 * q)) = 1 / Real.log (3 * q) + 1 / (2 * Real.log (3 * q)) := by
      field_simp
      try ring
    have hab := abs_le.1 hre
    apply lfunction_norm_le_near_one χ hχ z
    · rw [e3]; linarith
    · linarith
    · calc ‖z‖ = ‖(z - σ) + σ‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - σ‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 := by
          rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          linarith
        _ ≤ 2 := by norm_num
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd hC
  calc _ ≤ 38 * Real.exp (3 / 2) * Real.log (3 * q) / (1 / (2 * Real.log (3 * q))) := this
    _ = 76 * Real.exp (3 / 2) * Real.log (3 * q) ^ 2 := by field_simp; try ring

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LandauLemmaLfunctionZeros
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma landau_lemma_lfunction_zeros (hLL : LandauLocal3) {C : ℝ}
    (hC : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, 1 / 2 ≤ s.re →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖))
    (hInv : LInvBound) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {s : ℂ}
    (hσ1 : 26 / 27 ≤ s.re) (hσ2 : s.re < 11 / 10) (hfs : DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall ((21 / 20 : ℂ) + s.im * I) (11 / 20 / 3) ∧
        DirichletCharacter.LFunction χ ρ = 0)) ∧
      (∀ ρ ∈ Z, deriv (DirichletCharacter.LFunction χ) ρ ≠ 0 → m ρ = 1) ∧
      (∑ ρ ∈ Z, (m ρ : ℝ)) ≤ (Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
        Real.log ((q : ℝ) * (|s.im| + 2)) / Real.log 2 ∧
      ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s -
          ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤
        1440 / 11 * ((Real.log (2 * (21 * (|C| + 1))) / Real.log 2 + 1) *
          Real.log ((q : ℝ) * (|s.im| + 2))) := by
  set z₀ : ℂ := (21 / 20 : ℂ) + s.im * I with hz₀
  have hz₀re : z₀.re = 21 / 20 := by simp [hz₀]
  set A : ℝ := 21 * (|C| + 1) with hAdef
  have hq1 := one_le_modulus_real q
  have hX : (0 : ℝ) < (q : ℝ) * (|s.im| + 2) := by positivity
  set M : ℝ := 2 * A * ((q : ℝ) * (|s.im| + 2)) with hMdef
  have hA1 : 1 ≤ A := by
    have := abs_nonneg C
    rw [hAdef]
    nlinarith
  have hM1 : 1 ≤ M := by
    have h2 : 2 ≤ (q : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
    rw [hMdef]
    nlinarith
  have hf0 : DirichletCharacter.LFunction χ z₀ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by rw [hz₀re]; norm_num)
  have hinv := hInv q χ z₀ (by rw [hz₀re]; norm_num)
  rw [hz₀re] at hinv
  have h21 : ‖DirichletCharacter.LFunction χ z₀‖⁻¹ ≤ 21 := by
    have e : (21 / 20 : ℝ) / (21 / 20 - 1) = 21 := by norm_num
    linarith
  have hlow : 1 ≤ 21 * ‖DirichletCharacter.LFunction χ z₀‖ := by
    have hp : 0 < ‖DirichletCharacter.LFunction χ z₀‖ := norm_pos_iff.2 hf0
    have := mul_le_mul_of_nonneg_right h21 hp.le
    rwa [inv_mul_cancel₀ hp.ne'] at this
  have hbound : ∀ z ∈ Metric.closedBall z₀ (11 / 20),
      ‖DirichletCharacter.LFunction χ z‖ ≤ M * ‖DirichletCharacter.LFunction χ z₀‖ := by
    intro z hz
    have hre := re_ge_of_mem_closedBall hz
    rw [hz₀re] at hre
    have h1 := hC q χ hχ z (by linarith)
    have hn := norm_le_norm_add_of_mem_closedBall' hz
    have hn0 := norm_disc_center_le s.im
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hz1 : 1 + ‖z‖ ≤ 2 * (|s.im| + 2) := by linarith [abs_nonneg s.im]
    have hY : 0 ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by positivity
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ C * q * (1 + ‖z‖) := h1
      _ ≤ |C| * q * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hq0)
            (by positivity)
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hq0) hz1 (by positivity)
          positivity
      _ = (|C| + 1) * q * (2 * (|s.im| + 2)) * 1 := by ring
      _ ≤ (|C| + 1) * q * (2 * (|s.im| + 2)) * (21 * ‖DirichletCharacter.LFunction χ z₀‖) :=
          mul_le_mul_of_nonneg_left hlow hY
      _ = M * ‖DirichletCharacter.LFunction χ z₀‖ := by
          rw [hMdef, hAdef]
          ring
  obtain ⟨Z, m, hZ, -, -, hm1, hsum, hder⟩ := hLL (DirichletCharacter.LFunction χ) z₀ (11 / 20) M
    (by norm_num) hM1 (DirichletCharacter.differentiable_LFunction hχ).differentiableOn hf0 hbound
  have hlogM : Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * Real.log ((q : ℝ) * (|s.im| + 2)) :=
    log_le_of_le_exp_log_conductor hA1 hM1 (log_two_le_log_analytic_conductor q s.im) (Real.exp_pos _)
      (by rw [Real.exp_log hX, hMdef])
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Z, m, hZ, hm1, ?_, ?_⟩
  · push_cast at hsum
    calc ∑ ρ ∈ Z, (m ρ : ℝ) ≤ Real.log M / Real.log 2 := hsum
      _ ≤ _ := div_le_div_of_nonneg_right hlogM hl2.le
  · have hs6 : s ∈ Metric.closedBall z₀ (11 / 20 / 6) := by
      rw [Metric.mem_closedBall, Complex.dist_eq]
      have e : s - z₀ = ((s.re - 21 / 20 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hz₀]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ ≤ 72 * Real.log M / (11 / 20) := hder s hs6 hfs
      _ = 1440 / 11 * Real.log M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlogM (by norm_num)

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRealPos
open Complex Filter Topology

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma real_character_lfunction_im_eq_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (hχ1 : χ ≠ 1)
    (σ : ℝ) : (DirichletCharacter.LFunction χ σ).im = 0 := by
  have h := realCharConj q χ hχ hχ1 (σ : ℂ)
  rw [Complex.conj_ofReal] at h
  exact Complex.conj_eq_iff_im.1 h.symm

lemma lfunction_tendsto_one_atTop {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Tendsto (fun x : ℝ ↦ DirichletCharacter.LFunction χ x) atTop (𝓝 1) := by
  have ha : LSeries.abscissaOfAbsConv (fun n : ℕ => χ n) < ⊤ := by
    rw [DirichletCharacter.absicssaOfAbsConv_eq_one (NeZero.ne q) χ]
    exact EReal.coe_lt_top 1
  have ht := LSeries.tendsto_atTop ha
  simp only [Nat.cast_one, map_one] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact (DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hx)).symm

theorem real_lfunction_real_on_reals : LRealPos := by
  intro q _ χ hχ hχ1 σ₀ hnz σ hσ
  have him : ∀ t : ℝ, (DirichletCharacter.LFunction χ t).im = 0 := real_character_lfunction_im_eq_zero χ hχ hχ1
  refine ⟨him σ, ?_⟩
  by_contra hneg
  rw [not_lt] at hneg
  have hcont : Continuous fun t : ℝ => (DirichletCharacter.LFunction χ t).re :=
    Complex.continuous_re.comp
      ((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp Complex.continuous_ofReal)
  obtain ⟨x, hx1, hx⟩ : ∃ x : ℝ, σ ≤ x ∧ 0 < (DirichletCharacter.LFunction χ x).re := by
    have hev : ∀ᶠ x : ℝ in atTop, 0 < (DirichletCharacter.LFunction χ x).re :=
      ((Complex.continuous_re.tendsto 1).comp (lfunction_tendsto_one_atTop χ)).eventually
        (lt_mem_nhds (by norm_num))
    obtain ⟨x, hx⟩ := (hev.and (eventually_ge_atTop σ)).exists
    exact ⟨x, hx.2, hx.1⟩
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hx1 hcont.continuousOn ⟨hneg, hx.le⟩
  apply hnz c (le_trans hσ hc.1)
  exact Complex.ext (by simpa using hc0) (by simpa using him c)

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.CharExists
open Complex
noncomputable section
namespace Formalism.ZeroFreeDirichlet

theorem isProdChar_changeLevel_mul {q₁ q₂ : ℕ} (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) :
    IsProdChar χ₁ χ₂ (DirichletCharacter.changeLevel (dvd_mul_right q₁ q₂) χ₁ *
      DirichletCharacter.changeLevel (dvd_mul_left q₂ q₁) χ₂) := by
  intro n
  rw [MulChar.mul_apply]
  by_cases h : IsUnit (n : ZMod (q₁ * q₂))
  · have h1 : ∀ {q : ℕ} (hq : q ∣ q₁ * q₂) (χ : DirichletCharacter ℂ q),
        DirichletCharacter.changeLevel hq χ (n : ZMod (q₁ * q₂)) = χ (n : ZMod q) := by
      intro q hq χ
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd (χ := χ) hq h.unit
      rw [IsUnit.unit_spec] at this
      rw [this]
      congr 1
      first
        | exact ZMod.cast_natCast hq n
        | exact ZMod.cast_natCast hq _ n
        | exact ZMod.cast_nat_cast hq n
    rw [h1, h1]
  · rw [MulChar.map_nonunit _ h]
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right] at h
    rcases not_and_or.mp h with h' | h'
    · rw [MulChar.map_nonunit χ₁ (by rwa [ZMod.isUnit_iff_coprime])]
      simp
    · rw [MulChar.map_nonunit χ₂ (by rwa [ZMod.isUnit_iff_coprime])]
      simp

theorem exists_product_character : ProdCharExists :=
  fun _ _ χ₁ χ₂ => ⟨_, isProdChar_changeLevel_mul χ₁ χ₂⟩

def characterModFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem characterModFour_apply (a : ZMod 4) :
    characterModFour a = ((ZMod.χ₄ a : ℤ) : ℂ) := rfl

theorem characterModFour_sq : characterModFour ^ 2 = 1 := by
  first
    | exact (ZMod.isQuadratic_χ₄.comp _).sq_eq_one
    | exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

theorem characterModFour_ne_one : characterModFour ≠ 1 := by
  intro h
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, by decide, by decide⟩, rfl⟩
  have h3 := DFunLike.congr_fun h (3 : ZMod 4)
  rw [characterModFour_apply, MulChar.one_apply hu] at h3
  have hv : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [hv] at h3
  norm_num at h3

theorem exists_real_nontrivial_character : RealCharExists :=
  ⟨4, ⟨by norm_num⟩, characterModFour, characterModFour_sq, characterModFour_ne_one⟩

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqGrowth
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma circle_about_two_geometry {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) :
    1 / 2 ≤ s.re ∧ ‖s‖ ≤ 7 / 2 ∧ 1 / 2 ≤ ‖s - 1‖ := by
  refine ⟨?_, ?_, ?_⟩
  · have h := Complex.abs_re_le_norm (s - 2)
    rw [hs] at h
    have e : (s - 2).re = s.re - 2 := by simp
    rw [e] at h
    linarith [(abs_le.mp h).1]
  · have h := norm_add_le (s - 2) (2 : ℂ)
    rw [sub_add_cancel, hs] at h
    have e : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  · have h := norm_add_le (s - 1) (-1 : ℂ)
    have e : s - 1 + -1 = s - 2 := by ring
    rw [e, hs] at h
    have e1 : ‖(-1 : ℂ)‖ = 1 := by simp
    linarith

lemma zeta_norm_le_on_circle {s : ℂ} (hs : ‖s - 2‖ = 3 / 2) : ‖riemannZeta s‖ ≤ 14 := by
  obtain ⟨hre, hn, h1⟩ := circle_about_two_geometry hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at h1
    norm_num at h1
  have hg := Formalism.ZF.growthBound s (by linarith) hs1
  have ha : 1 / ‖s - 1‖ ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hb : 1 / s.re ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hp : 0 ≤ 1 + 1 / s.re := by
    have : 0 < 1 / s.re := by apply div_pos <;> linarith
    linarith
  have hc : ‖s‖ * (1 + 1 / s.re) ≤ 7 / 2 * 3 := by
    calc ‖s‖ * (1 + 1 / s.re) ≤ 7 / 2 * (1 + 1 / s.re) := mul_le_mul_of_nonneg_right hn hp
      _ ≤ 7 / 2 * 3 := by linarith
  linarith

theorem product_lfunction_growth_bound : BqGrowth := by
  obtain ⟨C, hC⟩ := lfunction_polynomial_growth
  refine ⟨14 * (9 / 2 * |C|) ^ 3, 3, ?_⟩
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 h3 s hs
  obtain ⟨hre, hn, -⟩ := circle_about_two_geometry hs
  have hz := zeta_norm_le_on_circle hs
  have L : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ 9 / 2 * |C| * q := by
    intro q _ χ hχ
    have h := hC q χ hχ s hre
    have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hCq : C * q ≤ |C| * q := mul_le_mul_of_nonneg_right (le_abs_self C) hq
    have hp : 0 ≤ |C| * q := by positivity
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ C * q * (1 + ‖s‖) := h
      _ ≤ |C| * q * (1 + ‖s‖) := mul_le_mul_of_nonneg_right hCq (by positivity)
      _ ≤ |C| * q * (9 / 2) := mul_le_mul_of_nonneg_left (by linarith) hp
      _ = 9 / 2 * |C| * q := by ring
  have e1 := L q₁ χ₁ h1
  have e2 := L q₂ χ₂ h2
  have e3 := L (q₁ * q₂) ψ h3
  have hq1 : (q₁ : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_right q₁ (Nat.pos_of_ne_zero (NeZero.ne q₂))
  have hq2 : (q₂ : ℝ) ≤ ((q₁ * q₂ : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left q₂ (Nat.pos_of_ne_zero (NeZero.ne q₁))
  have ha : 0 ≤ 9 / 2 * |C| := by positivity
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  unfold Fbq
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖riemannZeta s‖ * ‖DirichletCharacter.LFunction χ₁ s‖ * ‖DirichletCharacter.LFunction χ₂ s‖ *
        ‖DirichletCharacter.LFunction ψ s‖
      ≤ 14 * (9 / 2 * |C| * q₁) * (9 / 2 * |C| * q₂) * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) := by
        gcongr
    _ ≤ 14 * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) * (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) *
          (9 / 2 * |C| * ((q₁ * q₂ : ℕ) : ℝ)) := by gcongr
    _ = 14 * (9 / 2 * |C|) ^ 3 * ((q₁ * q₂ : ℕ) : ℝ) ^ 3 := by ring

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.SameCharacterLFunctionOne
open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem prod_one_sub_inv_ge_inv_card_succ (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    1 / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hsub : s ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨hs p hp, ha p hp⟩
    have hcard : s.card + 2 ≤ a := by
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Ico] at h1
      omega
    have hc : (insert a s).card = s.card + 1 := by simp [has]
    rw [Finset.prod_insert has, hc]
    push_cast
    have ih' := ih hs
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have ha' : (s.card : ℝ) + 2 ≤ a := by exact_mod_cast hcard
    have hk : (0 : ℝ) < (s.card : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) ≤ 1 - 1 / (a : ℝ) := by
      have h1 : (1 : ℝ) / a ≤ 1 := by rw [div_le_one ha0]; linarith
      linarith
    have e1 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) - 1 / ((s.card : ℝ) + 1 + 1) =
        ((a : ℝ) - ((s.card : ℝ) + 2)) / ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2)) := by
      field_simp
      ring
    have e2 : 0 ≤ ((a : ℝ) - ((s.card : ℝ) + 2)) /
        ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2)) :=
      div_nonneg (by linarith) (by positivity)
    have e3 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) ≤
        (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left ih' hpos
    linarith

theorem changeLevel_eq_of_agree_coprime {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁)
    (χ : DirichletCharacter ℂ q)
    (h : ∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q)) :
    DirichletCharacter.changeLevel (dvd_mul_right q₁ q) χ₁ =
      DirichletCharacter.changeLevel (dvd_mul_left q q₁) χ := by
  haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  ext a
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.cast_eq_val, ZMod.cast_eq_val]
  exact h _ (ZMod.val_coe_unit_coprime a)

theorem euler_factor_term_norm_le {M : ℕ} (φ : DirichletCharacter ℂ M) (p : ℕ) :
    ‖φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 / (p : ℝ) := by
  rw [norm_mul]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have h1 : ‖(p : ℂ) ^ (-(1 : ℂ))‖ = 1 / (p : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hp]
      simp [Real.rpow_neg_one]
    rw [h1]
    exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one φ _)

theorem euler_factor_product_upper {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ) :
    ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => ?_
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  linarith [euler_factor_term_norm_le φ p]

theorem euler_factor_product_lower {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
  rw [norm_prod]
  refine Finset.prod_le_prod₀ (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  · have h1 := euler_factor_term_norm_le φ p
    have h2 := norm_sub_norm_le (1 : ℂ) (φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))
    rw [norm_one] at h2
    linarith

theorem prod_one_add_mul_one_sub_le_one (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∏ p ∈ S, (1 + 1 / (p : ℝ))) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_one₀ (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : (0 : ℝ) ≤ 1 / p := by positivity
    nlinarith
  · have h2 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    nlinarith

theorem lfunction_one_same_character : SameCharacterLFunctionOne := by
  intro q₁ q _ _ χ₁ χ hχ₁ hχ h
  haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  have hS : ∀ p ∈ (q₁ * q).primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hL₁ := DirichletCharacter.LFunction_changeLevel (dvd_mul_right q₁ q) χ₁ (s := 1)
    (Or.inl hχ₁)
  have hL := DirichletCharacter.LFunction_changeLevel (dvd_mul_left q q₁) χ (s := 1) (Or.inl hχ)
  rw [changeLevel_eq_of_agree_coprime χ₁ χ h, hL] at hL₁
  have hnorm : ‖DirichletCharacter.LFunction χ₁ 1‖ *
      ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ =
      ‖DirichletCharacter.LFunction χ 1‖ *
      ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
    rw [← norm_mul, ← norm_mul, hL₁]
  have hlow := euler_factor_product_lower χ₁ _ hS
  have hup := euler_factor_product_upper χ (q₁ * q).primeFactors
  have hge := prod_one_sub_inv_ge_inv_card_succ _ hS
  have hAB := prod_one_add_mul_one_sub_le_one _ hS
  have hk : (0 : ℝ) < ((q₁ * q).primeFactors.card : ℝ) + 1 := by positivity
  have hA0 : (0 : ℝ) ≤ ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hB' : 1 ≤ (∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
      (((q₁ * q).primeFactors.card : ℝ) + 1) := by
    have h1 := mul_le_mul_of_nonneg_right hge hk.le
    rwa [one_div, inv_mul_cancel₀ hk.ne'] at h1
  have hx := norm_nonneg (DirichletCharacter.LFunction χ₁ 1)
  have hy := norm_nonneg (DirichletCharacter.LFunction χ 1)
  have h1 : ‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ)) ≤
      ‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) := by
    calc _ ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ *
          ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ :=
          mul_le_mul_of_nonneg_left hlow hx
      _ = _ := hnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left hup hy
  have hA : ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) ≤
      ((q₁ * q).primeFactors.card : ℝ) + 1 := by nlinarith
  calc ‖DirichletCharacter.LFunction χ₁ 1‖
        ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ * ((∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1)) := le_mul_of_one_le_right hx hB'
    _ = (‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) := by ring
    _ ≤ (‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) := mul_le_mul_of_nonneg_right h1 hk.le
    _ ≤ (‖DirichletCharacter.LFunction χ 1‖ * (((q₁ * q).primeFactors.card : ℝ) + 1)) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hy) hk.le
    _ = (((q₁ * q).primeFactors.card : ℝ) + 1) ^ 2 * ‖DirichletCharacter.LFunction χ 1‖ := by ring

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.BqCoeff
section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ConvolutionNonnegOfDivisors
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma convolution_nonneg_of_divisors (f g : ArithmeticFunction ℂ) (n : ℕ)
    (hf : ∀ d, d ∣ n → 0 ≤ f d) (hg : ∀ d, d ∣ n → 0 ≤ g d) : 0 ≤ (f * g) n := by
  change 0 ≤ ∑ x ∈ Nat.divisorsAntidiagonal n, f x.1 * g x.2
  refine Finset.sum_nonneg fun x hx => ?_
  have h := (Nat.mem_divisorsAntidiagonal.1 hx).1
  exact mul_nonneg (hf _ (Dvd.intro _ h)) (hg _ (Dvd.intro_left _ h))

lemma character_convolution_eq {N N' M : ℕ} (χ : DirichletCharacter ℂ N) (χ' : DirichletCharacter ℂ N')
    (ψ : DirichletCharacter ℂ M) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    (n : ℕ) :
    (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) * toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M))) n
      = χ' (n : ZMod N') * DirichletCharacter.zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) a *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)) b), DirichletCharacter.zetaMul,
    coe_zeta_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hdvd : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
  have hni : n / i ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hi0)).ne'
  simp only [toArithmeticFunction, coe_mk, hi0, hni, if_false]
  rw [hψ i]
  calc χ' ((n / i : ℕ) : ZMod N') * (χ (i : ZMod N) * χ' (i : ZMod N'))
      = (χ' ((n / i : ℕ) : ZMod N') * χ' (i : ZMod N')) * χ (i : ZMod N) := by ring
    _ = χ' (n : ZMod N') * χ (i : ZMod N) := by
      rw [← map_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]


set_option backward.isDefEq.respectTransparency.types false in
lemma prime_power_coefficient_nonneg {N N' M : ℕ} {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ N'}
    {ψ : DirichletCharacter ℂ M} (hχ : χ ^ 2 = 1) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    {p : ℕ} (hp : p.Prime)
    (hc : χ' (p : ZMod N') = 0 ∨ χ' (p : ZMod N') = 1 ∨ (χ' (p : ZMod N') = -1 ∧ χ (p : ZMod N) = -1))
    (k : ℕ) :
    0 ≤ (DirichletCharacter.zetaMul χ * (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)))) (p ^ k) := by
  have hζ : ∀ j, DirichletCharacter.zetaMul χ (p ^ j) = ∑ i ∈ Finset.range (j + 1), χ (p : ZMod N) ^ i := by
    intro j
    rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [toArithmeticFunction, hp.ne_zero]
  apply convolution_nonneg_of_divisors
  · intro d _
    exact DirichletCharacter.zetaMul_nonneg hχ d
  · intro d hd
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [character_convolution_eq χ χ' ψ hψ, Nat.cast_pow, map_pow]
    rcases hc with h | h | ⟨h, h'⟩
    · exact mul_nonneg (by rw [h]; exact pow_nonneg le_rfl j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · exact mul_nonneg (by rw [h]; exact pow_nonneg zero_le_one j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · rw [h, hζ, h', neg_one_geom_sum]
      split_ifs with he
      · simp
      · have hj : Even j := by
          rcases Nat.even_or_odd j with hj | hj
          · exact hj
          · exact absurd hj.add_one he
        rw [hj.neg_one_pow]
        norm_num

end Formalism.ZeroFreeDirichlet
end
end

open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma dirichlet_character_lseries_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s := by
  refine (LSeriesSummable_congr s (fun {n} hn => ?_)).mpr (χ.LSeriesSummable_of_one_lt_re hs)
  simp [toArithmeticFunction, hn]

lemma dirichlet_character_lseries_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_congr (fun {n} hn => by simp [toArithmeticFunction, hn]) s

set_option backward.isDefEq.respectTransparency.types false in
lemma lseries_zetaMul_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (DirichletCharacter.zetaMul χ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have h1 : LSeriesSummable ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    have := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    exact (LSeriesSummable_congr s (fun {n} hn => by simp [hn])).mp this
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' h1 (dirichlet_character_lseries_summable χ hs),
    dirichlet_character_lseries_eq χ hs]
  congr 1
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact LSeries_congr (fun {n} hn => by simp [hn]) s

theorem dirichlet_product_coefficients : BqCoeff := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 hψ
  set f : ArithmeticFunction ℂ := DirichletCharacter.zetaMul χ₁ *
    (toArithmeticFunction (fun m : ℕ => χ₂ (m : ZMod q₂)) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) with hf

  have hvals : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 →
      ∀ x, χ x = 0 ∨ χ x = 1 ∨ χ x = -1 := by
    intro N χ hχ x
    by_cases hx : IsUnit x
    · have h := congrArg (fun φ : DirichletCharacter ℂ N => φ x) hχ
      simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hx] at h
      have h' : χ x * χ x = 1 := by rw [← sq]; exact h
      rcases (mul_self_eq_one_iff).mp h' with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · exact Or.inl (MulChar.map_nonunit χ hx)
  have hmul : f.IsMultiplicative :=
    (DirichletCharacter.isMultiplicative_zetaMul χ₁).mul
      ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ₂).mul
        (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))
  have hswap : f = DirichletCharacter.zetaMul χ₂ *
      (toArithmeticFunction (fun m : ℕ => χ₁ (m : ZMod q₁)) *
        toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) := by
    simp only [hf, DirichletCharacter.zetaMul]
    ring
  have hψ' : ∀ n : ℕ, ψ (n : ZMod (q₁ * q₂)) = χ₂ (n : ZMod q₂) * χ₁ (n : ZMod q₁) := by
    intro n
    rw [hψ n, mul_comm]
  have hpp : ∀ p k : ℕ, p.Prime → 0 ≤ f (p ^ k) := by
    intro p k hp
    rcases hvals χ₂ h2 (p : ZMod q₂) with h | h | h
    · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inl h) k
    · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inl h)) k
    · rcases hvals χ₁ h1 (p : ZMod q₁) with h' | h' | h'
      · rw [hswap]; exact prime_power_coefficient_nonneg h2 hψ' hp (Or.inl h') k
      · rw [hswap]; exact prime_power_coefficient_nonneg h2 hψ' hp (Or.inr (Or.inl h')) k
      · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inr ⟨h, h'⟩)) k
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization f hmul hn, Finsupp.prod]
      exact Finset.prod_nonneg fun p hp =>
        hpp p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))
  have hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (⇑f) s := fun s hs =>
    ArithmeticFunction.LSeriesSummable_mul (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs)
      (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs)
        (dirichlet_character_lseries_summable ψ hs))
  refine ⟨⇑f, hnn, hmul.map_one, ?_, ?_⟩
  · have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := ⇑f) (x := 1)
      (fun y hy => hsum y (by simpa using hy))
    simpa using this
  · intro s hs
    rw [Fbq, ArithmeticFunction.LSeries_mul' (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs)
      (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs)
        (dirichlet_character_lseries_summable ψ hs)),
      ArithmeticFunction.LSeries_mul' (dirichlet_character_lseries_summable χ₂ hs) (dirichlet_character_lseries_summable ψ hs),
      lseries_zetaMul_eq χ₁ hs, dirichlet_character_lseries_eq χ₂ hs, dirichlet_character_lseries_eq ψ hs]
    ring

end Formalism.ZeroFreeDirichlet
end
end
