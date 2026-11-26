module

public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardSpacedDetectedLe
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LFunctionConjEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedExplicitFormula

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsFurther
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DensityAndRegions
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReLtOneOfZero
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardUnitCellsDirichletLZerosNearOneLe
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZetaZeroDetect
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRiemannZetaSubPartialSumLe
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRiemannZetaSubPartialSumLe
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open Set

namespace GlobalTheory.ZetaPartialSum
open GlobalTheory.ZetaHalfPlane

noncomputable def tailInt (s : ℂ) (a : ℝ) : ℂ :=
  ∫ t in Ioi a, ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))

lemma norm_tailInt_le {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ‖tailInt s a‖ ≤ a ^ (-s.re) / s.re := by
  have h : -(s.re + 1) < -1 := by linarith
  calc ‖tailInt s a‖ ≤ ∫ t in Ioi a, t ^ (-(s.re + 1)) := by
        refine norm_integral_le_of_norm_le (integrableOn_Ioi_rpow_of_lt h ha) ?_
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine Eventually.of_forall fun t ht => ?_
        have ht0 : 0 < t := lt_trans ha ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        simp only [neg_re, add_re, one_re]
        exact mul_le_of_le_one_left (by positivity) (norm_fract_le t)
    _ = a ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt h ha,
          show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq]

lemma piece {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    s * ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      = (M : ℂ) ^ (1 - s) / (s - 1) - ((M : ℂ) + 1) ^ (1 - s) / (s - 1)
        - ((M : ℂ) + 1) ^ (-s) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have hle : (M : ℝ) ≤ M + 1 := by linarith
  have hmem : (0 : ℝ) ∉ uIcc (M : ℝ) (M + 1) := by
    rw [uIcc_of_le hle]
    intro h
    linarith [h.1]
  have e : ∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
      = ∫ t in (M : ℝ)..(M + 1), ((t : ℂ) ^ (-s) - (M : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := lt_trans hM0 ht.1
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
    have e1 : (t : ℂ) ^ (-s) = t * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = 1 + -(s + 1) by ring, cpow_add _ _ htc, cpow_one]
    have e2 : ⌊t⌋ = (M : ℤ) := by
      rw [Int.floor_eq_iff]
      exact ⟨by simpa using ht.1.le, by simpa using ht.2⟩
    have e3 : Int.fract t = t - M := by
      rw [Int.fract, e2]; simp
    rw [e1, e3]
    push_cast
    ring
  have i1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s)) volume (M : ℝ) (M + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)
  have i2 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) volume (M : ℝ) (M + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr hmem)
  have n1 : -s ≠ -1 := fun h => hs1 (neg_injective h)
  have n2 : -(s + 1) ≠ -1 := fun h => hs0 (by linear_combination -h)
  rw [e, intervalIntegral.integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨n1, hmem⟩), integral_cpow (Or.inr ⟨n2, hmem⟩)]
  push_cast
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hMc1 : (M : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero M)
  have a1 : (M : ℂ) ^ (1 - s) = M * (M : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hMc, cpow_one]
  have a2 : ((M : ℂ) + 1) ^ (1 - s) = (M + 1) * ((M : ℂ) + 1) ^ (-s) := by
    rw [sub_eq_add_neg, cpow_add _ _ hMc1, cpow_one]
  rw [show -s + 1 = 1 - s by ring, show -(s + 1) + 1 = -s by ring, a1, a2]
  have hs1'' : 1 - s ≠ 0 := sub_ne_zero.2 hs1.symm
  field_simp
  ring

theorem zeta_eq_sum {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    riemannZeta s = ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) + (M : ℂ) ^ (1 - s) / (s - 1)
      - s * tailInt s M := by
  induction M, hM using Nat.le_induction with
  | base =>
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.2 hs1
    rw [zeta_eq hs hs1]
    simp only [Finset.Icc_self, Finset.sum_singleton, Nat.cast_one, one_cpow, tailInt, fractInt]
    field_simp
    ring
  | succ M hM ih =>
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hle : (M : ℝ) ≤ M + 1 := by linarith
    have hsplit : tailInt s M
        = (∫ t in Ioc (M : ℝ) (M + 1), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
          + tailInt s ((M : ℝ) + 1) := by
      unfold tailInt
      rw [← Ioc_union_Ioi_eq_Ioi hle, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi]
      · exact (integrableOn_integrand hs).mono_set fun t ht => lt_of_le_of_lt hM1 ht.1
      · exact (integrableOn_integrand hs).mono_set fun t ht =>
          lt_of_le_of_lt (hM1.trans hle) ht
    rw [ih, Finset.sum_Icc_succ_top (by omega), hsplit, mul_add, piece hs hs1 hM]
    push_cast
    ring

theorem norm_zeta_sub_sum_le :
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ M : ℕ, 1 ≤ M →
      ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)‖
        ≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re) := by
  intro s hs hs1 M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have e : riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)
      = -(s * tailInt s M) := by
    rw [zeta_eq_sum hs hs1 hM]; ring
  rw [e, norm_neg, norm_mul, div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (norm_tailInt_le hs hM0) (norm_nonneg s)

end GlobalTheory.ZetaPartialSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormRiemannZetaSubPartialSumLeStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_riemannZeta_sub_partial_sum_le : ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ M : ℕ, 1 ≤ M → ‖riemannZeta s - ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) - (M : ℂ) ^ (1 - s) / (s - 1)‖ ≤ ‖s‖ / s.re * (M : ℝ) ^ (-s.re) := by
  first | exact @GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le | exact GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le | (intros; apply GlobalTheory.ZetaPartialSum.norm_zeta_sub_sum_le <;> assumption)
end
end

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroDetect

theorem pole_small : ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    (1 + Real.log ((Q ^ 3 : ℕ) : ℝ)) * (((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) / (Q : ℝ) ^ ((1 : ℝ) / 20))
      ≤ 1 / 4 := by
  have h : Tendsto (fun Q : ℕ => (Q : ℝ) ^ ((1 : ℝ) / 40)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨Q₀, hQ₀⟩ := eventually_atTop.mp (h.eventually_ge_atTop 1204)
  refine ⟨max Q₀ 1, fun Q hQ => ?_⟩
  have h1 := hQ₀ Q (le_of_max_le_left hQ)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast le_of_max_le_right hQ
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hlog := Real.log_le_rpow_div hQ0.le (show (0 : ℝ) < 1 / 100 by norm_num)
  have hone : (1 : ℝ) ≤ (Q : ℝ) ^ ((1 : ℝ) / 100) := Real.one_le_rpow hQ1 (by norm_num)
  have h2 : 1 + Real.log ((Q ^ 3 : ℕ) : ℝ) ≤ 301 * (Q : ℝ) ^ ((1 : ℝ) / 100) := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith
  have h3 : (Q : ℝ) ^ ((1 : ℝ) / 20) = (Q : ℝ) ^ ((1 : ℝ) / 100) *
      ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) * (Q : ℝ) ^ ((1 : ℝ) / 40) := by
    rw [← Real.rpow_natCast (Q : ℝ) 6, ← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0,
      ← Real.rpow_add hQ0]
    norm_num
  have ha : 0 < ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) := by positivity
  rw [h3]
  set a := ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400)
  set b := (Q : ℝ) ^ ((1 : ℝ) / 100)
  set c := (Q : ℝ) ^ ((1 : ℝ) / 40)
  have hb : 0 < b := by linarith
  have hc : 0 < c := by linarith
  calc _ ≤ 301 * b * (a / (b * a * c)) := by gcongr
    _ = 301 / c := by field_simp
    _ ≤ 1 / 4 := by rw [div_le_iff₀ hc]; linarith

theorem zeta_zero_detect : ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q → ∀ ρ : ℂ, 1 - 1 / 400 ≤ ρ.re → ρ.re < 1 → (Q : ℝ) ^ ((1 : ℝ) / 20) ≤ |ρ.im| → |ρ.im| ≤ Q → riemannZeta ρ = 0 → (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * (1 : ℂ) * (n : ℂ) ^ (-ρ)‖ := by
  obtain ⟨Q₀, hQ₀⟩ := pole_small
  refine ⟨max Q₀ 1024, fun Q hQ' ρ hre hre1 hlow him hL => ?_⟩
  have hpole := hQ₀ Q (le_of_max_le_left hQ')
  have hQ : 1024 ≤ Q := le_of_max_le_right hQ'
  set f : ℕ → ℂ := fun n => (n : ℂ) ^ (-ρ) with hfdef
  have hf : ∀ m n, 0 < m → 0 < n → f (m * n) = f m * f n := by
    intro m n _ _
    simp only [hfdef, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have hf1 : f 1 = 1 := by simp [hfdef]
  have hQ1 : 1 ≤ Q := by omega
  have hQr : (1024 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hD1 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ1
  have hD2 : 2 ≤ Q ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) Q)
  have hX : Q ^ 6 = Q ^ 3 * Q ^ 3 := by ring
  have hDX : Q ^ 3 ≤ Q ^ 6 := Nat.pow_le_pow_right hQ1 (by norm_num)
  have hσ : 0 < ρ.re := by linarith
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at hre1; simp at hre1
  have hρ : ‖ρ‖ / ρ.re ≤ 4 * Q := by
    have h1 : ‖ρ‖ ≤ ρ.re + Q := by
      have := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_pos hσ] at this; linarith
    rw [div_le_iff₀ hσ]; nlinarith
  have hG : 0 < (Q : ℝ) ^ ((1 : ℝ) / 20) := by positivity
  have hden : (Q : ℝ) ^ ((1 : ℝ) / 20) ≤ ‖ρ - 1‖ := by
    have := Complex.abs_im_le_norm (ρ - 1)
    simp only [sub_im, one_im, sub_zero] at this
    linarith
  set B : ℝ := ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) / (Q : ℝ) ^ ((1 : ℝ) / 20) with hB
  have hB0 : 0 ≤ B := by positivity
  have hconv := sum_trunc_conv (fun d => ((moebius d : ℤ) : ℂ)) f hf (Q ^ 3) (Q ^ 6)
  have hinit := sum_initial f (Q ^ 3) hD1
  have hbound : ‖∑ d ∈ Finset.Icc 1 (Q ^ 3), ((moebius d : ℤ) : ℂ) * f d *
      ∑ m ∈ Finset.Icc 1 (Q ^ 6 / d), f m‖ ≤ 1 / 2 := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun d : ℕ => 1 / (4 * (Q : ℝ) ^ 3) + (d : ℝ)⁻¹ * B) ?_).trans ?_
    · intro d hd
      obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
      have hN : 1 ≤ Q ^ 6 / d := Nat.div_pos (hdD.trans hDX) hd1
      have ht := GlobalTheory.T.norm_riemannZeta_sub_partial_sum_le ρ hσ hρ1 _ hN
      have hy : Q ^ 6 ≤ 2 * (d * (Q ^ 6 / d)) := by
        have h1 := Nat.div_add_mod (Q ^ 6) d
        have h2 := Nat.mod_lt (Q ^ 6) hd1
        have h3 : 2 * Q ^ 3 ≤ Q ^ 6 := by rw [hX]; exact Nat.mul_le_mul_right _ hD2
        omega
      have hy2 : d * (Q ^ 6 / d) ≤ Q ^ 6 := Nat.mul_div_le _ _
      generalize Q ^ 6 / d = M at *
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hM0 : (0 : ℝ) < M := by exact_mod_cast hN
      rw [hL, zero_sub, ← neg_add', norm_neg] at ht
      have hμ : ‖((moebius d : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
      have hfd : ‖f d‖ = (d : ℝ) ^ (-ρ.re) := by
        simp only [hfdef]
        rw [Complex.norm_natCast_cpow_of_pos hd1, Complex.neg_re]
      have hr := rpow_bound (y := (d : ℝ) * (M : ℝ)) (σ := ρ.re) hQr
        (by exact_mod_cast hy) (by linarith)
      rw [Real.mul_rpow (by positivity) (by positivity)] at hr
      have hp : ‖(M : ℂ) ^ (1 - ρ) / (ρ - 1)‖ ≤ (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by
        rw [norm_div, Complex.norm_natCast_cpow_of_pos hN]
        simp only [sub_re, one_re]
        gcongr
      have ht2 : ‖∑ m ∈ Finset.Icc 1 M, f m‖
          ≤ 4 * Q * (M : ℝ) ^ (-ρ.re) + (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by
        have h1 := norm_sub_le (∑ m ∈ Finset.Icc 1 M, f m + (M : ℂ) ^ (1 - ρ) / (ρ - 1))
          ((M : ℂ) ^ (1 - ρ) / (ρ - 1))
        rw [add_sub_cancel_right] at h1
        have h2 : ‖ρ‖ / ρ.re * (M : ℝ) ^ (-ρ.re) ≤ 4 * Q * (M : ℝ) ^ (-ρ.re) := by gcongr
        simp only [hfdef] at h1 ⊢
        linarith
      have hq : (d : ℝ) ^ (-ρ.re) * (M : ℝ) ^ (1 - ρ.re)
          ≤ (d : ℝ)⁻¹ * ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) := by
        have h1 : (d : ℝ) ^ (-ρ.re) = (d : ℝ)⁻¹ * (d : ℝ) ^ (1 - ρ.re) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hd0]; congr 1; ring
        rw [h1, mul_assoc, ← Real.mul_rpow hd0.le hM0.le]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h2 : (d : ℝ) * M ≤ (Q : ℝ) ^ 6 := by exact_mod_cast hy2
        refine (Real.rpow_le_rpow (by positivity) h2 (by linarith)).trans ?_
        exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by linarith)) (by linarith)
      have h3 : 4 * (Q : ℝ) * (16 * (Q : ℝ) ^ 5)⁻¹ ≤ 1 / (4 * (Q : ℝ) ^ 3) := by
        have : 4 * (Q : ℝ) * (16 * (Q : ℝ) ^ 5)⁻¹ = 1 / (4 * (Q : ℝ) ^ 4) := by
          field_simp; norm_num
        rw [this]
        gcongr
        · linarith
        · norm_num
      rw [norm_mul, norm_mul, hfd]
      calc _ ≤ 1 * (d : ℝ) ^ (-ρ.re) *
              (4 * Q * (M : ℝ) ^ (-ρ.re) + (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20)) := by
            gcongr
        _ = 4 * Q * ((d : ℝ) ^ (-ρ.re) * (M : ℝ) ^ (-ρ.re)) +
              (d : ℝ) ^ (-ρ.re) * (M : ℝ) ^ (1 - ρ.re) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by ring
        _ ≤ 4 * Q * (16 * (Q : ℝ) ^ 5)⁻¹ +
              (d : ℝ)⁻¹ * ((Q : ℝ) ^ 6) ^ ((1 : ℝ) / 400) / (Q : ℝ) ^ ((1 : ℝ) / 20) := by gcongr
        _ ≤ _ := by rw [hB, mul_div_assoc]; linarith
    · rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const]
      have hh : ∑ d ∈ Finset.Icc 1 (Q ^ 3), (d : ℝ)⁻¹ ≤ 1 + Real.log ((Q ^ 3 : ℕ) : ℝ) := by
        have := harmonic_le_one_add_log (Q ^ 3)
        rw [harmonic_eq_sum_Icc] at this
        push_cast at this ⊢
        exact this
      have h1 : (Finset.Icc 1 (Q ^ 3)).card • (1 / (4 * (Q : ℝ) ^ 3)) = 1 / 4 := by
        simp only [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_pow]
        field_simp
      have h2 := mul_le_mul_of_nonneg_right hh hB0
      linarith
  rw [← hconv, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hDX] at hbound
  simp only [Int.cast_sum] at hinit
  rw [hinit, hf1] at hbound
  simp only [Int.cast_sum, mul_one]
  have := norm_sub_le (1 + ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
    (∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), ((moebius d : ℤ) : ℂ)) * f n)
    (∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6),
    (∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), ((moebius d : ℤ) : ℂ)) * f n)
  rw [add_sub_cancel_right, norm_one] at this
  simp only [hfdef] at this hbound
  linarith

end GlobalTheory.ZeroDetect
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardUnitCellsDirichletLZerosNearOneLe
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroCells

lemma one_le_abs_sub_of_floor {x y : ℝ} (hne : ⌊x⌋ ≠ ⌊y⌋) (hpar : ⌊x⌋ % 2 = ⌊y⌋ % 2) :
    1 ≤ |x - y| := by
  obtain ⟨k, hk⟩ := Int.ModEq.dvd hpar
  have hx1 := Int.floor_le x
  have hx2 := Int.lt_floor_add_one x
  have hy1 := Int.floor_le y
  have hy2 := Int.lt_floor_add_one y
  rcases lt_or_gt_of_ne hne with h | h
  · have h2 : ⌊x⌋ + 2 ≤ ⌊y⌋ := by omega
    have h2' : (⌊x⌋ : ℝ) + 2 ≤ ⌊y⌋ := by exact_mod_cast h2
    rw [le_abs]
    right
    linarith
  · have h2 : ⌊y⌋ + 2 ≤ ⌊x⌋ := by omega
    have h2' : (⌊y⌋ : ℝ) + 2 ≤ ⌊x⌋ := by exact_mod_cast h2
    rw [le_abs]
    left
    linarith

lemma ne_one_of_primitive {N : ℕ} (hN : N ≠ 0) {χ : DirichletCharacter ℂ (N + 1)}
    (h : χ.IsPrimitive) : χ ≠ 1 := by
  rintro rfl
  rw [isPrimitive_def, conductor_one] at h
  omega

private theorem exists_subset_injOn_card_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    [Nonempty α] (U : Finset α) (f : α → β) :
    ∃ R ⊆ U, (U.image f).card = R.card ∧ ∀ r ∈ R, ∀ r' ∈ R, f r = f r' → r = r' := by
  have hback : ∀ r ∈ (U.image f).image (Function.invFunOn f ↑U),
      Function.invFunOn f ↑U (f r) = r := by
    intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    rw [Function.invFunOn_eq (f := f) (s := ↑U) ⟨p, hp, rfl⟩]
  refine ⟨(U.image f).image (Function.invFunOn f ↑U), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    exact Function.invFunOn_mem ⟨p, hp, rfl⟩
  · refine (Finset.card_image_of_injOn ?_).symm
    intro c hc c' hc' h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc')
    calc f p = f (Function.invFunOn f ↑U (f p)) :=
          (Function.invFunOn_eq (f := f) (s := ↑U) ⟨p, hp, rfl⟩).symm
      _ = f (Function.invFunOn f ↑U (f p')) := by rw [h]
      _ = f p' := Function.invFunOn_eq (f := f) (s := ↑U) ⟨p', hp', rfl⟩
  · intro r hr r' hr' h
    rw [← hback r hr, ← hback r' hr', h]

theorem ncard_cells_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((((fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => (⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) '' (T : Set (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))).ncard : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 8) := by
  classical
  obtain ⟨Q₁, hQ₁⟩ := GlobalTheory.ZeroDetect.zero_detect
  obtain ⟨Q₂, hQ₂⟩ := GlobalTheory.ZeroDetect.zeta_zero_detect
  obtain ⟨C₁, hC₁, hsp⟩ := GlobalTheory.SpacedDetected.card_spaced_detected_le
  refine ⟨(2 * C₁ + 5) * ((Q₁ + Q₂ + 2 : ℕ) : ℝ), by positivity, ?_⟩
  intro Q hQ T hT
  set Qn : ℕ := max (max Q₁ Q₂) ⌈Q⌉₊ with hQn_def
  have hceil3 : 2 < ⌈Q⌉₊ := Nat.lt_ceil.2 (by push_cast; linarith)
  have hQn2 : 2 ≤ Qn := le_trans (by omega : 2 ≤ ⌈Q⌉₊) (le_max_right _ _)
  have hQle : Q ≤ (Qn : ℝ) := (Nat.le_ceil Q).trans (by exact_mod_cast le_max_right _ _)
  have hQn1 : (1 : ℝ) ≤ Qn := by exact_mod_cast (by omega : 1 ≤ Qn)
  have hQnpos : (0 : ℝ) < Qn := by linarith
  have hQnle : (Qn : ℝ) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q := by
    have h1 : Qn ≤ Q₁ + Q₂ + ⌈Q⌉₊ := max_le (max_le (by omega) (by omega)) (by omega)
    have h2 : (⌈Q⌉₊ : ℝ) < Q + 1 := Nat.ceil_lt_add_one (by linarith)
    have h1' : (Qn : ℝ) ≤ Q₁ + Q₂ + ⌈Q⌉₊ := by exact_mod_cast h1
    have h3 : (0 : ℝ) ≤ Q₁ := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ Q₂ := Nat.cast_nonneg _
    push_cast
    nlinarith
  have hpow : (Qn : ℝ) ^ ((1 : ℝ) / 8) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by
    have hB : (1 : ℝ) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q₁ + Q₂ + 2)
    calc (Qn : ℝ) ^ ((1 : ℝ) / 8) ≤ (((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q) ^ ((1 : ℝ) / 8) :=
          Real.rpow_le_rpow hQnpos.le hQnle (by norm_num)
      _ = ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) * Q ^ ((1 : ℝ) / 8) :=
          Real.mul_rpow (by positivity) (by linarith)
      _ ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by
          gcongr
          calc ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ ((1 : ℝ) / 8) ≤ ((Q₁ + Q₂ + 2 : ℕ) : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hB (by norm_num)
            _ = _ := Real.rpow_one _
  have hA : ∀ p ∈ T, ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)) →
      p.1 + 1 ≤ Qn ∧ p.2.1.IsPrimitive ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ p.2.2.re ≤ 1 ∧
        |p.2.2.im| ≤ Qn ∧ (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Qn ^ 3) (Qn ^ 6),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Qn ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
            p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2)‖ := by
    rintro ⟨N, χ, ρ⟩ hp hns
    obtain ⟨hlev, hprim, hL, hre, him⟩ : ((N + 1 : ℕ) : ℝ) ≤ Q ∧ χ.IsPrimitive ∧
        LFunction χ ρ = 0 ∧ 1 - 1 / 400 ≤ ρ.re ∧ |ρ.im| ≤ Q := hT _ hp
    have hlevN : N + 1 ≤ Qn := by
      have : ((N + 1 : ℕ) : ℝ) ≤ (Qn : ℝ) := hlev.trans hQle
      exact_mod_cast this
    have him' : |ρ.im| ≤ (Qn : ℝ) := him.trans hQle
    have hre1 : ρ.re ≤ 1 := by
      by_contra hgt
      rw [not_le] at hgt
      have hne : ρ ≠ 1 := by
        intro h
        rw [h, Complex.one_re] at hgt
        exact lt_irrefl _ hgt
      exact LFunction_ne_zero_of_one_le_re χ (.inr hne) hgt.le hL
    refine ⟨hlevN, hprim, hre, hre1, him', ?_⟩
    by_cases hN : N = 0
    · subst hN
      have hpos : 0 < (Qn : ℝ) ^ ((1 : ℝ) / 20) := Real.rpow_pos_of_pos hQnpos _
      have hbig : (Qn : ℝ) ^ ((1 : ℝ) / 20) ≤ |ρ.im| := by
        by_contra h
        rw [not_le] at h
        exact hns ⟨rfl, h⟩
      have hne1 : ρ ≠ 1 := by
        intro h
        rw [h, Complex.one_im, abs_zero] at hbig
        linarith
      have hrelt : ρ.re < 1 := by
        rcases lt_or_eq_of_le hre1 with h | h
        · exact h
        · exact absurd hL (LFunction_ne_zero_of_one_le_re χ (.inr hne1) h.ge)
      have hz : riemannZeta ρ = 0 := by
        have e : LFunction χ ρ = riemannZeta ρ := congrFun LFunction_modOne_eq ρ
        rw [← e]
        exact hL
      have key := hQ₂ Qn (le_trans (le_max_right _ _) (le_max_left _ _)) ρ hre hrelt hbig him' hz
      have : Subsingleton (ZMod (0 + 1)) := ZMod.subsingleton_iff.2 rfl
      have hχ : ∀ a : ZMod (0 + 1), χ a = 1 := fun a => by
        rw [Subsingleton.elim a 1, MulChar.map_one]
      show (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Qn ^ 3) (Qn ^ 6),
          ((∑ d ∈ n.divisors.filter (fun d => d ≤ Qn ^ 3), (moebius d : ℤ) : ℤ) : ℂ) *
            χ (n : ZMod (0 + 1)) * (n : ℂ) ^ (-ρ)‖
      simp only [hχ]
      exact key
    · exact hQ₁ Qn (le_trans (le_max_left _ _) (le_max_left _ _)) (N + 1) χ
        (ne_one_of_primitive hN hprim) hlevN ρ hre him' hL
  rw [← Finset.coe_image, Set.ncard_coe_finset]
  set f : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) :=
    fun p => ⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ with hf
  have : Nonempty (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) := ⟨⟨0, 1, 0⟩⟩
  have hcount : ∀ U ⊆ T, (∀ p ∈ U, ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20))) →
      (∀ p ∈ U, ∀ p' ∈ U, ⌊p.2.2.im⌋ % 2 = ⌊p'.2.2.im⌋ % 2) →
      ((U.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) := by
    intro U hU hns hpar
    obtain ⟨R, hRU, hcard, hinj⟩ := exists_subset_injOn_card_image U f
    rw [hcard]
    refine hsp Qn hQn2 R ?_ ?_
    · intro p hp
      exact hA p (hU (hRU hp)) (hns p (hRU hp))
    · intro N χ ρ ρ' h1 h2 hne
      by_cases hfl : ⌊ρ.im⌋ = ⌊ρ'.im⌋
      · exfalso
        apply hne
        have e := hinj _ h1 _ h2 (by
          show (⟨N, χ, ⌊ρ.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) = ⟨N, χ, ⌊ρ'.im⌋⟩
          rw [hfl])
        exact congrArg (fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => p.2.2) e
      · exact one_le_abs_sub_of_floor hfl (hpar _ (hRU h1) _ (hRU h2))
  set Ts := T.filter (fun p => p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)) with hTs
  set Tb := T.filter (fun p => ¬ (p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20))) with hTb
  set T0 := Tb.filter (fun p => ⌊p.2.2.im⌋ % 2 = 0) with hT0
  set T1 := Tb.filter (fun p => ¬ ⌊p.2.2.im⌋ % 2 = 0) with hT1
  have hsub : T.image f ⊆ Ts.image f ∪ (T0.image f ∪ T1.image f) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    by_cases h1 : p.1 = 0 ∧ |p.2.2.im| < (Qn : ℝ) ^ ((1 : ℝ) / 20)
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem f (Finset.mem_filter.2 ⟨hp, h1⟩))
    · by_cases h2 : ⌊p.2.2.im⌋ % 2 = 0
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_image_of_mem f
          (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp, h1⟩, h2⟩)))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_image_of_mem f
          (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hp, h1⟩, h2⟩)))
  have hb0 : ((T0.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    hcount T0 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2)
      (fun p hp p' hp' => by rw [(Finset.mem_filter.1 hp).2, (Finset.mem_filter.1 hp').2])
  have hb1 : ((T1.image f).card : ℝ) ≤ C₁ * (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    hcount T1 (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1)
      (fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).2)
      (fun p hp p' hp' => by
        have e1 := (Finset.mem_filter.1 hp).2
        have e2 := (Finset.mem_filter.1 hp').2
        omega)
  set M : ℕ := ⌈(Qn : ℝ) ^ ((1 : ℝ) / 20)⌉₊ with hM
  have : Subsingleton (DirichletCharacter ℂ (0 + 1)) :=
    (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
  have hsmallsub : Ts.image f ⊆ (Finset.range (2 * M + 1)).image
      (fun k : ℕ => (⟨0, 1, (k : ℤ) - M⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨N, χ, ρ⟩ := p
    obtain ⟨-, hN0, hlt⟩ := Finset.mem_filter.1 hp
    have hN : N = 0 := hN0
    subst hN
    have hlt' : |ρ.im| < (M : ℝ) := lt_of_lt_of_le hlt (Nat.le_ceil _)
    have hfl1 : (⌊ρ.im⌋ : ℝ) ≤ ρ.im := Int.floor_le _
    have hfl2 : ρ.im < ⌊ρ.im⌋ + 1 := Int.lt_floor_add_one _
    have ha := abs_lt.1 hlt'
    have hA1 : ⌊ρ.im⌋ < (M : ℤ) := by
      have : (⌊ρ.im⌋ : ℝ) < ((M : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hA2 : -(M : ℤ) < ⌊ρ.im⌋ + 1 := by
      have : ((-(M : ℤ) : ℤ) : ℝ) < ((⌊ρ.im⌋ + 1 : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have ht : (((⌊ρ.im⌋ + M).toNat : ℕ) : ℤ) = ⌊ρ.im⌋ + M := Int.toNat_of_nonneg (by omega)
    refine Finset.mem_image.2 ⟨(⌊ρ.im⌋ + M).toNat, Finset.mem_range.2 (by omega), ?_⟩
    have hχ : χ = 1 := Subsingleton.elim _ _
    subst hχ
    show (⟨0, 1, (((⌊ρ.im⌋ + M).toNat : ℕ) : ℤ) - M⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) =
      ⟨0, 1, ⌊ρ.im⌋⟩
    rw [ht, add_sub_cancel_right]
  have hsmallcard : ((Ts.image f).card : ℝ) ≤ 2 * (M : ℝ) + 1 := by
    have h := (Finset.card_le_card hsmallsub).trans Finset.card_image_le
    rw [Finset.card_range] at h
    exact_mod_cast h
  have hcard : ((T.image f).card : ℝ) ≤
      (Ts.image f).card + ((T0.image f).card + (T1.image f).card) := by
    have h := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (add_le_add (le_refl _) (Finset.card_union_le _ _)))
    exact_mod_cast h
  have hM1 : (M : ℝ) < (Qn : ℝ) ^ ((1 : ℝ) / 20) + 1 := Nat.ceil_lt_add_one (by positivity)
  have he1 : (Qn : ℝ) ^ ((1 : ℝ) / 20) ≤ (Qn : ℝ) ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_le hQn1 (by norm_num)
  have he2 : (1 : ℝ) ≤ (Qn : ℝ) ^ ((1 : ℝ) / 8) := Real.one_le_rpow hQn1 (by norm_num)
  calc ((T.image f).card : ℝ) ≤ (2 * C₁ + 5) * (Qn : ℝ) ^ ((1 : ℝ) / 8) := by linarith
    _ ≤ (2 * C₁ + 5) * (((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_left hpow (by linarith)
    _ = (2 * C₁ + 5) * ((Q₁ + Q₂ + 2 : ℕ) : ℝ) * Q ^ ((1 : ℝ) / 8) := by ring

end GlobalTheory.ZeroCells
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardUnitCellsDirichletLZerosNearOneLeStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ncard_unitCells_dirichletLZeros_near_one_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((((fun p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) => (⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ)) '' (T : Set (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))).ncard : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 8) := by
  first | exact @GlobalTheory.ZeroCells.ncard_cells_le | exact GlobalTheory.ZeroCells.ncard_cells_le | (intros; apply GlobalTheory.ZeroCells.ncard_cells_le <;> assumption)
end
end

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ZeroDensityMult

theorem re_lt_one_of_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h : LFunction χ ρ = 0) : ρ.re < 1 := by
  by_contra hc
  push Not at hc
  by_cases h1 : χ = 1
  · have hN : N = 1 := by
      have h := hχ
      rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at h
      exact h.symm
    subst hN
    rw [LFunction_modOne_eq] at h
    exact riemannZeta_ne_zero_of_one_le_re hc h
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl h1) hc h

theorem log_le {Q N t : ℝ} (hQ : 3 ≤ Q) (hN0 : 0 < N) (hN : N ≤ Q) (ht : |t| ≤ Q + 1) :
    Real.log (N * (|t| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
  have h0 := abs_nonneg t
  have h1 : N * (|t| + 2) ≤ Q ^ 3 := by
    have : N * (|t| + 2) ≤ Q * (Q + 3) := mul_le_mul hN (by linarith) (by linarith) (by linarith)
    have h4 : Q + 3 ≤ Q ^ 2 := by nlinarith
    have h5 : Q * (Q + 3) ≤ Q * Q ^ 2 := mul_le_mul_of_nonneg_left h4 (by linarith)
    have h6 : Q * Q ^ 2 = Q ^ 3 := by ring
    linarith
  have h2 : Real.log (N * (|t| + 2)) ≤ Real.log (Q ^ 3) := Real.log_le_log (by positivity) h1
  have h3 := Real.log_le_rpow_div (x := Q) (ε := (1 : ℝ) / 8) (by linarith) (by norm_num)
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

theorem zero_density_mult : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C * Q ^ ((1 : ℝ) / 4) := by
  classical
  obtain ⟨C₁, hC₁, H₁⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  obtain ⟨C₂, hC₂, H₂⟩ := GlobalTheory.T.ncard_unitCells_dirichletLZeros_near_one_le
  refine ⟨C₂ * (C₁ * 24), by positivity, ?_⟩
  intro Q hQ T hT
  have hQ0 : 0 < Q := by linarith
  have hcard := H₂ Q hQ T hT
  set g : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℤ) :=
    fun p => ⟨p.1, p.2.1, ⌊p.2.2.im⌋⟩ with hg
  rw [← Finset.coe_image, Set.ncard_coe_finset] at hcard
  push_cast
  rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := T.image g) (g := g)
    (fun p hp => Finset.mem_image_of_mem g hp)]
  have hcell : ∀ c ∈ T.image g, ∑ p ∈ T with g p = c,
      ((analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C₁ * (24 * Q ^ ((1 : ℝ) / 8)) := by
    intro c hc
    obtain ⟨⟨n, χ, z⟩, hz, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨a1, a2, -, -, a5⟩ := hT _ hz
    simp only at a1 a2 a5
    obtain ⟨hfin, hsum⟩ := H₁ (n + 1) χ a2 (⌊z.im⌋ : ℤ)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    have hl : Real.log (((n + 1 : ℕ) : ℝ) * (|((⌊z.im⌋ : ℤ) : ℝ)| + 2)) ≤ 24 * Q ^ ((1 : ℝ) / 8) := by
      refine log_le hQ (by positivity) a1 ?_
      have b1 := Int.floor_le z.im
      have b2 := Int.lt_floor_add_one z.im
      rw [abs_le] at a5 ⊢
      constructor <;> linarith [a5.1, a5.2]
    refine le_trans ?_ (hsum.trans (mul_le_mul_of_nonneg_left hl hC₁.le))
    have hinj : Function.Injective
        (fun ρ : ℂ => (⟨n, χ, ρ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) := by
      intro x y h
      simpa using h
    have e := Finset.sum_image (s := hfin.toFinset)
      (g := fun ρ : ℂ => (⟨n, χ, ρ⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ))
      (f := fun p => ((analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ)) hinj.injOn
    refine le_trans ?_ e.le
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Nat.cast_nonneg _
    rintro ⟨m, ψ, ρ⟩ hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hp, hgp⟩ := hp
    obtain ⟨-, b2, b3, b4, -⟩ := hT _ hp
    simp only [hg] at hgp b2 b3 b4
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 hgp
    have h3 := eq_of_heq h2
    obtain ⟨rfl, h4⟩ := Prod.mk.inj h3
    refine Finset.mem_image.2 ⟨ρ, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    refine ⟨by linarith, re_lt_one_of_zero _ b2 b3, ?_, b3⟩
    have c1 := Int.floor_le ρ.im
    have c2 := Int.lt_floor_add_one ρ.im
    rw [← h4, abs_le]
    constructor <;> linarith
  refine (Finset.sum_le_card_nsmul _ _ _ hcell).trans ?_
  rw [nsmul_eq_mul]
  have hp : Q ^ ((1 : ℝ) / 4) = Q ^ ((1 : ℝ) / 8) * Q ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_add hQ0]; norm_num
  rw [hp]
  calc _ ≤ (C₂ * Q ^ ((1 : ℝ) / 8)) * (C₁ * (24 * Q ^ ((1 : ℝ) / 8))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end GlobalTheory.ZeroDensityMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NeOneOfIsPrimitive
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZeroFreeHalf

theorem inRegion_of_max {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 3 ≤ N) {ρ : ℂ}
    (h : 1 - c / 2 / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re) : Formalism.ZeroFreeDirichlet.InRegion c N ρ := by
  unfold Formalism.ZeroFreeDirichlet.InRegion
  set M := max (N : ℝ) (N * |ρ.im|) with hM
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hMN : (N : ℝ) ≤ M := le_max_left _ _
  have hMt : (N : ℝ) * |ρ.im| ≤ M := le_max_right _ _
  have hMpos : 0 < M := by linarith
  have ht := abs_nonneg ρ.im
  have hA : (N : ℝ) * (|ρ.im| + 2) ≤ M ^ 2 := by nlinarith
  have hA1 : 1 < (N : ℝ) * (|ρ.im| + 2) := by nlinarith
  have hL : 0 < Real.log ((N : ℝ) * (|ρ.im| + 2)) := Real.log_pos hA1
  have hle : Real.log ((N : ℝ) * (|ρ.im| + 2)) ≤ 2 * Real.log M := by
    have e := Real.log_le_log (by linarith) hA
    rw [Real.log_pow] at e
    push_cast at e
    linarith
  have hdiv : c / (2 * Real.log M) ≤ c / Real.log ((N : ℝ) * (|ρ.im| + 2)) :=
    div_le_div_of_nonneg_left hc.le hL hle
  rw [div_div] at h
  linarith

theorem isRealChar_of_sq {N : ℕ} (χ : DirichletCharacter ℂ N) (h : χ ^ 2 = 1) : IsRealChar χ := by
  intro a
  by_cases ha : IsUnit a
  · have h2 : χ a * χ a = 1 := by
      rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, h, MulChar.one_apply ha]
    rcases mul_self_eq_one_iff.mp h2 with e | e <;> simp [e]
  · simp [MulChar.map_nonunit χ ha]

theorem ne_one_of_isPrimitive {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive)
    (hN : 3 ≤ N) : χ ≠ 1 := by
  intro h1
  rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hp
  omega

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet → ∃ c : ℝ, 0 < c ∧ (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧ (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  intro hZ
  obtain ⟨c, hc, hZ⟩ := hZ
  refine ⟨c / 2, by positivity, ?_, ?_⟩
  · intro N _ χ hp hN ρ hρ hreg
    have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive χ hp hN
    obtain ⟨hsq, -, him, hder, huniq⟩ :=
      hZ N χ ρ (inRegion_of_max hc hN hreg) ⟨Or.inl hχ1, hρ⟩
    refine ⟨isRealChar_of_sq χ hsq, him, ?_, ?_⟩
    · have han : AnalyticAt ℂ (LFunction χ) ρ :=
        (DirichletCharacter.differentiable_LFunction hχ1).analyticAt ρ
      simp [analyticOrderNatAt, han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hρ hder]
    · intro ρ' hρ' hreg'
      exact (huniq χ ρ' (inRegion_of_max hc hN hreg') ⟨Or.inl hχ1, hρ'⟩).2
  · intro ρ hρ _ hre1
    by_contra hlt
    rw [not_le] at hlt
    have ht := abs_nonneg ρ.im
    have hR : Formalism.ZeroFreeDirichlet.InRegion c 1 ρ := by
      unfold Formalism.ZeroFreeDirichlet.InRegion
      have ha : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith)
      have hab : Real.log (|ρ.im| + 2) ≤ 2 * Real.log (|ρ.im| + 3) := by
        have e := Real.log_le_log (by linarith) (by linarith : |ρ.im| + 2 ≤ |ρ.im| + 3)
        have e2 : 0 ≤ Real.log (|ρ.im| + 3) := Real.log_nonneg (by linarith)
        linarith
      have hdiv := div_le_div_of_nonneg_left hc.le ha hab
      rw [div_div] at hlt
      simp only [Nat.cast_one, one_mul]
      linarith
    have hne : ρ ≠ 1 := by
      rintro rfl
      simp at hre1
    have hZ0 : Formalism.ZeroFreeDirichlet.IsLZero (1 : DirichletCharacter ℂ 1) ρ :=
      ⟨Or.inr hne, by rw [DirichletCharacter.LFunction_modOne_eq]; exact hρ⟩
    exact (hZ 1 1 ρ hR hZ0).2.1 rfl

end GlobalTheory.ZeroFreeHalf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InRegionMono
open Complex DirichletCharacter

namespace GlobalTheory.LandauPageRegion

theorem inRegion_mono {c c' : ℝ} (h : c ≤ c') (q : ℕ) [NeZero q] {s : ℂ}
    (hs : Formalism.ZeroFreeDirichlet.InRegion c q s) : 1 - c' / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hL : 0 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ |s.im| + 2 := by linarith [abs_nonneg s.im]
    nlinarith
  have hdiv : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c' / Real.log ((q : ℝ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_right h hL
  have hs' : 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hs
  linarith

private theorem real_zero_of_mem_zeroFreeRegion {c₁ c₂ c₃ c : ℝ} (hc₁ : c ≤ c₁) (hc₂ : c ≤ c₂) (hc₃ : c ≤ c₃)
    (hA : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), χ ≠ 1 → LFunction χ s = 0 →
      (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c₁ / Real.log (q * (|s.im| + 2)))
    (hC : ∀ (q : ℕ) [NeZero q] (s : ℂ), s ≠ 1 → LFunction (1 : DirichletCharacter ℂ q) s = 0 →
      s.re < 1 - c₃ / Real.log (q * (|s.im| + 2)))
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s : ℂ}
    (hs : Formalism.ZeroFreeDirichlet.InRegion c q s) (hz : Formalism.ZeroFreeDirichlet.IsLZero χ s) :
    χ ≠ 1 ∧ χ ^ 2 = 1 ∧ s.im = 0 ∧ 1 - c₂ / Real.log (2 * q) ≤ s.re ∧
      LFunction χ (s.re : ℂ) = 0 ∧ s = (s.re : ℂ) := by
  obtain ⟨hne, hL⟩ := hz
  have h1 : χ ≠ 1 := by
    rintro rfl
    have hs1 : s ≠ 1 := hne.resolve_left (fun h => h rfl)
    have h3 := hC q s hs1 hL
    have h4 := inRegion_mono hc₃ q hs
    linarith
  have h2 : ¬ (χ ^ 2 ≠ 1 ∨ s.im ≠ 0) := by
    intro h
    have h3 := hA q χ s h1 hL h
    have h4 := inRegion_mono hc₁ q hs
    linarith
  push Not at h2
  obtain ⟨hsq, him⟩ := h2
  have hseq : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
  refine ⟨h1, hsq, him, ?_, ?_, hseq⟩
  · have h4 := inRegion_mono hc₂ q hs
    rw [him, abs_zero, zero_add, mul_comm] at h4
    exact h4
  · rw [← hseq]
    exact hL

theorem main : Formalism.ZeroFreeDirichlet.ZFRDirichlet := by
  obtain ⟨c₁, hc₁, hA⟩ := GlobalTheory.ZeroFreeComplex.zero_free_region
  obtain ⟨c₂, hc₂, hB⟩ := GlobalTheory.RealZeroNearOne.main
  obtain ⟨c₃, hc₃, hC⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  refine ⟨min c₁ (min c₂ c₃), lt_min hc₁ (lt_min hc₂ hc₃), ?_⟩
  intro q _ χ s hs hz
  have m₁ : min c₁ (min c₂ c₃) ≤ c₁ := min_le_left _ _
  have m₂ : min c₁ (min c₂ c₃) ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have m₃ : min c₁ (min c₂ c₃) ≤ c₃ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨h1, hsq, him, hre, hL, hseq⟩ := real_zero_of_mem_zeroFreeRegion m₁ m₂ m₃ hA hC hs hz
  have hself := hB q χ χ s.re s.re h1 h1 hsq hsq hre hre hL hL
  refine ⟨hsq, h1, him, ?_, ?_⟩
  · rw [hseq]
    exact hself.2.2
  · intro χ' s' hs' hz'
    obtain ⟨h1', hsq', -, hre', hL', hseq'⟩ := real_zero_of_mem_zeroFreeRegion m₁ m₂ m₃ hA hC hs' hz'
    obtain ⟨hχ, hβ, -⟩ := hB q χ' χ s'.re s.re h1' h1 hsq' hsq hre' hre hL' hL
    refine ⟨hχ, ?_⟩
    rw [hseq', hseq, hβ]

end GlobalTheory.LandauPageRegion
end

open Complex DirichletCharacter Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ZerosNearOne

theorem density_and_regions : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧
    (∀ Q : ℝ, 3 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.2.1.IsPrimitive ∧ LFunction p.2.1 p.2.2 = 0 ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ |p.2.2.im| ≤ Q) → ((∑ p ∈ T, analyticOrderNatAt (LFunction p.2.1) p.2.2 : ℕ) : ℝ) ≤ C1 * Q ^ ((1 : ℝ) / 4)) ∧
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → 3 ≤ N → ∀ ρ : ℂ, LFunction χ ρ = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ.im|)) ≤ ρ.re → IsRealChar χ ∧ ρ.im = 0 ∧ analyticOrderNatAt (LFunction χ) ρ = 1 ∧ ∀ ρ' : ℂ, LFunction χ ρ' = 0 → 1 - c / Real.log (max (N : ℝ) (N * |ρ'.im|)) ≤ ρ'.re → ρ' = ρ) ∧
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 → ρ.re ≤ 1 - c / Real.log (|ρ.im| + 3)) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.ZeroDensityMult.zero_density_mult
  obtain ⟨c, hc, H2, H3⟩ := GlobalTheory.ZeroFreeHalf.main GlobalTheory.LandauPageRegion.main
  exact ⟨C, c, hC, hc, H, H2, H3⟩

end GlobalTheory.ZerosNearOne
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZerosNearOne

theorem main : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ D : D7, adm6 D C1 c := by
  obtain ⟨C, c, hC, hc, H⟩ := density_and_regions
  exact ⟨C, c, hC, hc, fun _ => H⟩

end GlobalTheory.ZerosNearOne
end

namespace GlobalTheory.ZeroBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes in
theorem explicit_formula_and_window_count :
    (∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm7 D C) ∧ ∃ C : ℝ, 0 < C ∧ ∀ D : D7, adm11 D C := by
  obtain ⟨C, hC, h⟩ := GlobalTheory.ExplicitFormula.truncated_explicit_formula
  obtain ⟨C', hC', h'⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  exact ⟨⟨C, hC, fun _ => h⟩, ⟨C', hC', fun _ => h'⟩⟩

end GlobalTheory.ZeroBounds

namespace GlobalTheory.ThinScaleLiterature

theorem litThin : Formalism.MainNotions.LitThin :=
  ⟨GlobalTheory.ZerosNearOne.main, GlobalTheory.ZeroBounds.explicit_formula_and_window_count⟩

end GlobalTheory.ThinScaleLiterature
