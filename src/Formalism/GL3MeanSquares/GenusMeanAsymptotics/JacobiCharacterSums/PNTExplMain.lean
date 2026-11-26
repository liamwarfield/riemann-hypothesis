module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplPick
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplRectF

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplNeg
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

lemma ex_sum_le {δ : ℝ} (hδ : 0 < δ) (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ)
    (h : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) / δ := by
  rw [Nat.cast_sum, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (h ρ hρ)

lemma ex_one_le_log {M : ℕ} (hM : 3 ≤ M) (t : ℝ) : 1 ≤ Real.log ((M : ℝ) * (|t| + 2)) := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h0 := abs_nonneg t
  have h6 : (6 : ℝ) ≤ (M : ℝ) * (|t| + 2) := by nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem ex_negLD_bound : ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (s : ℂ) (δ : ℝ),
    3 ≤ M → 0 < δ → δ ≤ 1 / 20 → 19 / 20 ≤ s.re → s.re ≤ 3 → s ≠ 1 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → ‖ρ - s‖ ≤ 1 / 5 → δ ≤ ‖ρ - s‖) →
    ‖negLD χ s‖ ≤ C * Real.log ((M : ℝ) * (|s.im| + 2)) / δ + (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
  obtain ⟨C₀, hC₀, hR⟩ := Formalism.ZeroFreeDirichlet.l_log_deriv_right
  obtain ⟨C₁, hC₁, hloc⟩ := ex_local
  refine ⟨2 * C₁ + (100 / 7 + C₀), by positivity, ?_⟩
  intro M _ χ s δ hM hδ hδ' hs1 _ hsne hz
  set large₂ : ℝ := Real.log ((M : ℝ) * (|s.im| + 2)) with hLg
  have hL1 : 1 ≤ large₂ := ex_one_le_log hM s.im
  have hif : (0 : ℝ) ≤ (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
    split_ifs
    · positivity
    · exact le_rfl

  have hup : ∀ x : ℝ, 0 ≤ x → x ≤ x * large₂ / δ := by
    intro x hx
    rw [le_div_iff₀ hδ]
    have : x * δ ≤ x * 1 := mul_le_mul_of_nonneg_left (by linarith) hx
    have h2 : x * 1 ≤ x * large₂ := mul_le_mul_of_nonneg_left hL1 hx
    linarith
  by_cases hcase : 107 / 100 ≤ s.re
  · have h1 := hR M χ s (by linarith)
    have h2 : 1 / (s.re - 1) ≤ 100 / 7 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h3 := hup (2 * C₁ + (100 / 7 + C₀)) (by positivity)
    linarith
  · rw [not_le] at hcase
    obtain ⟨Z, hZ, hcard, hexp⟩ := hloc M χ s.im hM
    have hne : exLF χ s ≠ 0 := by
      intro h0
      have := hz s h0 (by linarith) (by simp)
      simp at this
      linarith
    have hsb : s ∈ Metric.closedBall ((101 / 100 : ℂ) + s.im * I) (1 / 15) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : s - ((101 / 100 : ℂ) + s.im * I) = ((s.re - 101 / 100 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    have hE := hexp s hsb hne
    have hdist : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖ := by
      intro ρ hρ
      obtain ⟨hρb, hρ0⟩ := (hZ ρ).1 hρ
      rw [norm_sub_rev]
      by_cases h9 : 9 / 10 ≤ ρ.re
      · refine hz ρ hρ0 h9 ?_
        rw [Metric.mem_closedBall] at hρb hsb
        have := dist_triangle_right ρ s ((101 / 100 : ℂ) + s.im * I)
        rw [dist_eq_norm] at this
        linarith
      · rw [not_le] at h9
        have := Complex.abs_re_le_norm (ρ - s)
        rw [Complex.sub_re] at this
        have h3 := neg_abs_le (ρ.re - s.re)
        linarith
    have hS := ex_sum_le hδ Z (exOrd χ) s hdist
    have hS2 : ((∑ ρ ∈ Z, exOrd χ ρ : ℕ) : ℝ) / δ ≤ C₁ * large₂ / δ :=
      div_le_div_of_nonneg_right hcard hδ.le
    have hD : ‖deriv (exLF χ) s / exLF χ s‖ ≤ C₁ * large₂ + C₁ * large₂ / δ := by
      have := norm_sub_norm_le (deriv (exLF χ) s / exLF χ s) (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) / (s - ρ))
      linarith
    have hCL : C₁ * large₂ ≤ C₁ * large₂ / δ := by
      rw [le_div_iff₀ hδ]
      have : 0 ≤ C₁ * large₂ := by positivity
      nlinarith
    have hI : ‖(if χ = 1 then 1 / (s - 1) else 0 : ℂ)‖ = (if χ = 1 then 1 / ‖s - 1‖ else 0) := by
      split_ifs <;> simp
    rw [negLD_eq_exLF χ hsne hne]
    have hN := norm_sub_le (if χ = 1 then 1 / (s - 1) else 0 : ℂ) (deriv (exLF χ) s / exLF χ s)
    rw [hI] at hN
    have hex : (2 * C₁ + (100 / 7 + C₀)) * large₂ / δ = 2 * (C₁ * large₂ / δ) + (100 / 7 + C₀) * large₂ / δ := by ring
    have hpos : 0 ≤ (100 / 7 + C₀) * large₂ / δ := by positivity
    rw [hex]
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplEdge
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_left_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ T' B : ℝ) (hy : 1 ≤ y)
    (hσ : 1 / 2 ≤ σ₁) (hσ1 : σ₁ < 1) (hT' : 0 ≤ T')
    (hB : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ B) :
    ‖∫ t in (-T')..T', Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ 2 * T' * B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
  have hy0 : 0 < y := by linarith
  have hσp : 0 < σ₁ := by linarith
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simpa using hT'))
  have hpt : ∀ t ∈ Set.uIoc (-T') T', ‖Fchi χ y ((σ₁ : ℂ) + t * I)‖ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hBt := hB t (abs_le.mpr ⟨ht.1.le, ht.2⟩)
    set w : ℂ := (σ₁ : ℂ) + (t : ℂ) * I with hw
    have hre : w.re = σ₁ := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : σ₁ ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      rw [hre, abs_of_pos hσp] at this; exact this
    have hw2 : 1 - σ₁ ≤ ‖w - 1‖ := by
      have h1 : (w - 1).re = σ₁ - 1 := by simp [hre]
      have := Complex.abs_re_le_norm (w - 1)
      rw [h1, abs_of_neg (by linarith)] at this; linarith
    have hden : σ₁ * (1 - σ₁) ≤ ‖w‖ * ‖w - 1‖ :=
      mul_le_mul hw1 hw2 (by linarith) (norm_nonneg _)
    have hdp : 0 < σ₁ * (1 - σ₁) := mul_pos hσp (by linarith)
    have hyp : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ σ₁ / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₁ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₁ / (σ₁ * (1 - σ₁)) :=
          div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) hdp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  have : |T' - -T'| = 2 * T' := by rw [abs_of_nonneg (by linarith)]; ring
  rw [this]; ring

theorem ex_horiz_bound {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₁ σ₀ v B : ℝ) (hy : 1 ≤ y)
    (hσ : σ₁ ≤ σ₀) (hv : 1 ≤ |v|) (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ B) :
    ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤ (σ₀ - σ₁) * B * y ^ σ₀ / v ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hpt : ∀ x ∈ Set.uIoc σ₁ σ₀, ‖Fchi χ y ((x : ℂ) + v * I)‖ ≤ B * y ^ σ₀ / v ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hσ] at hx
    have hBx := hB x hx.1.le hx.2
    set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
    have hre : w.re = x := by simp [hw]
    have him : w.im = v := by simp [hw]
    rw [norm_perron_integrand_eq χ y hy0 w, hre]
    have hw1 : |v| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
    have hw2 : |v| ≤ ‖w - 1‖ := by
      have : (w - 1).im = v := by simp [him]
      rw [← this]; exact Complex.abs_im_le_norm _
    have hpow : y ^ x ≤ y ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hy hx.2
    have hden : v ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
      rw [← sq_abs]; nlinarith [abs_nonneg v]
    have htp : 0 < v ^ 2 := by rw [← sq_abs]; positivity
    have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
    calc ‖negLD χ w‖ * y ^ x / (‖w‖ * ‖w - 1‖)
        ≤ B * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
      _ ≤ B * y ^ σ₀ / v ^ 2 := div_le_div_of_nonneg_left (mul_nonneg hB0 hyp) htp hden
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  refine h.trans (le_of_eq ?_)
  rw [abs_of_nonneg (by linarith)]; ring

theorem ex_tail_half (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T)
    (hf : ∀ t : ℝ, T < t → ‖f t‖ ≤ K / t ^ 2) :
    ‖∫ t in Set.Ioi T, f t‖ ≤ K / T := by
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => K * t ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul K
  have h := MeasureTheory.norm_integral_le_of_norm_le (μ := MeasureTheory.volume.restrict (Set.Ioi T))
    (f := f) hint
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun t ht => by
      have ht0 : 0 < t := lt_trans hT ht
      have := hf t ht
      rw [Real.rpow_neg ht0.le, Real.rpow_two]
      simpa [div_eq_mul_inv] using this)))
  refine h.trans (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
  have : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [this, Real.rpow_neg_one]
  field_simp

theorem ex_tail_gen (f : ℝ → ℂ) (K T : ℝ) (hT : 0 < T) (hi : MeasureTheory.Integrable f)
    (hf : ∀ t : ℝ, T < |t| → ‖f t‖ ≤ K / t ^ 2) :
    ‖(∫ t : ℝ, f t) - ∫ t in (-T)..T, f t‖ ≤ 2 * K / T := by
  have h1 : (∫ t in Set.Iic (-T), f t) + ∫ t in Set.Ioi (-T), f t = ∫ t : ℝ, f t :=
    intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn
  have h2 : (∫ t in (-T)..T, f t) + ∫ t in Set.Ioi T, f t = ∫ t in Set.Ioi (-T), f t :=
    intervalIntegral.integral_interval_add_Ioi hi.integrableOn hi.integrableOn
  have h3 : (∫ t in Set.Ioi T, f (-t)) = ∫ t in Set.Iic (-T), f t := integral_comp_neg_Ioi T f
  have e : (∫ t : ℝ, f t) - ∫ t in (-T)..T, f t
      = (∫ t in Set.Ioi T, f (-t)) + ∫ t in Set.Ioi T, f t := by
    rw [← h1, ← h2, h3]; ring
  rw [e]
  have a := ex_tail_half (fun t => f (-t)) K T hT (fun t ht => by
    have := hf (-t) (by rw [abs_neg]; exact lt_of_lt_of_le ht (le_abs_self t))
    simpa using this)
  have b := ex_tail_half f K T hT (fun t ht => hf t (lt_of_lt_of_le ht (le_abs_self t)))
  calc _ ≤ ‖∫ t in Set.Ioi T, f (-t)‖ + ‖∫ t in Set.Ioi T, f t‖ := norm_add_le _ _
    _ ≤ K / T + K / T := add_le_add a b
    _ = 2 * K / T := by ring

theorem ex_tail_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (y σ₀ T' : ℝ),
    1 ≤ y → 1 < σ₀ → 1 ≤ T' →
    ‖(∫ t : ℝ, Fchi χ y ((σ₀ : ℂ) + t * I)) - ∫ t in (-T')..T', Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * (1 / (σ₀ - 1) + C) * y ^ σ₀ / T' := by
  obtain ⟨C, hC, hR⟩ := l_log_deriv_right
  refine ⟨C, hC, ?_⟩
  intro M _ χ y σ₀ T' hy hσ hT'
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T' := by linarith
  obtain ⟨hint, -⟩ := perron_formula_character M χ y hy σ₀ hσ
  have h := ex_tail_gen (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) ((1 / (σ₀ - 1) + C) * y ^ σ₀) T' hT0 hint
    (fun t ht => by
      have ht0 : 0 < |t| := lt_trans hT0 ht
      show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _
      set w : ℂ := (σ₀ : ℂ) + (t : ℂ) * I with hw
      have hre : w.re = σ₀ := by simp [hw]
      have him : w.im = t := by simp [hw]
      rw [norm_perron_integrand_eq χ y hy0 w, hre]
      have hζ : ‖negLD χ w‖ ≤ 1 / (σ₀ - 1) + C := by
        have := hR M χ w (by rw [hre]; exact hσ)
        rwa [hre] at this
      have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
      have hw2 : |t| ≤ ‖w - 1‖ := by
        have : (w - 1).im = t := by simp [him]
        rw [← this]; exact Complex.abs_im_le_norm _
      have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
        rw [← sq_abs]; nlinarith [abs_nonneg t]
      have htp : 0 < t ^ 2 := by rw [← sq_abs]; positivity
      have hnum : 0 ≤ 1 / (σ₀ - 1) + C := le_trans (norm_nonneg _) hζ
      have hyp : 0 ≤ y ^ σ₀ := Real.rpow_nonneg hy0.le _
      calc ‖negLD χ w‖ * y ^ σ₀ / (‖w‖ * ‖w - 1‖)
          ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by gcongr
        _ ≤ (1 / (σ₀ - 1) + C) * y ^ σ₀ / t ^ 2 :=
            div_le_div_of_nonneg_left (mul_nonneg hnum hyp) htp hden)
  refine h.trans (le_of_eq ?_)
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMainB
section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplMainA
open Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem exm_alg (S Ifull R Lf Bt Tp K D Sg : ℂ) (y : ℝ) (hy : 0 < y)
    (hS : S = (1 / (2 * Real.pi) : ℂ) * Ifull)
    (hrect : Bt - Tp + I * R - I * Lf = 2 * Real.pi * I * (K * y + D - Sg)) :
    S / y - K - D / y + Sg / y =
      (1 / (2 * Real.pi * y) : ℂ) * ((Ifull - R) + Lf + I * (Bt - Tp)) := by
  subst hS
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have key : (Ifull - R) + Lf + I * (Bt - Tp) =
      Ifull - 2 * (Real.pi : ℂ) * (K * (y : ℂ) + D - Sg) := by
    linear_combination I * hrect + (-R + Lf + 2 * (Real.pi : ℂ) * (K * (y : ℂ) + D - Sg)) * I_sq
  rw [key]
  field_simp
  ring

theorem exm_norm (Ifull R Lf Bt Tp : ℂ) (y a b c d : ℝ) (hy : 0 < y)
    (ha : ‖Ifull - R‖ ≤ a) (hb : ‖Lf‖ ≤ b) (hc : ‖Bt‖ ≤ c) (hd : ‖Tp‖ ≤ d) :
    ‖(1 / (2 * Real.pi * y) : ℂ) * ((Ifull - R) + Lf + I * (Bt - Tp))‖ ≤
      1 / (2 * Real.pi * y) * (a + b + (c + d)) := by
  have hpos : 0 < 2 * Real.pi * y := mul_pos (mul_pos two_pos Real.pi_pos) hy
  have hk : (1 / (2 * Real.pi * y) : ℂ) = ((1 / (2 * Real.pi * y) : ℝ) : ℂ) := by
    norm_cast
  rw [hk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (one_div_pos.2 hpos).le]
  apply mul_le_mul_of_nonneg_left _ (one_div_pos.2 hpos).le
  have h1 := norm_add_le (Ifull - R) Lf
  have h2 : ‖I * (Bt - Tp)‖ = ‖Bt - Tp‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h3 := norm_sub_le Bt Tp
  have h4 := norm_add_le (Ifull - R + Lf) (I * (Bt - Tp))
  linarith

theorem exm_log_le (M T u : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (hu0 : 0 ≤ u) (hu : u ≤ T + 1) :
    Real.log (M * (u + 2)) ≤ 2 * Real.log (M * T) := by
  have hM0 : 0 ≤ M := by linarith
  have hpos : 0 < M * (u + 2) := mul_pos (by linarith) (by linarith)
  have h3 : T + 3 ≤ M * T ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hM (sq_nonneg T),
      mul_nonneg (sub_nonneg.2 hT) (by linarith : (0:ℝ) ≤ T)]
  have h4 : M * (u + 2) ≤ M * (T + 3) := mul_le_mul_of_nonneg_left (by linarith) hM0
  have h5 : M * (T + 3) ≤ M * (M * T ^ 2) := mul_le_mul_of_nonneg_left h3 hM0
  have h2 : M * (u + 2) ≤ (M * T) ^ 2 := by nlinarith
  calc Real.log (M * (u + 2)) ≤ Real.log ((M * T) ^ 2) := Real.log_le_log hpos h2
    _ = 2 * Real.log (M * T) := by rw [Real.log_pow]; push_cast; ring

theorem exm_log_ge_one (M T : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) : 1 ≤ Real.log (M * T) := by
  have h6 : 6 ≤ M * T := by nlinarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (M * T) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])

theorem exm_N_le (κ C₁ C₂ M T δ : ℝ) (hκ : 0 < κ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hM : 3 ≤ M) (hT : 2 ≤ T)
    (_hδ0 : 0 < δ) (hδ : κ / (C₁ * (T + 1) * Real.log (M * (T + 2))) ≤ δ) :
    C₂ * (2 * Real.log (M * T)) / δ ≤ 6 * C₁ * C₂ / κ * (T * Real.log (M * T) ^ 2) := by
  have hL : 1 ≤ Real.log (M * T) := exm_log_ge_one M T hM hT
  have hL' : Real.log (M * (T + 2)) ≤ 2 * Real.log (M * T) :=
    exm_log_le M T T hM hT (by linarith) (by linarith)
  have hL'1 : 1 ≤ Real.log (M * (T + 2)) := exm_log_ge_one M (T + 2) hM (by linarith)
  have hA : 0 < C₁ * (T + 1) * Real.log (M * (T + 2)) :=
    mul_pos (mul_pos hC₁ (by linarith)) (by linarith)
  have hinv : 1 / δ ≤ C₁ * (T + 1) * Real.log (M * (T + 2)) / κ := by
    have := one_div_le_one_div_of_le (div_pos hκ hA) hδ
    rwa [one_div_div] at this
  have hP : 0 ≤ C₁ * C₂ * Real.log (M * T) := mul_nonneg (mul_nonneg hC₁.le hC₂.le) (by linarith)
  have e1 : (T + 1) * Real.log (M * (T + 2)) ≤ (T + 1) * (2 * Real.log (M * T)) :=
    mul_le_mul_of_nonneg_left hL' (by linarith)
  have e2 : (T + 1) * (2 * Real.log (M * T)) ≤ 3 * T * Real.log (M * T) := by
    nlinarith [mul_le_mul_of_nonneg_right hT (by linarith : (0:ℝ) ≤ Real.log (M * T))]
  have hnum : 2 * (C₁ * C₂ * Real.log (M * T)) * ((T + 1) * Real.log (M * (T + 2))) ≤
      2 * (C₁ * C₂ * Real.log (M * T)) * (3 * T * Real.log (M * T)) :=
    mul_le_mul_of_nonneg_left (e1.trans e2) (by linarith)
  calc C₂ * (2 * Real.log (M * T)) / δ = C₂ * (2 * Real.log (M * T)) * (1 / δ) := by ring
    _ ≤ C₂ * (2 * Real.log (M * T)) * (C₁ * (T + 1) * Real.log (M * (T + 2)) / κ) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg hC₂.le (by linarith))
    _ = 2 * (C₁ * C₂ * Real.log (M * T)) * ((T + 1) * Real.log (M * (T + 2))) * κ⁻¹ := by ring
    _ ≤ 2 * (C₁ * C₂ * Real.log (M * T)) * (3 * T * Real.log (M * T)) * κ⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.2 hκ.le)
    _ = 6 * C₁ * C₂ / κ * (T * Real.log (M * T) ^ 2) := by ring

theorem exm_log_y (y : ℝ) (hy : 2 ≤ y) : 1 / 2 ≤ Real.log y := by
  calc (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    _ ≤ Real.log y := Real.log_le_log (by norm_num) hy

theorem exm_tail_num (C₃ T T' y l : ℝ) (hC₃ : 0 ≤ C₃) (hT : 2 ≤ T) (hT' : T ≤ T') (hy : 2 ≤ y) (hl : 1 ≤ l) :
    1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T') ≤
      (1 + 2 * C₃) * (Real.log y * l ^ 2 / T) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hT'ne : T' ≠ 0 := hT'0.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLy : 1 / 2 ≤ Real.log y := exm_log_y y hy
  have hepi : Real.exp 1 ≤ Real.pi := by linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have key : 1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T') =
      (Real.log y + C₃) * (Real.exp 1 / (Real.pi * T')) := by
    field_simp
  have hprod : Real.exp 1 * T ≤ 1 * (Real.pi * T') := by
    rw [one_mul]; exact mul_le_mul hepi hT' hT0.le Real.pi_pos.le
  have h1 : Real.exp 1 / (Real.pi * T') ≤ 1 / T := by
    rw [div_le_div_iff₀ (mul_pos Real.pi_pos hT'0) hT0]; exact hprod
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hA : 0 ≤ (1 + 2 * C₃) * Real.log y := mul_nonneg (by linarith) (by linarith)
  have hnum : Real.log y + C₃ ≤ (1 + 2 * C₃) * Real.log y * l ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl2 hA, mul_le_mul_of_nonneg_left hLy hC₃]
  rw [key]
  calc (Real.log y + C₃) * (Real.exp 1 / (Real.pi * T')) ≤ (Real.log y + C₃) * (1 / T) :=
        mul_le_mul_of_nonneg_left h1 (by linarith)
    _ ≤ (1 + 2 * C₃) * Real.log y * l ^ 2 * (1 / T) :=
        mul_le_mul_of_nonneg_right hnum (one_div_pos.2 hT0).le
    _ = (1 + 2 * C₃) * (Real.log y * l ^ 2 / T) := by ring

theorem exm_horiz_num (G N T T' y l : ℝ) (hG : 0 ≤ G) (hN0 : 0 ≤ N) (hN : N ≤ G * (T * l ^ 2))
    (hT : 2 ≤ T) (hT' : T ≤ T') (hy : 2 ≤ y) (hl : 1 ≤ l) :
    1 / (2 * Real.pi * y) * (3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2) ≤
      3 * (G + 1) * (Real.log y * l ^ 2 / T) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hT'0 : 0 < T' := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hTne : T ≠ 0 := hT0.ne'
  have hT'ne : T' ≠ 0 := hT'0.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hLy : 1 / 2 ≤ Real.log y := exm_log_y y hy
  have key : 1 / (2 * Real.pi * y) * (3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2) =
      3 * (N + 1) * (Real.exp 1 / (2 * Real.pi * T' ^ 2)) := by
    field_simp
  have hX : 0 ≤ Real.exp 1 / (2 * Real.pi * T' ^ 2) := by positivity
  have hl2 : 1 ≤ l ^ 2 := by nlinarith
  have hTl : 1 ≤ T * l ^ 2 := by nlinarith
  have hN1 : 3 * (N + 1) ≤ 3 * (G + 1) * (T * l ^ 2) := by nlinarith
  have hA : Real.exp 1 ≤ 2 * Real.pi * Real.log y := by
    nlinarith [Real.exp_one_lt_d9, Real.pi_gt_three, mul_le_mul_of_nonneg_left hLy Real.pi_pos.le]
  have hTT : T ^ 2 ≤ T' ^ 2 := by nlinarith
  have hprod : Real.exp 1 * T ^ 2 ≤ Real.log y * (2 * Real.pi * T' ^ 2) := by
    nlinarith [mul_le_mul hA hTT (sq_nonneg T) (by nlinarith [Real.pi_pos] : (0:ℝ) ≤ 2 * Real.pi * Real.log y)]
  have h1 : Real.exp 1 / (2 * Real.pi * T' ^ 2) ≤ Real.log y / T ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos (mul_pos two_pos Real.pi_pos) (pow_pos hT'0 2)) (pow_pos hT0 2)]; exact hprod
  have hB : 0 ≤ 3 * (G + 1) * (T * l ^ 2) := by nlinarith
  rw [key]
  calc 3 * (N + 1) * (Real.exp 1 / (2 * Real.pi * T' ^ 2))
        ≤ 3 * (G + 1) * (T * l ^ 2) * (Real.exp 1 / (2 * Real.pi * T' ^ 2)) :=
        mul_le_mul_of_nonneg_right hN1 hX
    _ ≤ 3 * (G + 1) * (T * l ^ 2) * (Real.log y / T ^ 2) := mul_le_mul_of_nonneg_left h1 hB
    _ = 3 * (G + 1) * (Real.log y * l ^ 2 / T) := by field_simp

theorem exm_left_num (κ G N M T T' σ₁ y : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ 1 / 20) (hG : 0 ≤ G) (hN0 : 0 ≤ N)
    (hN : N ≤ G * (T * Real.log (M * T) ^ 2)) (hM : 3 ≤ M) (hT : 2 ≤ T) (hT0' : T ≤ T') (hT' : T' ≤ T + 1)
    (hσ : 1 - κ ≤ σ₁) (hσ' : σ₁ ≤ 1 - 3 * κ / 4) (hy : 2 ≤ y) :
    1 / (2 * Real.pi * y) * (2 * T' * (N + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁))) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * ((M * T) ^ 4 * y ^ (-(κ / 2))) := by
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hM0 : 0 < M := by linarith
  have hMT : 0 < M * T := mul_pos hM0 hT0
  have hs1 : 19 / 20 ≤ σ₁ := by linarith
  have hs2 : 3 * κ / 4 ≤ 1 - σ₁ := by linarith
  have hs0 : 0 < σ₁ := by linarith
  have hs3 : 0 < 1 - σ₁ := by linarith
  have hyne : y ≠ 0 := hy0.ne'
  have hsne : σ₁ ≠ 0 := hs0.ne'
  have hs3ne : 1 - σ₁ ≠ 0 := hs3.ne'
  have hs4 : σ₁ ≠ 1 := (by linarith : σ₁ < 1).ne
  have hs5 : (1 : ℝ) ≠ σ₁ := (by linarith : σ₁ < 1).ne'
  have hκne : κ ≠ 0 := hκ.ne'
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  have hP : 57 * κ / 80 ≤ σ₁ * (1 - σ₁) := by
    nlinarith [mul_le_mul hs1 hs2 (by linarith) hs0.le]
  have hD : 2 * κ ≤ Real.pi * (σ₁ * (1 - σ₁)) := by
    nlinarith [mul_le_mul Real.pi_gt_three.le hP (by linarith) Real.pi_pos.le]
  have hDpos : 0 < Real.pi * (σ₁ * (1 - σ₁)) := by linarith
  have hc0 : 0 ≤ 4 / (3 * κ) := div_nonneg (by norm_num) (by linarith)
  have hL1 : 1 ≤ Real.log (M * T) := exm_log_ge_one M T hM hT
  have hLle : Real.log (M * T) ≤ M * T := by
    have := Real.log_le_sub_one_of_pos hMT
    linarith
  have hTL : 1 ≤ T * Real.log (M * T) ^ 2 := by nlinarith
  have hNc : N + 4 / (3 * κ) ≤ (G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hTL hc0]
  have hT'le : T' ≤ 3 * T / 2 := by linarith
  have hnum1 : T' * (N + 4 / (3 * κ)) ≤
      (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) :=
    mul_le_mul hT'le hNc (by linarith) (by linarith)
  have hGc : 0 ≤ G + 4 / (3 * κ) := by linarith
  have hTMT : T ≤ M * T := by nlinarith
  have hTL2 : T * Real.log (M * T) ≤ (M * T) * (M * T) :=
    mul_le_mul hTMT hLle (by linarith) hMT.le
  have hQ : (T * Real.log (M * T)) * (T * Real.log (M * T)) ≤
      ((M * T) * (M * T)) * ((M * T) * (M * T)) :=
    mul_le_mul hTL2 hTL2 (mul_nonneg hT0.le (by linarith)) (mul_self_nonneg _)
  have hnum2 : (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) ≤
      12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := by
    have h1 := mul_le_mul_of_nonneg_left hQ hGc
    have h2 := mul_nonneg hGc (pow_nonneg hMT.le 4)
    have e1 : (3 * T / 2) * ((G + 4 / (3 * κ)) * (T * Real.log (M * T) ^ 2)) =
        3 / 2 * ((G + 4 / (3 * κ)) * ((T * Real.log (M * T)) * (T * Real.log (M * T)))) := by ring
    have e2 : (G + 4 / (3 * κ)) * (((M * T) * (M * T)) * ((M * T) * (M * T))) =
        (G + 4 / (3 * κ)) * (M * T) ^ 4 := by ring
    rw [e1]
    rw [e2] at h1
    linarith
  have hk0 : 0 ≤ 2 / κ := div_nonneg (by norm_num) hκ.le
  have hB0 : 0 ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hGc) hk0) (pow_nonneg hMT.le 4)
  have hB2 : 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (2 * κ) =
      12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := by
    field_simp
    ring
  have hchain : T' * (N + 4 / (3 * κ)) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (Real.pi * (σ₁ * (1 - σ₁))) :=
    calc T' * (N + 4 / (3 * κ)) ≤ 12 * ((G + 4 / (3 * κ)) * (M * T) ^ 4) := hnum1.trans hnum2
      _ = 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (2 * κ) := hB2.symm
      _ ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * (Real.pi * (σ₁ * (1 - σ₁))) :=
          mul_le_mul_of_nonneg_left hD hB0
  have hA : T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) ≤
      3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 := by
    rw [div_le_iff₀ hDpos]; exact hchain
  have hA0 : 0 ≤ T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hDpos.le
  have hYle : y ^ σ₁ / y ≤ y ^ (-(κ / 2)) := by
    rw [← Real.rpow_sub_one hyne]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 ≤ y ^ (-(κ / 2)) := Real.rpow_nonneg hy0.le _
  calc 1 / (2 * Real.pi * y) * (2 * T' * (N + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁)))
        = T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) * (y ^ σ₁ / y) := by
        field_simp
    _ ≤ T' * (N + 4 / (3 * κ)) / (Real.pi * (σ₁ * (1 - σ₁))) * y ^ (-(κ / 2)) :=
        mul_le_mul_of_nonneg_left hYle hA0
    _ ≤ 3 * (G + 4 / (3 * κ)) * (2 / κ) * (M * T) ^ 4 * y ^ (-(κ / 2)) :=
        mul_le_mul_of_nonneg_right hA hY0
    _ = 3 * (G + 4 / (3 * κ)) * (2 / κ) * ((M * T) ^ 4 * y ^ (-(κ / 2))) := by ring

theorem sum_le_mul_rpow_add (AL AW C X Y W : ℝ) (hC4 : 4 ≤ C) (hCL : AL ≤ C) (hCW : AW ≤ C) (hX : 1 ≤ X)
    (hY : 0 ≤ Y) (hW : 0 ≤ W) : AL * (X ^ 4 * Y) + AW * W ≤ C * (X ^ C * Y + W) := by
  have hX0 : 0 ≤ X := by linarith
  have hC0 : 0 ≤ C := by linarith
  have h4 : X ^ 4 ≤ X ^ C := by
    have h := Real.rpow_le_rpow_of_exponent_le hX hC4
    have e : X ^ (4 : ℝ) = X ^ (4 : ℕ) := by exact_mod_cast Real.rpow_natCast X 4
    rwa [e] at h
  have h1 := mul_le_mul_of_nonneg_right hCL (mul_nonneg (pow_nonneg hX0 4) hY)
  have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4 hY) hC0
  have h3 := mul_le_mul_of_nonneg_right hCW hW
  nlinarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem exm_neg {C₂ : ℝ} (hC₂ : 0 < C₂) {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (T δ E : ℝ) (s : ℂ)
    (hM : 3 ≤ M) (hT : 2 ≤ T) (hδ0 : 0 < δ) (him : |s.im| ≤ T + 1) (hE : 1 / ‖s - 1‖ ≤ E) (hE0 : 0 ≤ E)
    (h : ‖negLD χ s‖ ≤ C₂ * Real.log ((M : ℝ) * (|s.im| + 2)) / δ + (if χ = 1 then 1 / ‖s - 1‖ else 0)) :
    ‖negLD χ s‖ ≤ C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + E := by
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 := exm_log_le (M : ℝ) T |s.im| hM' hT (abs_nonneg _) him
  have h2 : (if χ = 1 then 1 / ‖s - 1‖ else 0) ≤ E := by split_ifs <;> assumption
  refine h.trans (add_le_add ?_ h2)
  gcongr

theorem exm_rpow_sigma (y : ℝ) (hy : 2 ≤ y) : y ^ (1 + 1 / Real.log y) = Real.exp 1 * y := by
  have hy0 : 0 < y := by linarith
  have hl := exm_log_y y hy
  have hl0 : Real.log y ≠ 0 := by linarith
  rw [Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0, mul_one_div_cancel hl0, mul_comm]

theorem exm_core : ∃ C₂ C₃ : ℝ, 0 < C₂ ∧ 0 ≤ C₃ ∧ ∀ (κ : ℝ), 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T σ₁ T' δ : ℝ), 3 ≤ M → 2 ≤ T →
    1 - κ ≤ σ₁ → σ₁ ≤ 1 - 3 * κ / 4 → T ≤ T' → T' ≤ T + 1 → 0 < δ → δ ≤ 1 / 20 →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) →
    (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) →
    ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T')) →
    ∀ y : ℝ, 2 ≤ y →
      ‖Formalism.ZeroFreeDirichlet.Schi χ y / (y : ℂ) - explicitFormulaConstant χ - (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) +
                ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))‖ ≤
        1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T' +
          2 * T' * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 4 / (3 * κ)) * y ^ σ₁ / (σ₁ * (1 - σ₁)) +
          (3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2 +
           3 * (C₂ * (2 * Real.log ((M : ℝ) * T)) / δ + 1) * (Real.exp 1 * y) / T' ^ 2)) := by
  obtain ⟨C₂, hC₂, hneg⟩ := ex_negLD_bound
  obtain ⟨C₃, hC₃, htail⟩ := ex_tail_bound
  refine ⟨C₂, C₃, hC₂, hC₃, ?_⟩
  intro κ hκ hκ' M _ χ T σ₁ T' δ hM hT hσ hσ' hTT' hT'T hδ0 hδ' hgapre hgapim Z hZ y hy
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hy0 : 0 < y := by linarith
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have hly := exm_log_y y hy
  have hl1 := exm_log_ge_one (M : ℝ) T hM' hT
  set N := C₂ * (2 * Real.log ((M : ℝ) * T)) / δ with hN
  have hN0 : 0 ≤ N := by rw [hN]; positivity
  set σ₀ := 1 + 1 / Real.log y with hσ₀
  have hσ₀1 : 1 < σ₀ := by
    have : 0 < 1 / Real.log y := by positivity
    linarith
  have hσ₀3 : σ₀ ≤ 3 := by
    have : 1 / Real.log y ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hly
    rw [hσ₀]; linarith
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := exm_rpow_sigma y hy
  have hσ19 : 19 / 20 ≤ σ₁ := by linarith
  have hσ1 : σ₁ < 1 := by linarith
  have hT'0 : 0 < T' := by linarith

  have hBL : ∀ t : ℝ, |t| ≤ T' → ‖negLD χ ((σ₁ : ℂ) + t * I)‖ ≤ N + 4 / (3 * κ) := by
    intro t ht
    have hre : ((σ₁ : ℂ) + t * I).re = σ₁ := by simp
    have him : ((σ₁ : ℂ) + t * I).im = t := by simp
    have hnorm : 3 * κ / 4 ≤ ‖(σ₁ : ℂ) + t * I - 1‖ := by
      have h1 := Complex.abs_re_le_norm ((σ₁ : ℂ) + t * I - 1)
      have h2 : ((σ₁ : ℂ) + t * I - 1).re = σ₁ - 1 := by simp
      rw [h2, abs_of_neg (by linarith)] at h1
      linarith
    have hne : (σ₁ : ℂ) + t * I ≠ 1 := by
      intro h
      rw [h] at hnorm
      simp at hnorm
      linarith
    apply exm_neg hC₂ χ T δ _ _ hM hT hδ0 (by rw [him]; linarith) _ (by positivity)
    · apply hneg M χ _ δ hM hδ0 hδ' (by rw [hre]; exact hσ19) (by rw [hre]; linarith) hne
      intro ρ hρ hρre hρs
      have h1 := Complex.abs_re_le_norm (ρ - ((σ₁ : ℂ) + t * I))
      have h2 := Complex.abs_im_le_norm (ρ - ((σ₁ : ℂ) + t * I))
      rw [Complex.sub_re, hre] at h1
      rw [Complex.sub_im, him] at h2
      have h3 : |ρ.im| ≤ T + 3 := by
        have : |ρ.im| ≤ |ρ.im - t| + |t| := by
          have := abs_add_le (ρ.im - t) t
          simpa using this
        linarith
      have h4 := hgapre ρ hρ hρre h3
      rw [abs_sub_comm] at h4
      linarith
    · have := one_div_le_one_div_of_le (by positivity : 0 < 3 * κ / 4) hnorm
      rwa [one_div_div] at this

  have hBH : ∀ v : ℝ, |v| = T' → ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₀ → ‖negLD χ ((x : ℂ) + v * I)‖ ≤ N + 1 := by
    intro v hv x hx hx'
    have hre : ((x : ℂ) + v * I).re = x := by simp
    have him : ((x : ℂ) + v * I).im = v := by simp
    have hnorm : 1 ≤ ‖(x : ℂ) + v * I - 1‖ := by
      have h1 := Complex.abs_im_le_norm ((x : ℂ) + v * I - 1)
      have h2 : ((x : ℂ) + v * I - 1).im = v := by simp
      rw [h2, hv] at h1
      linarith
    have hne : (x : ℂ) + v * I ≠ 1 := by
      intro h
      rw [h] at hnorm
      simp at hnorm
      linarith
    apply exm_neg hC₂ χ T δ _ _ hM hT hδ0 (by rw [him, hv]; linarith) _ (by norm_num)
    · apply hneg M χ _ δ hM hδ0 hδ' (by rw [hre]; linarith) (by rw [hre]; linarith) hne
      intro ρ hρ hρre _
      have h2 := Complex.abs_im_le_norm (ρ - ((x : ℂ) + v * I))
      rw [Complex.sub_im, him] at h2
      have h4 := hgapim ρ hρ hρre
      rw [← hv] at h4
      have h5 := abs_abs_sub_abs_le ρ.im v
      linarith
    · have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hnorm
      simpa using this
  have hH : ∀ v : ℝ, |v| = T' → ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + v * I)‖ ≤
      3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2 := by
    intro v hv
    have h := ex_horiz_bound χ y σ₁ σ₀ v (N + 1) (by linarith) (by linarith) (by rw [hv]; linarith)
      (by linarith) (hBH v hv)
    have hv2 : v ^ 2 = T' ^ 2 := by rw [← hv, sq_abs]
    rw [hv2, hyσ₀] at h
    refine h.trans ?_
    have : σ₀ - σ₁ ≤ 3 := by linarith
    gcongr
  have hLf := ex_left_bound χ y σ₁ T' (N + 4 / (3 * κ)) (by linarith) (by linarith) hσ1 hT'0.le hBL
  have hTl := htail M χ y σ₀ T' (by linarith) hσ₀1 (by linarith)
  have hinv : 1 / (σ₀ - 1) = Real.log y := by rw [hσ₀]; simp
  rw [hinv, hyσ₀] at hTl
  have hedge : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T' → exLF χ w = 0 → σ₁ < w.re ∧ |w.im| < T' := by
    intro w hw1 _ hw3 hw0
    have h1 := hgapre w hw0 (by linarith) (by linarith)
    have h2 := hgapim w hw0 (by linarith)
    constructor
    · rcases hw1.lt_or_eq with h | h
      · exact h
      · rw [h] at h1; simp at h1; linarith
    · rcases hw3.lt_or_eq with h | h
      · exact h
      · rw [h] at h2; simp at h2; linarith
  have hrect := ex_rect_Fchi χ y hy0 σ₁ σ₀ T' (by linarith) hσ1 hσ₀1 hT'0 Z hZ hedge
  have hper := (perron_formula_character M χ y (by linarith) σ₀ hσ₀1).2
  unfold Formalism.ZF.rectInt at hrect
  have halg := exm_alg _ _ _ _ _ _ _ _ _ y hy0 hper hrect
  have hD : (if χ = 1 then (y : ℂ) * (Real.log y : ℂ) - y else 0) / (y : ℂ) =
      (if χ = 1 then ((Real.log y - 1 : ℝ) : ℂ) else 0) := by
    split_ifs
    · push_cast; field_simp
    · simp
  have hS : (∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * exKer y ρ) / (y : ℂ) =
      ∑ ρ ∈ Z, (exOrd χ ρ : ℂ) * (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ρ _
    rw [exKer, Complex.cpow_sub _ _ hyC, Complex.cpow_one]
    ring
  rw [hD, hS] at halg
  rw [halg]
  exact exm_norm _ _ _ _ _ y _ _ _ _ hy0 hTl hLf (hH (-T') (by rw [abs_neg, abs_of_pos hT'0]))
    (hH T' (abs_of_pos hT'0))

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem smoothed_explicit_formula : ExplicitS := by
  intro κ hκ hκ'
  obtain ⟨C₁, hC₁, hch⟩ := ex_choose
  obtain ⟨C₄, hC₄, hbox⟩ := ex_box
  obtain ⟨C₂, C₃, hC₂, hC₃, hcore⟩ := exm_core
  set G := 6 * C₁ * C₂ / κ with hG
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  set AL := 3 * (G + 4 / (3 * κ)) * (2 / κ) with hAL
  set AW := (1 + 2 * C₃) + (3 * (G + 1) + 3 * (G + 1)) with hAW
  set C := max (max 4 C₄) (max AL AW) with hC
  have hC4 : 4 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCC₄ : C₄ ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCL : AL ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCW : AW ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, by linarith, ?_⟩
  intro M _ χ T hM hT
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  obtain ⟨σ₁, T', δ, hσ, hσ', hTT', hT'T, hδ0, hδ', hδlow, hgapre, hgapim⟩ := hch κ hκ hκ' M χ T hM hT
  obtain ⟨Z₀, hZ₀, hwin, _⟩ := hbox M χ (T + 1) hM (by linarith)
  have hZ : ∀ ρ : ℂ, ρ ∈ Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T') ↔
      (exLF χ ρ = 0 ∧ σ₁ < ρ.re ∧ |ρ.im| < T') := by
    intro ρ
    rw [Finset.mem_filter, hZ₀]
    constructor
    · rintro ⟨⟨h0, _, _⟩, h1, h2⟩
      exact ⟨h0, h1, h2⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨⟨h0, by linarith, by linarith⟩, h1, h2⟩
  refine ⟨Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T'), exOrd χ, explicitFormulaConstant χ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨h0, h1, h2⟩ := (hZ ρ).1 hρ
    exact ⟨(isLZero_iff_exLF χ ρ).2 h0, by linarith, by linarith⟩
  · intro ρ hρ hre him
    have h0 := (isLZero_iff_exLF χ ρ).1 hρ
    refine (hZ ρ).2 ⟨h0, by linarith, ?_⟩
    have h2 := hgapim ρ h0 (by linarith)
    rcases (him.trans hTT').lt_or_eq with h | h
    · exact h
    · rw [h] at h2; simp at h2; linarith
  · intro ρ hρ
    exact exOrd_pos χ ((hZ ρ).1 hρ).1
  · intro ρ hρ hd
    have h0 := ((hZ ρ).1 hρ).1
    exact exOrd_eq_one χ h0 (exLF_deriv_ne_zero χ h0 hd)
  · intro t
    have hsub : (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1) ⊆
        Z₀.filter (fun ρ => |ρ.im - t| ≤ 1) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    have h1 : (∑ ρ ∈ (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1),
        exOrd χ ρ) ≤ ∑ ρ ∈ Z₀.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ :=
      Finset.sum_le_sum_of_subset hsub
    have h2 : (0 : ℝ) ≤ Real.log ((M : ℝ) * (|t| + 2)) := by
      apply Real.log_nonneg
      have := abs_nonneg t
      nlinarith
    calc ((∑ ρ ∈ (Z₀.filter (fun ρ => σ₁ < ρ.re ∧ |ρ.im| < T')).filter (fun ρ => |ρ.im - t| ≤ 1),
        exOrd χ ρ : ℕ) : ℝ) ≤ ((∑ ρ ∈ Z₀.filter (fun ρ => |ρ.im - t| ≤ 1), exOrd χ ρ : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ ≤ C₄ * Real.log ((M : ℝ) * (|t| + 2)) := hwin t
      _ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) := by gcongr
  · intro y hy
    have hmain := hcore κ hκ hκ' M χ T σ₁ T' δ hM hT hσ hσ' hTT' hT'T hδ0 hδ' hgapre hgapim _ hZ y hy
    refine hmain.trans ?_
    have hl1 := exm_log_ge_one (M : ℝ) T hM' hT
    have hNle := exm_N_le κ C₁ C₂ (M : ℝ) T δ hκ hC₁ hC₂ hM' hT hδ0 hδlow
    rw [← hG] at hNle
    set N := C₂ * (2 * Real.log ((M : ℝ) * T)) / δ with hN
    have hN0 : 0 ≤ N := by rw [hN]; positivity
    have ht := exm_tail_num C₃ T T' y (Real.log ((M : ℝ) * T)) hC₃ hT hTT' hy hl1
    have hh := exm_horiz_num G N T T' y (Real.log ((M : ℝ) * T)) hG0 hN0 hNle hT hTT' hy hl1
    have hl := exm_left_num κ G N (M : ℝ) T T' σ₁ y hκ hκ' hG0 hN0 hNle hM' hT hTT' hT'T hσ hσ' hy
    have hy0 : 0 < y := by linarith
    have hly := exm_log_y y hy
    have hX : 1 ≤ (M : ℝ) * T := by nlinarith
    have hfin := sum_le_mul_rpow_add AL AW C ((M : ℝ) * T) (y ^ (-(κ / 2)))
      (Real.log y * Real.log ((M : ℝ) * T) ^ 2 / T) hC4 hCL hCW hX (Real.rpow_nonneg hy0.le _)
      (by have : 0 < T := by linarith
          positivity)
    refine le_trans ?_ hfin
    have hsum := add_le_add (add_le_add ht hl) (add_le_add hh hh)
    calc _ = _ := by ring
      _ ≤ _ := hsum
      _ = _ := by rw [hAW, hAL]; ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
