module

public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth

@[expose] public section

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExpGainFromZeroFreeRegion
section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ChebyshevCharacterExplicitGeneral
section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsContourAvoidingRealZero
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem exists_contour_avoiding_real_zero (B : Finset ℝ) (hB : B.card ≤ 1) (L c₁ : ℝ) (hL : 0 < L) (hc₁ : 0 < c₁) :
    ∃ σ₁ : ℝ, (σ₁ = 1 - c₁ / (3 * L) ∨ σ₁ = 1 - c₁ / (4 * L)) ∧
      ∀ β ∈ B, c₁ / (24 * L) ≤ |σ₁ - β| := by
  have hab : (1 - c₁ / (3 * L)) - (1 - c₁ / (4 * L)) = -(2 * (c₁ / (24 * L))) := by
    field_simp
    ring
  have he : 0 < c₁ / (24 * L) := by positivity
  rcases Finset.eq_empty_or_nonempty B with hB0 | ⟨β, hβ⟩
  · exact ⟨_, Or.inl rfl, fun β hβ => by simp [hB0] at hβ⟩
  have hBs : ∀ β' ∈ B, β' = β := fun β' hβ' => Finset.card_le_one.mp hB β' hβ' β hβ
  by_cases h : c₁ / (24 * L) ≤ |(1 - c₁ / (3 * L)) - β|
  · exact ⟨_, Or.inl rfl, fun β' hβ' => by rw [hBs β' hβ']; exact h⟩
  · refine ⟨_, Or.inr rfl, fun β' hβ' => ?_⟩
    rw [hBs β' hβ']
    push_neg at h
    have tri := abs_sub_le (1 - c₁ / (3 * L)) β (1 - c₁ / (4 * L))
    rw [hab, abs_neg, abs_of_pos (by positivity), abs_sub_comm β] at tri
    linarith

theorem perron_contour_decomposition (hP : PerronChi) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (y σ₁ σ₀ T : ℝ) (R : ℂ) (hy : 1 ≤ y) (hσ₀ : 1 < σ₀) (hT : 0 ≤ T)
    (hrect : Formalism.ZF.rectInt (Fchi χ y) σ₁ σ₀ (-T) T = 2 * Real.pi * I * R) :
    2 * Real.pi * ‖Schi χ y - R‖ ≤
      ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖
      + ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I)‖
      + ‖∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I)‖ := by
  obtain ⟨hint, hS⟩ := hP q χ y hy σ₀ hσ₀
  have hsplit := integral_add_compl (s := Set.Ioc (-T) T) measurableSet_Ioc hint
  have hIoc : ∫ t in Set.Ioc (-T) T, Fchi χ y ((σ₀ : ℂ) + t * I) =
      ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  unfold Formalism.ZF.rectInt at hrect
  set Cp := ∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I) with hCp
  set Bt := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hBt
  set Tp := ∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (T : ℂ) * I) with hTp
  set Lf := ∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I) with hLf
  set Rt := ∫ t in (-T)..T, Fchi χ y ((σ₀ : ℂ) + t * I) with hRt
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hinv : (2 * (Real.pi : ℂ)) * (1 / (2 * Real.pi)) = 1 := by field_simp
  have hI : I * I = -1 := Complex.I_mul_I
  have key : (2 * (Real.pi : ℂ)) * (Schi χ y - R) = Cp + I * (Bt - Tp) + Lf := by
    rw [hS, ← hsplit, hIoc]
    linear_combination (-I) * hrect + (Rt + Cp) * hinv + (Rt - Lf - 2 * Real.pi * R) * hI
  have hn : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_of_nonneg (by positivity)]
  have hsub := norm_sub_le Bt Tp
  calc 2 * Real.pi * ‖Schi χ y - R‖ = ‖(2 * (Real.pi : ℂ)) * (Schi χ y - R)‖ := by
        rw [norm_mul, hn]
    _ = ‖Cp + I * (Bt - Tp) + Lf‖ := by rw [key]
    _ ≤ ‖Cp‖ + ‖I * (Bt - Tp)‖ + ‖Lf‖ := norm_add₃_le
    _ ≤ ‖Cp‖ + ‖Bt‖ + ‖Tp‖ + ‖Lf‖ := by
        rw [norm_mul, Complex.norm_I, one_mul]
        linarith

end Formalism.ZeroFreeDirichlet
end
end

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

set_option maxHeartbeats 1000000 in
theorem chebyshev_character_explicit_general (hP : PerronChi) (hRS : RectShiftChi) (c₁ C C₀ : ℝ) (hc₁ : 0 < c₁)
    (hc₁' : c₁ ≤ 1 / 20) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (hχ : χ ≠ 1)
    (hE : ExcZeros c₁ χ B)
    (hD : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
        ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2)
    (hR : ∀ s : ℂ, 1 < s.re → ‖negLD χ s‖ ≤ 1 / (s.re - 1) + C₀)
    (y T L : ℝ) (hy : 2 ≤ y) (hT : 1 ≤ T) (hL : Real.log ((q : ℝ) * (T + 2)) = L) :
    ∃ σ₁ : ℝ, σ₁ ≤ 1 - c₁ / (4 * L) ∧
      ‖Schi χ y - negLD χ 1 * y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤
        2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T)
        + y ^ σ₁ * (8 * L / c₁) := by
  obtain ⟨hBc, hBz, hBall⟩ := hE
  have hy0 : (0:ℝ) < y := by linarith
  have hy1 : (1:ℝ) ≤ y := by linarith
  have hy1' : (1:ℝ) < y := by linarith
  have hlog2 : (1:ℝ) / 2 < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    linarith
  have hlogy2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hly : (1:ℝ) / 2 < Real.log y := by linarith
  have hlogy : 0 < Real.log y := by linarith
  have hlogyne : Real.log y ≠ 0 := hlogy.ne'
  have hT0 : (0:ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    exact_mod_cast hq
  have hL2 : Real.log 2 ≤ L := by
    rw [← hL]
    exact Real.log_le_log (by norm_num) (by nlinarith)
  have hLh : (1:ℝ) / 2 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hLne : L ≠ 0 := hL0.ne'
  have hc₁ne : c₁ ≠ 0 := hc₁.ne'
  have ha : 0 < c₁ / L := div_pos hc₁ hL0
  have haL : c₁ / L * L = c₁ := by field_simp
  have ha' : c₁ / L ≤ 1 / 10 := by nlinarith
  have e3 : c₁ / (3 * L) = c₁ / L / 3 := by rw [mul_comm 3 L, ← div_div]
  have e4 : c₁ / (4 * L) = c₁ / L / 4 := by rw [mul_comm 4 L, ← div_div]
  have e2 : c₁ / 2 / L = c₁ / L / 2 := div_right_comm c₁ 2 L
  have h2ε : 2 / (c₁ / (4 * L)) = 8 * L / c₁ := by rw [div_div_eq_mul_div]; ring
  have h1δ : 1 / (c₁ / (24 * L)) = 24 * L / c₁ := one_div_div _ _
  obtain ⟨σ₁, hσ₁c, hσ₁B⟩ := exists_contour_avoiding_real_zero B hBc L c₁ hL0 hc₁
  rw [e3, e4] at hσ₁c
  have hσ₁b : 1 - c₁ / L / 3 ≤ σ₁ ∧ σ₁ ≤ 1 - c₁ / L / 4 := by
    rcases hσ₁c with h | h <;> rw [h] <;> constructor <;> linarith
  obtain ⟨hσ₁lo, hσ₁up⟩ := hσ₁b
  refine ⟨σ₁, by rw [e4]; exact hσ₁up, ?_⟩
  have hσ₁lt1 : σ₁ < 1 := by linarith
  have hσ₁pos : 0 < σ₁ := by linarith
  have hhalf : 1 / 2 ≤ σ₁ := by linarith
  have hgap : c₁ / (4 * L) ≤ 1 - σ₁ := by rw [e4]; linarith
  have hσ₁reg : 1 - c₁ / 2 / Real.log ((q : ℝ) * (T + 2)) ≤ σ₁ := by
    rw [hL, e2]; linarith

  obtain ⟨σ₀, hσ₀e⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / Real.log y := ⟨_, rfl⟩
  have hinv : 1 / Real.log y * Real.log y = 1 := by field_simp
  have hinvpos : 0 < 1 / Real.log y := div_pos one_pos hlogy
  have hinv2 : 1 / Real.log y < 2 := by nlinarith
  have hσ₀gt : 1 < σ₀ := by rw [hσ₀e]; linarith
  have hσσ : σ₁ ≤ σ₀ := by linarith
  have hσdiff : |σ₀ - σ₁| ≤ 3 := by
    rw [abs_of_nonneg (by linarith), hσ₀e]; linarith
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := by
    rw [hσ₀e, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hlogyne, mul_comm]

  have hB₁ : ∀ β ∈ B.filter (fun β => σ₁ < β),
      σ₁ < β ∧ β < σ₀ ∧ deriv (DirichletCharacter.LFunction χ) (β : ℂ) ≠ 0 := by
    intro β hβ
    rw [Finset.mem_filter] at hβ
    obtain ⟨-, -, hz, hd⟩ := hBz β hβ.1
    refine ⟨hβ.2, ?_, hd⟩
    have hβ1 : β < 1 := by
      by_contra hc
      push_neg at hc
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by simpa using hc) hz
    linarith
  have hB₁z : ∀ β ∈ B.filter (fun β => σ₁ < β), DirichletCharacter.LFunction χ (β : ℂ) = 0 := by
    intro β hβ
    rw [Finset.mem_filter] at hβ
    exact (hBz β hβ.1).2.2.1
  have hzer : ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T →
      DirichletCharacter.LFunction χ w = 0 → ∃ β ∈ B.filter (fun β => σ₁ < β), w = (β : ℂ) := by
    intro w h1 _ h3 h4
    have hreg : InRegion c₁ q w := by
      unfold InRegion
      have hm := log_analytic_conductor_mono q w.im T h3
      rw [hL] at hm
      have hpos := log_conductor_pos_real q w.im
      have key : c₁ / L ≤ c₁ / Real.log ((q : ℝ) * (|w.im| + 2)) := by
        rw [div_eq_mul_one_div c₁ L, div_eq_mul_one_div c₁ (Real.log ((q : ℝ) * (|w.im| + 2)))]
        exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpos hm) hc₁.le
      linarith
    obtain ⟨β, hβB, hwβ⟩ := hBall w hreg ⟨Or.inl hχ, h4⟩
    refine ⟨β, Finset.mem_filter.mpr ⟨hβB, ?_⟩, hwβ⟩
    have h1' : σ₁ ≤ β := by rw [hwβ] at h1; simpa using h1
    have hne := hσ₁B β hβB
    rcases lt_or_eq_of_le h1' with h | h
    · exact h
    · exfalso
      rw [h, sub_self, abs_zero] at hne
      have hp : 0 < c₁ / (24 * L) := div_pos hc₁ (by linarith)
      linarith
  have hrect := hRS q χ hχ y hy0 σ₁ σ₀ T (B.filter (fun β => σ₁ < β)) hσ₁pos hσ₁lt1 hσ₀gt hT0
    hB₁ hzer hB₁z
  have hdec := perron_contour_decomposition hP χ y σ₁ σ₀ T _ hy1 hσ₀gt hT0.le hrect

  have hAnn : 0 ≤ (Real.log y + C₀) * (Real.exp 1 * y) :=
    mul_nonneg (by linarith) (mul_pos (Real.exp_pos 1) hy0).le
  have hI1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T := by
    refine Formalism.ZF.norm_integral_compl_le (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) _ T hAnn hT0 (fun t ht => ?_)
    show ‖Fchi χ y ((σ₀ : ℂ) + t * I)‖ ≤ _
    rw [hσ₀e]
    exact perron_right_line_bound χ C₀ hR y T t hy1' hT0 ht

  have hHnn : 0 ≤ (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 := by
    have hCL : 0 ≤ C * L ^ 2 + 1 := by
      have := mul_nonneg hC (sq_nonneg L)
      linarith
    exact div_nonneg (mul_nonneg hCL (mul_pos (Real.exp_pos 1) hy0).le) (sq_nonneg T)
  have hH : ∀ v : ℝ, |v| = T → ‖∫ x in σ₁..σ₀, Fchi χ y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3 := by
    intro v hv
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := σ₁) (b := σ₀) (f := fun x : ℝ => Fchi χ y ((x : ℂ) + (v : ℂ) * I))
      (C := (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2) (fun x hx => by
        rw [Set.uIoc_of_le hσσ] at hx
        have hx' := perron_horizontal_segment_bound χ c₁ C B hBc hD y T x v σ₀ σ₁ hy1 hT hv hσ₁reg
          hx.1.le hx.2
        rw [hL, hyσ₀] at hx'
        exact hx')
    exact hb.trans (mul_le_mul_of_nonneg_left hσdiff hHnn)

  have hV : ‖∫ u in (-T)..T, Fchi χ y ((σ₁ : ℂ) + u * I)‖ ≤
      (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T) := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -T) (b := T) (f := fun u : ℝ => Fchi χ y ((σ₁ : ℂ) + u * I))
      (C := (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁)) (fun u hu => by
        rw [Set.uIoc_of_le (by linarith)] at hu
        have hu' : |u| ≤ T := abs_le.mpr ⟨hu.1.le, hu.2⟩
        have hb' := perron_left_line_bound χ c₁ C hc₁.le hC B hBc hD y T u σ₁ (c₁ / (24 * L))
          (c₁ / (4 * L)) hy0 hu' hσ₁reg hhalf (div_pos hc₁ (by linarith)) hgap
          (div_pos hc₁ (by linarith)) hσ₁B
        rw [hL, h1δ, h2ε] at hb'
        exact hb')
    have h2T : |T - -T| = 2 * T := by
      rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring
    rw [h2T] at hb
    exact hb

  have hO : ‖∑ β ∈ B \ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ ≤ y ^ σ₁ * (8 * L / c₁) := by
    refine norm_sum_le_of_card_le_one _ ((Finset.card_le_card Finset.sdiff_subset).trans hBc)
      (fun β : ℝ => (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))) _
      (mul_nonneg (Real.rpow_nonneg hy0.le _) (div_pos (by linarith) hc₁).le) (fun β hβ => ?_)
    rw [Finset.mem_sdiff] at hβ
    have hβσ : β ≤ σ₁ := by
      by_contra hc
      push_neg at hc
      exact hβ.2 (Finset.mem_filter.mpr ⟨hβ.1, hc⟩)
    have hreg := (hBz β hβ.1).2.1
    unfold InRegion at hreg
    simp only [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add] at hreg
    have hl2 : Real.log 2 ≤ Real.log ((q : ℝ) * 2) := Real.log_le_log (by norm_num) (by nlinarith)
    have hlq : (1:ℝ) / 2 < Real.log ((q : ℝ) * 2) := by linarith
    have hlqne : Real.log ((q : ℝ) * 2) ≠ 0 := by linarith
    have hr : c₁ / Real.log ((q : ℝ) * 2) * Real.log ((q : ℝ) * 2) = c₁ := by field_simp
    have hrpos : 0 ≤ c₁ / Real.log ((q : ℝ) * 2) := div_nonneg hc₁.le (by linarith)
    have hrh : c₁ / Real.log ((q : ℝ) * 2) ≤ 1 / 2 := by nlinarith
    have hβhalf : 1 / 2 ≤ β := by linarith
    have hom := real_zero_residue_term_bound y β σ₁ (c₁ / (4 * L)) hy1 hβhalf hβσ (div_pos hc₁ (by linarith)) hgap
    rw [h2ε] at hom
    exact hom

  have hmain : ‖Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))‖ ≤
      2 * Real.pi * ((Real.log y + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * y ^ σ₁ * (8 * L / c₁) * (2 * T) := by
    have hX := norm_nonneg (Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
      (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))))
    have h2pi : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hXX := mul_le_mul_of_nonneg_right h2pi hX
    have hbot := hH (-T) (by rw [abs_neg]; exact hTabs)
    have htop := hH T hTabs
    linarith
  rw [← Finset.sum_sdiff (Finset.filter_subset (fun β => σ₁ < β) B)]
  calc ‖Schi χ y - negLD χ 1 * y + (∑ β ∈ B \ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)) + ∑ β ∈ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))‖
        = ‖(Schi χ y - (negLD χ 1 * y - ∑ β ∈ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1)))) + ∑ β ∈ B \ B.filter (fun β => σ₁ < β),
          (y : ℂ) ^ (β : ℂ) / ((β : ℂ) * ((β : ℂ) - 1))‖ := by congr 1; ring
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ := add_le_add hmain hO

end Formalism.ZeroFreeDirichlet
end
end

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem perron_error_terms_sum_bound (C C₀ c₁ y T X L Pw Y ℓ : ℝ) (hc₁ : 0 < c₁) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hy0 : 0 < y) (hT1 : 1 ≤ T) (hTX : T * X = 1) (hL0 : 0 ≤ L) (hY : 0 ≤ Y)
    (hℓP : ℓ ≤ Pw) (hP1 : 1 ≤ Pw) (hL2P : L ^ 2 ≤ Pw) (hL3P : L ^ 3 ≤ Pw) (hLP : L ≤ Pw) :
    2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) / T
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 1) * (Real.exp 1 * y) / T ^ 2 * 3
        + (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T)
        + Y * (8 * L / c₁) ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
        16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁) * Pw * (y * X + T * Y) := by
  have hT0 : 0 < T := by linarith
  have hX0 : 0 < X := by nlinarith
  have hX1 : X ≤ 1 := by nlinarith
  have e1 : ∀ z : ℝ, z / T = z * X := fun z => by
    rw [div_eq_iff hT0.ne', mul_assoc, mul_comm X T, hTX, mul_one]
  have e2 : ∀ z : ℝ, z / T ^ 2 = z * X * X := fun z => by
    rw [div_eq_iff (pow_pos hT0 2).ne']
    calc z = z * (T * X) * (T * X) := by rw [hTX]; ring
      _ = z * X * X * T ^ 2 := by ring
  simp only [e1, e2]
  have hPw : 0 ≤ Pw := by linarith
  have hyX : 0 ≤ y * X := mul_nonneg hy0.le hX0.le
  have hTY : 0 ≤ T * Y := mul_nonneg hT0.le hY
  have hcC : 0 ≤ C / c₁ := div_nonneg hC hc₁.le
  have hc2 : 0 ≤ 24 / c₁ ^ 2 := by positivity
  have h8 : 0 ≤ 8 / c₁ := div_nonneg (by norm_num) hc₁.le
  have k1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
  have k2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
  have k3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) := mul_nonneg (by norm_num) (add_nonneg hcC hc2)
  have h1 : 2 * Real.pi * ((ℓ + C₀) * (Real.exp 1 * y)) * X ≤
      2 * Real.pi * Real.exp 1 * (1 + C₀) * Pw * (y * X) := by
    have hA : ℓ + C₀ ≤ (1 + C₀) * Pw := by nlinarith
    have hk : 0 ≤ 2 * Real.pi * Real.exp 1 * (y * X) := mul_nonneg (by positivity) hyX
    have := mul_le_mul_of_nonneg_left hA hk
    linarith
  have hB0 : 0 ≤ C * L ^ 2 + 1 := add_nonneg (mul_nonneg hC (sq_nonneg L)) zero_le_one
  have hB : C * L ^ 2 + 1 ≤ (C + 1) * Pw := by
    linarith [mul_le_mul_of_nonneg_left hL2P hC]
  have hXX : X * X ≤ X := mul_le_of_le_one_right hX0.le hX1
  have h2 : (C * L ^ 2 + 1) * (Real.exp 1 * y) * X * X * 3 ≤ 3 * Real.exp 1 * (C + 1) * Pw * (y * X) := by
    have s1 : (C * L ^ 2 + 1) * (X * X) ≤ (C * L ^ 2 + 1) * X := mul_le_mul_of_nonneg_left hXX hB0
    have s2 : (C * L ^ 2 + 1) * X ≤ (C + 1) * Pw * X := mul_le_mul_of_nonneg_right hB hX0.le
    have s3 := mul_le_mul_of_nonneg_left (s1.trans s2)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (mul_nonneg (Real.exp_pos 1).le hy0.le))
    linarith
  have h3 : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) ≤
      16 * (C / c₁ + 24 / c₁ ^ 2) * Pw * (T * Y) := by
    have hid : (C * L ^ 2 + 24 * L / c₁) * Y * (8 * L / c₁) * (2 * T) =
        (16 * (C / c₁) * L ^ 3 + 16 * (24 / c₁ ^ 2) * L ^ 2) * (T * Y) := by ring
    rw [hid]
    apply mul_le_mul_of_nonneg_right _ hTY
    linarith [mul_le_mul_of_nonneg_left hL3P hcC, mul_le_mul_of_nonneg_left hL2P hc2]
  have h4 : Y * (8 * L / c₁) ≤ 8 / c₁ * Pw * (T * Y) := by
    have hid : Y * (8 * L / c₁) = 8 / c₁ * L * Y := by ring
    rw [hid]
    have s1 : 8 / c₁ * L ≤ 8 / c₁ * Pw := mul_le_mul_of_nonneg_left hLP h8
    have s2 : Y ≤ T * Y := by nlinarith
    calc 8 / c₁ * L * Y ≤ 8 / c₁ * Pw * Y := mul_le_mul_of_nonneg_right s1 hY
      _ ≤ 8 / c₁ * Pw * (T * Y) := mul_le_mul_of_nonneg_left s2 (mul_nonneg h8 hPw)
  nlinarith [mul_nonneg (mul_nonneg k1 hPw) hTY, mul_nonneg (mul_nonneg k2 hPw) hTY,
    mul_nonneg (mul_nonneg k3 hPw) hyX, mul_nonneg (mul_nonneg h8 hPw) hyX]

theorem exp_gain_from_zero_free_region (y s c₁ σ₁ L : ℝ) (hy0 : 0 < y) (hℓ : Real.log y = s ^ 2) (hs0 : 0 < s)
    (hc₁ : 0 < c₁) (hL : 0 < L) (hL4 : 4 * L ≤ s) (hσ : σ₁ ≤ 1 - c₁ / (4 * L)) :
    Real.exp (c₁ * s / 2) * y ^ σ₁ ≤ y * Real.exp (-(c₁ * s / 2)) := by
  have hy : y = Real.exp (s ^ 2) := by rw [← hℓ, Real.exp_log hy0]
  have hyσ : y ^ σ₁ = Real.exp (s ^ 2 * σ₁) := by rw [Real.rpow_def_of_pos hy0, hℓ]
  rw [hyσ, ← Real.exp_add, hy, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h4L : 0 < 4 * L := by linarith
  have hq : c₁ ≤ c₁ / (4 * L) * s := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h4L]; nlinarith
  have hc : c₁ ≤ (1 - σ₁) * s := by
    nlinarith [mul_le_mul_of_nonneg_right (by linarith : c₁ / (4 * L) ≤ 1 - σ₁) hs0.le]
  nlinarith [mul_le_mul_of_nonneg_right hc hs0.le]

theorem small_scale_exp_bounds (c₁ s : ℝ) (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 20) (hs : s < 10) :
    Real.exp (c₁ * s / 2) ≤ 3 ∧ 1 ≤ 3 * Real.exp (-(c₁ / 4) * s) := by
  constructor
  · have h : c₁ * s / 2 ≤ 1 := by nlinarith
    calc Real.exp (c₁ * s / 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr h
      _ ≤ 3 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  · have h : -(1 / 8 : ℝ) ≤ -(c₁ / 4) * s := by nlinarith
    have := Real.add_one_le_exp (-(c₁ / 4) * s)
    linarith

theorem cube_mul_exp_le_poly_bound (c₁ s y X : ℝ) (hc₁ : 0 < c₁) (hs0 : 0 < s) (hy0 : 0 < y)
    (hX : X = Real.exp (-(c₁ * s / 2))) :
    s ^ 3 * X * y ≤ 6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s)) := by
  have hu0 : 0 < c₁ * s / 4 := div_pos (mul_pos hc₁ hs0) (by norm_num)
  have hexp : (c₁ * s / 4) ^ 3 / 6 ≤ Real.exp (c₁ * s / 4) := by
    have h := Real.pow_div_factorial_le_exp (c₁ * s / 4) hu0.le 3
    norm_num [Nat.factorial] at h
    linarith
  have hX' : X = Real.exp (-(c₁ * s / 4)) * Real.exp (-(c₁ * s / 4)) := by
    rw [hX, ← Real.exp_add]; congr 1; ring
  have he : Real.exp (-(c₁ / 4) * s) = Real.exp (-(c₁ * s / 4)) := by congr 1; ring
  rw [he, hX']
  have hu3 : (c₁ * s / 4) ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 := by
    have h2 : Real.exp (c₁ * s / 4) * Real.exp (-(c₁ * s / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := mul_le_mul_of_nonneg_right (by linarith : (c₁ * s / 4) ^ 3 ≤ 6 * Real.exp (c₁ * s / 4))
      (Real.exp_pos (-(c₁ * s / 4))).le
    linarith
  have hsu : s = 8 / (2 * c₁) * (c₁ * s / 4) := by
    have := hc₁.ne'
    field_simp
    try ring
  have hK : 0 ≤ (8 / (2 * c₁)) ^ 3 := pow_nonneg (div_nonneg (by norm_num) (by linarith)) 3
  have key : s ^ 3 * Real.exp (-(c₁ * s / 4)) ≤ 6 * (8 / (2 * c₁)) ^ 3 := by
    have hs3 : s ^ 3 = (8 / (2 * c₁)) ^ 3 * (c₁ * s / 4) ^ 3 := by
      rw [← mul_pow, ← hsu]
    rw [hs3]
    nlinarith [mul_le_mul_of_nonneg_left hu3 hK]
  nlinarith [mul_le_mul_of_nonneg_right key (mul_pos (Real.exp_pos (-(c₁ * s / 4))) hy0).le]

end Formalism.ZeroFreeDirichlet
end
end

open Complex MeasureTheory

noncomputable section

namespace Formalism.ZeroFreeDirichlet

theorem smoothed_character_sum_of : SmoothChiOf := by
  intro hP hRS hD hRight c₁ hc₁ hc₁'
  obtain ⟨CD, hCD⟩ := hD c₁ hc₁ hc₁'
  obtain ⟨C₀, hC₀, hR⟩ := hRight
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max CD 0 := ⟨_, rfl⟩
  have hC : 0 ≤ C := hCdef ▸ le_max_right _ _
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * Real.pi * Real.exp 1 * (1 + C₀) + 6 * Real.exp 1 * (C + 1) +
      16 * (C / c₁ + 24 / c₁ ^ 2) + 8 / c₁ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    have ha1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₀) := mul_nonneg (by positivity) (by linarith)
    have ha2 : 0 ≤ 6 * Real.exp 1 * (C + 1) := mul_nonneg (by positivity) (by linarith)
    have ha3 : 0 ≤ 16 * (C / c₁ + 24 / c₁ ^ 2) :=
      mul_nonneg (by norm_num) (add_nonneg (div_nonneg hC hc₁.le) (by positivity))
    have ha4 : 0 ≤ 8 / c₁ := by positivity
    rw [hAdef]; linarith
  refine ⟨c₁ / 4, max (16 * A * (6 * (8 / (2 * c₁)) ^ 3)) (3 * (4 * 12 ^ 3 * A)), by positivity, ?_⟩
  intro q _ χ B y hχ hE hy hq
  have hD' : ∀ s : ℂ, InRegion (c₁ / 2) q s → (∀ β ∈ B, s ≠ (β : ℂ)) →
      ‖negLD χ s + ∑ β ∈ B, 1 / (s - (β : ℂ))‖ ≤ C * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 :=
    fun s h1 h2 => (hCD q χ B hχ hE s h1 h2).trans
      (mul_le_mul_of_nonneg_right (hCdef ▸ le_max_left _ _) (sq_nonneg _))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hℓpos : 0 < Real.log y := Real.log_pos (by linarith)
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (Real.log y) := ⟨_, rfl⟩
  rw [← hsdef] at hq ⊢
  have hℓ : Real.log y = s ^ 2 := by rw [hsdef]; exact (Real.sq_sqrt hℓpos.le).symm
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hℓpos
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp (c₁ * s / 2) := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = Real.exp (-(c₁ * s / 2)) := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp (by positivity)
  have hT0 : 0 < T := by linarith
  have hTX : T * X = 1 := by rw [hTdef, hXdef, ← Real.exp_add]; simp
  have hX0 : 0 < X := by rw [hXdef]; exact Real.exp_pos _
  have hX1 : X ≤ 1 := by
    rw [hXdef]; exact Real.exp_le_one_iff.mpr (by linarith [mul_pos hc₁ hs0])
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log ((q : ℝ) * (T + 2)) := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁, hmain⟩ :=
    chebyshev_character_explicit_general hP hRS c₁ C C₀ hc₁ hc₁' hC hC₀ χ B hχ hE hD' (hR q χ) y T L hy hT1 hLdef.symm

  have hqT1 : (1 : ℝ) ≤ (q : ℝ) * (T + 2) := one_le_mul_of_one_le_of_one_le hq1 (by linarith)
  have hL0 : 0 ≤ L := by rw [hLdef]; exact Real.log_nonneg hqT1
  have hlogq : Real.log q ≤ c₁ / 4 * s := (Real.log_le_iff_le_exp (by linarith)).mpr hq
  have hlogT : Real.log (T + 2) ≤ 2 + c₁ * s / 2 := by
    rw [Real.log_le_iff_le_exp (by linarith), Real.exp_add, ← hTdef]
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
    have := mul_le_mul_of_nonneg_right h3 hT0.le
    linarith
  have hLb : L ≤ 3 * c₁ / 4 * s + 2 := by
    rw [hLdef, Real.log_mul (by linarith) (by linarith)]
    linarith
  have hs'1 : 1 ≤ s + 2 := by linarith
  have hLs' : L ≤ s + 2 := by
    have : 3 * c₁ / 4 * s ≤ s := mul_le_of_le_one_left hs0.le (by linarith)
    linarith
  have hP1 : 1 ≤ (s + 2) ^ 3 := one_le_pow₀ hs'1
  have h23 : (s + 2) ^ 2 ≤ (s + 2) ^ 3 := pow_le_pow_right₀ hs'1 (by norm_num)
  have hℓP : Real.log y ≤ (s + 2) ^ 3 := by
    rw [hℓ]
    have h1 : s ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ hs0.le (by linarith) 2
    linarith
  have hL2P : L ^ 2 ≤ (s + 2) ^ 3 := by
    have h1 : L ^ 2 ≤ (s + 2) ^ 2 := pow_le_pow_left₀ hL0 hLs' 2
    linarith
  have hL3P : L ^ 3 ≤ (s + 2) ^ 3 := pow_le_pow_left₀ hL0 hLs' 3
  have hLP : L ≤ (s + 2) ^ 3 := by
    have : s + 2 ≤ (s + 2) ^ 3 := le_self_pow₀ hs'1 (by norm_num)
    linarith
  have hyσ0 : 0 ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le _
  have hterms := perron_error_terms_sum_bound C C₀ c₁ y T X L ((s + 2) ^ 3) (y ^ σ₁) (Real.log y) hc₁ hC hC₀ hy0
    hT1 hTX hL0 hyσ0 hℓP hP1 hL2P hL3P hLP
  rw [← hAdef] at hterms
  have htot := hmain.trans hterms
  have hyX : 0 ≤ y * X := by positivity
  by_cases hs : 10 ≤ s
  ·
    have hL4 : 4 * L ≤ s := by
      have := mul_le_mul_of_nonneg_right hc₁' hs0.le
      linarith
    have hLpos : 0 < L := by
      rw [hLdef]; apply Real.log_pos
      have := mul_le_mul hq1 (show (3 : ℝ) ≤ T + 2 by linarith) (by norm_num) (by linarith)
      linarith
    have hWX : T * y ^ σ₁ ≤ y * X := by
      rw [hTdef, hXdef]; exact exp_gain_from_zero_free_region y s c₁ σ₁ L hy0 hℓ hs0 hc₁ hLpos hL4 hσ₁
    have hs'2 : (s + 2) ^ 3 ≤ 8 * s ^ 3 := by
      calc (s + 2) ^ 3 ≤ (2 * s) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
        _ = 8 * s ^ 3 := by ring
    have hX3 := cube_mul_exp_le_poly_bound c₁ s y X hc₁ hs0 hy0 hXdef
    calc _ ≤ A * (s + 2) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * (8 * s ^ 3) * (y * X + y * X) := by gcongr
      _ = 16 * A * (s ^ 3 * X * y) := by ring
      _ ≤ 16 * A * (6 * (8 / (2 * c₁)) ^ 3 * (y * Real.exp (-(c₁ / 4) * s))) := by gcongr
      _ = 16 * A * (6 * (8 / (2 * c₁)) ^ 3) * y * Real.exp (-(c₁ / 4) * s) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  ·
    rw [not_le] at hs
    obtain ⟨hT3', hexp⟩ := small_scale_exp_bounds c₁ s hc₁ hc₁' hs
    have hT3 : T ≤ 3 := hTdef ▸ hT3'
    have hPs : (s + 2) ^ 3 ≤ 12 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
    have hσ₁1 : σ₁ ≤ 1 := by
      have : 0 ≤ c₁ / (4 * L) := by positivity
      linarith
    have hyσ : y ^ σ₁ ≤ y := by
      have := Real.rpow_le_rpow_of_exponent_le hy1 hσ₁1
      rwa [Real.rpow_one] at this
    have hW3 : T * y ^ σ₁ ≤ 3 * y := mul_le_mul hT3 hyσ hyσ0 (by norm_num)
    have hyX1 : y * X ≤ y := mul_le_of_le_one_right hy0.le hX1
    calc _ ≤ A * (s + 2) ^ 3 * (y * X + T * y ^ σ₁) := htot
      _ ≤ A * 12 ^ 3 * (y + 3 * y) := by gcongr
      _ = 4 * 12 ^ 3 * A * y * 1 := by ring
      _ ≤ 4 * 12 ^ 3 * A * y * (3 * Real.exp (-(c₁ / 4) * s)) := by gcongr
      _ = 3 * (4 * 12 ^ 3 * A) * y * Real.exp (-(c₁ / 4) * s) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end Formalism.ZeroFreeDirichlet
