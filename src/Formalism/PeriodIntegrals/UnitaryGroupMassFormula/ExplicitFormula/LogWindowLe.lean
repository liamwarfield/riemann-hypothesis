module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.NormSubCtrSq
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.HalfLeNormLentCtr
noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

lemma one_le_level (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

def LL (N : ℕ) (t : ℝ) : ℝ := Real.log (N * (|t| + 2))

lemma two_le_arg (N : ℕ) [NeZero N] (t : ℝ) : (2 : ℝ) ≤ N * (|t| + 2) := by
  have h1 := one_le_level N
  have h2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  calc (2 : ℝ) = 1 * 2 := by ring
    _ ≤ N * (|t| + 2) := mul_le_mul h1 h2 (by norm_num) (by linarith)

lemma log_two_le_LL (N : ℕ) [NeZero N] (t : ℝ) : Real.log 2 ≤ LL N t := Real.log_le_log (by norm_num) (two_le_arg N t)

lemma one_le_two_LL (N : ℕ) [NeZero N] (t : ℝ) : 1 ≤ 2 * LL N t := by
  have h1 := log_two_le_LL N t
  have h2 := Real.log_two_gt_d9
  linarith

lemma Lent_eq (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : z ≠ 1) :
    Lent χ z = (1 + del1 χ * (z - 2)) * LFunction χ z := by
  unfold Lent del1
  split_ifs with h
  · subst h
    have e : DirichletCharacter.LFunctionTrivChar₁ N z =
        (z - 1) * DirichletCharacter.LFunctionTrivChar N z := by
      simp [DirichletCharacter.LFunctionTrivChar₁, hz]
    rw [e]
    show (z - 1) * LFunction 1 z = (1 + 1 * (z - 2)) * LFunction 1 z
    ring
  · simp

lemma Lent_bound_ne {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {z : ℂ} (h1 : -4 ≤ z.re)
    (h2 : z.re ≤ 8) (h3 : |z.im| ≤ |t| + 6) (hz : z ≠ 1) :
    ‖Lent χ z‖ ≤ C * (4 * (N * (|t| + 2))) ^ A := by
  rw [Lent_eq χ hz]
  refine (hG N χ hχ z h1 h2).trans ?_
  have hN := one_le_level N
  have hb : (N : ℝ) * (|z.im| + 2) ≤ 4 * (N * (|t| + 2)) := by
    have := mul_le_mul_of_nonneg_left (show |z.im| + 2 ≤ 4 * (|t| + 2) by linarith [abs_nonneg t])
      (show (0 : ℝ) ≤ N by linarith)
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hA.le) hC.le

lemma Lent_bound {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {z : ℂ} (h1 : -4 ≤ z.re)
    (h2 : z.re ≤ 8) (h3 : |z.im| ≤ |t| + 6) :
    ‖Lent χ z‖ ≤ C * (4 * (N * (|t| + 2))) ^ A := by
  by_cases hz : z = 1
  · subst hz
    have hcont : Continuous (Lent χ) := by
      unfold Lent
      split_ifs with h
      · exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).continuous
      · exact (DirichletCharacter.differentiable_LFunction h).continuous
    have hc : Continuous (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) :=
      (hcont.comp (continuous_const.add Complex.continuous_ofReal)).norm
    have h0 : ‖Lent χ 1‖ = ‖Lent χ (1 + ((0 : ℝ) : ℂ))‖ := by simp
    have hT : Filter.Tendsto (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhds ‖Lent χ 1‖) := by
      rw [h0]
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hT ?_
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) {0}ᶜ :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [hmem, self_mem_nhdsWithin] with x hx hx0
    have hx1 : (1 + (x : ℂ)) ≠ 1 := by
      intro h
      apply hx0
      have h' := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at h'
      show x = 0
      linarith
    refine Lent_bound_ne hA hC hG hχ ?_ ?_ ?_ hx1
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith [hx.1]
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith [hx.2]
    · simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero, abs_zero]
      positivity
  · exact Lent_bound_ne hA hC hG hχ h1 h2 h3 hz

def ctr (t : ℝ) : ℂ := 2 + t * I

@[simp] lemma ctr_re (t : ℝ) : (ctr t).re = 2 := by
  simp [ctr]
@[simp] lemma ctr_im (t : ℝ) : (ctr t).im = t := by
  simp [ctr]

lemma ctr_ne_one (t : ℝ) : ctr t ≠ 1 := by
  intro h
  have h' := congrArg Complex.re h
  rw [ctr_re] at h'
  norm_num at h'

lemma half_le_norm_Lent_ctr (hI : PI.LInvRight) (χ : DirichletCharacter ℂ N) (t : ℝ) :
    1 / 2 ≤ ‖Lent χ (ctr t)‖ := by
  have hL := hI N χ (ctr t) (by rw [ctr_re]; norm_num)
  have h21 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  rw [ctr_re, h21] at hL
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (s := ctr t)
    (Or.inr (ctr_ne_one t)) (by rw [ctr_re]; norm_num)
  have hpos : 0 < ‖LFunction χ (ctr t)‖ := norm_pos_iff.mpr hne
  have hL2 : 1 / 2 ≤ ‖LFunction χ (ctr t)‖ := by
    have h1 := mul_le_mul_of_nonneg_left hL hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at h1
    linarith
  rw [Lent_eq χ (ctr_ne_one t), norm_mul]
  have hf : 1 ≤ ‖1 + del1 χ * (ctr t - 2)‖ := by
    have hre : (1 + del1 χ * (ctr t - 2)).re = 1 := by
      unfold del1 ctr
      split_ifs <;> norm_num
    have := Complex.abs_re_le_norm (1 + del1 χ * (ctr t - 2))
    rw [hre, abs_one] at this
    exact this
  have := mul_le_mul hf hL2 (by norm_num) (by positivity)
  linarith

def Mfun (A C : ℝ) (N : ℕ) (t : ℝ) : ℝ := |Real.log (2 * C)| + A * Real.log (4 * (N * (|t| + 2)))

lemma Mfun_nonneg {A C : ℝ} (hA : 0 < A) (N : ℕ) [NeZero N] (t : ℝ) : 0 ≤ Mfun A C N t := by
  unfold Mfun
  have h := two_le_arg N t
  have h3 : 0 ≤ Real.log (4 * (N * (|t| + 2))) := Real.log_nonneg (by linarith)
  have h4 := abs_nonneg (Real.log (2 * C))
  have h5 := mul_nonneg hA.le h3
  linarith

lemma Mfun_le {A C : ℝ} (hA : 0 < A) (N : ℕ) [NeZero N] (t : ℝ) :
    Mfun A C N t ≤ (2 * |Real.log (2 * C)| + 3 * A) * LL N t := by
  unfold Mfun
  have hX : (0 : ℝ) < N * (|t| + 2) := by linarith [two_le_arg N t]
  have h4 : Real.log (4 * (N * (|t| + 2))) = Real.log 4 + LL N t := by
    rw [Real.log_mul (by norm_num) hX.ne']
    rfl
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h1 := one_le_two_LL N t
  have h2 := log_two_le_LL N t
  have ha := abs_nonneg (Real.log (2 * C))
  rw [h4, hl4]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hA.le]

lemma le_exp_Mfun {A C : ℝ} (hC : 0 < C) (N : ℕ) [NeZero N] (t : ℝ) :
    2 * C * (4 * (N * (|t| + 2))) ^ A ≤ Real.exp (Mfun A C N t) := by
  unfold Mfun
  have hY : (0 : ℝ) < 4 * (N * (|t| + 2)) := by linarith [two_le_arg N t]
  rw [Real.exp_add, Real.rpow_def_of_pos hY, mul_comm (Real.log (4 * (N * (|t| + 2)))) A]
  have h2C : 2 * C ≤ Real.exp |Real.log (2 * C)| := by
    calc 2 * C = Real.exp (Real.log (2 * C)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_abs_self _)
  exact mul_le_mul_of_nonneg_right h2C (Real.exp_pos _).le

theorem Lent_disc_bound {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C) (hI : PI.LInvRight)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (t : ℝ) :
    ∀ z ∈ closedBall (ctr t) 6, ‖Lent χ z‖ ≤ Real.exp (Mfun A C N t) * ‖Lent χ (ctr t)‖ := by
  intro z hz
  have hz' : ‖z - ctr t‖ ≤ 6 := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - ctr t)).trans hz'
  have him := (Complex.abs_im_le_norm (z - ctr t)).trans hz'
  rw [Complex.sub_re, ctr_re] at hre
  rw [Complex.sub_im, ctr_im] at him
  have h1 : -4 ≤ z.re := by linarith [neg_abs_le (z.re - 2)]
  have h2 : z.re ≤ 8 := by linarith [le_abs_self (z.re - 2)]
  have h3 : |z.im| ≤ |t| + 6 := by
    have := abs_sub_abs_le_abs_sub z.im t
    linarith
  have hb := Lent_bound hA hC hG hχ h1 h2 h3
  have he := le_exp_Mfun (A := A) hC N t
  have hh := half_le_norm_Lent_ctr hI χ t
  have hE := Real.exp_pos (Mfun A C N t)
  have hP : 0 ≤ C * (4 * (N * (|t| + 2))) ^ A := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hh hE.le]

end PI.EF
end
end

noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

def DZ (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ := {ρ | ρ ∈ closedBall (ctr t) (11 / 4) ∧ Lent χ ρ = 0}

lemma norm_sub_ctr_sq (ρ : ℂ) (t : ℝ) : ‖ρ - ctr t‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ctr_re, ctr_im]
  ring

private lemma Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ : ρ ≠ 1) :
    Lent χ ρ = 0 ↔ LFunction χ ρ = 0 := by
  unfold Lent
  split_ifs with h
  · subst h
    simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hρ, sub_eq_zero]
  · exact Iff.rfl

lemma DZ_facts (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ DZ χ t) :
    ρ ≠ 1 ∧ LFunction χ ρ = 0 ∧ |ρ.im - t| ≤ 3 ∧
      ((0 < ρ.re ∧ ρ.re < 1) ∨ (ρ = 0 ∧ χ.Even ∧ χ ≠ 1)) := by
  obtain ⟨hb, hz⟩ := hρ
  rw [Metric.mem_closedBall, dist_eq_norm] at hb
  have hsq := norm_sub_ctr_sq ρ t
  have hn := norm_nonneg (ρ - ctr t)
  have hx2 : ‖ρ - ctr t‖ ^ 2 ≤ (11 / 4) ^ 2 := by nlinarith
  have hre : -3 / 4 ≤ ρ.re := by nlinarith [sq_nonneg (ρ.im - t)]
  have him : |ρ.im - t| ≤ 3 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (ρ.re - 2)]
  have hne : ρ ≠ 1 := by
    rintro rfl
    unfold Lent at hz
    split_ifs at hz with h
    · subst h
      first
        | exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero _ hz
        | exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero hz
    · exact DirichletCharacter.LFunction_apply_one_ne_zero h hz
  have hL : LFunction χ ρ = 0 := (Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one χ hne).1 hz
  refine ⟨hne, hL, him, ?_⟩
  rcases hZL N χ hχ ρ (by linarith) hne hL with h | h | ⟨rfl, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · norm_num at hre

lemma far_sum_le {Cw : ℝ} (hW : ZerosWindowWith Cw) (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {t : ℝ} (s : ℂ) (hs : s.im = t) (E : Finset ℂ)
    (hE : ∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) :
    ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      Cw * Real.log (N * (|t + 2| + 2)) + Cw * Real.log (N * (|t - 2| + 2)) := by
  classical
  have hE' : ∀ ρ ∈ E, 1 ≤ ‖s - ρ‖ ∧ (ρ ∈ ZerosNear χ (t + 2) ∨ ρ ∈ ZerosNear χ (t - 2)) := by
    intro ρ hρ
    obtain ⟨hD, hN, h0⟩ := hE ρ hρ
    obtain ⟨-, hL, him, hcase⟩ := DZ_facts hZL hχ hD
    have hstrip : 0 < ρ.re ∧ ρ.re < 1 := by
      rcases hcase with h | ⟨h, -⟩
      · exact h
      · exact absurd h h0
    have hfar : 1 < |ρ.im - t| := by
      by_contra hc
      push_neg at hc
      exact hN ⟨hstrip.1, hstrip.2, hc, hL⟩
    refine ⟨?_, ?_⟩
    · calc (1 : ℝ) ≤ |ρ.im - t| := hfar.le
        _ = |(s - ρ).im| := by rw [Complex.sub_im, hs, abs_sub_comm]
        _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
    · rcases le_or_gt 0 (ρ.im - t) with h | h
      · left
        refine ⟨hstrip.1, hstrip.2, ?_, hL⟩
        rw [abs_of_nonneg h] at hfar him
        rw [abs_le]
        constructor <;> linarith
      · right
        refine ⟨hstrip.1, hstrip.2, ?_, hL⟩
        rw [abs_of_neg h] at hfar him
        rw [abs_le]
        constructor <;> linarith
  obtain ⟨hfinP, hsumP⟩ := hW N χ hχ (t + 2)
  obtain ⟨hfinM, hsumM⟩ := hW N χ hχ (t - 2)
  have step1 : ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ E, (mult χ ρ : ℝ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    rw [norm_div]
    have h1 := (hE' ρ hρ).1
    have hc : ‖(mult χ ρ : ℂ)‖ = (mult χ ρ : ℝ) := by
      first
        | exact Complex.norm_natCast _
        | simp
    rw [hc]
    exact div_le_self (Nat.cast_nonneg _) h1
  have step2 : ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤
      ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) := by
    have hsub : E ⊆ hfinP.toFinset ∪ hfinM.toFinset := by
      intro ρ hρ
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact (hE' ρ hρ).2
    calc ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤ ∑ ρ ∈ hfinP.toFinset ∪ hfinM.toFinset, (mult χ ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hP : ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t + 2| + 2)) := by
    calc _ = ∑ᶠ ρ ∈ ZerosNear χ (t + 2), (mult χ ρ : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ hfinP).symm
      _ ≤ _ := hsumP
  have hM : ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t - 2| + 2)) := by
    calc _ = ∑ᶠ ρ ∈ ZerosNear χ (t - 2), (mult χ ρ : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ hfinM).symm
      _ ≤ _ := hsumM
  linarith

lemma zero_term_le (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ}
    (s : ℂ) (hs : s.im = t) :
    ‖(open Classical in if (0 : ℂ) ∈ DZ χ t then (mult χ 0 : ℂ) / (s - 0) else 0) - eps0 χ / s‖
      ≤ 1 := by
  classical
  by_cases h0 : (0 : ℂ) ∈ DZ χ t
  · obtain ⟨-, hL, -, h⟩ := DZ_facts hZL hχ h0
    rcases h with h | h
    · simp at h
    · obtain ⟨-, he, h1⟩ := h
      have hm := (mult_zero_of_even hχ he h1).2
      simp only [h0, if_true, mult, hm, eps0, he, h1, ne_eq, not_false_eq_true, and_self, sub_zero]
      simp
  · simp only [h0, if_false, zero_sub, norm_neg]
    unfold eps0
    split_ifs with he
    · have hL := (mult_zero_of_even hχ he.1 he.2).1
      have h0' : ¬ ((0 : ℂ) ∈ closedBall (ctr t) (11 / 4)) := by
        intro hb
        exact h0 ⟨hb, (Lent_eq_zero_iff χ (by norm_num)).2 hL⟩
      rw [mem_closedBall, dist_eq_norm, not_le, zero_sub] at h0'
      have h1 := norm_sub_ctr_sq 0 t
      simp only [zero_re, zero_im, zero_sub] at h1
      have h2 : 1 < t ^ 2 := by nlinarith [norm_nonneg (-ctr t)]
      have h3 : 1 ≤ ‖s‖ := by
        have h4 := Complex.abs_im_le_norm s
        rw [hs] at h4
        have h5 : 1 < |t| := by
          by_contra h6
          have := abs_le.1 (not_lt.1 h6)
          nlinarith
        linarith
      rw [norm_div, norm_one]
      exact div_le_one_of_le₀ h3 (norm_nonneg _)
    · simp

end PI.EF
end
end

noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

lemma log_window_le (N : ℕ) [NeZero N] {t u : ℝ} (hu : |u| ≤ |t| + 2) :
    Real.log (N * (|u| + 2)) ≤ 2 * LL N t := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht := abs_nonneg t
  have hu0 := abs_nonneg u
  rw [LL.eq_1]
  have hpos : 0 < (N : ℝ) * (|u| + 2) := by positivity
  have h1 : (N : ℝ) * (|u| + 2) ≤ N * (|t| + 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : |t| + 4 ≤ (|t| + 2) ^ 2 := by nlinarith
  have h3 : (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := by
    calc (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 4) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
      _ ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc Real.log (N * (|u| + 2)) ≤ Real.log ((N * (|t| + 2)) ^ 2) :=
        Real.log_le_log hpos (by rw [mul_pow]; linarith)
    _ = 2 * Real.log (N * (|t| + 2)) := by rw [Real.log_pow]; norm_num

theorem mem_ball_ctr (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) :
    s ∈ closedBall (ctr s.im) (5 / 2) := by
  rw [Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]
  have h : s - (2 + (s.im : ℂ) * Complex.I) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

lemma sum_DZ_eq {χ : DirichletCharacter ℂ N} (t : ℝ)
    (hfin : (DZ χ t).Finite) (F : ℂ → ℂ) :
    ∃ E : Finset ℂ, (∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) ∧
      ∑ᶠ ρ ∈ DZ χ t, F ρ = ∑ᶠ ρ ∈ ZerosNear χ t, F ρ + ∑ ρ ∈ E, F ρ +
        (open Classical in if (0 : ℂ) ∈ DZ χ t then F 0 else 0) := by
  classical
  have hsub : ZerosNear χ t ⊆ DZ χ t := by
    intro ρ hρ
    rw [ZerosNear.eq_1] at hρ
    obtain ⟨h0, h1, him, hL⟩ := hρ
    rw [DZ.eq_1, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]
      have hre : (ρ - (2 + (t : ℂ) * Complex.I)).re = ρ.re - 2 := by simp
      have him' : (ρ - (2 + (t : ℂ) * Complex.I)).im = ρ.im - t := by simp
      obtain ⟨ha, hb⟩ := abs_le.mp him
      rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply,
        hre, him']
      nlinarith
    · have hne : ρ ≠ 1 := by
        intro h
        rw [h] at h1
        norm_num at h1
      rw [Lent.eq_1]
      split_ifs with hχ
      · subst hχ
        have key : DirichletCharacter.LFunctionTrivChar₁ N ρ =
            (ρ - 1) * DirichletCharacter.LFunctionTrivChar N ρ := by
          first
          | simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hne]
          | (unfold DirichletCharacter.LFunctionTrivChar₁; rw [Function.update_of_ne hne])
          | exact DirichletCharacter.LFunctionTrivChar₁_apply_ne_one N hne
        rw [key]
        exact mul_eq_zero_of_right _ hL
      · exact hL
  have h0Z : (0 : ℂ) ∉ ZerosNear χ t := by
    intro h
    rw [ZerosNear.eq_1] at h
    obtain ⟨h0, -⟩ := h
    simp at h0
  have hZ : (ZerosNear χ t).Finite := hfin.subset hsub
  refine ⟨(hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter (fun ρ => ρ ≠ 0), ?_, ?_⟩
  · intro ρ hρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.1.1, hρ.1.2, hρ.2⟩
  · rw [finsum_mem_eq_finite_toFinset_sum F hfin, finsum_mem_eq_finite_toFinset_sum F hZ,
      ← Finset.sum_filter_add_sum_filter_not hfin.toFinset (fun ρ => ρ ∈ ZerosNear χ t)]
    have e1 : hfin.toFinset.filter (fun ρ => ρ ∈ ZerosNear χ t) = hZ.toFinset := by
      ext ρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    rw [e1, add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not
      (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)) (fun ρ => ρ ≠ 0)]
    congr 1
    split_ifs with hD
    · have e2 : (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter
          (fun ρ => ¬ ρ ≠ 0) = {0} := by
        ext ρ
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton, ne_eq,
          not_not]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · rintro rfl
          exact ⟨⟨hD, h0Z⟩, rfl⟩
      rw [e2, Finset.sum_singleton]
    · apply Finset.sum_eq_zero
      intro ρ hρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, ne_eq, not_not] at hρ
      exact absurd (hρ.2 ▸ hρ.1.1) hD

theorem localLemma_of (hI : PI.LInvRight) : GlueLocalLemma := by
  intro hLA hG hZL hW
  obtain ⟨A, C, hA, hC, hG⟩ := hG
  obtain ⟨Cw, hCw, hW⟩ := hW
  obtain ⟨C₀, hC₀, hloc⟩ := hLA (5 / 2) (11 / 4) 6 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C₀ * (2 * |Real.log (2 * C)| + 3 * A) + 4 * Cw + 2, by positivity, ?_⟩
  intro N _ χ hχ s h1 h2 hLs hs1
  have hc0 : Lent χ (ctr s.im) ≠ 0 := by
    have := half_le_norm_Lent_ctr hI χ s.im
    exact norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) this)
  obtain ⟨hfin, hbound⟩ := hloc (Lent χ) (ctr s.im) (Mfun A C N s.im)
    (fun z _ => (differentiable_Lent χ).analyticAt z) hc0 (Mfun_nonneg hA N s.im)
    (Lent_disc_bound hA hC hG hI hχ s.im)
  have hLs' : Lent χ s ≠ 0 := fun h => hLs ((Lent_eq_zero_iff χ hs1).1 h)
  have hb := hbound s (mem_ball_ctr s h1 h2) hLs'
  have hfin' : (DZ χ s.im).Finite := hfin
  have econgr : ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall (ctr s.im) (11 / 4) ∧ Lent χ ρ = 0},
      (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) =
      ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ) :=
    finsum_mem_congr rfl (fun ρ hρ => by rw [order_Lent χ (DZ_facts hZL hχ hρ).1])
  rw [econgr] at hb
  obtain ⟨E, hE, hdec⟩ := sum_DZ_eq s.im hfin' (fun ρ => (mult χ ρ : ℂ) / (s - ρ))
  have hfar := far_sum_le hW hZL hχ s rfl E hE
  have hzero := zero_term_le hZL hχ s rfl
  have hM := Mfun_le (C := C) hA N s.im
  have hw1 := log_window_le N (t := s.im) (u := s.im + 2)
    ((abs_add_le _ _).trans (by norm_num))
  have hw2 := log_window_le N (t := s.im) (u := s.im - 2)
    ((abs_sub _ _).trans (by norm_num))
  have hL1 := one_le_two_LL N s.im
  have key : logDeriv (LFunction χ) s - ∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ) -
      eps0 χ / s + del1 χ / (s - 1) =
      (logDeriv (Lent χ) s - ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ)) +
        ∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ) +
        ((open Classical in if (0 : ℂ) ∈ DZ χ s.im then (mult χ 0 : ℂ) / (s - 0) else 0) -
          eps0 χ / s) := by
    rw [logDeriv_Lent χ hs1 hLs, hdec]
    ring
  rw [key]
  have hMnn := Mfun_nonneg (C := C) hA N s.im
  calc _ ≤ ‖logDeriv (Lent χ) s - ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ +
        ‖(open Classical in if (0 : ℂ) ∈ DZ χ s.im then (mult χ 0 : ℂ) / (s - 0) else 0) -
          eps0 χ / s‖ := norm_add₃_le
    _ ≤ C₀ * Mfun A C N s.im + (Cw * Real.log (N * (|s.im + 2| + 2)) +
        Cw * Real.log (N * (|s.im - 2| + 2))) + 1 := add_le_add (add_le_add hb hfar) hzero
    _ ≤ C₀ * ((2 * |Real.log (2 * C)| + 3 * A) * LL N s.im) +
        (Cw * (2 * LL N s.im) + Cw * (2 * LL N s.im)) + 2 * LL N s.im := by
        gcongr
    _ = (C₀ * (2 * |Real.log (2 * C)| + 3 * A) + 4 * Cw + 2) * Real.log (N * (|s.im| + 2)) := by
        unfold LL
        ring

end PI.EF
