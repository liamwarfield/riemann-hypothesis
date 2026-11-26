module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing
noncomputable section

namespace PI.EF

open Complex

theorem fractionFieldToGenericStalk_algebraMap_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (u : ℝ) :
    psi0 χ u = psiRaw χ u - del1 χ * u := by
  unfold psi0 psiRaw del1
  split_ifs <;> simp

theorem first_character_sum_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : 0 ≤ S1 χ := by
  unfold S1
  exact finsum_nonneg (fun ρ => finsum_nonneg (fun _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))

theorem explicitFormula_of_perron_shift (κ : ℝ) (h1 : ∃ C, 0 < C ∧ PerronL C)
    (h2 : ∃ C, 0 < C ∧ ShiftBound κ C) (h3 : GoodHeightExists κ)
    (h4 : ∃ C, 0 < C ∧ TruncChange C) (h5 : ZerosFinite) : PI.ExplicitFormula := by
  obtain ⟨C1, hC1, H1⟩ := h1
  obtain ⟨C2, hC2, H2⟩ := h2
  obtain ⟨C4, hC4, H4⟩ := h4
  refine ⟨C1 + C2 + C4, by positivity, ?_⟩
  intro N _ χ hχ u T hT hTu
  refine ⟨h5 N χ hχ T, ?_⟩
  obtain ⟨T', hT1, hT2, hg⟩ := h3 N χ hχ T hT
  have e1 := H1 N χ u T T' hT hTu hT1 hT2
  have e2 := H2 N χ hχ u T T' hT hTu hT1 hT2 hg
  have e4 := H4 N χ hχ u T T' hT hTu hT1 hT2
  have hS : 0 ≤ S1 χ := first_character_sum_nonneg χ
  have key : psi0 χ u + zsum χ T u = (psiRaw χ u - vertInt χ u T') +
      (vertInt χ u T' - del1 χ * u + zsum χ T' u) - (zsum χ T' u - zsum χ T u) := by
    rw [fractionFieldToGenericStalk_algebraMap_eq]; ring
  show ‖psi0 χ u + zsum χ T u‖ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ)
  rw [key]
  calc ‖(psiRaw χ u - vertInt χ u T') + (vertInt χ u T' - del1 χ * u + zsum χ T' u) -
        (zsum χ T' u - zsum χ T u)‖
      ≤ ‖psiRaw χ u - vertInt χ u T'‖ + ‖vertInt χ u T' - del1 χ * u + zsum χ T' u‖ +
        ‖zsum χ T' u - zsum χ T u‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ C1 * Err N u T + C2 * (Err N u T + S1 χ) + C4 * Err N u T := by gcongr
    _ ≤ (C1 + C2 + C4) * (Err N u T + S1 χ) := by
        nlinarith [mul_nonneg hC1.le hS, mul_nonneg hC4.le hS]

def GlueLocalLemma : Prop :=
  LocalAbstract → (∃ A C, 0 < A ∧ 0 < C ∧ LGrowth A C) → ZeroLocus → PI.ZerosWindow →
    ∃ C, 0 < C ∧ LocalLemma C

def GlueContour : Prop := RectResidue → ZeroLocus → ZerosFinite → ContourIdentity

def GlueSides : Prop :=
  ∀ κ, 0 < κ → (∃ C, 0 < C ∧ LogDerivHoriz κ C) → (∃ C, 0 < C ∧ LogDerivLeft C) →
    ∃ C, 0 < C ∧ SidesBound κ C

end PI.EF
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronTruncOf
namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real ArithmeticFunction LSeries

lemma one_lt_cLine {u : ℝ} (hu : 2 ≤ u) : 1 < cLine u := by
  have h := Real.log_pos (by linarith : (1:ℝ) < u)
  have h2 := one_div_pos.mpr h
  show 1 < 1 + 1 / Real.log u
  linarith

lemma kernel_le_kb (hK : PerronKernel) (y c T : ℝ) (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) :
    ‖perronK y c T - (if 1 ≤ y then 1 else 0)‖ ≤ y ^ c * kb T y := by
  obtain ⟨h1, h2⟩ := hK y c T hy hc hT
  by_cases h : T * |Real.log y| ≤ 1
  · rw [kb, if_pos h]
    linarith
  · rw [kb, if_neg h]
    push_neg at h
    rw [mul_one_div, le_div_iff₀ (by linarith)]
    linarith

lemma term_mul_kernel (a : ℕ → ℂ) (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    term a s n * ((u : ℂ) ^ s / s) = a n * (((u / n : ℝ) : ℂ) ^ s / s) := by
  rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg hu.le (Nat.cast_nonneg n)]
  push_cast
  ring

theorem perronTrunc_of {C : ℝ} (hK : PerronKernel) (hS : PerronSumBound C) : PerronTrunc C := by
  intro a ha u T hu hT
  have hc1 : 1 < cLine u := one_lt_cLine hu
  set c := cLine u with hcdef
  have hc0 : 0 < c := by linarith
  have hu0 : 0 < u := by linarith
  have hT0 : 0 < T := by linarith
  obtain ⟨hSs, hSle⟩ := hS u T hu hT
  have ha0 : a 0 = 0 := by
    have h := ha 0
    rw [ArithmeticFunction.map_zero] at h
    exact norm_le_zero_iff.mp h

  have hΛsum : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
    have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ)) (by simpa using hc1)
    refine Complex.summable_ofReal.mp (h.congr (fun n => ?_))
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      rfl
  have hterm : ∀ (n : ℕ) (s : ℂ), s.re = c →
      ‖LSeries.term a s n‖ ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c := by
    intro n s hs
    rw [LSeries.norm_term_eq, hs]
    split_ifs with hn
    · subst hn
      simp
    · exact div_le_div_of_nonneg_right (ha n) (by positivity)
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := by intro t; simp
  have hkern : ∀ t : ℝ, ‖(u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)‖ ≤ u ^ c / c := by
    intro t
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hu0, hre]
    apply div_le_div_of_nonneg_left (by positivity) hc0
    have h := Complex.abs_re_le_norm ((c : ℂ) + t * I)
    rw [hre, abs_of_pos hc0] at h
    exact h

  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := MeasureTheory.volume)
    (a := -T) (b := T)
    (F := fun (n : ℕ) (t : ℝ) => LSeries.term a ((c : ℂ) + t * I) n *
      ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (f := fun t : ℝ => LSeries a ((c : ℂ) + t * I) * ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)))
    (fun n _ => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c * (u ^ c / c))
    (fun n => by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, zero_mul]
        exact MeasureTheory.aestronglyMeasurable_const
      · simp only [LSeries.term_of_ne_zero hn]
        apply Measurable.aestronglyMeasurable
        fun_prop)
    (fun n => Filter.Eventually.of_forall (fun t _ => by
      rw [norm_mul]
      exact mul_le_mul (hterm n _ (hre t)) (hkern t) (norm_nonneg _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))))
    (Filter.Eventually.of_forall (fun t _ => hΛsum.mul_right _))
    intervalIntegrable_const
    (Filter.Eventually.of_forall (fun t _ => by
      have hsum : LSeriesSummable a ((c : ℂ) + t * I) :=
        Summable.of_norm_bounded hΛsum (fun n => hterm n _ (hre t))
      exact hsum.hasSum.mul_right _))

  have hG : HasSum (fun n : ℕ => a n * perronK (u / n) c T)
      ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in (-T)..T, LSeries a ((c : ℂ) + t * I) *
        ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) := by
    have hfun : (fun n : ℕ => a n * perronK (u / n) c T) = fun n : ℕ => (1 / (2 * Real.pi) : ℂ) *
        ∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
          ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)) := by
      funext n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [ha0, LSeries.term_zero]
      · have h1 : (∫ t : ℝ in (-T)..T, LSeries.term a ((c : ℂ) + t * I) n *
              ((u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I))) =
            a n * ∫ t : ℝ in (-T)..T, ((u / n : ℝ) : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I) := by
          rw [← intervalIntegral.integral_const_mul]
          congr 1
          funext t
          exact term_mul_kernel a u hu0 n hn _
        rw [h1, perronK]
        ring
    rw [hfun]
    exact hDC.mul_left _

  have hind : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
      (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) := by
    have h : HasSum (fun n : ℕ => a n * (if 1 ≤ u / n then (1 : ℂ) else 0))
        (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n * (if 1 ≤ u / n then (1 : ℂ) else 0)) := by
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · have hn0 : n = 0 := by omega
        subst hn0
        simp [ha0]
      · push_neg at hn
        have hlt : u < n := by
          have h1 := Nat.lt_floor_add_one u
          have h2 : (⌊u⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
          linarith
        have h3 : ¬ (1 ≤ u / n) := by
          rw [not_le, div_lt_one (by linarith)]
          exact hlt
        simp [h3]
    convert h using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hnu : (n : ℝ) ≤ u := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hu0.le)
    have h4 : 1 ≤ u / n := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    simp [h4]
  have hdiff := hind.sub hG
  rw [← hdiff.tsum_eq]
  calc _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (u / n) ^ c * kb T (u / n) := by
        apply tsum_of_norm_bounded hSs.hasSum
        intro n
        rw [← mul_sub, norm_mul]
        rcases eq_or_ne n 0 with rfl | hn
        · simp [ha0]
        · have hy : 0 < u / n := div_pos hu0 (by exact_mod_cast Nat.pos_of_ne_zero hn)
          have h1 := kernel_le_kb hK (u / n) c T hy hc0 hT0
          rw [norm_sub_rev] at h1
          rw [mul_assoc]
          exact mul_le_mul (ha n) h1 (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ _ := hSle

end PI.EF.PK
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LogDerivBounds
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem norm_root_number_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖eps0 χ‖ ≤ 1 := by
  unfold PI.EF.eps0
  split_ifs <;> simp

theorem norm_character_correction_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ‖del1 χ‖ ≤ 1 := by
  unfold PI.EF.del1
  split_ifs <;> simp

theorem norm_near_sum_le {C : ℝ} (hC : ZerosWindowWith C) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      C * Real.log (N * (|s.im| + 2)) / d := by
  have hf := (hC N χ hχ s.im).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hf]
  calc ‖∑ ρ ∈ hf.toFinset, (mult χ ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ hf.toFinset, ‖(mult χ ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ) / d := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hd (h ρ ((Set.Finite.mem_toFinset hf).mp hρ))
    _ = (∑ ρ ∈ hf.toFinset, (mult χ ρ : ℝ)) / d := by rw [Finset.sum_div]
    _ ≤ C * Real.log (N * (|s.im| + 2)) / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
        exact (hC N χ hχ s.im).2

private lemma norm_le_add_add_four_of_norm_sub_le {a b c e : ℂ} {x y : ℝ} (h1 : ‖a - b - c + e‖ ≤ x) (h2 : ‖b‖ ≤ y)
    (h3 : ‖c‖ ≤ 2) (h4 : ‖e‖ ≤ 2) : ‖a‖ ≤ x + y + 4 := by
  have e1 : a = (a - b - c + e) + b + c - e := by ring
  rw [e1]
  have k1 := norm_sub_le ((a - b - c + e) + b + c) e
  have k2 := norm_add_le ((a - b - c + e) + b) c
  have k3 := norm_add_le (a - b - c + e) b
  linarith

theorem norm_logDeriv_le {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3)
    (h0 : LFunction χ s ≠ 0) (hs0 : 1 / 2 ≤ ‖s‖) (hs1 : 1 / 2 ≤ ‖s - 1‖) {d : ℝ} (hd : 0 < d)
    (h : ∀ ρ ∈ ZerosNear χ s.im, d ≤ ‖s - ρ‖) :
    ‖logDeriv (LFunction χ) s‖ ≤
      Cl * Real.log (N * (|s.im| + 2)) + Cw * Real.log (N * (|s.im| + 2)) / d + 4 := by
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hs1
  have hmain := hL N χ hχ s h1 h2 h0 hs1'
  have hsum := norm_near_sum_le hW χ hχ s hd h
  have hE : ‖eps0 χ / s‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_root_number_le_one χ]
  have hD : ‖del1 χ / (s - 1)‖ ≤ 2 := by
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [norm_character_correction_le χ]
  exact norm_le_add_add_four_of_norm_sub_le hmain hsum hE hD

theorem log_two_le_log {N : ℕ} [NeZero N] {x : ℝ} (hx : 2 ≤ x) : Real.log 2 ≤ Real.log (N * x) := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact Real.log_le_log (by norm_num) (by nlinarith)

theorem logDerivLeft_of {Cw Cl : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hW : ZerosWindowWith Cw)
    (hL : LocalLemma Cl) (hZ : ZeroLocus) : LogDerivLeft (Cl + 2 * Cw + 6) := by
  unfold PI.EF.LogDerivLeft PI.EF.ZeroLocus at *
  intro N _ χ hχ t
  have hre : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).re = -1 / 2 := by norm_num
  have him : (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im = t := by norm_num
  have hne1 : ((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro a
    have := congrArg Complex.re a
    rw [hre] at this
    norm_num at this
  have hL0 : LFunction χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro h0
    rcases hZ N χ hχ _ (by rw [hre]; norm_num) hne1 h0 with ⟨a, _⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · rw [hre] at a
      norm_num at a
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
    · have := congrArg Complex.re a
      rw [hre] at this
      norm_num at this
  have hs0 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ :=
    le_trans (by rw [hre]; norm_num) (Complex.abs_re_le_norm _)
  have hs1 : 1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - 1‖ :=
    le_trans (by rw [Complex.sub_re, hre, Complex.one_re]; norm_num) (Complex.abs_re_le_norm _)
  have hnear : ∀ ρ ∈ ZerosNear χ (((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I).im,
      1 / 2 ≤ ‖((-1 / 2 : ℝ) : ℂ) + (t : ℂ) * I - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, -⟩ := hρ
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, hre, abs_of_neg (by linarith)]
    linarith
  have key := norm_logDeriv_le hW hL χ hχ _ hre.symm.le (by rw [hre]; norm_num) hL0 hs0 hs1
    (by norm_num : (0 : ℝ) < 1 / 2) hnear
  rw [him] at key
  have hlog2 : Real.log 2 ≤ Real.log (N * (|t| + 2)) := log_two_le_log (by linarith [abs_nonneg t])
  have hl2 := Real.log_two_gt_d9
  refine le_trans key ?_
  calc Cl * Real.log (N * (|t| + 2)) + Cw * Real.log (N * (|t| + 2)) / (1 / 2) + 4
        = Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) + 4 := by ring
    _ ≤ Cl * Real.log (N * (|t| + 2)) + 2 * Cw * Real.log (N * (|t| + 2)) +
          6 * Real.log (N * (|t| + 2)) := by linarith
    _ = (Cl + 2 * Cw + 6) * Real.log (N * (|t| + 2)) := by ring

theorem norm_logDeriv_horiz {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) {T' : ℝ} (hT' : 2 ≤ T')
    (hg : GoodHeight χ κ T') (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) (him : |s.im| = T') :
    ‖logDeriv (LFunction χ) s‖ ≤ (4 * Cl + 2 * Cw * κ + 16) * Real.log (N * T') ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hℓ2 : Real.log 2 ≤ Real.log (N * T') := log_two_le_log hT'
  have hl2 := Real.log_two_gt_d9
  have hlogT2 : Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * T') := by
    have e : 2 * Real.log (N * T') = Real.log ((N * T') ^ 2) := by
      rw [Real.log_pow]
      norm_num
    rw [e]
    apply Real.log_le_log (by nlinarith)
    have hN2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hT2 : T' + 2 ≤ T' ^ 2 := by nlinarith
    calc (N : ℝ) * (T' + 2) ≤ N * T' ^ 2 := mul_le_mul_of_nonneg_left hT2 (by linarith)
      _ ≤ N ^ 2 * T' ^ 2 := mul_le_mul_of_nonneg_right hN2 (by positivity)
      _ = (N * T') ^ 2 := by ring
  have hlogpos2 : 0 ≤ Real.log (N * (T' + 2)) := Real.log_nonneg (by nlinarith)
  unfold PI.EF.GoodHeight at hg
  set ℓ := Real.log (N * T') with hℓ
  have hℓpos : 0 < ℓ := by linarith
  have hd : 0 < 1 / (κ * ℓ) := one_div_pos.mpr (mul_pos hκ hℓpos)
  have hsim : 2 ≤ |s.im| := by rw [him]; exact hT'
  have hs0 : 1 / 2 ≤ ‖s‖ := by linarith [Complex.abs_im_le_norm s]
  have hs1 : 1 / 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1)
    rw [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hs1' : s ≠ 1 := by
    rintro rfl
    norm_num at hsim
  have hL0 : LFunction χ s ≠ 0 := by
    intro h0
    rcases hZ N χ hχ s (by linarith) hs1' h0 with ⟨a1, a2⟩ | ⟨a, _⟩ | ⟨a, _⟩
    · have := hg s a1 a2 h0
      rw [him, sub_self, abs_zero] at this
      linarith
    · rw [a] at hsim
      norm_num at hsim
    · rw [a] at hsim
      norm_num at hsim
  have hnear : ∀ ρ ∈ ZerosNear χ s.im, 1 / (κ * ℓ) ≤ ‖s - ρ‖ := by
    intro ρ hρ
    unfold PI.ZerosNear at hρ
    simp only [Set.mem_setOf_eq] at hρ
    obtain ⟨a1, a2, -, a4⟩ := hρ
    have hgρ := hg ρ a1 a2 a4
    have k1 : |(|ρ.im|) - T'| ≤ |s.im - ρ.im| := by
      rw [← him, abs_sub_comm]
      exact abs_abs_sub_abs_le_abs_sub s.im ρ.im
    have k2 : |s.im - ρ.im| ≤ ‖s - ρ‖ := by
      rw [← Complex.sub_im]
      exact Complex.abs_im_le_norm _
    linarith
  have key := norm_logDeriv_le hW hL χ hχ s h1 h2 hL0 hs0 hs1 hd hnear
  rw [him, div_div_eq_mul_div, div_one] at key
  refine le_trans key ?_
  have h_a : Cl * Real.log (N * (T' + 2)) ≤ Cl * (2 * ℓ) := mul_le_mul_of_nonneg_left hlogT2 hCl
  have h_b : 2 * ℓ ≤ 4 * ℓ ^ 2 := by nlinarith
  have h_c : Cl * (2 * ℓ) ≤ Cl * (4 * ℓ ^ 2) := mul_le_mul_of_nonneg_left h_b hCl
  have h_d : Cw * Real.log (N * (T' + 2)) * (κ * ℓ) ≤ Cw * (2 * ℓ) * (κ * ℓ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogT2 hCw) (mul_pos hκ hℓpos).le
  have h_e : 4 ≤ 16 * ℓ ^ 2 := by nlinarith
  nlinarith [h_a, h_c, h_d, h_e]

theorem logDerivHoriz_of {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) :
    LogDerivHoriz κ (4 * Cl + 2 * Cw * κ + 16) := by
  unfold PI.EF.LogDerivHoriz
  intro N _ χ hχ T' hT' hg σ h1 h2
  have hT0 : (0 : ℝ) ≤ T' := by linarith
  constructor
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])
  · exact norm_logDeriv_horiz hCw hCl hκ hW hL hZ χ hχ hT' hg _ (by simpa using h1) (by simpa using h2)
      (by simp [abs_of_nonneg hT0])

end PI.EF
end
end
