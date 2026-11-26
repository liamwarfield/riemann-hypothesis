module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.StrongMultOneReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CentChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NotSummableTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.OneLeNorm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Deplete
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.PolyInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.HolTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.CuspZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.HermOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.EvPl

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.UnfMMp
open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

private lemma UpperTheory.V.Af.Rs.unfM_mp (γ : SL(2, ℤ)) :
    MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
  rw [this]
  exact measurePreserving_smul _ _

theorem UpperTheory.V.Af.Rs.unfM :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.FdCount → UpperTheory.V.Af.Rs.UnfM := by
  intro hFin hCount
  unfold UpperTheory.V.Af.Rs.UnfM
  unfold UpperTheory.V.Af.Rs.FdFin at hFin
  unfold UpperTheory.V.Af.Rs.FdCount at hCount
  obtain ⟨hfdm, -⟩ := hFin
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  ext s hs
  rw [Measure.sum_apply _ hs]
  have step : ∀ γ : SL(2, ℤ), Measure.map (fun z : ℍ => γ • z) (volume.restrict ModularGroup.fd) s
      = ∫⁻ z in s, ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z) := by
    intro γ
    have hm : Measurable (fun z : ℍ => γ • z) := (UpperTheory.V.Af.Rs.unfM_mp γ).measurable
    have hm' : Measurable (fun z : ℍ => γ⁻¹ • z) := (UpperTheory.V.Af.Rs.unfM_mp γ⁻¹).measurable
    have hP : MeasurableSet ((fun z : ℍ => γ⁻¹ • z) ⁻¹' ModularGroup.fd) := hm' hfdm
    rw [Measure.map_apply hm hs, Measure.restrict_apply (hm hs)]
    have hind : (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z))
        = ((fun z : ℍ => γ⁻¹ • z) ⁻¹' ModularGroup.fd).indicator 1 := by
      ext z
      by_cases h : γ⁻¹ • z ∈ ModularGroup.fd
      · rw [indicator_of_mem h, indicator_of_mem (show z ∈ _ from h)]
        rfl
      · rw [indicator_of_notMem h, indicator_of_notMem (show z ∉ _ from h)]
    rw [hind, lintegral_indicator_one hP, Measure.restrict_apply hP,
      ← (UpperTheory.V.Af.Rs.unfM_mp γ).measure_preimage (hP.inter hs).nullMeasurableSet]
    congr 1
    ext z
    simp only [mem_preimage, mem_inter_iff, inv_smul_smul]
    exact and_comm
  rw [tsum_congr step]
  have hmeas : ∀ γ : SL(2, ℤ), AEMeasurable
      (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z))
      (volume.restrict s) := fun γ =>
    ((measurable_const.indicator hfdm).comp (UpperTheory.V.Af.Rs.unfM_mp γ⁻¹).measurable).aemeasurable
  rw [← lintegral_tsum hmeas]
  have hre : ∀ z : ℍ, ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ⁻¹ • z)
      = ∑' γ : SL(2, ℤ), ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z) :=
    fun z => (Equiv.inv SL(2, ℤ)).tsum_eq
      (fun γ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (γ • z))
  simp_rw [hre]
  rw [lintegral_congr_ae (ae_restrict_of_ae hCount), setLIntegral_const, Measure.smul_apply]
  first
    | rw [two_mul, two_nsmul]
    | rw [smul_eq_mul]
    | simp [two_mul, two_smul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.LBd
theorem UpperTheory.V.Af.Rs.lBd :
    UpperTheory.V.Af.Rs.LBd := by
  intro L _ ψ s hs
  set f : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hf
  set g : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hg
  have hs2 : (2 * s) ≠ 0 := by linarith
  have hbd : ∀ n, ‖f n‖ ≤ g n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hf, hg, Real.zero_rpow hs2]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n : ℝ) ^ (2 * s) := Real.rpow_pos_of_pos (by linarith) _
      have hle : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (2 * s) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      rw [Real.rpow_two] at hle
      simp only [hf, hg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      calc ‖ψ n‖ / (n : ℝ) ^ (2 * s) ≤ 1 / (n : ℝ) ^ (2 * s) :=
            div_le_div_of_nonneg_right (DirichletCharacter.norm_le_one ψ _) hpos.le
        _ ≤ 1 / (n : ℝ) ^ 2 := one_div_le_one_div_of_le (by positivity) hle
  have hgs : HasSum g (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hsum : Summable f := Summable.of_norm_bounded hgs.summable hbd
  refine ⟨hsum, ?_⟩
  have hg2 : HasSum (fun n => g (n + 2)) (Real.pi ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' (f := g) 2).mpr hgs
    simpa [Finset.sum_range_succ, hg] using this
  have htail : ‖∑' n, f (n + 2)‖ ≤ Real.pi ^ 2 / 6 - 1 :=
    tsum_of_norm_bounded hg2 (fun n => hbd (n + 2))
  have hsplit : UpperTheory.V.Af.Rs.Lps ψ s = 1 + ∑' n, f (n + 2) := by
    rw [UpperTheory.V.Af.Rs.Lps, ← hsum.sum_add_tsum_nat_add 2]
    simp [Finset.sum_range_succ, hf, Real.zero_rpow hs2]
  have hpi : Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
    have h1 := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  rw [hsplit]
  constructor
  · have := norm_sub_norm_le (1 : ℂ) (-(∑' n, f (n + 2)))
    rw [sub_neg_eq_add, norm_neg, norm_one] at this
    linarith
  · have := norm_add_le (1 : ℂ) (∑' n, f (n + 2))
    rw [norm_one] at this
    linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.LineExp
open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

namespace UpperTheory.V.Af.Rs

private noncomputable def ex (n : ℕ) (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * n * x)

private theorem ex_norm (n : ℕ) (x : ℝ) : ‖ex n x‖ = 1 := by
  unfold ex
  have h : (2 * Real.pi * Complex.I * n * x : ℂ) = ((2 * Real.pi * n * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private theorem ex_cont (n : ℕ) : Continuous (ex n) := by unfold ex; fun_prop

private theorem ex_orth (m n : ℕ) : ∫ x in (0 : ℝ)..1, conj (ex m x) * ex n x = if m = n then 1 else 0 := by
  unfold ex
  have key : ∀ x : ℝ, conj (Complex.exp (2 * Real.pi * Complex.I * m * x)) *
      Complex.exp (2 * Real.pi * Complex.I * n * x) =
      Complex.exp ((2 * Real.pi * Complex.I * ((n : ℂ) - m)) * x) := by
    intro x
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  simp_rw [key]
  split_ifs with hmn
  · subst hmn
    simp
  · have hc : (2 * Real.pi * Complex.I * ((n : ℂ) - m)) ≠ 0 := by
      have h1 : ((n : ℂ) - m) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm hmn)
      have h2 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [h1, h2, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have e1 : Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) - m) * ((1 : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [e1]
    simp

private theorem pars_abs (a b : ℕ → ℂ) (ha : Summable a) (hb : Summable b) (F G : ℝ → ℂ)
    (hF : ∀ x, HasSum (fun n => a n * ex n x) (F x)) (hG : ∀ x, HasSum (fun n => b n * ex n x) (G x)) :
    HasSum (fun n => conj (b n) * a n) (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
  have han : Summable (fun n => ‖a n‖) := summable_norm_iff.mpr ha
  have hbn : Summable (fun n => ‖b n‖) := summable_norm_iff.mpr hb
  have hGc : Continuous G := by
    have e : G = fun x => ∑' n, b n * ex n x := funext fun x => (hG x).tsum_eq.symm
    rw [e]
    refine continuous_tsum (fun n => continuous_const.mul (ex_cont n)) hbn ?_
    intro n x
    rw [norm_mul, ex_norm, mul_one]
  have hGb : ∀ t, ‖G t‖ ≤ ∑' n, ‖b n‖ := by
    intro t
    rw [← (hG t).tsum_eq]
    have e : (fun n => ‖b n * ex n t‖) = fun n => ‖b n‖ := by
      funext n
      rw [norm_mul, ex_norm, mul_one]
    refine (norm_tsum_le_tsum_norm ?_).trans (le_of_eq ?_)
    · rw [e]; exact hbn
    · rw [e]
  have hC : ∀ n, ∫ x in (0 : ℝ)..1, conj (G x) * ex n x = conj (b n) := by
    intro n
    have hs : HasSum (fun m => ∫ x in (0 : ℝ)..1, conj (b m) * (conj (ex m x) * ex n x))
        (∫ x in (0 : ℝ)..1, conj (G x) * ex n x) := by
      refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun m _ => ‖b m‖)
        ?_ ?_ ?_ ?_ ?_
      · intro m
        exact (continuous_const.mul
          ((Complex.continuous_conj.comp (ex_cont m)).mul (ex_cont n))).aestronglyMeasurable
      · intro m
        refine Filter.Eventually.of_forall (fun t _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, ex_norm, ex_norm]
        simp
      · exact Filter.Eventually.of_forall (fun t _ => hbn)
      · exact intervalIntegrable_const
      · refine Filter.Eventually.of_forall (fun t _ => ?_)
        have e : (fun m => conj (b m) * (conj (ex m t) * ex n t)) =
            fun m => conj (b m * ex m t) * ex n t := by
          funext m
          rw [map_mul, mul_assoc]
        rw [e]
        exact (Complex.hasSum_conj'.mpr (hG t)).mul_right (ex n t)
    simp_rw [intervalIntegral.integral_const_mul, ex_orth] at hs
    have h2 : HasSum (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) (conj (b n)) := by
      have e : (fun m => conj (b m) * if m = n then (1 : ℂ) else 0) =
          fun m => if m = n then conj (b n) else 0 := by
        funext m
        split_ifs with h
        · rw [h, mul_one]
        · rw [mul_zero]
      rw [e]
      exact hasSum_ite_eq n (conj (b n))
    exact hs.unique h2
  have hB : HasSum (fun n => ∫ x in (0 : ℝ)..1, a n * (conj (G x) * ex n x))
      (∫ x in (0 : ℝ)..1, conj (G x) * F x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => ‖a n‖ * ∑' m, ‖b m‖) ?_ ?_ ?_ ?_ ?_
    · intro n
      exact (continuous_const.mul
        ((Complex.continuous_conj.comp hGc).mul (ex_cont n))).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall (fun t _ => ?_)
      rw [norm_mul, norm_mul, ex_norm, mul_one, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hGb t) (norm_nonneg _)
    · exact Filter.Eventually.of_forall (fun t _ => han.mul_right _)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t _ => ?_)
      have e : (fun n => a n * (conj (G t) * ex n t)) = fun n => conj (G t) * (a n * ex n t) := by
        funext n
        ring
      rw [e]
      exact (hF t).mul_left (conj (G t))
  simp_rw [intervalIntegral.integral_const_mul, hC] at hB
  have e : (fun n => conj (b n) * a n) = fun n => a n * conj (b n) := by
    funext n
    ring
  rw [e]
  exact hB

private theorem line_exp (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)) (y : ℝ) (hy : 0 < y) (x : ℝ) :
    HasSum (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) (f (pt x y)) := by
  have hp : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 L)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma1]
    exact AddSubgroup.mem_zmultiples 1
  have hs := ModularForm.hasSum_qExpansion f one_pos hp (pt x y)
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  have hc : ((pt x y : ℍ) : ℂ) = x + y * Complex.I := by
    unfold pt
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have e : (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ) * ex n x) =
      fun m => (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 ↑(pt x y) ^ m := by
    funext n
    rw [hc, mul_assoc]
    unfold coef ex Function.Periodic.qParam
    congr 1
    rw [← Complex.exp_nat_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(2 * (Real.pi : ℂ) * n * y)) * Complex.I_sq
  rw [e]
  exact hs

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.pars :
    UpperTheory.V.Af.Rs.Pars := by
  intro k L _ f g y hy
  have hF := line_exp k L f y hy
  have hG := line_exp k L g y hy
  have ex0 : ∀ n, ex n 0 = 1 := by
    intro n
    simp [ex]
  have ha : Summable (fun n : ℕ => coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) :=
    (hF 0).summable.congr (fun n => by rw [ex0, mul_one])
  have hb : Summable (fun n : ℕ => coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) :=
    (hG 0).summable.congr (fun n => by rw [ex0, mul_one])
  have h := pars_abs _ _ ha hb (fun x => f (pt x y)) (fun x => g (pt x y)) hF hG
  have e : (fun n : ℕ => conj (coef g n) * coef f n * ((Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ)) =
      fun n => conj (coef g n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) *
        (coef f n * (Real.exp (-(2 * Real.pi * n) * y) : ℂ)) := by
    funext n
    rw [map_mul, Complex.conj_ofReal,
      show -(4 * Real.pi * n) * y = (-(2 * Real.pi * n) * y) + (-(2 * Real.pi * n) * y) by ring,
      Real.exp_add]
    push_cast
    ring
  rw [e]
  exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIntAlt
open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped MatrixGroups

private lemma UpperTheory.V.Af.Rs.stripInt_maj (A B s : ℝ) (hs : 1 < s) :
    IntegrableOn (fun y : ℝ => (if y ≤ 1 then A * y ^ s else B) / y ^ 2) (Ioi 0) := by
  have hsplit : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  rw [← hsplit]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun y : ℝ => y ^ (s - 2)) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1.mono_set
        (le_of_eq (uIoc_of_le zero_le_one).symm)
    have h1' : IntegrableOn (fun y : ℝ => A * y ^ (s - 2)) (Ioc 0 1) := h1.const_mul A
    refine h1'.congr_fun ?_ measurableSet_Ioc
    intro y hy
    have hy0 : 0 < y := hy.1
    simp only [if_pos hy.2]
    rw [Real.rpow_sub hy0, Real.rpow_two, mul_div_assoc]
  · have h2 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
    have h2' : IntegrableOn (fun y : ℝ => B * y ^ (-2 : ℝ)) (Ioi 1) := h2.const_mul B
    refine h2'.congr_fun ?_ measurableSet_Ioi
    intro y hy
    have hy1 : (1:ℝ) < y := hy
    have hy0 : 0 < y := by linarith
    simp only [if_neg (not_le.mpr hy1)]
    rw [Real.rpow_neg hy0.le, Real.rpow_two, div_eq_mul_inv]

theorem UpperTheory.V.Af.Rs.stripInt :
    UpperTheory.V.Af.Rs.StripIm → UpperTheory.V.Af.Rs.StripInt := by
  intro hIm F hF s hs
  obtain ⟨hcont, C, hC⟩ := hF
  have hbound : ∀ z : ℍ, ‖F z‖ ≤ 8 * C := by
    intro z
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    have h4 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
    have hpos := (g • z).im_pos
    have hw : 1 / 2 ≤ (g • z).im := by nlinarith
    have hC' := hC g⁻¹ (g • z) hw
    rw [inv_smul_smul] at hC'
    have h3 : (1 / 2 : ℝ) ^ 3 ≤ (g • z).im ^ 3 := pow_le_pow_left₀ (by norm_num) hw 3
    nlinarith [norm_nonneg (F z)]
  have hhigh : ∀ z : ℍ, 1 < z.im → ‖F z‖ * z.im ^ s ≤ C := by
    intro z hz
    have hC' := hC 1 z (by linarith)
    rw [one_smul] at hC'
    have hle : z.im ^ s ≤ z.im ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hz.le (by push_cast; linarith [hs.2])
    calc ‖F z‖ * z.im ^ s ≤ ‖F z‖ * z.im ^ 3 :=
          mul_le_mul_of_nonneg_left hle (norm_nonneg _)
      _ ≤ C := hC'
  have hmeas : Measurable (fun y : ℝ => if y ≤ 1 then 8 * C * y ^ s else C) :=
    Measurable.ite measurableSet_Iic ((measurable_id.pow_const s).const_mul _) measurable_const
  have hφ := hIm _ hmeas (UpperTheory.V.Af.Rs.stripInt_maj (8 * C) C s hs.1)
  refine Integrable.mono' hφ ?_ ?_
  · have hc : Continuous fun z : ℍ => F z * ((z.im ^ s : ℝ) : ℂ) :=
      hcont.mul (Complex.continuous_ofReal.comp
        (UpperHalfPlane.continuous_im.rpow_const fun _ => Or.inr (by linarith [hs.1])))
    exact hc.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun z => ?_
    have hy := z.im_pos
    rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hy.le s)]
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right (hbound z) (Real.rpow_nonneg hy.le s)
    · exact hhigh z (not_le.mp h)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Rankin
open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Af.Rs
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

private theorem pt_im (x y : ℝ) (hy : 0 < y) : (pt x y).im = y := by
  simp [pt, UpperHalfPlane.ofComplex_apply_of_im_pos, hy]

private theorem coef_zero (k L : ℕ) [NeZero L] (f : CuspForm (Gamma1 L) (k : ℤ)) : coef f 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (by simp)

private theorem integrableOn_rpow_mul_exp_neg_Ioi (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    IntegrableOn (fun y : ℝ => y ^ (A - 1) * Real.exp (-r * y)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := A - 1) (b := r)
    (by linarith) one_pos hr
  refine h.congr_fun (fun y _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

private theorem integral_rpow_mul_exp_neg_Ioi_eq_gamma_div (A r : ℝ) (hA : 0 < A) (hr : 0 < r) :
    ∫ y in Ioi (0:ℝ), y ^ (A - 1) * Real.exp (-r * y) = Real.Gamma A / r ^ A := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hA hr
  simp only [neg_mul] at h ⊢
  rw [h, Real.div_rpow zero_le_one hr.le, Real.one_rpow]
  ring

private theorem gamma_div_four_pi_mul_rpow_eq (A : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.Gamma A / (4 * Real.pi * n) ^ A = Real.Gamma A / (4 * Real.pi) ^ A / (n : ℝ) ^ A := by
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (0:ℝ) < (4 * Real.pi) ^ A := by positivity
  have h2 : (0:ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by exact_mod_cast hn) A
  field_simp

theorem UpperTheory.V.Af.Rs.rankin :
    UpperTheory.V.Af.Rs.StripFub → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.Pars → UpperTheory.V.Af.Rs.RankSum → UpperTheory.V.Af.Rs.Rankin := by
  intro hFub hInt hNice hPars hSum k L _ f g s hs
  have hs1 : 1 < s := hs.1
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  set A : ℝ := (k:ℝ) + s - 1 with hAdef
  have hA : 0 < A := by rw [hAdef]; linarith
  set a : ℕ → ℂ := fun n => starRingEnd ℂ (coef g n) * coef f n with ha
  have ha0 : a 0 = 0 := by simp [ha, coef_zero k L f]
  set G : ℕ → ℝ → ℂ := fun n y =>
    a n * ((y ^ (A - 1) * Real.exp (-(4 * Real.pi * n) * y) : ℝ) : ℂ) with hG
  have hpt : ∀ y : ℝ, 0 < y →
      (∫ x in (0:ℝ)..1, UpperHalfPlane.petersson (k : ℤ) g f (pt x y) * (((pt x y).im ^ s : ℝ) : ℂ))
        / ((y ^ 2 : ℝ) : ℂ) = ∑' n, G n y := by
    intro y hy
    have h1 : ∀ x : ℝ, UpperHalfPlane.petersson (k : ℤ) g f (pt x y) * (((pt x y).im ^ s : ℝ) : ℂ)
        = (starRingEnd ℂ (g (pt x y)) * f (pt x y)) * ((y : ℂ) ^ k * ((y ^ s : ℝ) : ℂ)) := by
      intro x
      simp only [UpperHalfPlane.petersson, pt_im x y hy, zpow_natCast]
      ring
    have hyA : ((y ^ (A - 1) : ℝ) : ℂ) = (y : ℂ) ^ k * ((y ^ s : ℝ) : ℂ) / ((y ^ 2 : ℝ) : ℂ) := by
      have hr : y ^ (A - 1) = y ^ k * y ^ s / y ^ 2 := by
        rw [show A - 1 = ((k:ℝ) + s) - 2 by rw [hAdef]; ring, Real.rpow_sub hy, Real.rpow_add hy,
          Real.rpow_natCast, Real.rpow_two]
      rw [hr]
      push_cast
      ring
    simp_rw [h1]
    rw [intervalIntegral.integral_mul_const, ← (hPars k L f g y hy).tsum_eq, ← tsum_mul_right,
      ← tsum_div_const]
    congr 1
    ext n
    simp only [hG, ha]
    rw [Complex.ofReal_mul, hyA]
    ring
  have hr : ∀ n : ℕ, 0 < n → (0:ℝ) < 4 * Real.pi * n := fun n hn => by
    have : (0:ℝ) < n := by exact_mod_cast hn
    positivity
  have hGi : ∀ n, Integrable (G n) (volume.restrict (Ioi (0:ℝ))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : G 0 = fun _ => 0 := by funext y; simp [hG, ha0]
      rw [this]
      exact integrable_zero _ _ _
    · exact ((integrableOn_rpow_mul_exp_neg_Ioi A _ hA (hr n hn)).ofReal).const_mul (a n)
  have hsum : Summable (fun n : ℕ => ‖a n‖ / (n:ℝ) ^ A) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (((hSum k L f s hs).add (hSum k L g s hs)).div_const 2)
    have key : ‖coef g n‖ * ‖coef f n‖ ≤ (‖coef f n‖ ^ 2 + ‖coef g n‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖coef f n‖ - ‖coef g n‖)]
    have hn : (0:ℝ) ≤ (n:ℝ) ^ A := by positivity
    calc ‖a n‖ / (n:ℝ) ^ A = (‖coef g n‖ * ‖coef f n‖) / (n:ℝ) ^ A := by
          simp [ha, norm_mul]
      _ ≤ ((‖coef f n‖ ^ 2 + ‖coef g n‖ ^ 2) / 2) / (n:ℝ) ^ A := by gcongr
      _ = _ := by ring
  have hGs : Summable (fun n => ∫ y in Ioi (0:ℝ), ‖G n y‖) := by
    refine (hsum.mul_left (Real.Gamma A / (4 * Real.pi) ^ A)).congr (fun n => ?_)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hG, ha0]
    · have hc : ∫ y in Ioi (0:ℝ), ‖G n y‖
          = ∫ y in Ioi (0:ℝ), ‖a n‖ * (y ^ (A - 1) * Real.exp (-(4 * Real.pi * n) * y)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
        have hy' : (0:ℝ) < y := hy
        simp only [hG, norm_mul, Complex.norm_real]
        rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [hc, integral_const_mul, integral_rpow_mul_exp_neg_Ioi_eq_gamma_div A _ hA (hr n hn), gamma_div_four_pi_mul_rpow_eq A n hn]
      ring
  have hI := hInt _ (hNice k L f g) s hs
  obtain ⟨-, heq⟩ := hFub _ hI
  show (∫ z in strip, _) = _
  rw [heq, setIntegral_congr_fun measurableSet_Ioi (fun y hy => hpt y hy),
    ← integral_tsum_of_summable_integral_norm hGi hGs, ← tsum_mul_left]
  congr 1
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hG, ha0, coef_zero k L f]
  · simp only [hG]
    rw [integral_const_mul, integral_complex_ofReal, integral_rpow_mul_exp_neg_Ioi_eq_gamma_div A _ hA (hr n hn), gamma_div_four_pi_mul_rpow_eq A n hn, gam]
    have h2 : (0:ℝ) < (n : ℝ) ^ A := Real.rpow_pos_of_pos (by exact_mod_cast hn) A
    push_cast
    field_simp
    simp only [ha]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TEq
open MeasureTheory Set UpperTheory.V.Af.Rs
open UpperHalfPlane hiding I
open scoped MatrixGroups

theorem UpperTheory.V.Af.Rs.tEq :
    UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.Unfold → UpperTheory.V.Af.Rs.GcdSum → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.Swap → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.TEq := by
  intro hRB hSI hUnf hGcd hKer hSw hLB L _ ψ F G hG hF hGn s hs
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hkc, hk0, hkz, hkrow, hkn, -⟩ := hKer s hs'
  obtain ⟨hint, hsum⟩ := hSw L G hGn s hs
  have hrow : ∀ x : Cop, ∃ γ : SL(2, ℤ), row γ = (x : Fin 2 → ℤ) := fun x =>
    ((hRB.2 UpperHalfPlane.I x).exists).imp fun γ h => h.1
  have hone : ∀ (γ : SL(2, ℤ)) (z : ℍ), G (cls L (row γ)) z = F (γ • z) := by
    intro γ z
    have := hG 1 γ z
    simpa using this
  have hGn' : ∀ (n : ℕ) (γ : SL(2, ℤ)) (z : ℍ),
      G (cls L ((n : ℤ) • row γ)) z = ψ n * G (cls L (row γ)) z := by
    intro n γ z
    rw [hG, hone]
  set a : (Fin 2 → ℤ) → ℂ := fun x => ∫ z in ModularGroup.fd, G (cls L x) z * (ker s x z : ℂ) with ha
  set c : ℕ → ℂ := fun n => ψ n / ((n : ℝ) ^ (2 * s) : ℝ) with hc
  have hs2 : (2 * s) ≠ 0 := by have := hs.1; linarith
  have hgcd := hGcd a c hsum.summable (hLB L ψ s hs.1.le).1
    (by simp [ha, hkz])
    (by simp [hc, Real.zero_rpow hs2])
    (by
      intro n x
      obtain ⟨γ, hγ⟩ := hrow x
      simp only [ha, hc]
      rw [← hγ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hkn]
      rw [hGn', Complex.ofReal_div]
      ring)
  have hunf := hUnf (fun z => F z * ((z.im ^ s : ℝ) : ℂ)) (fun x z => G (cls L x) z * (ker s x z : ℂ))
    (by
      have hc1 : Continuous (fun z : ℍ => z.im ^ s) :=
        UpperHalfPlane.continuous_im.rpow_const (fun _ => Or.inr (by linarith [hs.1]))
      exact hF.1.mul (Complex.continuous_ofReal.comp hc1))
    (hSI F hF s hs)
    (by intro γ z; rw [hkrow, hone])
    (fun x => hint x)
  rw [← hsum.tsum_eq, hgcd]
  congr 1
  exact hunf.tsum_eq
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripFub
open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private lemma strip_meas : MeasurableSet strip := by
  have hre : Continuous fun z : ℍ => z.re := Complex.continuous_re.comp UpperHalfPlane.continuous_coe
  exact (measurableSet_le measurable_const hre.measurable).inter
    (measurableSet_lt hre.measurable measurable_const)

private lemma pt_re (x y : ℝ) (hy : 0 < y) : (pt x y).re = x := by
  rw [pt, ← UpperHalfPlane.coe_re, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

private lemma vol_strip (hV : VolMap) :
    (volume : Measure ℍ).restrict strip = Measure.map (fun p : ℝ × ℝ => pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  obtain ⟨hm, hv⟩ := hV
  have hS := hm strip_meas
  have h1 : ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have h2 : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' strip ∩ univ ×ˢ Ioi 0 = Ico 0 1 ×ˢ Ioi 0 := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico, strip,
      mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [pt_re x y hy] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [pt_re x y hy]
      exact ⟨h, hy⟩
  rw [hv, Measure.restrict_map hm strip_meas, restrict_withDensity hS, h1,
    Measure.restrict_restrict hS, h2, Measure.prod_restrict]

end UpperTheory.V.Af.Rs

open UpperTheory.V.Af.Rs in
theorem UpperTheory.V.Af.Rs.stripFub :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripFub := by
  intro hV H hH
  have hf : Measurable fun p : ℝ × ℝ => pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hμ := vol_strip hV
  have hI : Integrable H ((volume : Measure ℍ).restrict strip) := hH
  rw [hμ] at hI
  have hHm := hI.1
  rw [integrable_map_measure hHm hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt] at hI
  have hpt : ∀ p : ℝ × ℝ, (ENNReal.ofReal (1 / p.2 ^ 2)).toReal • (H ∘ fun p : ℝ × ℝ => pt p.1 p.2) p
      = ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2) := by
    intro p
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    rfl
  have hF : Integrable (fun p : ℝ × ℝ => ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2))
      (((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))) :=
    hI.congr (Filter.Eventually.of_forall hpt)
  have hinner : ∀ y : ℝ, ∫ x, ((1 / y ^ 2 : ℝ) : ℂ) * H (pt x y) ∂(volume.restrict (Ico (0:ℝ) 1))
      = (∫ x in (0:ℝ)..1, H (pt x y)) / ((y ^ 2 : ℝ) : ℂ) := by
    intro y
    rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one,
      integral_Ico_eq_integral_Ioc, one_div, Complex.ofReal_inv, div_eq_inv_mul]
  refine ⟨?_, ?_⟩
  · have := hF.integral_prod_right
    simp only [hinner] at this
    exact this
  · calc ∫ z in strip, H z
        = ∫ p, H (pt p.1 p.2) ∂((((volume : Measure ℝ).restrict (Ico 0 1)).prod
            (volume.restrict (Ioi 0))).withDensity fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
          rw [hμ, integral_map hf.aemeasurable hHm]
      _ = ∫ p, ((1 / p.2 ^ 2 : ℝ) : ℂ) * H (pt p.1 p.2) ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod
            (volume.restrict (Ioi 0))) := by
          rw [integral_withDensity_eq_integral_toReal_smul hg hlt]
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = ∫ y in Ioi 0, ∫ x, ((1 / y ^ 2 : ℝ) : ℂ) * H (pt x y) ∂(volume.restrict (Ico (0:ℝ) 1)) :=
          integral_prod_symm _ hF
      _ = _ := by simp only [hinner]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.PetChar
open CongruenceSubgroup UpperTheory.V.Af
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

theorem UpperTheory.V.Af.Rs.petChar :
    UpperTheory.V.Af.Rs.PetChar := by
  intro k L _ χ ψ f g hf hg γ hγ z
  have h := UpperHalfPlane.petersson_slash_SL (k : ℤ) g f γ z
  rw [hg γ hγ, hf γ hγ] at h
  rw [← h]
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply,
    MulChar.star_apply', MulChar.mul_apply]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.NicePet
open Filter Asymptotics CongruenceSubgroup Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Pointwise

private theorem bounded_petersson_weight (H : ℍ → ℂ) (B a : ℝ) (ha : 0 < a) (hB : ∀ z, ‖H z‖ ≤ B)
    (hd : H =O[atImInfty] fun τ => Real.exp (-a * τ.im)) : ∃ C : ℝ, ∀ z : ℍ, ‖H z‖ * z.im ^ 3 ≤ C := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hd
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp hc
  set M := max A 0 with hM
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB UpperHalfPlane.I)
  have hM0 : 0 ≤ M := le_max_right _ _
  refine ⟨B * M ^ 3 + |c| * (6 / a ^ 3), fun z => ?_⟩
  have ht := z.im_pos
  have h1 : 0 ≤ B * M ^ 3 := by positivity
  have h2 : 0 ≤ |c| * (6 / a ^ 3) := by positivity
  rcases le_total z.im M with h | h
  · have : ‖H z‖ * z.im ^ 3 ≤ B * M ^ 3 :=
      mul_le_mul (hB z) (pow_le_pow_left₀ ht.le h 3) (by positivity) hB0
    linarith
  · have hz := hA z ((le_max_left _ _).trans h)
    simp only [Set.mem_setOf_eq] at hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hz
    have hexp : (a * z.im) ^ 3 / 6 ≤ Real.exp (a * z.im) := by
      have := Real.pow_div_factorial_le_exp (a * z.im) (by positivity) 3
      simpa [Nat.factorial] using this
    have he := Real.exp_pos (a * z.im)
    have hkey : Real.exp (-a * z.im) * z.im ^ 3 ≤ 6 / a ^ 3 := by
      rw [le_div_iff₀ (by positivity), neg_mul, Real.exp_neg, inv_mul_eq_div, div_mul_eq_mul_div,
        div_le_iff₀ he]
      rw [mul_pow] at hexp
      nlinarith
    have : ‖H z‖ * z.im ^ 3 ≤ |c| * (6 / a ^ 3) :=
      calc ‖H z‖ * z.im ^ 3 ≤ c * Real.exp (-a * z.im) * z.im ^ 3 :=
            mul_le_mul_of_nonneg_right hz (by positivity)
        _ ≤ |c| * (Real.exp (-a * z.im) * z.im ^ 3) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity)
        _ ≤ |c| * (6 / a ^ 3) := mul_le_mul_of_nonneg_left hkey (abs_nonneg c)
    linarith

theorem UpperTheory.V.Af.Rs.nicePet :
    UpperTheory.V.Af.Rs.NicePet := by
  intro k L _ f g
  refine ⟨by fun_prop, ?_⟩
  obtain ⟨B, hB⟩ := CuspFormClass.petersson_bounded_left (k : ℤ) (Subgroup.map (mapGL ℝ) (Gamma1 L)) g f
  have hdec : ∀ h : SL(2, ℤ), ∃ a > 0,
      (fun τ => UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • τ)) =O[atImInfty]
        fun τ => Real.exp (-a * τ.im) := by
    intro h
    have : ((ConjAct.toConjAct (h : GL (Fin 2) ℝ)⁻¹) •
        (Subgroup.map (mapGL ℝ) (Gamma1 L))).IsArithmetic := by
      simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
        using! Subgroup.IsArithmetic.conj (Subgroup.map (mapGL ℝ) (Gamma1 L)) (mapGL ℚ h)⁻¹
    simp_rw [← UpperHalfPlane.petersson_slash_SL]
    exact (CuspFormClass.zero_at_infty (CuspForm.translate g h)).petersson_exp_decay_left
      (k : ℤ) _ (ModularForm.translate f h)
  have key : ∀ h : SL(2, ℤ), ∃ C : ℝ, ∀ z : ℍ,
      ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • z)‖ * z.im ^ 3 ≤ C := by
    intro h
    obtain ⟨a, ha, hd⟩ := hdec h
    exact bounded_petersson_weight (fun τ => UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (h • τ)) B a ha
      (fun z => hB _) hd
  choose Cf hCf using key
  let Γ' : Subgroup SL(2, ℤ) :=
    (Subgroup.map (mapGL ℝ) (Gamma1 L)).comap (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
  have : Fintype (SL(2, ℤ) ⧸ Γ') := Subgroup.fintypeQuotientOfFiniteIndex
  have hinv : ∀ j ∈ Γ', ∀ w : ℍ,
      ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f (j • w)‖ = ‖UpperHalfPlane.petersson (k : ℤ) ⇑g ⇑f w‖ :=
    fun j hj w => SlashInvariantFormClass.norm_petersson_smul (g := mapGL ℝ j) hj
  refine ⟨∑ q : SL(2, ℤ) ⧸ Γ', |Cf (Quotient.out q)⁻¹|, fun γ z _ => ?_⟩
  obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul Γ' γ⁻¹
  have hγ : γ = (j : SL(2, ℤ)) * (Quotient.out (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ Γ'))⁻¹ := by
    rw [hj]; group
  rw [hγ, mul_smul, hinv _ j.2]
  refine (hCf _ z).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun q : SL(2, ℤ) ⧸ Γ' => |Cf (Quotient.out q)⁻¹|)
    (fun q _ => abs_nonneg _) (Finset.mem_univ _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ClsExKey
open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups

private theorem clsEx_key (L : ℕ) (ψ : DirichletCharacter ℂ L) (F : ℍ → ℂ)
    (hF : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 L → ∀ z, F (γ • z) = ψ ((γ 1 1 : ℤ) : ZMod L) * F z)
    (n m : ℕ) (γ δ : SL(2, ℤ))
    (h : UpperTheory.V.Af.Rs.cls L ((m : ℤ) • UpperTheory.V.Af.Rs.row δ) = UpperTheory.V.Af.Rs.cls L ((n : ℤ) • UpperTheory.V.Af.Rs.row γ))
    (z : ℍ) : ψ (m : ZMod L) * F (δ • z) = ψ (n : ZMod L) * F (γ • z) := by
  classical
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [UpperTheory.V.Af.Rs.cls, UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul, Int.cast_mul,
    Int.cast_natCast] at h0 h1
  have hdet : ((γ 0 0 : ℤ) : ZMod L) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact_mod_cast congrArg (fun t : ℤ => (t : ZMod L)) this
  have hn : (n : ZMod L) = m * (((γ 0 0 : ℤ) : ZMod L) * (δ 1 1 : ℤ) - (γ 0 1 : ℤ) * (δ 1 0 : ℤ)) := by
    linear_combination (-(n : ZMod L)) * hdet - ((γ 0 0 : ℤ) : ZMod L) * h1 +
      ((γ 0 1 : ℤ) : ZMod L) * h0
  by_cases hm : IsUnit (m : ZMod L)
  · obtain ⟨η, hη⟩ : ∃ η : SL(2, ℤ), η = δ * γ⁻¹ := ⟨_, rfl⟩
    have e10 : (η 1 0 : ℤ) = δ 1 0 * γ 1 1 - δ 1 1 * γ 1 0 := by
      rw [hη]
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have e11 : (η 1 1 : ℤ) = δ 1 1 * γ 0 0 - δ 1 0 * γ 0 1 := by
      rw [hη]
      simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
        Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    have hmem : η ∈ Gamma0 L := by
      rw [Gamma0_mem, e10]
      push_cast
      refine (hm.mul_right_eq_zero).1 ?_
      linear_combination ((γ 1 1 : ℤ) : ZMod L) * h0 - ((γ 1 0 : ℤ) : ZMod L) * h1
    have hδ : δ = η * γ := by
      rw [hη, inv_mul_cancel_right]
    have hn' : (n : ZMod L) = m * ((η 1 1 : ℤ) : ZMod L) := by
      rw [e11, hn]
      push_cast
      ring
    rw [hδ, mul_smul, hF η hmem, hn', map_mul]
    ring
  · have hn' : ¬IsUnit (n : ZMod L) := by
      intro hu
      rw [hn] at hu
      exact hm (isUnit_of_mul_isUnit_left hu)
    rw [MulChar.map_nonunit _ hm, MulChar.map_nonunit _ hn']
    simp

theorem UpperTheory.V.Af.Rs.clsEx :
    UpperTheory.V.Af.Rs.RowBij → UpperTheory.V.Af.Rs.ClsEx := by
  intro _ L _ ψ F hF
  classical
  refine ⟨fun v z => if h : ∃ p : ℕ × SL(2, ℤ), cls L ((p.1 : ℤ) • row p.2) = v then
    ψ (h.choose.1 : ZMod L) * F (h.choose.2 • z) else 0, ?_⟩
  intro n γ z
  have h : ∃ p : ℕ × SL(2, ℤ), cls L ((p.1 : ℤ) • row p.2) = cls L ((n : ℤ) • row γ) := ⟨(n, γ), rfl⟩
  simp only [dif_pos h]
  exact clsEx_key L ψ F hF n _ γ _ h.choose_spec z
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RankSum
open MeasureTheory Set CongruenceSubgroup UpperTheory.V.Af UpperTheory.V.Sd
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm ComplexConjugate

private lemma UpperTheory.V.Af.Rs.upper_half_plane_point_im (x y : ℝ) (hy : 0 < y) : (UpperTheory.V.Af.Rs.pt x y).im = y := by
  unfold UpperTheory.V.Af.Rs.pt
  have him : 0 < ((x : ℂ) + y * Complex.I).im := by simp [hy]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  simp

theorem UpperTheory.V.Af.Rs.rankSum :
    UpperTheory.V.Af.Rs.StripFub → UpperTheory.V.Af.Rs.StripInt → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.Pars → UpperTheory.V.Af.Rs.MelSum → UpperTheory.V.Af.Rs.RankSum := by
  intro hFub hInt hNice hPars hMel k L _ f s hs
  have hs1 : 1 < s := hs.1
  have hI := hInt _ (hNice k L f f) s hs
  obtain ⟨hY, -⟩ := hFub _ hI
  have hPa := hPars k L f f
  have hPsum : ∀ y, 0 < y → HasSum (fun n => ‖coef f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y))
      ((∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)).re) := by
    intro y hy
    have h := Complex.reCLM.hasSum (hPa y hy)
    have e : (fun n => ‖coef f n‖ ^ 2 * Real.exp (-(4 * Real.pi * n) * y)) =
        fun n => Complex.reCLM (conj (coef f n) * coef f n * (Real.exp (-(4 * Real.pi * n) * y) : ℂ)) := by
      funext n
      rw [Complex.reCLM_apply, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [e]
    simpa only [Complex.reCLM_apply] using h
  have hY2 : IntegrableOn (fun y : ℝ => ((∫ x in (0 : ℝ)..1,
      UpperHalfPlane.petersson (k : ℤ) f f (UpperTheory.V.Af.Rs.pt x y) *
        (((UpperTheory.V.Af.Rs.pt x y).im ^ s : ℝ) : ℂ)) / ((y ^ 2 : ℝ) : ℂ)).re) (Ioi 0) := hY.re
  have hIntP : IntegrableOn (fun y : ℝ =>
      (∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)).re *
        y ^ ((k : ℝ) + s - 1 - 1)) (Ioi 0) := by
    refine hY2.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy' : 0 < y := hy
    have him : ∀ x, (UpperTheory.V.Af.Rs.pt x y).im = y := fun x => UpperTheory.V.Af.Rs.upper_half_plane_point_im x y hy'
    have hx : (∫ x in (0 : ℝ)..1, UpperHalfPlane.petersson (k : ℤ) f f (UpperTheory.V.Af.Rs.pt x y) *
        (((UpperTheory.V.Af.Rs.pt x y).im ^ s : ℝ) : ℂ)) =
        (∫ x in (0 : ℝ)..1, conj (f (UpperTheory.V.Af.Rs.pt x y)) * f (UpperTheory.V.Af.Rs.pt x y)) *
          ((y ^ k * y ^ s : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_mul_const]
      congr 1
      funext x
      simp [UpperHalfPlane.petersson, him, mul_assoc]
    dsimp only
    rw [hx, mul_div_assoc, ← Complex.ofReal_div, Complex.re_mul_ofReal]
    congr 1
    rw [show (k : ℝ) + s - 1 - 1 = ((k : ℝ) + s) - 2 by ring, Real.rpow_sub hy', Real.rpow_add hy',
      Real.rpow_natCast, Real.rpow_two]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact hMel (fun n => ‖coef f n‖ ^ 2) _ ((k : ℝ) + s - 1) (by linarith)
    (fun n => by positivity) hPsum hIntP
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.PNewform
open NumberField GlobalTheory.CuspRep UpperTheory.V

theorem UpperTheory.V.Af.newformRep :
    UpperTheory.V.Published.NewformRep :=
  UpperTheory.V.Af.newformRepOf UpperTheory.V.Af.cuspSemisimpleReal UpperTheory.V.Af.admissibleReal
end

theorem UpperTheory.V.Af.repNewform :
    UpperTheory.V.Published.RepNewform := by
  have hVolMap : UpperTheory.V.Af.Rs.VolMap := UpperTheory.V.Af.Rs.volMap
  have hStripFub : UpperTheory.V.Af.Rs.StripFub := UpperTheory.V.Af.Rs.stripFub hVolMap
  have hStripIm : UpperTheory.V.Af.Rs.StripIm := UpperTheory.V.Af.Rs.stripIm hVolMap
  have hFdFin : UpperTheory.V.Af.Rs.FdFin := UpperTheory.V.Af.Rs.fdFin hStripIm hVolMap
  have hFdNull : UpperTheory.V.Af.Rs.FdNull := UpperTheory.V.Af.Rs.fdNull hVolMap
  have hFdPos : UpperTheory.V.Af.Rs.FdPos := UpperTheory.V.Af.Rs.fdPos hVolMap
  have hStripInt : UpperTheory.V.Af.Rs.StripInt := UpperTheory.V.Af.Rs.stripInt hStripIm
  have hFdCount : UpperTheory.V.Af.Rs.FdCount := UpperTheory.V.Af.Rs.fdCount hFdNull
  have hUnfM : UpperTheory.V.Af.Rs.UnfM := UpperTheory.V.Af.Rs.unfM hFdFin hFdCount
  have hRowBij : UpperTheory.V.Af.Rs.RowBij := UpperTheory.V.Af.Rs.rowBij
  have hRowRep : UpperTheory.V.Af.Rs.RowRep := UpperTheory.V.Af.Rs.rowRep
  have hUnfold : UpperTheory.V.Af.Rs.Unfold := UpperTheory.V.Af.Rs.unfold hFdFin hUnfM hRowBij
  have hGcdSum : UpperTheory.V.Af.Rs.GcdSum := UpperTheory.V.Af.Rs.gcdSum
  have hKerBd : UpperTheory.V.Af.Rs.KerBd := UpperTheory.V.Af.Rs.kerBd
  have hKerLow : UpperTheory.V.Af.Rs.KerLow := UpperTheory.V.Af.Rs.kerLow
  have hKerDiff : UpperTheory.V.Af.Rs.KerDiff := UpperTheory.V.Af.Rs.kerDiff
  have hWTop : UpperTheory.V.Af.Rs.WTop := UpperTheory.V.Af.Rs.wTop
  have hZDiff : UpperTheory.V.Af.Rs.ZDiff := UpperTheory.V.Af.Rs.zDiff hKerBd hKerDiff hWTop
  have hZLow : UpperTheory.V.Af.Rs.ZLow := UpperTheory.V.Af.Rs.zLow hKerBd hKerLow hWTop
  have hZInt : UpperTheory.V.Af.Rs.ZInt := UpperTheory.V.Af.Rs.zInt hFdFin hKerBd hWTop
  have hSwap : UpperTheory.V.Af.Rs.Swap := UpperTheory.V.Af.Rs.swap hFdFin hKerBd hWTop
  have hTBdd : UpperTheory.V.Af.Rs.TBdd := UpperTheory.V.Af.Rs.tBdd hFdFin hZDiff hZInt
  have hTTop : UpperTheory.V.Af.Rs.TTop := UpperTheory.V.Af.Rs.tTop hFdFin hFdPos hWTop hZDiff hZLow hZInt
  have hClsEx : UpperTheory.V.Af.Rs.ClsEx := UpperTheory.V.Af.Rs.clsEx hRowBij
  have hClsProp : UpperTheory.V.Af.Rs.ClsProp := UpperTheory.V.Af.Rs.clsProp hRowRep
  have hLBd : UpperTheory.V.Af.Rs.LBd := UpperTheory.V.Af.Rs.lBd
  have hNicePet : UpperTheory.V.Af.Rs.NicePet := UpperTheory.V.Af.Rs.nicePet
  have hPetChar : UpperTheory.V.Af.Rs.PetChar := UpperTheory.V.Af.Rs.petChar
  have hPars : UpperTheory.V.Af.Rs.Pars := UpperTheory.V.Af.Rs.pars
  have hMelSum : UpperTheory.V.Af.Rs.MelSum := UpperTheory.V.Af.Rs.melSum
  have hRankSum : UpperTheory.V.Af.Rs.RankSum := UpperTheory.V.Af.Rs.rankSum hStripFub hStripInt hNicePet hPars hMelSum
  have hRankin : UpperTheory.V.Af.Rs.Rankin := UpperTheory.V.Af.Rs.rankin hStripFub hStripInt hNicePet hPars hRankSum
  have hArFact : UpperTheory.V.Af.Rs.ArFact := UpperTheory.V.Af.Rs.arFact
  have hArSum : UpperTheory.V.Af.Rs.ArSum := UpperTheory.V.Af.Rs.arSum
  have hCmp : UpperTheory.V.Af.Rs.Cmp := UpperTheory.V.Af.Rs.cmp hRankSum hRankin hArFact hArSum
  have hDeplete : UpperTheory.V.Af.Rs.Deplete := UpperTheory.V.Af.Rs.deplete
  have hSl2Two : UpperTheory.V.Af.Rn.Sl2Two := UpperTheory.V.Af.Rn.sl2Two
  have hLowTwo : UpperTheory.V.Af.Rn.LowTwo := UpperTheory.V.Af.Rn.lowTwo hSl2Two
  have hHolTwo : UpperTheory.V.Af.Rn.HolTwo := UpperTheory.V.Af.Rn.holTwo hLowTwo
  have hNoLow : UpperTheory.V.Af.Rn.NoLow := UpperTheory.V.Af.Rn.noLow UpperTheory.V.Af.Rn.centChar
  have hSatHerm : UpperTheory.V.Af.Rn.SatHerm := UpperTheory.V.Af.Rn.satHerm
  have hHermOf : UpperTheory.V.Af.Rn.HermOf := UpperTheory.V.Af.Rn.hermOf
  have hEigOfLow : UpperTheory.V.Af.Rn.EigOfLow := UpperTheory.V.Af.Rn.eigOfLow UpperTheory.V.Af.Rn.centChar
  have hUnitTw : UpperTheory.V.Af.Rn.UnitTw := UpperTheory.V.Af.Rn.unitTw
  have hEvPl : UpperTheory.V.Af.Rn.EvPl := UpperTheory.V.Af.Rn.evPl
  have hNewHerm : UpperTheory.V.Af.Rn.NewHerm := UpperTheory.V.Af.Rn.newHerm UpperTheory.V.Af.newformRep hUnitTw hHermOf hSatHerm
  have hPolyInj : UpperTheory.V.Af.Rn.PolyInj := UpperTheory.V.Af.Rn.polyInj
  have hTEq : UpperTheory.V.Af.Rs.TEq := UpperTheory.V.Af.Rs.tEq hRowBij hStripInt hUnfold hGcdSum hKerBd hSwap hLBd
  have hCore : UpperTheory.V.Af.Rs.Core := UpperTheory.V.Af.Rs.core hTBdd hTTop hClsEx hClsProp hTEq hLBd hNicePet hPetChar hCmp
  have hCharEq2 : UpperTheory.V.Af.Rs.CharEq2 := UpperTheory.V.Af.Rs.charEq2 hCore hDeplete
  exact UpperTheory.V.Af.Rn.repNewform_of
    (UpperTheory.V.Af.Rn.newAE_of hUnitTw hHermOf (UpperTheory.V.Af.Rn.holAll_of UpperTheory.V.Br.holVec hHolTwo hNoLow) hEigOfLow hSatHerm hEvPl hNewHerm
      UpperTheory.V.Br.minNew hCharEq2)
    hEvPl hPolyInj (fun w => (UpperTheory.V.Af.Nf.places w).1.pos) UpperTheory.V.Af.newformRep UpperTheory.V.Af.strongMultOneReal
