module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOneStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOne
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem stripLow_integrableOn_im_rpow : ∀ (s : ℝ), 0 < s →
    IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro s hs
  have hmeasIm : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hf : Measurable (fun τ : ℍ => τ.im ^ (s + 1)) := hmeasIm.pow_const _
  have hT : MeasurableSet {τ : ℍ | τ.im < 1} := measurableSet_lt hmeasIm measurable_const
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  set F : ℍ → ENNReal := Set.indicator {τ : ℍ | τ.im < 1} (fun τ => ‖τ.im ^ (s + 1)‖ₑ) with hFdef
  have hFm : Measurable F := hf.enorm.indicator hT
  have h1 : ∫⁻ τ in {τ | τ ∈ strip ∧ τ.im < 1}, ‖τ.im ^ (s + 1)‖ₑ = ∫⁻ τ in strip, F τ := by
    rw [hFdef, lintegral_indicator hT, Measure.restrict_restrict hT]
    congr 2
    ext τ
    simp [and_comm]
  rw [h1, (GlobalTheory.T.unitStrip_integral_eq_iterated).1 F hFm]
  have h2 : ∀ y ∈ Set.Ioi (0:ℝ), (∫⁻ x in Set.Ico (0 : ℝ) 1, F (ofComplex (x + y * Complex.I))) *
      ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s - 1))) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x:ℂ) + y * Complex.I)).im = y := by
      intro x
      rw [ofComplex_apply_of_im_pos (by simpa using hy0)]
      simp [UpperHalfPlane.im]
    have hin : ∀ x : ℝ, F (ofComplex ((x:ℂ) + y * Complex.I)) =
        Set.indicator (Set.Iio 1) (fun y : ℝ => ENNReal.ofReal (y ^ (s + 1))) y := by
      intro x
      simp only [hFdef, Set.indicator, Set.mem_setOf_eq, him, Set.mem_Iio]
      split_ifs
      · exact Real.enorm_eq_ofReal (Real.rpow_nonneg hy0.le _)
      · rfl
    simp_rw [hin]
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico]
    simp only [sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h : y < 1
    · simp only [Set.indicator, Set.mem_Iio, h, if_true]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy0.le _)]
      congr 1
      have : y ^ (s + 1) = y ^ (s - 1) * y ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hy0]; norm_num; ring_nf
      rw [this]; field_simp
    · simp [Set.indicator, h]
  rw [setLIntegral_congr_fun measurableSet_Ioi h2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
  have hI : IntegrableOn (fun y : ℝ => y ^ (s - 1)) (Set.Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  exact hI.lintegral_lt_top

end GlobalTheory.EisM
end

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one : ∀ (s : ℝ), 0 < s → IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.stripLow_integrableOn_im_rpow | exact GlobalTheory.EisM.stripLow_integrableOn_im_rpow | (intros; apply GlobalTheory.EisM.stripLow_integrableOn_im_rpow <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLe
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem im_ofComplex_xy (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  change ((x : ℂ) + (y : ℂ) * Complex.I).im = y
  simp

theorem integrableOn_rpow_sub_two_mul_exp_Ioi_one (r c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ (r - 2) * Real.exp (-c * y)) (Set.Ioi 1) := by
  have hI : IntegrableOn (fun y : ℝ => y ^ (max (r - 2) 0) * Real.exp (-c * y ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have := le_max_right (r - 2) 0; linarith)
      one_pos hc
  have hI' := hI.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  refine Integrable.mono' hI' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _)
      (Real.exp_pos _).le), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)) (Real.exp_pos _).le

theorem integrableOn_im_rpow_mul_exp_strip_one_le :
    ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im))
      {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  intro r c hc
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmeas : Measurable (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) :=
    (hmim.pow_const r).mul (Real.measurable_exp.comp (measurable_const.mul hmim))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hmT : MeasurableSet {τ : ℍ | 1 ≤ τ.im} := measurableSet_le measurable_const hmim
  have hS : {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} = {τ : ℍ | 1 ≤ τ.im} ∩ strip := by
    ext τ; simp [and_comm]
  show ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im}, ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ < ⊤
  rw [hS, ← Measure.restrict_restrict hmT, ← lintegral_indicator hmT,
    (GlobalTheory.T.unitStrip_integral_eq_iterated).1 _ ((hmeas.enorm).indicator hmT)]
  have hinner : Set.EqOn
      (fun y : ℝ => (∫⁻ x in Set.Ico (0 : ℝ) 1, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I))) *
          ENNReal.ofReal (1 / y ^ 2))
      (fun y : ℝ => (Set.Ici (1 : ℝ)).indicator
        (fun y => ENNReal.ofReal (y ^ (r - 2) * Real.exp (-c * y))) y) (Set.Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hpt : ∀ x : ℝ, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I)) =
        (Set.Ici (1 : ℝ)).indicator
          (fun y => ENNReal.ofReal (y ^ r * Real.exp (-c * y))) y := by
      intro x
      by_cases h1 : (1 : ℝ) ≤ y
      · rw [Set.indicator_of_mem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_mem (by simpa using h1), im_ofComplex_xy x y hy0,
          Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      · rw [Set.indicator_of_notMem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_notMem (by simpa using h1)]
    simp only [hpt]
    rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h1 : (1 : ℝ) ≤ y
    · rw [Set.indicator_of_mem (by simpa using h1), Set.indicator_of_mem (by simpa using h1),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      congr 1
      rw [Real.rpow_sub hy0, Real.rpow_two]
      field_simp
    · rw [Set.indicator_of_notMem (by simpa using h1), Set.indicator_of_notMem (by simpa using h1),
        zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Set.Ici_subset_Ioi.2 one_pos)]
  have hfin := ((integrableOn_Ici_iff_integrableOn_Ioi).2
    (integrableOn_rpow_sub_two_mul_exp_Ioi_one r c hc)).hasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hfin

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLeStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le : ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  first | exact @GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le | exact GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le | (intros; apply GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnSqQExpansionUnitStripLow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnSqQExpansionUnitStripLow
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lintegral_sq_qs_line (b : ℕ → ℂ) (hb : PolyB b) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in Set.Ico (0 : ℝ) 1, ENNReal.ofReal (‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2)
      = ∑' n : ℕ, ENNReal.ofReal (‖b n‖ ^ 2 * Real.exp (-4 * π * n * y)) := by
  have him : ∀ x : ℝ, 0 < ((x : ℂ) + y * Complex.I).im := fun x => by simpa using hy
  have hc0 : Continuous fun x : ℝ => ofComplex ((x : ℂ) + y * Complex.I) := by
    have : (fun x : ℝ => ofComplex ((x : ℂ) + y * Complex.I))
        = fun x : ℝ => (⟨(x : ℂ) + y * Complex.I, him x⟩ : ℍ) := by
      funext x; exact ofComplex_apply_of_im_pos (him x)
    rw [this, UpperHalfPlane.isEmbedding_coe.continuous_iff]
    show Continuous fun x : ℝ => (x : ℂ) + y * Complex.I
    fun_prop
  have hc : Continuous fun x : ℝ => ‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2 :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2.comp hc0).norm.pow 2
  have hP := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line b b y hb hb hy
  have h1 : (∫ x in (0 : ℝ)..1, conj (qs b (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I)))
      = ((∫ x in (0 : ℝ)..1, ‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    push_cast
    rfl
  have h2 : (fun n : ℕ => conj (b n) * b n * (Real.exp (-4 * π * n * y) : ℝ))
      = fun n : ℕ => ((‖b n‖ ^ 2 * Real.exp (-4 * π * n * y) : ℝ) : ℂ) := by
    funext n
    rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]
  rw [h1, h2, Complex.hasSum_ofReal] at hP
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hP.summable, hP.tsum_eq,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal]
  · exact (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  · exact Eventually.of_forall fun x => by positivity

theorem lintegral_exp_rpow_le (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ y in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(c * y)))
      ≤ ENNReal.ofReal ((1 / c) ^ a * Real.Gamma a) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hc
  have hpos : 0 < (1 / c) ^ a * Real.Gamma a := mul_pos (by positivity) (Real.Gamma_pos_of_pos ha)
  have hi : Integrable (fun y : ℝ => y ^ (a - 1) * Real.exp (-(c * y))) (volume.restrict (Set.Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact hpos.ne')
  rw [← h, ofReal_integral_eq_lintegral_ofReal hi]
  · exact lintegral_mono_set Set.Ioo_subset_Ioi_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have : 0 < y := hy
    simp only [Pi.zero_apply]
    positivity

theorem tsum_lintegral_exp_rpow_lt_top (b : ℕ → ℂ) (a : ℝ) (ha0 : 0 < a)
    (hsum : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ a) :
    ∑' n : ℕ, ENNReal.ofReal (‖b n‖ ^ 2) *
      ∫⁻ y in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) < ⊤ := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_, ?_⟩
  · have hi : IntegrableOn (fun y : ℝ => y ^ (a - 1)) (Set.Ioo 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)).1.mono_set Set.Ioo_subset_Ioc_self
    simpa using hi.lintegral_lt_top
  · have hs1 : Summable fun n : ℕ => ‖b (n + 1)‖ ^ 2 * ((1 / (4 * π * ((n + 1 : ℕ) : ℝ))) ^ a * Real.Gamma a) := by
      refine (((summable_nat_add_iff 1).2 hsum).mul_left ((1 / (4 * π)) ^ a * Real.Gamma a)).congr fun n => ?_
      rw [show 1 / (4 * π * ((n + 1 : ℕ) : ℝ)) = (1 / (4 * π)) / ((n + 1 : ℕ) : ℝ) by field_simp,
        Real.div_rpow (x := 1 / (4 * π)) (by positivity) (by positivity)]
      ring
    have hG0 := Real.Gamma_pos_of_pos ha0
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun n : ℕ => ENNReal.ofReal
      (‖b (n + 1)‖ ^ 2 * ((1 / (4 * π * ((n + 1 : ℕ) : ℝ))) ^ a * Real.Gamma a))) fun n => ?_) ?_
    · rw [ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact lintegral_exp_rpow_le a _ ha0 (by positivity)
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs1]
      exact ENNReal.ofReal_lt_top

theorem integrableOn_sq_qs_low : ∀ (e : ℕ) (b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → PolyB b →
    (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) →
    IntegrableOn (fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro e b s he hs hb hsum
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  set a : ℝ := 2 * (e : ℝ) - 1 + s with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hp : 2 * (e : ℝ) + s = a + 1 := by rw [ha]; ring
  rw [hp]
  have hcont : Continuous fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (a + 1) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2.norm.pow 2).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ => Or.inr (by linarith))
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hmeas : MeasurableSet {τ : ℍ | τ.im < 1} :=
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).measurableSet
  set G : ℍ → ENNReal := fun τ => ENNReal.ofReal (‖qs b τ‖ ^ 2 * τ.im ^ (a + 1)) with hG
  have hGm : Measurable G := ENNReal.measurable_ofReal.comp hcont.measurable
  have e1 : ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ τ.im < 1}, ‖‖qs b τ‖ ^ 2 * τ.im ^ (a + 1)‖ₑ
      = ∫⁻ τ in strip, Set.indicator {τ : ℍ | τ.im < 1} G τ := by
    rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas]
    have : {τ : ℍ | τ ∈ strip ∧ τ.im < 1} = {τ : ℍ | τ.im < 1} ∩ strip := by
      ext τ; simp [and_comm]
    rw [this]
    refine lintegral_congr fun τ => ?_
    have := τ.im_pos
    exact Real.enorm_of_nonneg (by positivity)
  rw [hasFiniteIntegral_iff_enorm, e1, GlobalTheory.T.unitStrip_integral_eq_iterated.1 _ (hGm.indicator hmeas)]
  set T : ℕ → ℝ → ENNReal := fun n y =>
    ENNReal.ofReal (‖b n‖ ^ 2) * ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) with hT
  have hTm : ∀ n : ℕ, Measurable fun y : ℝ => ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) := fun n => by
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  have e2 : ∀ y ∈ Set.Ioi (0 : ℝ),
      (∫⁻ x in Set.Ico (0 : ℝ) 1, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I)))
        * ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y => ∑' n, T n y) y := by
    intro y hy
    have hy : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x : ℂ) + y * Complex.I)).im = y := fun x => by
      have h : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
      rw [ofComplex_apply_of_im_pos h]
      show ((x : ℂ) + y * Complex.I).im = y
      simp
    by_cases h1 : y < 1
    · have : ∀ x : ℝ, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I))
          = ENNReal.ofReal (‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2) * ENNReal.ofReal (y ^ (a + 1)) := fun x => by
        rw [Set.indicator_of_mem (by simpa [him x] using h1), hG]
        simp only [him x]
        rw [ENNReal.ofReal_mul (by positivity)]
      simp only [this]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_sq_qs_line b hb y hy,
        Set.indicator_of_mem (by simpa using h1), mul_assoc, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun n => ?_
      simp only [hT]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : y ^ (a + 1) = y ^ (a - 1) * y ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add hy]; congr 1; ring
      rw [this, show -4 * π * n * y = -(4 * π * n * y) by ring]
      field_simp
    · have : ∀ x : ℝ, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I)) = 0 := fun x =>
        Set.indicator_of_notMem (by simpa [him x] using h1) _
      simp only [this]
      rw [Set.indicator_of_notMem (by simpa using h1)]
      simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio,
    lintegral_tsum (f := T) fun n => ((hTm n).const_mul _).aemeasurable]
  simp only [hT, lintegral_const_mul _ (hTm _)]
  exact tsum_lintegral_exp_rpow_lt_top b a ha0 hsum

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnSqQExpansionUnitStripLowStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low : ∀ (e : ℕ) (b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.integrableOn_sq_qs_low | exact GlobalTheory.EisM.integrableOn_sq_qs_low | (intros; apply GlobalTheory.EisM.integrableOn_sq_qs_low <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QsBddAboveOneStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QsBddAboveOne
open UpperHalfPlane Complex
open scoped Real

namespace GlobalTheory.EisM

private theorem norm_cexp_qterm (n : ℕ) (τ : ℍ) :
    ‖cexp (2 * π * Complex.I * n * τ)‖ = Real.exp (-(2 * π * n * τ.im)) := by
  rw [Complex.norm_exp]
  congr 1
  have h : (2 * π * Complex.I * n * τ : ℂ) = ((2 * π * n : ℝ) : ℂ) * (Complex.I * τ) := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

theorem qs_bdd_above_one : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  intro b hb
  obtain ⟨hs, -⟩ := qs_summable_continuous b hb
  refine ⟨∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖, fun τ hτ => ?_⟩
  have hpt : ∀ n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ ≤
      ‖b n * cexp (2 * π * Complex.I * n * (UpperHalfPlane.I : ℍ))‖ := by
    intro n
    rw [norm_mul, norm_mul, norm_cexp_qterm, norm_cexp_qterm]
    gcongr
    simp only [UpperHalfPlane.I_im, mul_one]
    have h0 : (0 : ℝ) ≤ 2 * π * n := by positivity
    nlinarith
  calc ‖qs b τ‖ ≤ ∑' n : ℕ, ‖b n * cexp (2 * π * Complex.I * n * τ)‖ := by
        unfold qs; exact norm_tsum_le_tsum_norm (hs τ)
    _ ≤ _ := Summable.tsum_le_tsum hpt (hs τ) (hs _)

end GlobalTheory.EisM
end

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_norm_qs_of_one_le_im : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  first | exact @GlobalTheory.EisM.qs_bdd_above_one | exact GlobalTheory.EisM.qs_bdd_above_one | (intros; apply GlobalTheory.EisM.qs_bdd_above_one <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrand
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem strip_integrable_rankin : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  intro k e L N ε h b s hk he hs hL hNL hh hb hsum
  obtain ⟨-, hch⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1
  obtain ⟨-, hcb⟩ := GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb
  obtain ⟨C, hC⟩ := hh.2
  obtain ⟨C', δ, hδ, hdec⟩ := GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L N ε h 1 (by omega) hL hNL hh
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_bound_norm_qs_of_one_le_im b hb
  have fcont : Continuous (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) := by
    refine ((Complex.continuous_conj.comp hch).mul hcb).mul (Complex.continuous_ofReal.comp ?_)
    exact UpperHalfPlane.continuous_im.rpow_const (fun τ => Or.inl τ.im_pos.ne')
  have hnorm : ∀ τ : ℍ, ‖conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)‖ = ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ ((k : ℝ) + s) := by
    intro τ
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos τ.im_pos _)]
  have hsplit : strip = {τ | τ ∈ strip ∧ τ.im < 1} ∪ {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
    ext τ; simp only [Set.mem_union, Set.mem_setOf_eq]; constructor
    · intro h; rcases lt_or_ge τ.im 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
    · rintro (h | h) <;> exact h.1
  have hmre : Measurable (fun τ : ℍ => τ.re) := UpperHalfPlane.continuous_re.measurable
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmup : MeasurableSet {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} :=
    ((measurableSet_le measurable_const hmre).inter (measurableSet_lt hmre measurable_const)).inter
      (measurableSet_le measurable_const hmim)
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  ·
    have hg : IntegrableOn (fun τ : ℍ => (C * τ.im ^ (s + 1) + ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) / 2) {τ | τ ∈ strip ∧ τ.im < 1} :=
      (((GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one s hs).const_mul C).add (GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low e b s he hs hb hsum)).div_const 2
    refine hg.mono' fcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
    rw [hnorm]
    have hy := τ.im_pos
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have e1 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ (((k : ℝ) + 1 + s) / 2) = y ^ k * y ^ (s + 1) := by
      rw [← Real.rpow_add hy, ← Real.rpow_natCast, ← Real.rpow_add hy]; congr 1; ring
    have e2 : y ^ ((2 * (e : ℝ) + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ (2 * (e : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have e3 : y ^ (((k : ℝ) + 1 + s) / 2) * y ^ ((2 * (e : ℝ) + s) / 2) = y ^ ((k : ℝ) + s) := by
      rw [← Real.rpow_add hy]; congr 1; rw [hk]; push_cast; ring
    have amgm := two_mul_le_add_sq (A * y ^ (((k : ℝ) + 1 + s) / 2)) (B * y ^ ((2 * (e : ℝ) + s) / 2))
    have hCb : A ^ 2 * y ^ k ≤ C := hC τ
    have hp : 0 ≤ y ^ (s + 1) := (Real.rpow_pos_of_pos hy _).le
    have : A ^ 2 * (y ^ k * y ^ (s + 1)) ≤ C * y ^ (s + 1) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hCb hp
    have h1 : 2 * (A * y ^ (((k : ℝ) + 1 + s) / 2)) * (B * y ^ ((2 * (e : ℝ) + s) / 2)) = 2 * (A * B * y ^ ((k : ℝ) + s)) := by rw [← e3]; ring
    have h2 : (A * y ^ (((k : ℝ) + 1 + s) / 2)) ^ 2 = A ^ 2 * (y ^ k * y ^ (s + 1)) := by rw [← e1]; ring
    have h3 : (B * y ^ ((2 * (e : ℝ) + s) / 2)) ^ 2 = B ^ 2 * y ^ (2 * (e : ℝ) + s) := by rw [← e2]; ring
    rw [h1, h2, h3] at amgm
    linarith
  ·
    have hg := (GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le ((k : ℝ) / 2 + s) (δ / 2) (by linarith)).const_mul (Real.sqrt C' * M)
    refine hg.mono' fcont.aestronglyMeasurable ((ae_restrict_iff' hmup).2 (Eventually.of_forall fun τ hτ => ?_))
    rw [hnorm]
    have hy := τ.im_pos
    have hy1 : 1 ≤ τ.im := hτ.2
    have hd := hdec τ (by linarith)
    rw [one_smul] at hd
    have hB := hM τ hy1
    set A := ‖qs h τ‖
    set B := ‖qs b τ‖
    set y := τ.im
    have hA0 : 0 ≤ A := norm_nonneg _
    have hB0 : 0 ≤ B := norm_nonneg _
    have hyk : 0 ≤ y ^ ((k : ℝ) / 2) := (Real.rpow_pos_of_pos hy _).le
    have hsq : (A * y ^ ((k : ℝ) / 2)) ^ 2 = A ^ 2 * y ^ k := by
      rw [mul_pow, ← Real.rpow_natCast (y ^ ((k : ℝ) / 2)), ← Real.rpow_mul hy.le, ← Real.rpow_natCast y k]
      congr 2; push_cast; ring
    have hAy : A * y ^ ((k : ℝ) / 2) ≤ Real.sqrt C' * Real.exp (-(δ / 2) * y) := by
      have := Real.sqrt_le_sqrt hd
      rw [← hsq, Real.sqrt_sq (mul_nonneg hA0 hyk), Real.sqrt_mul' _ (Real.exp_pos _).le] at this
      convert this using 2
      rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]; congr 1; ring
    have hsplitpow : y ^ ((k : ℝ) + s) = y ^ ((k : ℝ) / 2) * y ^ ((k : ℝ) / 2 + s) := by
      rw [← Real.rpow_add hy]; congr 1; ring
    have hr : 0 ≤ y ^ ((k : ℝ) / 2 + s) := (Real.rpow_pos_of_pos hy _).le
    calc A * B * y ^ ((k : ℝ) + s) = (A * y ^ ((k : ℝ) / 2)) * B * y ^ ((k : ℝ) / 2 + s) := by rw [hsplitpow]; ring
      _ ≤ (Real.sqrt C' * Real.exp (-(δ / 2) * y)) * M * y ^ ((k : ℝ) / 2 + s) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul hAy hB hB0 (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)) hr
      _ = Real.sqrt C' * M * (y ^ ((k : ℝ) / 2 + s) * Real.exp (-(δ / 2) * y)) := by ring

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnStripUnfoldedRankinIntegrandStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_strip_unfolded_rankin_integrand : ∀ (k e L N : ℕ) (ε : DirichletCharacter ℂ N) (h b : ℕ → ℂ) (s : ℝ), k = 2 * e + 1 → 1 ≤ e → 0 < s → 0 < L → N ∣ L → CF k L (ch ε) h → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ ((k : ℝ) + s) : ℝ) : ℂ)) strip := by
  first | exact @GlobalTheory.EisM.strip_integrable_rankin | exact GlobalTheory.EisM.strip_integrable_rankin | (intros; apply GlobalTheory.EisM.strip_integrable_rankin <;> assumption)
end
