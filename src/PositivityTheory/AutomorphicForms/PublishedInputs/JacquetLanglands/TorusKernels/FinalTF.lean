module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorKernelAlgebraProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelTermsInvariantBoundedProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HeightsOnQuotientProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelTraceBoundProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.DiagonalIntegrandVanishesProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfKapInt
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.EllipticTermsContributionProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.AutomorphyFactorScalarMatrix
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.InverseSeriesSummable
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ExtendMatrixByIdentityAlongIndicesMul
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFhyp
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.DiagonalTermsContributionProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.DualNumberUnitMulDecomposition
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ImaginaryPartBoundProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.UnipotentIntegrandVanishesProof
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.DiagonalTruncatedIntegral

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicKappaPropertiesProof
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.HyperbolicKappaLemmas

open UpperTheory.Esk

theorem nsq (z w : ℂ) : ‖z - conj w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im + w.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  ring

theorem pos_den {z w : ℂ} (h : 0 < z.im * w.im) : 0 < ‖z - conj w‖ ^ 2 := by
  rw [nsq]
  nlinarith [sq_nonneg (z.re - w.re), sq_nonneg z.im, sq_nonneg w.im]

theorem kap_of {z w : P} (h : 0 < z.1.im * w.1.im) :
    kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
  unfold kap
  rw [if_pos h]

theorem kap_of_not {z w : P} (h : ¬ 0 < z.1.im * w.1.im) : kap z w = 0 := by
  unfold kap
  rw [if_neg h]

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem key {z w u : ℂ} (h1 : 0 < z.im * w.im) (h2 : 0 < w.im * u.im) :
    w.im ^ 2 * ‖z - conj u‖ ^ 2 ≤ ‖z - conj w‖ ^ 2 * ‖w - conj u‖ ^ 2 := by
  have h13 : 0 < z.im * u.im := by
    by_contra hc
    have hc := not_lt.mp hc
    nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.im)]
  have hp : 0 ≤ z.im ^ 2 + 2 * z.im * w.im := by nlinarith [sq_nonneg z.im]
  have hq : 0 ≤ u.im ^ 2 + 2 * w.im * u.im := by nlinarith [sq_nonneg u.im]
  rw [nsq, nsq, nsq]
  nlinarith [sq_nonneg ((z.re - w.re) * (w.re - u.re) - w.im ^ 2),
    mul_nonneg (sq_nonneg (z.re - w.re)) hq, mul_nonneg (sq_nonneg (w.re - u.re)) hp,
    mul_nonneg (sq_nonneg w.im) h1.le, mul_nonneg (sq_nonneg w.im) h2.le,
    mul_nonneg (sq_nonneg w.im) h13.le, mul_nonneg h13.le h1.le, mul_nonneg h13.le h2.le,
    sq_nonneg (z.im * u.im)]

theorem p1 (z w : P) : 0 ≤ kap z w ∧ kap z w ≤ 1 ∧ kap z w = kap w z := by
  refine ⟨kap_nonneg z w, ?_, ?_⟩
  · by_cases h : 0 < z.1.im * w.1.im
    · rw [kap_of h, div_le_iff₀ (pos_den h), nsq]
      nlinarith [sq_nonneg (z.1.re - w.1.re), sq_nonneg (z.1.im - w.1.im)]
    · rw [kap_of_not h]
      norm_num
  · have e2 : ‖w.1 - conj z.1‖ ^ 2 = ‖z.1 - conj w.1‖ ^ 2 := by
      rw [nsq, nsq]
      ring
    unfold kap
    rw [mul_comm w.1.im z.1.im, e2]

theorem p2 (z : P) : kap z z = 1 := by
  have h : 0 < z.1.im * z.1.im := mul_self_pos.mpr z.2
  rw [kap_of h, div_eq_one_iff_eq (pos_den h).ne', nsq]
  ring

theorem p3 (z w u : P) : kap z w * kap w u ≤ 4 * kap z u := by
  by_cases h1 : 0 < z.1.im * w.1.im
  · by_cases h2 : 0 < w.1.im * u.1.im
    · have h13 : 0 < z.1.im * u.1.im := by
        by_contra hc
        have hc := not_lt.mp hc
        nlinarith [mul_pos h1 h2, mul_nonneg (neg_nonneg.mpr hc) (sq_nonneg w.1.im)]
      have hA := pos_den h1
      have hB := pos_den h2
      have hC := pos_den h13
      have hk := mul_le_mul_of_nonneg_left (key h1 h2) h13.le
      rw [kap_of h1, kap_of h2, kap_of h13, div_mul_div_comm, mul_div_assoc', le_div_iff₀ hC,
        div_mul_eq_mul_div, div_le_iff₀ (mul_pos hA hB)]
      nlinarith [hk]
    · rw [kap_of_not h2, mul_zero]
      exact mul_nonneg (by norm_num) (kap_nonneg z u)
  · rw [kap_of_not h1, zero_mul]
    exact mul_nonneg (by norm_num) (kap_nonneg z u)

theorem p4 (z w : P) : kap z w * |w.1.im| ≤ 4 * |z.1.im| := by
  by_cases h : 0 < z.1.im * w.1.im
  · rw [kap_of h, div_mul_eq_mul_div, div_le_iff₀ (pos_den h), nsq]
    rcases lt_or_gt_of_ne w.2 with hw | hw
    · have hz : z.1.im < 0 := by nlinarith [h, hw]
      rw [abs_of_neg hw, abs_of_neg hz]
      nlinarith [mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg (z.1.re - w.1.re)),
        mul_nonneg (neg_nonneg.mpr hz.le) (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) (neg_nonneg.mpr hw.le)]
    · have hz : 0 < z.1.im := by nlinarith [h, hw]
      rw [abs_of_pos hw, abs_of_pos hz]
      nlinarith [mul_nonneg hz.le (sq_nonneg (z.1.re - w.1.re)), mul_nonneg hz.le (sq_nonneg z.1.im),
        mul_nonneg (sq_nonneg z.1.im) hw.le]
  · rw [kap_of_not h, zero_mul]
    positivity

theorem p5 : Continuous (fun p : P × P => kap p.1 p.2) := by
  have hv1 : Continuous (fun p : P × P => p.1.1) := continuous_subtype_val.comp continuous_fst
  have hv2 : Continuous (fun p : P × P => p.2.1) := continuous_subtype_val.comp continuous_snd
  have hc : Continuous (fun p : P × P => p.1.1.im * p.2.1.im) :=
    (Complex.continuous_im.comp hv1).mul (Complex.continuous_im.comp hv2)
  have hd : Continuous (fun p : P × P => ‖p.1.1 - conj p.2.1‖ ^ 2) :=
    ((hv1.sub (Complex.continuous_conj.comp hv2)).norm).pow 2
  have hopen : IsOpen {p : P × P | 0 < p.1.1.im * p.2.1.im} := isOpen_lt continuous_const hc
  have hclosed : IsClosed {p : P × P | 0 < p.1.1.im * p.2.1.im} := by
    have e : {p : P × P | 0 < p.1.1.im * p.2.1.im} = {p : P × P | 0 ≤ p.1.1.im * p.2.1.im} := by
      ext p
      simp only [Set.mem_setOf_eq]
      exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (Ne.symm (mul_ne_zero p.1.2 p.2.2))⟩
    rw [e]
    exact isClosed_le continuous_const hc
  have hfr : frontier {p : P × P | 0 < p.1.1.im * p.2.1.im} = ∅ := by
    rw [frontier, hclosed.closure_eq, hopen.interior_eq, Set.sdiff_self]
  show Continuous (fun p : P × P => if 0 < p.1.1.im * p.2.1.im then
    4 * (p.1.1.im * p.2.1.im) / ‖p.1.1 - conj p.2.1‖ ^ 2 else 0)
  apply continuous_if
  · intro a ha
    simp [hfr] at ha
  · rw [hclosed.closure_eq]
    exact ((continuous_const.mul hc).continuousOn).div hd.continuousOn
      (fun p hp => (pos_den (z := p.1.1) (w := p.2.1) hp).ne')
  · exact continuousOn_const

theorem p6 (z : P) : ∃ g : GL (Fin 2) ℝ, g 1 0 = 0 ∧ g 1 1 = 1 ∧ g • iP = z := by
  have hdet : (!![z.1.im, z.1.re; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simpa using z.2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, rfl, Subtype.ext ?_⟩
  rw [coe_smul]
  show num (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I /
    den (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) Complex.I = z.1
  have h00 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 0 = z.1.im := rfl
  have h01 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 0 1 = z.1.re := rfl
  have h10 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 0 = 0 := rfl
  have h11 : (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet) 1 1 = 1 := rfl
  rw [num, den, h00, h01, h10, h11]
  apply Complex.ext <;> simp

end UpperTheory.Esk.HyperbolicKappaLemmas

namespace UpperTheory.Esk

theorem hyperbolic_kappa_properties_proof : B1c := by
  unfold B1c
  exact ⟨HyperbolicKappaLemmas.p1, HyperbolicKappaLemmas.p2, HyperbolicKappaLemmas.p3, HyperbolicKappaLemmas.p4, HyperbolicKappaLemmas.p5, HyperbolicKappaLemmas.p6⟩

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HalfPlaneMeasureInvariantProof
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.HalfPlaneMeasureLemmas

open UpperTheory.Esk

def U : Set ℂ := {z | z.im ≠ 0}

theorem isOpen_U : IsOpen U := isOpen_ne_fun Complex.continuous_im continuous_const

def val (z : P) : ℂ := z.1

def mk (z : ℂ) (hz : z.im ≠ 0) : P := ⟨z, hz⟩

theorem openEmb : Topology.IsOpenEmbedding val :=
  isOpen_U.isOpenEmbedding_subtypeVal

theorem measEmb : MeasurableEmbedding val :=
  openEmb.measurableEmbedding

def rho (z : ℂ) : ℝ≥0∞ := ENNReal.ofReal (1 / z.im ^ 2)

def F (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num g z / den g z

def D (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ ((g.val.det : ℂ) / den g z ^ 2)).restrictScalars ℝ

theorem hasDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (F g) ((g.val.det : ℂ) / den g z ^ 2) z := by
  have h := ((hasDerivAt_id z).const_mul ((g 0 0 : ℝ) : ℂ) |>.add_const ((g 0 1 : ℝ) : ℂ)).div
    ((hasDerivAt_id z).const_mul ((g 1 0 : ℝ) : ℂ) |>.add_const ((g 1 1 : ℝ) : ℂ)) (den_ne g hz)
  refine h.congr_deriv ?_
  simp only [den, id, mul_one]
  rw [det_eq]
  push_cast
  ring

theorem hasFDerivAt_F (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : HasFDerivAt (F g) (D g z) z := by
  have := (hasDerivAt_F g hz).hasFDerivAt.restrictScalars ℝ
  simpa [D] using this

theorem det_D (g : GL (Fin 2) ℝ) (z : ℂ) :
    (D g z).det = Complex.normSq ((g.val.det : ℂ) / den g z ^ 2) := by
  simp [D, ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]

theorem F_eq (g : GL (Fin 2) ℝ) (z : P) : F g (val z) = val (g • z) := rfl

theorem injOn_F (g : GL (Fin 2) ℝ) : Set.InjOn (F g) U := by
  intro x hx y hy hxy
  have h : g • mk x hx = g • mk y hy := Subtype.ext hxy
  have := congrArg val (smul_left_cancel g h)
  exact this

theorem key (g : GL (Fin 2) ℝ) {S : Set ℂ} (hS : MeasurableSet S) (hSU : S ⊆ U) :
    ∫⁻ x in F g '' S, rho x = ∫⁻ x in S, rho x := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun x hx => (hasFDerivAt_F g (hSU hx)).hasFDerivWithinAt) ((injOn_F g).mono hSU)]
  refine setLIntegral_congr_fun hS (fun x hx => ?_)
  have hx' : x.im ≠ 0 := hSU hx
  have hd := den_ne g hx'
  have hn : Complex.normSq (den g x) ≠ 0 := by simpa using hd
  have hdet := g.det_ne_zero
  rw [det_D, rho, rho, F, im_div, abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul
    (Complex.normSq_nonneg _)]
  congr 1
  rw [Complex.normSq_div, Complex.normSq_ofReal, map_pow]
  field_simp

theorem vol_def : (volume : Measure P) = (Measure.comap val volume).withDensity fun z => rho (val z) := rfl

theorem vol_eq (s : Set P) (hs : MeasurableSet s) : volume s = ∫⁻ z in val '' s, rho z := by
  rw [vol_def, withDensity_apply _ hs, measEmb.restrict_comap,
    ← measEmb.lintegral_map, measEmb.map_comap,
    Measure.restrict_restrict (measEmb.measurableSet_range),
    Set.inter_eq_right.2 (Set.image_subset_range _ _)]

theorem image_pre (g : GL (Fin 2) ℝ) (s : Set P) :
    val '' ((fun z : P => g • z) ⁻¹' s) = F g⁻¹ '' (val '' s) := by
  ext x
  simp only [Set.mem_image, Set.mem_preimage]
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨val (g • p), ⟨g • p, hp, rfl⟩, ?_⟩
    rw [F_eq g⁻¹ (g • p), inv_smul_smul]
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨g⁻¹ • q, by rwa [smul_inv_smul], ?_⟩
    rw [F_eq]

theorem cont (g : GL (Fin 2) ℝ) : Continuous (fun z : P => g • z) := by
  have hv : Continuous (fun z : P => z.1) := continuous_subtype_val
  have h : Continuous (fun z : P => (g • z).1) := by
    change Continuous (fun z : P => num g z.1 / den g z.1)
    refine Continuous.div ?_ ?_ (fun z => den_ne g z.2)
    · simp only [num]; fun_prop
    · simp only [den]; fun_prop
  exact continuous_induced_rng.2 h

theorem meas_rho : Measurable (fun z : P => rho (val z)) :=
  ENNReal.measurable_ofReal.comp (measurable_const.div ((Complex.measurable_im.comp measEmb.measurable).pow_const 2))

end UpperTheory.Esk.HalfPlaneMeasureLemmas

namespace UpperTheory.Esk

open HalfPlaneMeasureLemmas in
theorem half_plane_measure_invariant_proof : B1a := by
  have : LocallyCompactSpace P := openEmb.locallyCompactSpace
  have : IsFiniteMeasureOnCompacts (Measure.comap val volume) := .comap' _ openEmb.continuous measEmb
  have : SigmaFinite (Measure.comap val volume) := inferInstance
  refine ⟨?_, ?_, fun g => ⟨cont g, ?_⟩⟩
  · rw [vol_def]
    exact SigmaFinite.withDensity_ofReal _
  · have : (Measure.comap val volume).IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap _ openEmb
    refine ⟨fun A hA hne => ?_⟩
    rw [vol_def, Ne, withDensity_apply_eq_zero meas_rho]
    have : {x : P | rho (val x) ≠ 0} ∩ A = A := by
      refine Set.inter_eq_right.2 (fun x _ => ?_)
      have := x.2
      simp only [Set.mem_ofPred_eq, rho, val, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [this]
    exact hA.measure_ne_zero _ hne
  · refine ⟨(cont g).measurable, Measure.ext fun s hs => ?_⟩
    rw [Measure.map_apply (cont g).measurable hs, vol_eq _ ((cont g).measurable hs), vol_eq _ hs,
      image_pre, key _ (measEmb.measurableSet_image.2 hs)]
    rintro _ ⟨p, -, rfl⟩
    exact p.2

end UpperTheory.Esk
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.FiniteSystemProof
noncomputable section

open scoped NNReal

namespace UpperTheory.Esk.Fin0Aux

theorem nat_le_one (ν : Valuation ℂ ℝ≥0) (n : ℕ) : ν (n : ℂ) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le ν ih (by simp)

theorem step (ν : Valuation ℂ ℝ≥0) (l : ℕ) (hl : l.Prime) (y : ℂ) (hy : ν y ≤ 1) :
    ν ((1 + y) ^ l - 1) ≤ max (ν (l : ℂ)) (ν y) * ν y := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by have := hl.two_le; omega⟩
  have e : (1 + y) ^ (m + 2) - 1 =
      ∑ k ∈ Finset.range (m + 1), y ^ (k + 1) * ((m + 2).choose (k + 1) : ℂ) + y ^ (m + 2) := by
    rw [add_comm (1 : ℂ) y, add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one]
    ring
  rw [e]
  apply Valuation.map_add_le
  · apply Valuation.map_sum_le
    intro k hk
    have hk' := Finset.mem_range.1 hk
    obtain ⟨q, hq⟩ := hl.dvd_choose_self (Nat.succ_ne_zero k) (by omega)
    rw [Valuation.map_mul, hq, Nat.cast_mul, Valuation.map_mul, Valuation.map_pow]
    have h1 : ν y ^ (k + 1) ≤ ν y := by
      rw [pow_succ]; exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hy)
    have h2 := nat_le_one ν q
    calc ν y ^ (k + 1) * (ν ((m + 2 : ℕ) : ℂ) * ν (q : ℂ)) ≤ ν y * (ν ((m + 2 : ℕ) : ℂ) * 1) := by gcongr
      _ ≤ max (ν ((m + 2 : ℕ) : ℂ)) (ν y) * ν y := by
          rw [mul_one, mul_comm]; gcongr; exact le_max_left _ _
  · rw [Valuation.map_pow]
    calc ν y ^ (m + 2) ≤ ν y ^ 2 := pow_le_pow_of_le_one zero_le hy (by omega)
      _ = ν y * ν y := sq _
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem iter (ν : Valuation ℂ ℝ≥0) (l : ℕ) (hl : l.Prime) (hνl : ν (l : ℂ) < 1) (x : ℂ) (hx : ν x < 1) :
    ∀ a : ℕ, ν ((1 + x) ^ (l ^ a) - 1) ≤ max (ν (l : ℂ)) (ν x) ^ a * ν x := by
  intro a
  induction a with
  | zero => simp
  | succ a ih =>
    have e : (1 + x) ^ (l ^ (a + 1)) - 1 = (1 + ((1 + x) ^ (l ^ a) - 1)) ^ l - 1 := by
      rw [add_sub_cancel, ← pow_mul, ← pow_succ]
    rw [e]
    have hθ : max (ν (l : ℂ)) (ν x) ≤ 1 := max_le hνl.le hx.le
    have hya : ν ((1 + x) ^ (l ^ a) - 1) ≤ ν x :=
      ih.trans (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hθ))
    calc _ ≤ max (ν (l : ℂ)) (ν ((1 + x) ^ (l ^ a) - 1)) * ν ((1 + x) ^ (l ^ a) - 1) :=
          step ν l hl _ (hya.trans hx.le)
      _ ≤ max (ν (l : ℂ)) (ν x) * (max (ν (l : ℂ)) (ν x) ^ a * ν x) :=
          mul_le_mul (max_le_max le_rfl hya) ih zero_le zero_le
      _ = max (ν (l : ℂ)) (ν x) ^ (a + 1) * ν x := by ring

def lam {J : Type} (S : Finset (J → ℂ)) (a : (J → ℂ) → ℂ) : ((J → ℂ) → ℂ) →ₗ[ℂ] ℂ :=
  ∑ s ∈ S, a s • (LinearMap.proj s : ((J → ℂ) → ℂ) →ₗ[ℂ] ℂ)

theorem lam_apply {J : Type} (S : Finset (J → ℂ)) (a : (J → ℂ) → ℂ) (g : (J → ℂ) → ℂ) :
    lam S a g = ∑ s ∈ S, a s * g s := by
  simp [lam, LinearMap.sum_apply]

theorem factors {J : Type} (ν : Valuation ℂ ℝ≥0) (Λ : ((J → ℂ) → ℂ) →ₗ[ℂ] ℂ) (P : List J → Prop)
    (hP : ∀ W j, P W → P (W ++ [j])) (B : ℝ≥0) (hB : ∀ W, P W → ν (Λ fun s => (W.map s).prod) ≤ B) :
    ∀ (Fs : List (ℂ × J × ℂ)), (∀ f ∈ Fs, ν f.1 ≤ 1 ∧ ν f.2.2 ≤ 1) → ∀ W, P W →
      ν (Λ fun s => (W.map s).prod * (Fs.map fun f => f.1 * s f.2.1 + f.2.2).prod) ≤ B := by
  intro Fs
  induction Fs with
  | nil => intro _ W hW; simpa using hB W hW
  | cons f Fs ih =>
    intro hF W hW
    have hf := hF f List.mem_cons_self
    have hF' : ∀ g ∈ Fs, ν g.1 ≤ 1 ∧ ν g.2.2 ≤ 1 := fun g hg => hF g (List.mem_cons_of_mem _ hg)
    have e : (fun s : J → ℂ => (W.map s).prod * ((f :: Fs).map fun f => f.1 * s f.2.1 + f.2.2).prod) =
        f.1 • (fun s : J → ℂ => ((W ++ [f.2.1]).map s).prod * (Fs.map fun f => f.1 * s f.2.1 + f.2.2).prod) +
        f.2.2 • (fun s : J → ℂ => (W.map s).prod * (Fs.map fun f => f.1 * s f.2.1 + f.2.2).prod) := by
      funext s
      simp only [List.map_cons, List.prod_cons, List.map_append, List.prod_append, List.map_nil,
        List.prod_nil, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    apply Valuation.map_add_le
    · rw [Valuation.map_mul]
      calc _ ≤ 1 * B := mul_le_mul' hf.1 (ih hF' _ (hP W _ hW))
        _ = B := one_mul B
    · rw [Valuation.map_mul]
      calc _ ≤ 1 * B := mul_le_mul' hf.2 (ih hF' _ hW)
        _ = B := one_mul B

theorem count_rep {J : Type} [DecidableEq J] (l : List J) (j : J) (n : ℕ) :
    ((List.replicate n l).flatten).count j = n * l.count j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.count_append, ih]; ring

theorem prod_rep {α : Type} (l : List α) (g : α → ℂ) (n : ℕ) :
    (((List.replicate n l).flatten).map g).prod = (l.map g).prod ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.map_append, List.prod_append, ih, pow_succ']

theorem prod_near_one (ν : Valuation ℂ ℝ≥0) (l : List ℂ) (h : ∀ y ∈ l, ν (y - 1) < 1) : ν (l.prod - 1) < 1 := by
  induction l with
  | nil => simp
  | cons y l ih =>
    have hy := h y List.mem_cons_self
    have hl := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    have hP : ν l.prod ≤ 1 := by
      have : l.prod = (l.prod - 1) + 1 := by ring
      rw [this]; exact Valuation.map_add_le ν hl.le (by simp)
    rw [List.prod_cons, show y * l.prod - 1 = (y - 1) * l.prod + (l.prod - 1) by ring]
    apply Valuation.map_add_lt ν _ hl
    rw [Valuation.map_mul]
    calc ν (y - 1) * ν l.prod ≤ ν (y - 1) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact hy

theorem integral {J : Type} [DecidableEq J] (ν : Valuation ℂ ℝ≥0) (L : Finset J) (S : Finset (J → ℂ))
    (a : (J → ℂ) → ℂ)
    (hB : ∀ W : List J, (∀ j ∈ L, 1 ≤ W.count j) → ν (∑ s ∈ S, a s * (W.map s).prod) ≤ 1)
    (t : J → ℂ) (ht : t ∈ S) (hat : a t ≠ 0) (htL : ∀ j ∈ L, t j ≠ 0) (j0 : J) : ν (t j0) ≤ 1 := by
  classical
  have hj : ∀ u ∈ S.erase t, ∃ j, u j ≠ t j := by
    intro u hu
    by_contra h
    push_neg at h
    exact (Finset.ne_of_mem_erase hu) (funext h)
  have : Nonempty J := ⟨j0⟩
  choose! jj hjj using hj
  let c : ℂ → ℂ := fun x => if ν x ≤ 1 then 1 else x⁻¹
  have hc : ∀ x, ν (c x) ≤ 1 ∧ ν (c x * x) ≤ 1 ∧ c x ≠ 0 := by
    intro x
    by_cases hx : ν x ≤ 1
    · simp only [c, if_pos hx, one_mul]; exact ⟨by simp, hx, one_ne_zero⟩
    · simp only [c, if_neg hx]
      push_neg at hx
      have hx0 : x ≠ 0 := by rintro rfl; simp at hx
      refine ⟨?_, ?_, inv_ne_zero hx0⟩
      · rw [map_inv₀]; exact inv_le_one_of_one_le₀ hx.le
      · rw [inv_mul_cancel₀ hx0]; simp
  let Fs : List (ℂ × J × ℂ) :=
    (S.erase t).toList.map fun u => (c (u (jj u)), jj u, -(c (u (jj u)) * u (jj u)))
  have hFs : ∀ f ∈ Fs, ν f.1 ≤ 1 ∧ ν f.2.2 ≤ 1 := by
    intro f hf
    obtain ⟨u, -, rfl⟩ := List.mem_map.1 hf
    exact ⟨(hc _).1, by rw [Valuation.map_neg]; exact (hc _).2.1⟩
  have hP : ∀ (W : List J) (j : J), (∀ i ∈ L, 1 ≤ W.count i) → (∀ i ∈ L, 1 ≤ (W ++ [j]).count i) := by
    intro W j hW i hi
    rw [List.count_append]
    have := hW i hi
    omega
  have key := factors ν (lam S a) (fun W => ∀ j ∈ L, 1 ≤ W.count j) hP 1
    (fun W hW => by rw [lam_apply]; exact hB W hW) Fs hFs
  have hR0 : ∀ u ∈ S, u ≠ t → (Fs.map fun f => f.1 * u f.2.1 + f.2.2).prod = 0 := by
    intro u hu hne
    apply List.prod_eq_zero
    refine List.mem_map.2 ⟨(c (u (jj u)), jj u, -(c (u (jj u)) * u (jj u))), ?_, ?_⟩
    · exact List.mem_map.2 ⟨u, Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hne, hu⟩), rfl⟩
    · simp
  have hRt : (Fs.map fun f => f.1 * t f.2.1 + f.2.2).prod ≠ 0 := by
    apply List.prod_ne_zero
    intro h
    obtain ⟨f, hf, hf0⟩ := List.mem_map.1 h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hf
    have hu' := Finset.mem_toList.1 hu
    have e : c (u (jj u)) * t (jj u) + -(c (u (jj u)) * u (jj u)) = c (u (jj u)) * (t (jj u) - u (jj u)) := by ring
    simp only at hf0
    rw [e] at hf0
    rcases mul_eq_zero.1 hf0 with h1 | h1
    · exact (hc _).2.2 h1
    · exact hjj u hu' (sub_eq_zero.1 h1).symm
  set K := a t * (L.toList.map t).prod * (Fs.map fun f => f.1 * t f.2.1 + f.2.2).prod with hKdef
  have hK : K ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hat ?_) hRt
    apply List.prod_ne_zero
    intro h
    obtain ⟨j, hj, hj0⟩ := List.mem_map.1 h
    exact htL j (Finset.mem_toList.1 hj) hj0
  have hn : ∀ n : ℕ, ν K * ν (t j0) ^ n ≤ 1 := by
    intro n
    have := key (L.toList ++ List.replicate n j0) (by
      intro j hj
      rw [List.count_append]
      have : 1 ≤ L.toList.count j := List.count_pos_iff.2 (Finset.mem_toList.2 hj)
      omega)
    rw [lam_apply, Finset.sum_eq_single t (fun u hu hne => mul_eq_zero_of_right _
      (mul_eq_zero_of_right _ (hR0 u hu hne))) (fun h => absurd ht h)] at this
    have e : a t * (((L.toList ++ List.replicate n j0).map t).prod *
        (Fs.map fun f => f.1 * t f.2.1 + f.2.2).prod) = K * t j0 ^ n := by
      rw [hKdef, List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]; ring
    rwa [e, Valuation.map_mul, Valuation.map_pow] at this
  by_contra hlt
  push_neg at hlt
  have hK0 : 0 < ν K := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff ν).2 hK)
  obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt (ν K)⁻¹ hlt
  have h1 : ν K * (ν K)⁻¹ < ν K * ν (t j0) ^ n := mul_lt_mul_of_pos_left hn' hK0
  rw [mul_inv_cancel₀ hK0.ne'] at h1
  exact absurd (hn n) (not_le.2 h1)

end UpperTheory.Esk.Fin0Aux

open UpperTheory.Esk.Fin0Aux in
theorem UpperTheory.Esk.finite_system_proof : UpperTheory.Esk.Sys → UpperTheory.Esk.Fin0 := by
  intro hSys ν l hl hνl J V V' _ _ _ _ _ _ _ T T' hT hT' L ε ρ hρ hε hW f s hf0 hfs hsL
  classical
  obtain ⟨S, m, hS, hm, hmsum, htr⟩ := hSys J V T hT
  obtain ⟨S', m', hS', hm', -, htr'⟩ := hSys J V' T' hT'

  have intV : ∀ u ∈ S, (∀ j ∈ L, u j ≠ 0) → ∀ j, ν (u j) ≤ 1 := fun u hu huL j =>
    integral ν L S (fun s => (m s : ℂ)) (fun W hW' => by rw [← htr W]; exact (hW W 1 le_rfl hW').1) u hu
      (Nat.cast_ne_zero.2 (by have := hm u hu; omega)) huL j
  have intV' : ∀ u ∈ S', (∀ j ∈ L, u j ≠ 0) → ∀ j, ν (u j) ≤ 1 := fun u hu huL j =>
    integral ν L S' (fun s => (m' s : ℂ)) (fun W hW' => by rw [← htr' W]; exact (hW W 1 le_rfl hW').2.1) u hu
      (Nat.cast_ne_zero.2 (by have := hm' u hu; omega)) huL j
  have hsS : s ∈ S := (hS s).2 ⟨f, hf0, hfs⟩
  have hs0 : ∀ j ∈ L, s j ≠ 0 := fun j hj h => by have := hsL j hj; rw [h, map_zero] at this; exact zero_ne_one this
  have hsint : ∀ j, ν (s j) ≤ 1 := intV s hsS hs0
  by_contra hcon
  push_neg at hcon
  have hS'nc : ∀ u ∈ S', ∃ j, 1 ≤ ν (u j - s j) := by
    intro u hu
    obtain ⟨f', hf', hu'⟩ := (hS' u).1 hu
    exact hcon f' u hf' hu'
  rcases isEmpty_or_nonempty J with hJ | hJ
  · have hS'e : S' = ∅ := Finset.eq_empty_of_forall_notMem fun u hu => by
      obtain ⟨j, -⟩ := hS'nc u hu; exact (IsEmpty.false j).elim
    have hd1 : 1 ≤ Module.finrank ℂ V :=
      hmsum ▸ (hm s hsS).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hsS)
    have hεd := hε _ hd1 le_rfl
    obtain ⟨r, hr⟩ := NNReal.exists_pow_lt_of_lt_one (lt_of_le_of_lt zero_le hεd) hρ
    have := (hW [] (r + 1) (by omega) (fun j _ => (IsEmpty.false j).elim)).2.2
    rw [htr, htr', hS'e, Finset.sum_empty, sub_zero] at this
    simp only [List.map_nil, List.prod_nil, mul_one] at this
    rw [← Nat.cast_sum, hmsum] at this
    exact absurd this (not_le.2 (max_lt hεd ((pow_le_pow_of_le_one zero_le hρ.le (by omega)).trans_lt hr)))

  let NC : Finset (J → ℂ) := (S ∪ S').filter fun u => (∀ j ∈ L, u j ≠ 0) ∧ ∃ j, 1 ≤ ν (u j - s j)
  have hNC : ∀ u ∈ NC, ∃ j, 1 ≤ ν (u j - s j) := fun u hu => (Finset.mem_filter.1 hu).2.2
  choose! jn hjn using hNC
  have hNCint : ∀ u ∈ NC, ∀ j, ν (u j) ≤ 1 := by
    intro u hu j
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hu
    rcases Finset.mem_union.1 h1 with h | h
    · exact intV u h h2 j
    · exact intV' u h h2 j
  have hne : ∀ u ∈ NC, s (jn u) - u (jn u) ≠ 0 := by
    intro u hu h
    have := hjn u hu
    rw [Valuation.map_sub_swap, h, map_zero] at this
    exact absurd this (by simp)
  let Fl : List (ℂ × J × ℂ) := NC.toList.map fun v =>
    ((s (jn v) - v (jn v))⁻¹, jn v, -(v (jn v) * (s (jn v) - v (jn v))⁻¹))
  have hFl : ∀ f ∈ Fl, ν f.1 ≤ 1 ∧ ν f.2.2 ≤ 1 := by
    intro f hf
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hf
    have hv' := Finset.mem_toList.1 hv
    have h1 : ν (s (jn v) - v (jn v))⁻¹ ≤ 1 := by
      rw [map_inv₀, Valuation.map_sub_swap]; exact inv_le_one_of_one_le₀ (hjn v hv')
    refine ⟨h1, ?_⟩
    rw [Valuation.map_neg, Valuation.map_mul]
    calc ν (v (jn v)) * ν (s (jn v) - v (jn v))⁻¹ ≤ 1 * 1 := mul_le_mul' (hNCint v hv' _) h1
      _ = 1 := one_mul 1
  let G : (J → ℂ) → ℂ := fun u => (L.toList.map u).prod * (Fl.map fun f => f.1 * u f.2.1 + f.2.2).prod
  have hG0 : ∀ u ∈ S ∪ S', (∃ j, 1 ≤ ν (u j - s j)) → G u = 0 := by
    intro u hu hnc
    by_cases hI : ∀ j ∈ L, u j ≠ 0
    · have huNC : u ∈ NC := Finset.mem_filter.2 ⟨hu, hI, hnc⟩
      apply mul_eq_zero_of_right
      apply List.prod_eq_zero
      refine List.mem_map.2 ⟨((s (jn u) - u (jn u))⁻¹, jn u, -(u (jn u) * (s (jn u) - u (jn u))⁻¹)), ?_, ?_⟩
      · exact List.mem_map.2 ⟨u, Finset.mem_toList.2 huNC, rfl⟩
      · simp only; ring
    · push_neg at hI
      obtain ⟨j, hj, hj0⟩ := hI
      apply mul_eq_zero_of_left
      apply List.prod_eq_zero
      exact List.mem_map.2 ⟨j, Finset.mem_toList.2 hj, hj0⟩
  let Cinv : ℂ := (L.toList.map fun j => (s j)⁻¹).prod
  have hCinv : ν Cinv = 1 := by
    have : ∀ l' : List J, (∀ j ∈ l', j ∈ L) → ν (l'.map fun j => (s j)⁻¹).prod = 1 := by
      intro l' hl'
      induction l' with
      | nil => simp
      | cons j l' ih =>
        rw [List.map_cons, List.prod_cons, Valuation.map_mul, map_inv₀, hsL j (hl' j List.mem_cons_self),
          ih fun i hi => hl' i (List.mem_cons_of_mem _ hi)]
        simp
    exact this _ fun j hj => Finset.mem_toList.1 hj

  let cong : Finset (J → ℂ) := S.filter fun u => ∀ j, ν (u j - s j) < 1
  have hcong : ∀ u ∈ cong, ν (Cinv * G u - 1) < 1 := by
    intro u hu
    have hu' := (Finset.mem_filter.1 hu).2
    have e : Cinv * G u = ((L.toList.map fun j => u j * (s j)⁻¹) ++
        (Fl.map fun f => f.1 * u f.2.1 + f.2.2)).prod := by
      rw [List.prod_append, List.prod_map_mul]
      simp only [G, Cinv]; ring
    rw [e]
    apply prod_near_one
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      have hsj := hs0 j (Finset.mem_toList.1 hj)
      rw [show u j * (s j)⁻¹ - 1 = (u j - s j) * (s j)⁻¹ by field_simp, Valuation.map_mul, map_inv₀,
        hsL j (Finset.mem_toList.1 hj), inv_one, mul_one]
      exact hu' j
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hy
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hf
      have hv' := Finset.mem_toList.1 hv
      have hn0 := hne v hv'
      simp only
      rw [show (s (jn v) - v (jn v))⁻¹ * u (jn v) + -(v (jn v) * (s (jn v) - v (jn v))⁻¹) - 1 =
          (u (jn v) - s (jn v)) * (s (jn v) - v (jn v))⁻¹ by field_simp; ring]
      rw [Valuation.map_mul]
      have h1 : ν (s (jn v) - v (jn v))⁻¹ ≤ 1 := by
        rw [map_inv₀, Valuation.map_sub_swap]; exact inv_le_one_of_one_le₀ (hjn v hv')
      calc ν (u (jn v) - s (jn v)) * ν (s (jn v) - v (jn v))⁻¹ ≤ ν (u (jn v) - s (jn v)) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact hu' _
  set d : ℕ := ∑ u ∈ cong, m u with hd
  have hscong : s ∈ cong := Finset.mem_filter.2 ⟨hsS, fun j => by simp⟩
  have hd1 : 1 ≤ d := (hm s hsS).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hscong)
  have hd2 : d ≤ Module.finrank ℂ V := hmsum ▸ Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hεd := hε d hd1 hd2
  have hd0 : 0 < ν (d : ℂ) := lt_of_le_of_lt zero_le hεd

  let τ : ℝ≥0 := cong.sup fun u => ν (Cinv * G u - 1)
  have hτ : τ < 1 := by
    rw [Finset.sup_lt_iff zero_lt_one]
    exact hcong
  set θ : ℝ≥0 := max (max (ν (l : ℂ)) τ) ρ with hθdef
  have hθ : θ < 1 := max_lt (max_lt hνl hτ) hρ
  obtain ⟨a, ha⟩ := NNReal.exists_pow_lt_of_lt_one hd0 hθ
  set n : ℕ := l ^ a with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hl.ne_zero)

  have hbound : ν ((lam S (fun u => (m u : ℂ)) - lam S' (fun u => (m' u : ℂ))) fun u => G u ^ n) ≤ max ε (ρ ^ n) := by
    have key := factors ν (lam S (fun u => (m u : ℂ)) - lam S' (fun u => (m' u : ℂ)))
      (fun W => ∀ j ∈ L, n ≤ W.count j)
      (fun W j hW i hi => by rw [List.count_append]; have := hW i hi; omega) (max ε (ρ ^ n))
      (fun W hW' => by
        rw [LinearMap.sub_apply, lam_apply, lam_apply, ← htr W, ← htr' W]
        exact (hW W n hn1 hW').2.2)
      ((List.replicate n Fl).flatten) (by
        intro f hf
        obtain ⟨l', hl', hfl⟩ := List.mem_flatten.1 hf
        rw [List.eq_of_mem_replicate hl'] at hfl
        exact hFl f hfl)
      ((List.replicate n L.toList).flatten) (by
        intro j hj
        rw [count_rep]
        have : 1 ≤ L.toList.count j := List.count_pos_iff.2 (Finset.mem_toList.2 hj)
        nlinarith)
    convert key using 3
    funext u
    rw [prod_rep, prod_rep, mul_pow]

  have hval : Cinv ^ n * ((lam S (fun u => (m u : ℂ)) - lam S' (fun u => (m' u : ℂ))) fun u => G u ^ n) =
      (d : ℂ) + ∑ u ∈ cong, (m u : ℂ) * ((1 + (Cinv * G u - 1)) ^ n - 1) := by
    rw [LinearMap.sub_apply, lam_apply, lam_apply, mul_sub, Finset.mul_sum, Finset.mul_sum]
    have h2 : ∑ u ∈ S', Cinv ^ n * ((m' u : ℂ) * G u ^ n) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [hG0 u (Finset.mem_union_right _ hu) (hS'nc u hu), zero_pow (by omega)]
      ring
    have h1 : ∑ u ∈ S, Cinv ^ n * ((m u : ℂ) * G u ^ n) = ∑ u ∈ cong, (m u : ℂ) * (Cinv * G u) ^ n := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      split_ifs with hc
      · ring
      · push_neg at hc
        rw [hG0 u (Finset.mem_union_left _ hu) (by obtain ⟨j, hj⟩ := hc; exact ⟨j, hj⟩), zero_pow (by omega)]
        ring
    rw [h1, h2, sub_zero, hd]
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hsmall : ν (∑ u ∈ cong, (m u : ℂ) * ((1 + (Cinv * G u - 1)) ^ n - 1)) ≤ θ ^ a := by
    apply Valuation.map_sum_le
    intro u hu
    rw [Valuation.map_mul]
    have hx := hcong u hu
    have h1 := iter ν l hl hνl _ hx a
    have hle : ν (Cinv * G u - 1) ≤ τ := Finset.le_sup (f := fun u => ν (Cinv * G u - 1)) hu
    calc ν (m u : ℂ) * ν ((1 + (Cinv * G u - 1)) ^ n - 1)
        ≤ 1 * (max (ν (l : ℂ)) (ν (Cinv * G u - 1)) ^ a * 1) :=
          mul_le_mul' (nat_le_one ν _) (h1.trans (mul_le_mul' le_rfl hx.le))
      _ ≤ θ ^ a := by
          rw [one_mul, mul_one]
          exact pow_le_pow_left₀ zero_le ((max_le_max le_rfl hle).trans (le_max_left _ _)) a
  have hρn : ρ ^ n ≤ θ ^ a :=
    (pow_le_pow_of_le_one zero_le hρ.le (Nat.lt_pow_self hl.one_lt).le).trans
      (pow_le_pow_left₀ zero_le (le_max_right _ _) a)
  have hdeq : (d : ℂ) = Cinv ^ n * ((lam S (fun u => (m u : ℂ)) - lam S' (fun u => (m' u : ℂ))) fun u => G u ^ n) -
      ∑ u ∈ cong, (m u : ℂ) * ((1 + (Cinv * G u - 1)) ^ n - 1) := by
    rw [hval]; ring
  have hfin : ν (d : ℂ) ≤ max (max ε (ρ ^ n)) (θ ^ a) := by
    rw [hdeq]
    apply Valuation.map_sub_le
    · rw [Valuation.map_mul, Valuation.map_pow, hCinv, one_pow, one_mul]
      exact hbound.trans (le_max_left _ _)
    · exact hsmall.trans (le_max_right _ _)
  have : max (max ε (ρ ^ n)) (θ ^ a) < ν (d : ℂ) := max_lt (max_lt hεd (hρn.trans_lt ha)) ha
  exact absurd hfin (not_le.2 this)
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.UpperHalfPlaneCoordinatesProof
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.UpperHalfPlaneCoordinates

def Ψ (x y : ℝ) : ℂ := (y : ℂ) * (x + Complex.I)

theorem cont_Ψ : Continuous (fun p : ℝ × ℝ => Ψ p.1 p.2) := by
  unfold Ψ; fun_prop

theorem key (G : ℂ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, ∫⁻ y, ENNReal.ofReal (1 / |y|) * G (Ψ x y)
      = ∫⁻ z, ENNReal.ofReal (1 / z.im ^ 2) * G z := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (1 / |p.2|) * G (Ψ p.1 p.2)) := by
    refine Measurable.mul ?_ (hG.comp cont_Ψ.measurable)
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hF : Measurable (fun z : ℂ => ENNReal.ofReal (1 / z.im ^ 2) * G z) := by
    refine Measurable.mul ?_ hG
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hR : ∫⁻ z, ENNReal.ofReal (1 / z.im ^ 2) * G z
      = ∫⁻ y : ℝ, ∫⁻ u : ℝ, ENNReal.ofReal (1 / y ^ 2) * G ((u : ℂ) + y * Complex.I) := by
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _)]
    rw [Measure.volume_eq_prod, lintegral_prod_symm]
    · congr 1; funext y; congr 1; funext u
      simp only [Complex.measurableEquivRealProd]
      congr 2
      exact Complex.mk_eq_add_mul_I u y
    · exact (hF.comp (MeasurableEquiv.measurable _)).aemeasurable
  rw [hR]
  congr 1; funext y
  have hmx : Measurable (fun x : ℝ => G (Ψ x y)) :=
    hG.comp (cont_Ψ.comp (Continuous.prodMk continuous_id continuous_const)).measurable
  rw [lintegral_const_mul _ hmx]
  have hmu : Measurable (fun u : ℝ => G ((u : ℂ) + y * Complex.I)) :=
    hG.comp (by fun_prop : Continuous (fun u : ℝ => (u : ℂ) + y * Complex.I)).measurable
  rw [lintegral_const_mul _ hmu]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hsc : ∫⁻ x, G (Ψ x y) = ENNReal.ofReal |y⁻¹| * ∫⁻ u : ℝ, G ((u : ℂ) + y * Complex.I) := by
      calc ∫⁻ x, G (Ψ x y) = ∫⁻ x : ℝ, G (((y * x : ℝ) : ℂ) + y * Complex.I) := by
            congr 1; funext x; congr 1; simp only [Ψ]; push_cast; ring
        _ = ∫⁻ u : ℝ, G ((u : ℂ) + y * Complex.I) ∂(Measure.map (fun x => y * x) volume) :=
            (lintegral_map hmu (measurable_const_mul y)).symm
        _ = _ := by rw [Real.map_volume_mul_left hy, lintegral_smul_measure, smul_eq_mul]
    rw [hsc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    rw [show 1 / |y| * |y⁻¹| = 1 / y ^ 2 by
      rw [abs_inv, one_div, one_div, ← mul_inv, ← pow_two, sq_abs]]

def ν0 : Measure P := Measure.comap Subtype.val volume

theorem vol_eq : (volume : Measure P) = ν0.withDensity (fun z => ENNReal.ofReal (1 / z.1.im ^ 2)) := rfl

theorem hS : MeasurableSet {z : ℂ | z.im ≠ 0} :=
  (isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet

theorem cont_pt : Continuous (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) := by
  unfold pt
  exact Continuous.subtype_mk (by fun_prop) _

theorem meas_pres : MeasurePreserving (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2)
    ((volume : Measure ℝ).prod ((Measure.comap Subtype.val volume).withDensity
      fun y => ENNReal.ofReal (1 / |y.1|))) volume := by
  have hemb : MeasurableEmbedding (Subtype.val : P → ℂ) := MeasurableEmbedding.subtype_coe hS
  have hY : MeasurableSet {y : ℝ | y ≠ 0} := (measurableSet_singleton 0).compl
  have hembY : MeasurableEmbedding (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) := MeasurableEmbedding.subtype_coe hY
  have : SigmaFinite (Measure.comap (Subtype.val : {y : ℝ // y ≠ 0} → ℝ) volume) :=
    SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by rw [hembY.map_comap]; infer_instance)
  refine ⟨cont_pt.measurable, ?_⟩
  ext s hs
  set G : ℂ → ℝ≥0∞ := (Subtype.val '' s).indicator 1 with hGdef
  have hGm : Measurable G := measurable_one.indicator (hemb.measurableSet_image.2 hs)
  have hGv : ∀ z : P, G z.1 = s.indicator 1 z := by
    intro z
    have hz : z.1 ∈ Subtype.val '' s ↔ z ∈ s :=
      ⟨fun ⟨w, hw, e⟩ => (Subtype.ext e : w = z) ▸ hw, fun h => ⟨z, h, rfl⟩⟩
    rw [hGdef]
    by_cases h : z ∈ s
    · rw [Set.indicator_of_mem (hz.2 h), Set.indicator_of_mem h]; rfl
    · rw [Set.indicator_of_notMem (mt hz.1 h), Set.indicator_of_notMem h]
  rw [Measure.map_apply cont_pt.measurable hs, ← lintegral_indicator_one (cont_pt.measurable hs)]
  have e1 : ∀ p : ℝ × {y : ℝ // y ≠ 0},
      ((fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) ⁻¹' s).indicator 1 p = G (Ψ p.1 p.2.1) := by
    intro p
    rw [show Ψ p.1 p.2.1 = (pt p.1 p.2.1 p.2.2).1 from rfl, hGv]
    rfl
  simp_rw [e1]
  have hGΨ : Measurable (fun p : ℝ × {y : ℝ // y ≠ 0} => G (Ψ p.1 p.2.1)) :=
    hGm.comp (cont_Ψ.comp (Continuous.prodMk continuous_fst
      (continuous_subtype_val.comp continuous_snd))).measurable
  rw [lintegral_prod _ hGΨ.aemeasurable]
  have e2 : ∀ x : ℝ, ∫⁻ y, G (Ψ x y.1) ∂((Measure.comap Subtype.val volume).withDensity
      fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|))
      = ∫⁻ y, ENNReal.ofReal (1 / |y|) * G (Ψ x y) := by
    intro x
    have hd : Measurable (fun y : {y : ℝ // y ≠ 0} => ENNReal.ofReal (1 / |y.1|)) :=
      (by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (1 / |y|))).comp measurable_subtype_coe
    have hg : Measurable (fun y : {y : ℝ // y ≠ 0} => G (Ψ x y.1)) :=
      hGm.comp (cont_Ψ.comp (Continuous.prodMk continuous_const continuous_subtype_val)).measurable
    rw [lintegral_withDensity_eq_lintegral_mul _ hd hg]
    have := lintegral_subtype_comap (μ := (volume : Measure ℝ)) hY
      (fun y => ENNReal.ofReal (1 / |y|) * G (Ψ x y))
    rw [show ({y : ℝ | y ≠ 0} : Set ℝ) = {0}ᶜ from rfl, restrict_compl_singleton] at this
    exact this
  simp_rw [e2]
  rw [key G hGm]
  have hv : (volume : Measure P) s = ∫⁻ z : P, ENNReal.ofReal (1 / z.1.im ^ 2) * G z.1 ∂ν0 := by
    rw [vol_eq, withDensity_apply _ hs, ← lintegral_indicator hs]
    congr 1; funext z
    rw [hGv]; by_cases h : z ∈ s <;> simp [Set.indicator, h]
  have hv2 : ∫⁻ z : P, ENNReal.ofReal (1 / z.1.im ^ 2) * G z.1 ∂ν0
      = ∫⁻ z in {z : ℂ | z.im ≠ 0}, ENNReal.ofReal (1 / z.im ^ 2) * G z :=
    lintegral_subtype_comap hS (fun z => ENNReal.ofReal (1 / z.im ^ 2) * G z)
  rw [hv, hv2, ← lintegral_indicator hS]
  congr 1; funext z
  by_cases h : z.im ≠ 0
  · simp [Set.indicator, h]
  · simp [Set.indicator, not_not.1 h]

theorem bij : Function.Bijective (fun p : ℝ × {y : ℝ // y ≠ 0} => pt p.1 p.2.1 p.2.2) := by
  constructor
  · rintro ⟨x, y, hy⟩ ⟨x', y', hy'⟩ h
    have h' : (y : ℂ) * (x + Complex.I) = (y' : ℂ) * (x' + Complex.I) := congrArg Subtype.val h
    have him := congrArg Complex.im h'
    have hre := congrArg Complex.re h'
    simp at him hre
    subst him
    have : x = x' := mul_left_cancel₀ hy hre
    subst this; rfl
  · rintro ⟨z, hz⟩
    refine ⟨(z.re / z.im, ⟨z.im, hz⟩), ?_⟩
    apply Subtype.ext
    show (z.im : ℂ) * ((z.re / z.im : ℝ) + Complex.I) = z
    apply Complex.ext <;> simp; field_simp

end UpperTheory.Esk.UpperHalfPlaneCoordinates

theorem UpperTheory.Esk.upper_half_plane_measure_coordinates : UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates :=
  ⟨UpperTheory.Esk.UpperHalfPlaneCoordinates.meas_pres, UpperTheory.Esk.UpperHalfPlaneCoordinates.bij, UpperTheory.Esk.UpperHalfPlaneCoordinates.cont_pt⟩
end
end

namespace UpperTheory.Esk

theorem half_plane_measure_invariant_holds : B1a := half_plane_measure_invariant_proof
theorem automorphy_factor_kernel_algebra_holds : B1b := automorphy_factor_kernel_algebra_proof
theorem kernel_terms_invariant_bounded_holds : KernelTermsInvariantBounded := kernel_terms_invariant_bounded_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds
theorem heights_on_quotient_holds : E0d := heights_on_quotient_proof half_plane_measure_invariant_holds
theorem hyperbolic_kappa_properties_holds : B1c := hyperbolic_kappa_properties_proof
theorem actions_preserve_measures_holds : E0a := actions_preserve_measures_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds
theorem s_Pack : Pack := pf_Pack automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds actions_preserve_measures_holds
theorem s_Mult : Mult := pf_Mult automorphy_factor_kernel_algebra_holds heights_on_quotient_holds
theorem upper_half_plane_coordinates_holds : UpperHalfPlaneMeasureCoordinates := upper_half_plane_measure_coordinates
theorem hyperbolic_ball_volume_holds : B6 := hyperbolic_ball_volume_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds upper_half_plane_coordinates_holds
theorem s_KapInt : KapInt := pf_KapInt half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds hyperbolic_ball_volume_holds
theorem s_KapSum : KapSum := pf_KapSum s_Pack s_Mult s_KapInt
theorem kernel_sum_bounded_holds : E2 := kernel_sum_bounded_proof kernel_terms_invariant_bounded_holds heights_on_quotient_holds s_KapSum
theorem orbit_cover_holds : C2 := orbit_cover_proof
theorem s_Ecut : Ecut := pf_Ecut automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds orbit_cover_holds actions_preserve_measures_holds heights_on_quotient_holds s_KapSum
theorem forms_stable_under_operators_holds : FormsStableUnderOperators := forms_stable_under_operators_proof
theorem cusp_region_volume_finite_holds : E3 := cusp_region_volume_finite_proof half_plane_measure_invariant_holds upper_half_plane_coordinates_holds orbit_cover_holds actions_preserve_measures_holds heights_on_quotient_holds
theorem kernel_level_transform_holds : E4 := kernel_level_transform_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds heights_on_quotient_holds s_KapSum s_KapInt
theorem kernel_inverse_symmetry_holds : faceMap_zero_comp_eq_one := kernel_inverse_symmetry half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds actions_preserve_measures_holds heights_on_quotient_holds s_KapSum
theorem inverse_series_summable_holds : C3 := inverse_series_summable
theorem cayley_transform_holds : B2 := cayley_transform_proof
theorem reproducing_formula_holds_alt : B3 := reproducing_formula_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds cayley_transform_holds hyperbolic_ball_volume_holds
theorem multivariable_reproducing_formula_holds : MultivariableReproducingFormula := multivariable_reproducing_formula_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds reproducing_formula_holds_alt s_KapInt
theorem reproducing_kernel_expansion_holds : E5 := e5_of_reproducing_formula automorphy_factor_kernel_algebra_holds inverse_series_summable_holds actions_preserve_measures_holds kernel_inverse_symmetry_holds multivariable_reproducing_formula_holds
theorem s_LinTr : LinTr := pf_LinTr
theorem linear_trace_identity_holds : E6 := e6_of_linear_trace_identity actions_preserve_measures_holds forms_stable_under_operators_holds kernel_terms_invariant_bounded_holds cusp_region_volume_finite_holds kernel_level_transform_holds kernel_inverse_symmetry_holds reproducing_kernel_expansion_holds s_LinTr
theorem action_integral_swap_holds : C1 := action_integral_swap_proof
theorem counting_measure_invariance_holds : C4 := counting_measure_invariance_proof action_integral_swap_holds
theorem kernel_series_converges_holds : E1 := kernel_series_converges_proof automorphy_factor_kernel_algebra_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds s_Pack s_Mult s_KapInt
theorem s_Fsum : Fsum := pf_Fsum actions_preserve_measures_holds
theorem diagonal_integrand_vanishes_holds : DiagonalIntegrandVanishes := diagonal_integrand_vanishes_proof
theorem s_Fcen : Fcen := pf_Fcen
theorem diagonal_terms_contribution_holds : F2 := diagonal_terms_contribution_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds upper_half_plane_coordinates_holds diagonal_integrand_vanishes_holds action_integral_swap_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds s_Ecut s_Fcen
theorem radial_integral_formula_holds : B4 := radial_integral_formula_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds cayley_transform_holds hyperbolic_ball_volume_holds
theorem elliptic_terms_contribution_holds : F3 := elliptic_terms_contribution_proof half_plane_measure_invariant_holds automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds radial_integral_formula_holds action_integral_swap_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds s_Mult s_Fcen
theorem imaginary_part_bound_holds : F4 := imaginary_part_bound_proof automorphy_factor_kernel_algebra_holds hyperbolic_kappa_properties_holds heights_on_quotient_holds s_Mult
theorem s_Fell : Fell := pf_Fell counting_measure_invariance_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds kernel_series_converges_holds cusp_region_volume_finite_holds s_Ecut s_Fsum diagonal_terms_contribution_holds elliptic_terms_contribution_holds imaginary_part_bound_holds
theorem kernel_trace_bound_holds : F5 := kernel_trace_bound_proof heights_on_quotient_holds kernel_series_converges_holds
theorem unipotent_integrand_vanishes_holds : ConstantTermVanishingAlt := unipotent_integrand_vanishes_proof half_plane_measure_invariant_holds upper_half_plane_coordinates_holds
theorem unipotent_truncated_integral_holds : DiagonalTruncatedIntegralZero := diagonal_truncated_integral_zero half_plane_measure_invariant_holds upper_half_plane_coordinates_holds diagonal_integrand_vanishes_holds action_integral_swap_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds s_Ecut s_Fcen unipotent_integrand_vanishes_holds
theorem unipotent_terms_contribution_holds : F6 := unipotent_terms_contribution_proof action_integral_swap_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds unipotent_truncated_integral_holds
theorem s_Fhyp : Fhyp := pf_Fhyp counting_measure_invariance_holds actions_preserve_measures_holds kernel_terms_invariant_bounded_holds heights_on_quotient_holds kernel_sum_bounded_holds cusp_region_volume_finite_holds s_Ecut s_Fsum kernel_trace_bound_holds unipotent_terms_contribution_holds
theorem s_TF : TF := pf_TF kernel_sum_bounded_holds s_Ecut linear_trace_identity_holds s_Fell s_Fhyp
theorem s_Sys : Sys := pf_Sys
theorem finite_system_holds : Fin0 := finite_system_proof s_Sys
theorem s_Osg : Osg := pf_Osg

end UpperTheory.Esk
