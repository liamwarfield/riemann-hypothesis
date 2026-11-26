module

public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix
public import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
open Complex ComplexConjugate Filter Topology Matrix

namespace ReciprocityTheory.L2DbarEstimates

noncomputable def wJac (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) : Matrix (Fin p) (Fin n) ℂ :=
  fun i k => wd n k (g i) x

def LeviLogNormSqStatement : Prop :=
  ∀ (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) (ξ : Fin n → ℂ),
    (∀ i, ContDiffAt ℂ 2 (g i) x) → (fun i => g i x) ≠ 0 →
    leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((sqNorm (projPerp (fun i => g i x) *ᵥ (wJac n p g x *ᵥ ξ)) / sqNorm (fun i => g i x) : ℝ) : ℂ)

variable {n : ℕ}

theorem contDiffAt_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by
  have h1 : ContDiffAt ℝ 2 g x := hg.restrict_scalars ℝ
  have h2 : (fun y => Complex.normSq (g y)) = fun y => ‖g y‖ ^ 2 :=
    funext fun y => Complex.normSq_eq_norm_sq _
  rw [h2]
  exact h1.norm_sq ℝ

theorem wd_normSq_comp {j : Fin n} {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    wd n j (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x = wd n j g x * conj (g x) := by
  have hgC : DifferentiableAt ℂ g x := hg.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := hgC.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun y => conj (g y)) x := Complex.conjCLE.differentiableAt.comp x hgR
  rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
    funext fun y => (Complex.mul_conj (g y)).symm, wd_mul hgR hc, wd_conj hgR,
    wdb_of_differentiableAt hgC, map_zero, mul_zero, add_zero]

theorem leviV_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
  have hcd : ∀ {f : V n → ℂ} {y : V n}, DifferentiableAt ℝ f y →
      DifferentiableAt ℝ (fun z => conj (f z)) y :=
    fun h => Complex.conjCLE.differentiableAt.comp _ h
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ 2 g y := hg.eventually (by simp)
  have hdC : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    hev.mono fun y hy => hy.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := (hg.differentiableAt (by norm_num)).restrictScalars ℝ

  have hwdk : ∀ k, wd n k g =ᶠ[𝓝 x] fun y => fderiv ℂ g y (bas n k) :=
    fun k => hdC.mono fun y hy => wd_of_differentiableAt hy
  have hfd : ∀ k, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x := by
    intro k
    have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
    exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hwdbwd : ∀ j k, wdb n j (wd n k g) x = 0 :=
    fun j k => (wdb_congr (hwdk k)).trans (wdb_of_differentiableAt (hfd k))
  have hwdR : ∀ k, DifferentiableAt ℝ (wd n k g) x :=
    fun k => ((hfd k).restrictScalars ℝ).congr_of_eventuallyEq (hwdk k)
  have hwdbf : ∀ k, wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => g y * conj (wd n k g y) := by
    intro k
    filter_upwards [hev] with y hy
    have hyC : DifferentiableAt ℂ g y := hy.differentiableAt (by norm_num)
    have hyR : DifferentiableAt ℝ g y := hyC.restrictScalars ℝ
    rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
      funext fun y => (Complex.mul_conj (g y)).symm, wdb_mul hyR (hcd hyR), wdb_conj hyR,
      wdb_of_differentiableAt hyC, zero_mul, zero_add]
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n k g x) := by
    intro j k
    rw [wd_congr (hwdbf k), wd_mul hgR (hcd (hwdR k)), wd_conj (hwdR k), hwdbwd j k, map_zero,
      mul_zero, add_zero]
  unfold leviV
  simp_rw [hterm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  ring

theorem leviLogNormSq : LeviLogNormSqStatement := by
  intro n p g x ξ hg hG
  set G : Fin p → ℂ := fun i => g i x with hGdef
  have hpos : 0 < sqNorm G := sqNorm_pos hG
  have hne : ((sqNorm G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hv : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x := by
    unfold sqNorm
    exact ContDiffAt.sum fun i _ => contDiffAt_normSq_comp (hg i)
  have hk : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x)) := Real.contDiffAt_log.mpr hpos.ne'
  have hc : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((deriv Real.log (sqNorm G) : ℝ) : ℂ) *
          leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ +
        ((deriv (deriv Real.log) (sqNorm G) : ℝ) : ℂ) *
          ((Complex.normSq (∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j) :
            ℝ) : ℂ) :=
    leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hv hk
  have hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
      ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ) := by
    have h1 : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
        ∑ i, leviV n (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x ξ :=
      leviV_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => contDiffAt_normSq_comp (hg i)) ξ
    rw [h1, sqNorm, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ
  have hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
      ∑ i, wd n j (g i) x * conj (g i x) := by
    intro j
    have h1 : wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
        ∑ i, wd n j (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x :=
      wd_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => (contDiffAt_normSq_comp (hg i)).differentiableAt (by norm_num))
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)
  have hS : ∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j =
      star G ⬝ᵥ (wJac n p g x *ᵥ ξ) := by
    simp only [hwd, dotProduct, Matrix.mulVec, wJac, Pi.star_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hGdef, Complex.star_def]
    ring
  rw [hc, hlv, hS, projPerp_sqNorm p G _ hG, Real.deriv_log, Real.deriv_log', deriv_inv]
  push_cast
  field_simp
  ring

end ReciprocityTheory.L2DbarEstimates
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.Cutoff
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

namespace SmoothCutoff

noncomputable def bump (s : ℝ) : ℝ :=
  Real.smoothTransition (20 * (s - 1 / 2)) * Real.smoothTransition (20 * (1 - s))

theorem bump_contDiff : ContDiff ℝ ∞ bump := by
  unfold bump
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

theorem bump_continuous : Continuous bump := bump_contDiff.continuous

theorem bump_nonneg (s : ℝ) : 0 ≤ bump s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem bump_le_one (s : ℝ) : bump s ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem bump_of_le_half {s : ℝ} (h : s ≤ 1 / 2) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem bump_of_one_le {s : ℝ} (h : 1 ≤ s) : bump s = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (x := 20 * (1 - s)) (by linarith), mul_zero]

theorem bump_of_mem {s : ℝ} (h1 : 11 / 20 ≤ s) (h2 : s ≤ 19 / 20) : bump s = 1 := by
  unfold bump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

noncomputable def prim (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, bump s

theorem prim_hasDerivAt (t : ℝ) : HasDerivAt prim (bump t) t :=
  (bump_continuous.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem deriv_prim : deriv prim = bump := funext fun t => (prim_hasDerivAt t).deriv

theorem prim_contDiff : ContDiff ℝ ∞ prim :=
  contDiff_infty_iff_deriv.2
    ⟨fun t => (prim_hasDerivAt t).differentiableAt, by rw [deriv_prim]; exact bump_contDiff⟩

theorem prim_monotone : Monotone prim :=
  monotone_of_deriv_nonneg (fun t => (prim_hasDerivAt t).differentiableAt)
    (fun t => by rw [deriv_prim]; exact bump_nonneg t)

theorem prim_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : prim t = 0 := by
  unfold prim
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro s hs
  apply bump_of_le_half
  have := (Set.mem_uIcc.1 hs)
  rcases this with h | h <;> linarith [h.1, h.2]

theorem prim_of_one_le {t : ℝ} (ht : 1 ≤ t) : prim t = prim 1 := by
  unfold prim
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (bump_continuous.intervalIntegrable _ _) (bump_continuous.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_congr (a := 1) (b := t) (g := fun _ => (0 : ℝ)),
    intervalIntegral.integral_zero, add_zero]
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  exact bump_of_one_le hs.1

theorem prim_one_ge : 2 / 5 ≤ prim 1 := by
  unfold prim
  have hi : ∀ a b : ℝ, IntervalIntegrable bump volume a b :=
    fun a b => bump_continuous.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 19 / 20) (hi _ _) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 11 / 20) (hi _ _) (hi _ _)]
  have h1 : 0 ≤ ∫ s in (0 : ℝ)..11 / 20, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h3 : 0 ≤ ∫ s in (19 / 20 : ℝ)..1, bump s :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => bump_nonneg s)
  have h2 : ∫ s in (11 / 20 : ℝ)..19 / 20, bump s = 2 / 5 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
    · simp; norm_num
    · intro s hs
      rw [Set.uIcc_of_le (by norm_num)] at hs
      exact bump_of_mem hs.1 hs.2
  linarith

theorem prim_nonneg (t : ℝ) : 0 ≤ prim t := by
  have := prim_monotone (min_le_left t (1 / 2))
  rwa [prim_of_le_half (min_le_right t (1 / 2))] at this

theorem prim_le (t : ℝ) : prim t ≤ prim 1 := by
  have := prim_monotone (le_max_left t 1)
  rwa [prim_of_one_le (le_max_right t 1)] at this

noncomputable def chi (t : ℝ) : ℝ := 1 - prim t / prim 1

theorem chi_hasDerivAt (t : ℝ) : HasDerivAt chi (-(bump t / prim 1)) t :=
  ((prim_hasDerivAt t).div_const (prim 1)).const_sub 1

theorem isCutoff_chi : IsCutoff chi := by
  have hI : 0 < prim 1 := by linarith [prim_one_ge]
  refine ⟨contDiff_const.sub (prim_contDiff.div_const _), ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp [chi, prim_of_le_half ht]
  · intro t ht
    simp [chi, prim_of_one_le ht, hI.ne']
  · intro t
    have h0 : 0 ≤ prim t / prim 1 := div_nonneg (prim_nonneg t) hI.le
    have h1 : prim t / prim 1 ≤ 1 := (div_le_one hI).2 (prim_le t)
    constructor <;> simp only [chi] <;> linarith
  · intro t
    rw [(chi_hasDerivAt t).deriv, abs_neg, abs_of_nonneg (div_nonneg (bump_nonneg t) hI.le),
      div_le_iff₀ hI]
    nlinarith [bump_le_one t, prim_one_ge]

end SmoothCutoff

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.HoloClosedNeed
namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Filter Topology
open scoped ENNReal

def HoloClosedNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (F : ℕ → M → ℂ) (f : M → ℂ),
    SmoothR n X.z ps → (∀ k, Holo n X.z (F k)) → Measurable f →
    Tendsto (fun k => wint n X.z (fun x => F k x - f x) ps) atTop (𝓝 0) →
    ∃ G : M → ℂ, Holo n X.z G ∧ f =ᵐ[vol n X.z] G

def EvalNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (x0 : M), SmoothR n X.z ps →
    ∃ C : ℝ, ∀ F : M → ℂ, Holo n X.z F →
      ENNReal.ofReal (‖F x0‖ ^ 2) ≤ ENNReal.ofReal C * wint n X.z F ps

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.CovDet
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem covDet (n : ℕ) (f' : V n →L[ℂ] V n) :
    |(f'.restrictScalars ℝ : V n →L[ℝ] V n).det| =
      ‖LinearMap.det (f' : V n →ₗ[ℂ] V n)‖ ^ 2 := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

theorem cov (n : ℕ) : CovStatement n := by
  intro W G f hW hG hinj _
  have hd : ∀ y ∈ W, HasFDerivWithinAt G ((fderiv ℂ G y).restrictScalars ℝ) W y := fun y hy =>
    (((hG y hy).differentiableAt (hW.mem_nhds hy)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hW.measurableSet hd hinj f]
  simp only [covDet]

end ReciprocityTheory.L2DbarEstimates.I
end

section -- merged from ReciprocityTheory.L2DbarEstimates.LeviForms.Vanish
universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem vanish_lintegral_ball_smul (n : ℕ) (F : V n → ℝ≥0∞) (hF : Measurable F) {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∫⁻ y in ball (0 : V n) 1, F (ρ • y) =
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| * ∫⁻ y in ball (0 : V n) ρ, F y := by
  have hind : ∀ y : V n, (ball (0 : V n) 1).indicator (fun y => F (ρ • y)) y =
      (ball (0 : V n) ρ).indicator F (ρ • y) := by
    intro y
    have hm : ρ • y ∈ ball (0 : V n) ρ ↔ y ∈ ball (0 : V n) 1 := by
      simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
      exact mul_lt_iff_lt_one_right hρ
    by_cases h : y ∈ ball (0 : V n) 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.mp h'))]
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  simp_rw [hind]
  have hFm : Measurable ((ball (0 : V n) ρ).indicator F) := hF.indicator measurableSet_ball
  rw [← lintegral_map hFm (measurable_const_smul ρ), Measure.map_addHaar_smul _ hρ.ne',
    lintegral_smul_measure, smul_eq_mul]

theorem vanish_div (n : ℕ) (hn : 1 ≤ n) (hDiv : C.MVDivStatement) {ρ c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝[>] 0)) :
    Tendsto (fun k => ∫⁻ y in ball (0 : V n) ρ,
      ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ)))) atTop (𝓝 ∞) := by
  have hn0 : 0 < n := hn
  have hcr : 0 < c * ρ ^ 2 := by positivity
  obtain ⟨hδ0, hδpos⟩ := tendsto_nhdsWithin_iff.mp hδ
  have hη : Tendsto (fun k => δ k / (c * ρ ^ 2)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using hδ0.div_const (c * ρ ^ 2)
    · exact hδpos.mono fun k hk => div_pos hk hcr
  have hΦ := (hDiv n hn0).comp hη
  set K : ℝ≥0∞ := ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
    ENNReal.ofReal ((c * ρ ^ 2) ^ (-(n : ℝ))) with hK
  have hK0 : K ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr (by positivity)).ne' (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hlim := ENNReal.Tendsto.const_mul (a := K) hΦ (Or.inl ENNReal.top_ne_zero)
  rw [ENNReal.mul_top hK0] at hlim
  refine hlim.congr' ?_
  filter_upwards [hδpos] with k hk
  have hk' : 0 < δ k := hk
  have hG : Measurable fun y : V n => ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    fun_prop
  have hs := vanish_lintegral_ball_smul n _ hG hρ
  have hd : ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
      ENNReal.ofReal |(ρ ^ Module.finrank ℝ (V n))⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
      mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one]
  have hrhs : ∫⁻ y in ball (0 : V n) ρ, ENNReal.ofReal ((c * ‖y‖ ^ 2 + δ k) ^ (-(n : ℝ))) =
      ENNReal.ofReal (ρ ^ Module.finrank ℝ (V n)) *
        ∫⁻ y in ball (0 : V n) 1, ENNReal.ofReal ((c * ‖ρ • y‖ ^ 2 + δ k) ^ (-(n : ℝ))) := by
    rw [hs, ← mul_assoc, hd, one_mul]
  show K * _ = _
  rw [hrhs, hK, mul_assoc]
  congr 1
  simp only [Function.comp_apply]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr (fun z => ?_)
  have hz : 0 ≤ ‖z‖ ^ 2 + δ k / (c * ρ ^ 2) := by positivity
  rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hcr.le hz]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  field_simp

end ReciprocityTheory.L2DbarEstimates.I
end
