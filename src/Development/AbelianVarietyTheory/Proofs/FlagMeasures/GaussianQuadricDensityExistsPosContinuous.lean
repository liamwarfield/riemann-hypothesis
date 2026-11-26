module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlows
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecSmoothAtGapOfDecSmooth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuous
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean

noncomputable section

namespace GlobalTheory.GaussMean.Density

theorem integral_norm_sq (f : ℝ → ℝ) :
    ∫ z : ℂ, f (‖z‖ ^ 2) = Real.pi * ∫ r in Set.Ioi (0 : ℝ), f r := by
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) (fun r => f (r ^ 2)),
    ← integral_comp_rpow_Ioi f (p := 2) two_ne_zero]
  have : ∫ x in Set.Ioi (0 : ℝ), (|(2 : ℝ)| * x ^ ((2 : ℝ) - 1)) • f (x ^ (2 : ℝ)) =
      2 * ∫ y in Set.Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • f (y ^ 2) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    norm_num [mul_assoc]
  rw [this]
  simp [Measure.real, Complex.volume_ball]
  ring

def expAvg (G : ℝ → ℝ) (σ t : ℝ) : ℝ := ∫ r in Set.Ioi (0 : ℝ), Real.exp (-r) * G (t - σ * r)

theorem hasDerivAt_expAvg_one {G : ℝ → ℝ} (hm : Measurable G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) {t : ℝ}
    (hc : ContinuousAt G t) : HasDerivAt (expAvg G 1) (G t - expAvg G 1 t) t := by
  have hint : ∀ s : ℝ, IntegrableOn (fun u => Real.exp u * G u) (Set.Iic s) := fun s =>
    (integrableOn_exp_Iic s).mul_bdd hm.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hE : ∀ s : ℝ, expAvg G 1 s = Real.exp (-s) * ∫ u in Set.Iic s, Real.exp u * G u := by
    intro s
    have h1 := integral_comp_neg_Iic s (fun x => Real.exp (-x) * G (-x))
    have h2 := integral_sub_right_eq_self
      ((Set.Ioi (-s)).indicator fun x => Real.exp (-x) * G (-x)) s (μ := volume)
    simp only [neg_neg] at h1
    rw [h1, ← integral_indicator measurableSet_Ioi, ← h2, ← integral_const_mul, expAvg,
      ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : x - s ∈ Set.Ioi (-s) ↔ x ∈ Set.Ioi 0 := by
      simp only [Set.mem_Ioi]; constructor <;> intro h <;> linarith
    simp only [Set.indicator, this]
    split_ifs
    · rw [← mul_assoc, ← Real.exp_add]; congr 2 <;> ring
    · simp
  have hI : HasDerivAt (fun s => ∫ u in Set.Iic s, Real.exp u * G u) (Real.exp t * G t) t := by
    have h1 : (fun s => ∫ u in Set.Iic s, Real.exp u * G u) =
        fun s => (∫ u in Set.Iic t, Real.exp u * G u) + ∫ u in t..s, Real.exp u * G u := by
      funext s
      rw [← intervalIntegral.integral_Iic_sub_Iic (hint t) (hint s)]; ring
    rw [h1]
    refine HasDerivAt.const_add _ (intervalIntegral.integral_hasDerivAt_right (by simp) ?_ ?_)
    · exact (Real.measurable_exp.mul hm).stronglyMeasurable.stronglyMeasurableAtFilter
    · exact Real.continuous_exp.continuousAt.mul hc
  have h := ((hasDerivAt_id t).neg.exp).mul hI
  rw [funext hE]
  refine HasDerivAt.congr_deriv h ?_
  simp only [Pi.neg_apply, id]
  rw [← mul_assoc, ← Real.exp_add]; simp; ring

theorem hasDerivAt_expAvg {G : ℝ → ℝ} (hm : Measurable G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) (s : Bool) {t : ℝ}
    (hc : ContinuousAt G t) :
    HasDerivAt (expAvg G (sgn ℝ s)) (sgn ℝ s * (G t - expAvg G (sgn ℝ s) t)) t := by
  cases s
  · have h1 : ∀ u, expAvg G (-1) u = expAvg (fun x => G (-x)) 1 (-u) := by
      intro u; unfold expAvg; congr 1; funext r; congr 2; ring
    have hc' : ContinuousAt (fun x => G (-x)) (-t) :=
      ContinuousAt.comp (f := fun x : ℝ => -x) (by simpa using hc) continuous_neg.continuousAt
    have h := (hasDerivAt_expAvg_one (G := fun x => G (-x)) (hm.comp measurable_neg) (fun u => hb _) hc').comp t
      (hasDerivAt_neg t)
    have hs : sgn ℝ false = -1 := by simp [sgn]
    rw [hs, funext h1]
    refine HasDerivAt.congr_deriv h ?_
    simp
  · have hs : sgn ℝ true = 1 := by simp [sgn]
    rw [hs, one_mul]
    exact hasDerivAt_expAvg_one hm hb hc

theorem expAvg_pos {G : ℝ → ℝ} (hm : Monotone G) {C : ℝ} (hb : ∀ u, |G u| ≤ C) (s : Bool)
    (h : G (-1) < G 1) : 0 < sgn ℝ s * (G (sgn ℝ s) - expAvg G (sgn ℝ s) (sgn ℝ s)) := by
  set σ := sgn ℝ s with hσ
  have he : IntegrableOn (fun r => Real.exp (-r)) (Set.Ioi (0 : ℝ)) := integrableOn_exp_neg_Ioi 0
  have h1 : IntegrableOn (fun r => Real.exp (-r) * G (σ - σ * r)) (Set.Ioi (0 : ℝ)) :=
    he.mul_bdd (hm.measurable.comp (by fun_prop)).aestronglyMeasurable (Filter.Eventually.of_forall fun _ => hb _)
  have h2 : σ * (G σ - expAvg G σ σ) =
      ∫ r in Set.Ioi (0 : ℝ), σ * (Real.exp (-r) * G σ - Real.exp (-r) * G (σ - σ * r)) := by
    rw [integral_const_mul, integral_sub (he.mul_const _) h1, integral_mul_const, integral_exp_neg_Ioi_zero,
      one_mul, expAvg]
  have hle : ∀ r, 0 ≤ r → 0 ≤ σ * (G σ - G (σ - σ * r)) := by
    intro r hr
    cases s
    · have : σ = -1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (-1 : ℝ) ≤ -1 - -1 * r by linarith)
      linarith
    · have : σ = 1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) - 1 * r ≤ 1 by linarith)
      linarith
  have hlt : ∀ r, 2 < r → 0 < σ * (G σ - G (σ - σ * r)) := by
    intro r hr
    cases s
    · have : σ = -1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) ≤ -1 - -1 * r by linarith)
      linarith
    · have : σ = 1 := by simp [hσ, sgn]
      rw [this]
      have := hm (show (1 : ℝ) - 1 * r ≤ -1 by linarith)
      linarith
  have e : ∀ r, σ * (Real.exp (-r) * G σ - Real.exp (-r) * G (σ - σ * r)) =
      Real.exp (-r) * (σ * (G σ - G (σ - σ * r))) := fun r => by ring
  rw [h2, setIntegral_pos_iff_support_of_nonneg_ae]
  · refine lt_of_lt_of_le (show 0 < volume (Set.Ioi (2 : ℝ)) by simp) (measure_mono fun r hr => ⟨?_, ?_⟩)
    · rw [Function.mem_support, e]
      exact (mul_pos (Real.exp_pos _) (hlt r hr)).ne'
    · exact (lt_trans two_pos (show (2 : ℝ) < r from hr) : (0 : ℝ) < r)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [e]
    exact mul_nonneg (Real.exp_pos _).le (hle r (le_of_lt hr))
  · exact ((he.mul_const _).sub h1).const_mul _

def cdf {n : ℕ} (ε : Fin n → Bool) (t : ℝ) : ℝ := ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y

theorem continuous_qEps {n : ℕ} (ε : Fin n → Bool) : Continuous (qEps ε) := by
  unfold qEps; fun_prop

theorem measurableSet_qEps {n : ℕ} (ε : Fin n → Bool) (t : ℝ) :
    MeasurableSet {y : Fin n → ℂ | qEps ε y ≤ t} :=
  measurableSet_le (continuous_qEps ε).measurable measurable_const

theorem integrable_gauss (n : ℕ) : Integrable (gauss : (Fin n → ℂ) → ℝ) := by
  have h1 : Integrable fun z : ℂ => Real.exp (-‖z‖ ^ 2) := by
    have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp) 0 0).norm
    refine h.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Complex.norm_exp, ← Complex.ofReal_pow]
  have h2 := Integrable.fintype_prod (ι := Fin n) (f := fun _ (z : ℂ) => Real.exp (-‖z‖ ^ 2)) fun _ => h1
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [gauss, ← Real.exp_sum, Finset.sum_neg_distrib]

theorem cdf_mono {n : ℕ} (ε : Fin n → Bool) : Monotone (cdf ε) := fun _ _ h =>
  setIntegral_mono_set (integrable_gauss n).integrableOn
    (Filter.Eventually.of_forall fun y => (gauss_pos y).le)
    (Filter.EventuallySubset.of_subset fun _ hy => le_trans hy h)

theorem abs_cdf_le {n : ℕ} (ε : Fin n → Bool) (t : ℝ) : |cdf ε t| ≤ ∫ y : Fin n → ℂ, gauss y := by
  rw [abs_of_nonneg (show 0 ≤ cdf ε t from integral_nonneg fun y => (gauss_pos y).le)]
  exact setIntegral_le_integral (integrable_gauss n) (Filter.Eventually.of_forall fun y => (gauss_pos y).le)

theorem cdf_lt {n : ℕ} (ε : Fin n → Bool) : cdf ε (-1) < cdf ε 1 := by
  have h := setIntegral_sdiff (measurableSet_qEps ε (-1))
    ((integrable_gauss n).integrableOn (s := {y | qEps ε y ≤ 1}))
    (fun y (hy : qEps ε y ≤ -1) => show qEps ε y ≤ 1 by linarith)
  rw [← sub_pos, cdf, cdf, ← h, setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => (gauss_pos y).le) (integrable_gauss n).integrableOn]
  have ho : IsOpen (qEps ε ⁻¹' Set.Ioo (-1) 1) := isOpen_Ioo.preimage (continuous_qEps ε)
  refine lt_of_lt_of_le (ho.measure_pos volume ⟨0, by simp [qEps]⟩) (measure_mono fun y hy => ⟨?_, ?_, ?_⟩)
  · exact (gauss_pos y).ne'
  · exact hy.2.le
  · exact not_le.2 hy.1

theorem cdf_succ {n : ℕ} (ε : Fin (n + 1) → Bool) (a : Fin (n + 1)) (t : ℝ) :
    cdf ε t = Real.pi * expAvg (cdf fun i => ε (a.succAbove i)) (sgn ℝ (ε a)) t := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) a).symm
  have hi := (integrable_gauss (n + 1)).indicator (measurableSet_qEps ε t)
  have hi' := (hp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hi
  rw [cdf, ← integral_indicator (measurableSet_qEps ε t), ← hp.integral_comp', expAvg,
    ← integral_norm_sq fun r => Real.exp (-r) * cdf (fun i => ε (a.succAbove i)) (t - sgn ℝ (ε a) * r)]
  refine (integral_prod _ hi').trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [cdf]
  rw [← integral_indicator (measurableSet_qEps _ _), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp, Set.indicator, Set.mem_ofPred_eq, qEps, gauss, Fin.sum_univ_succAbove _ a,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove, sgn, le_sub_iff_add_le']
  split_ifs <;> simp [Real.exp_add, mul_comm]

theorem hasDerivAt_cdf_succ {n : ℕ} (ε : Fin (n + 1) → Bool) (a : Fin (n + 1)) {t : ℝ}
    (hc : ContinuousAt (cdf fun i => ε (a.succAbove i)) t) :
    HasDerivAt (cdf ε) (Real.pi * (sgn ℝ (ε a) * (cdf (fun i => ε (a.succAbove i)) t -
      expAvg (cdf fun i => ε (a.succAbove i)) (sgn ℝ (ε a)) t))) t := by
  rw [funext (cdf_succ ε a)]
  exact (hasDerivAt_expAvg (cdf_mono _).measurable (abs_cdf_le _) (ε a) hc).const_mul _

theorem cdf_zero_eventually (ε : Fin 0 → Bool) {t : ℝ} (ht : t ≠ 0) : cdf ε =ᶠ[nhds t] fun _ => cdf ε t := by
  rcases ht.lt_or_gt with h | h
  · filter_upwards [Iio_mem_nhds h] with u (hu : u < 0)
    simp [cdf, qEps, not_le.2 h, not_le.2 hu]
  · filter_upwards [Ioi_mem_nhds h] with u (hu : 0 < u)
    simp [cdf, qEps, h.le, hu.le]

theorem differentiableAt_cdf : ∀ {n : ℕ} (ε : Fin n → Bool) {t : ℝ}, t ≠ 0 → DifferentiableAt ℝ (cdf ε) t
  | 0, ε, _, ht => (differentiableAt_const _).congr_of_eventuallyEq (cdf_zero_eventually ε ht)
  | _ + 1, ε, _, ht => (hasDerivAt_cdf_succ ε 0 (differentiableAt_cdf _ ht).continuousAt).differentiableAt

theorem continuousOn_gaussDens : ∀ {n : ℕ} (ε : Fin n → Bool), ContinuousOn (gaussDens ε) {β | β ≠ 0}
  | 0, ε => (continuousOn_const (c := (0 : ℝ))).congr fun t ht => by
      show deriv (cdf ε) t = 0
      rw [(cdf_zero_eventually ε ht).deriv_eq]; simp
  | n + 1, ε => by
      have hc : ∀ t : ℝ, t ≠ 0 → ContinuousAt (cdf fun i => ε ((0 : Fin (n + 1)).succAbove i)) t :=
        fun t ht => (differentiableAt_cdf _ ht).continuousAt
      refine ContinuousOn.congr (f := fun t => Real.pi * (sgn ℝ (ε 0) *
        (cdf (fun i => ε ((0 : Fin (n + 1)).succAbove i)) t -
          expAvg (cdf fun i => ε ((0 : Fin (n + 1)).succAbove i)) (sgn ℝ (ε 0)) t))) ?_ ?_
      · intro t ht
        exact (continuousAt_const.mul (continuousAt_const.mul ((hc t ht).sub
          (hasDerivAt_expAvg (cdf_mono _).measurable (abs_cdf_le _) (ε 0) (hc t ht)).continuousAt))).continuousWithinAt
      · intro t ht
        exact (hasDerivAt_cdf_succ ε 0 (hc t ht)).deriv

theorem gaussDens_spec (n : ℕ) (ε : Fin n → Bool) :
    (∀ β : ℝ, β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) (gaussDens ε β) β ∧
      0 ≤ gaussDens ε β) ∧ ContinuousOn (gaussDens ε) {β | β ≠ 0} ∧
      ∀ s : Bool, (∃ a, ε a = s) → 0 < gaussDens ε (sgn ℝ s) := by
  refine ⟨fun β hβ => ⟨(differentiableAt_cdf ε hβ).hasDerivAt, (cdf_mono ε).deriv_nonneg⟩,
    continuousOn_gaussDens ε, ?_⟩
  rintro s ⟨a, rfl⟩
  obtain _ | n := n
  · exact a.elim0
  have hs : sgn ℝ (ε a) ≠ 0 := by unfold sgn; split_ifs <;> simp
  show 0 < deriv (cdf ε) _
  rw [(hasDerivAt_cdf_succ ε a (differentiableAt_cdf _ hs).continuousAt).deriv]
  exact mul_pos Real.pi_pos (expAvg_pos (cdf_mono _) (abs_cdf_le _) _ (cdf_lt _))

end GlobalTheory.GaussMean.Density
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaussianQuadricDensityExistsPosContinuousStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianQuadricDensity_exists_pos_continuous : ∀ (n : ℕ) (ε : Fin n → Bool), (∀ β : ℝ, β ≠ 0 → HasDerivAt (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) (gaussDens ε β) β ∧ 0 ≤ gaussDens ε β) ∧ ContinuousOn (gaussDens ε) {β | β ≠ 0} ∧ ∀ s : Bool, (∃ a, ε a = s) → 0 < gaussDens ε (sgn ℝ s) := by
  first | exact @GlobalTheory.GaussMean.Density.gaussDens_spec | exact GlobalTheory.GaussMean.Density.gaussDens_spec | (intros; apply GlobalTheory.GaussMean.Density.gaussDens_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotCdomAdd
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.KType

theorem cdom_step {n : ℕ} {ε : Fin n → Bool} {ν μ : Fin n → ℝ} (h : CDom ε ν μ) {a b : Fin n}
    (hab : a < b) (he : ε a = ε b) : CDom ε (ν - Formalism.REAL.root a b) μ := by
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨fun i j => c i j + (if j = b then if i = a then 1 else 0 else 0), ?_, ?_⟩
  · intro i j hij
    by_cases h0 : c i j = 0
    · by_cases hj : j = b
      · by_cases hi : i = a
        · subst hi; subst hj; exact ⟨hab, he⟩
        · simp [h0, hi] at hij
      · simp [h0, hj] at hij
    · exact hc i j h0
  · have : μ - (ν - Formalism.REAL.root a b) = (μ - ν) + Formalism.REAL.root a b := by abel
    rw [this, hs]
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem cdom_word {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) : CDom ε (μ + wordWeightShift w) μ := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, by simp, by simp [wordWeightShift]⟩
  | cons p w ih =>
    have hp := hw p List.mem_cons_self
    have := cdom_step (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))) hp.2 hp.1.symm
    have e : μ + wordWeightShift (p :: w) = μ + wordWeightShift w - Formalism.REAL.root p.2 p.1 := by
      simp only [wordWeightShift, Formalism.REAL.root]; abel
    rw [e]; exact this

theorem not_cdom_add {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + Pi.single a 1 - Pi.single b 1) μ := by
  rintro ⟨c, hc, hs⟩
  have e : μ - (μ + Pi.single a 1 - Pi.single b 1) = Pi.single b (1 : ℝ) - Pi.single a 1 := by abel
  rw [e] at hs
  have h1 := congrArg heightFunctional hs
  rw [height_functional_root] at h1
  have hsum : heightFunctional (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) ≤ 0 := by
    refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
    · intro x y hx hy; rw [height_functional_add]; linarith
    · intro i _
      refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
      · intro x y hx hy; rw [height_functional_add]; linarith
      · intro j _
        have h2 : heightFunctional ((c i j : ℝ) • Formalism.REAL.root i j) = (c i j : ℝ) * ((i : ℝ) - j) := by
          rw [← height_functional_root i j]
          simp only [heightFunctional, Formalism.REAL.root, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [h2]
        by_cases h0 : c i j = 0
        · simp [h0]
        · have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (hc i j h0).1
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

theorem cdom_of_mem {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ V} (hR : KRel ε F) (hU : KUnit ε F) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε F μ x) (hy : y ∈ kSpan ε F x) (hy0 : y ≠ 0) (hw : IsWeight F ν y) :
    CDom ε ν μ := by
  by_contra hn
  rw [compact_span_eq_lowering hR hx] at hy
  have : lowSpan ε F x ≤ (ℂ ∙ y)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine compact_weight_orthogonal V n ε F ν (μ + wordWeightShift w) y _ hU hw
      (word_action_weight hR hx.1 w (fun q hq => (hw' q hq).1)) ?_
    rintro rfl
    exact hn (cdom_word μ w hw')
  exact hy0 (inner_self_eq_zero.mp (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (this hy)))

theorem kType_iff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (μ : Fin n → ℝ) (u : V), u ≠ 0 → KHighest ε E μ u → FiniteDimensional ℂ (kSpan ε E u) → IsKTypeOf ε σ μ ((kSpan ε E u).map V.subtype)) ∧ ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H) (u : V), IsKTypeOf ε σ μ S → S ≤ V → (u : H) ∈ S → u ≠ 0 → IsWtOn (Kset ε) σ μ (u : H) → KHighest ε E μ u ∧ (kSpan ε E u).map V.subtype = S ∧ FiniteDimensional ℂ (kSpan ε E u) := by
  intro n ε H _ _ _ σ V E hσ hD
  obtain ⟨-, hst, hwt⟩ := GlobalTheory.T.derivedModule_coefficients_and_stable_flows n ε H σ V E hσ hD
  have hR : KRel ε E := glRel_kRel ε E hD.1
  have hU : KUnit ε E := isUnitary_kUnit ε E hD.2.1
  have hIrr : KIrr := kIrr_of highestWeightExists_holds
    (kHiUniq_of compact_lowering_holds compact_weight_orthogonal (kOrth_of compact_lowering_holds compact_weight_orthogonal))
  have hmc : ∀ S : Submodule ℂ H, S ≤ V → (S.comap V.subtype).map V.subtype = S := by
    intro S hS
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hS]
  have hfd : ∀ S : Submodule ℂ H, S ≤ V → FiniteDimensional ℂ S →
      FiniteDimensional ℂ (S.comap V.subtype) := by
    intro S hS _
    exact (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  refine ⟨?_, ?_⟩
  · intro μ u hu0 hu hf
    have hfm : FiniteDimensional ℂ ((kSpan ε E u).map V.subtype) := inferInstance
    refine ⟨hfm, (hst _ hf).1 (compact_span_stable u), ?_, ?_, ?_⟩
    · intro S' hS' hK
      have hV : S' ≤ V := hS'.trans (Submodule.map_subtype_le V _)
      have hf' : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
      have hk : KStable ε E (S'.comap V.subtype) :=
        (hst _ (hfd S' hV hf')).2 (by rw [hmc S' hV]; exact hK)
      have hle : S'.comap V.subtype ≤ kSpan ε E u := by
        have := Submodule.comap_mono (f := V.subtype) hS'
        rwa [Submodule.comap_map_eq_of_injective V.injective_subtype] at this
      rcases hIrr V n ε E μ u hf hR hU hu _ hle hk with h | h
      · left; rw [← hmc S' hV, h, Submodule.map_bot]
      · right; rw [← hmc S' hV, h]
    · exact ⟨u, ⟨u, mem_compact_span_self u, rfl⟩, fun h => hu0 (Subtype.ext h), (hwt μ u).1 hu.1⟩
    · rintro ν _ ⟨y, hy, rfl⟩ hy0 hw
      exact cdom_of_mem hR hU hu hy (fun h => hy0 (by rw [h]; rfl)) ((hwt ν y).2 hw)
  · rintro μ S u ⟨hf, hK, hI, -, hC⟩ hV huS hu0 hw
    have hw' : IsWeight E μ u := (hwt μ u).2 hw
    have hfc := hfd S hV hf
    have hk : KStable ε E (S.comap V.subtype) := (hst _ hfc).2 (by rw [hmc S hV]; exact hK)
    have hle : kSpan ε E u ≤ S.comap V.subtype := compact_span_le_stable huS hk
    have hfk : FiniteDimensional ℂ (kSpan ε E u) := Submodule.finiteDimensional_of_le hle
    refine ⟨⟨hw', ?_⟩, ?_, hfk⟩
    · intro a b hab he
      by_contra hne
      exact not_cdom_add μ hab (hC _ (E a b u : V) (hk a b he u huS) (fun h => hne (Subtype.ext h))
        ((hwt _ _).1 (compact_weight_shift hR hw' he)))
    · rcases hI _ (Submodule.map_le_iff_le_comap.mpr hle) ((hst _ hfk).1 (compact_span_stable u)) with h | h
      · exfalso
        have : (u : H) ∈ (kSpan ε E u).map V.subtype := ⟨u, mem_compact_span_self u, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hu0 (Subtype.ext this)
      · exact h

end GlobalTheory.Jet.KType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingMulLeft
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.HaarLeftInv

def leftMat {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    Matrix (Fin j) (Fin j) ℂ →ₗ[ℝ] Matrix (Fin j) (Fin j) ℂ where
  toFun T := A * T
  map_add' S T := Matrix.mul_add _ _ _
  map_smul' c T := by simp

theorem det_leftMat {j : ℕ} (A : Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (leftMat A) = (‖A.det‖ ^ 2) ^ j := by
  have h := (GlobalTheory.TwoSidedJac.real_jacobians).1 j j A 1 (leftMat A) (fun T => by
    show A * T = A * T * 1
    rw [Matrix.mul_one])
  rw [h, Matrix.det_one, norm_one, one_pow, mul_one, ← pow_mul]

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def leftMul (a : MatInf E j) :
    (InfinitePlace E → Fin j → Fin j → ℂ) →ₗ[ℝ] (InfinitePlace E → Fin j → Fin j → ℂ) :=
  LinearMap.pi fun w => (show (Fin j → Fin j → ℂ) →ₗ[ℝ] (Fin j → Fin j → ℂ) from
    leftMat (Matrix.of (a w))).comp (LinearMap.proj w)

theorem det_leftMul (a : MatInf E j) : LinearMap.det (leftMul E j a) = detNorm E j a ^ j := by
  calc LinearMap.det (leftMul E j a)
      = ∏ w, LinearMap.det (leftMat (Matrix.of (a w))) := LinearMap.det_pi _
    _ = ∏ w, (‖(Matrix.of (a w)).det‖ ^ 2) ^ j := by simp only [det_leftMat]
    _ = (∏ w, ‖(Matrix.of (a w)).det‖ ^ 2) ^ j := Finset.prod_pow _ _ _
    _ = detNorm E j a ^ j := by rfl

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl
  rw [hw, Matrix.det_mul, norm_mul, mul_pow]

theorem continuous_detNorm :
    Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x) := by
  unfold detNorm
  refine continuous_finsetProd _ fun w _ => ?_
  exact ((Continuous.matrix_det (continuous_apply w)).norm).pow 2

theorem isAddHaar_volume : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  have : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem measurePreserving_mul_left : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (a : MatInf E j), 0 < detNorm E j a → MeasurableEmbedding (fun g : MatInf E j => a * g) ∧ MeasurePreserving (fun g : MatInf E j => a * g) (haarGL E j) (haarGL E j) := by
  intro E _ _ j a ha
  have : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure :=
    isAddHaar_volume E j
  have hdet0 : LinearMap.det (leftMul E j a) ≠ 0 := by
    rw [det_leftMul]
    exact pow_ne_zero _ ha.ne'
  have hemb : MeasurableEmbedding ⇑(leftMul E j a) :=
    ((LinearMap.toContinuousLinearMap (leftMul E j a)).toContinuousLinearEquivOfDetNeZero
      hdet0).toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpos : 0 < (detNorm E j a)⁻¹ ^ j := pow_pos (inv_pos.mpr ha) j
  have hmap : Measure.map (leftMul E j a) (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) =
      ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) • volume := by
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet0, det_leftMul, ← inv_pow,
      abs_of_pos hpos]
  have hc0 : ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hctop : ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hρ : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ =>
      ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((continuous_detNorm E j).measurable.inv).pow_const j).ennreal_ofReal
  have hρf : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ,
      ENNReal.ofReal ((detNorm E j (leftMul E j a x))⁻¹ ^ j) =
        ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j) * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    intro x
    have hx : detNorm E j (leftMul E j a x) = detNorm E j a * detNorm E j x := detNorm_mul E j a x
    rw [hx, mul_inv, mul_pow, ENNReal.ofReal_mul hpos.le]
  have hV : Measure.map (leftMul E j a)
      ((volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
        fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)) =
      (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).withDensity
        fun x => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, withDensity_apply _ (hemb.measurable hs),
      withDensity_apply _ hs]
    calc ∫⁻ x in ⇑(leftMul E j a) ⁻¹' s, ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j)
        = (ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j))⁻¹ *
            ∫⁻ x in ⇑(leftMul E j a) ⁻¹' s,
              ENNReal.ofReal ((detNorm E j (leftMul E j a x))⁻¹ ^ j) := by
          simp_rw [hρf]
          rw [lintegral_const_mul' _ _ hctop, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop,
            one_mul]
      _ = (ENNReal.ofReal ((detNorm E j a)⁻¹ ^ j))⁻¹ *
            ∫⁻ y in s, ENNReal.ofReal ((detNorm E j y)⁻¹ ^ j) ∂(Measure.map (leftMul E j a) volume) := by
          rw [setLIntegral_map hs hρ hemb.measurable]
      _ = ∫⁻ y in s, ENNReal.ofReal ((detNorm E j y)⁻¹ ^ j) := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
            ENNReal.inv_mul_cancel hc0 hctop, one_mul]
  exact ⟨hemb, hemb.measurable, hV⟩

end GlobalTheory.HaarLeftInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrable
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrable
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

variable {k r : ℕ}

theorem measurable_lmul_swap :
    Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
  have hc : Continuous (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
    refine continuous_finsetSum _ fun l _ => ?_
    fun_prop
  exact hc.measurable

theorem quotientMeasure_hypotheses_closed_bessel_subgroup {S : Set (Mat k r)} {μG μS ν : Measure (Mt k r)}
    (hS : IsClosedSub k r S) (hG : IsHaarOn (GG k r) μG) (hμS : IsHaarOn S μS)
    (hU : IsUnimod S μS) (hq : IsQuotMeas μG μS ν) :
    PI.QuotientSetting (GG k r) S μG μS ν := by
  obtain ⟨hGm, hGu⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  exact ⟨hGm, hS.isMatGroup, hS.1, hG, hμS, (hGu μG hG).2, hU.1, hq⟩

theorem eq_map_prod_of_isQuotMeas {μG μS ν : Measure (Mt k r)} [SFinite ν] [SFinite μS]
    (hq : IsQuotMeas μG μS ν) :
    μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) := by
  ext A hA
  have hm := measurable_lmul_swap (k := k) (r := r)
  rw [Measure.map_apply hm hA, ← lintegral_indicator_one hA,
    hq _ (measurable_one.indicator hA), ← lintegral_indicator_one (hm hA),
    lintegral_prod _ ((measurable_one.indicator (hm hA)).aemeasurable)]
  rfl

theorem weil_integrable :
    ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)), IsClosedSub k r S →
      IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν →
      SigmaFinite ν ∧ ν {x | Matrix.of x ∉ GG k r} = 0 ∧
      μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) ∧
      (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (f : Mt k r → B),
        Integrable f μG → Integrable (fun x => ∫ s, f (lmulM (Matrix.of s) x) ∂μS) ν ∧
          ∫ x, f x ∂μG = ∫ x, (∫ s, f (lmulM (Matrix.of s) x) ∂μS) ∂ν) ∧
      (∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) →
        ∀ y ∈ GG k r, ∫⁻ x, F (rmulM y x) ∂ν = ∫⁻ x, F x ∂ν) := by
  intro k r S μG μS ν hS hG hμS hU hq
  have hset := quotientMeasure_hypotheses_closed_bessel_subgroup hS hG hμS hU hq
  have : SigmaFinite μS := hμS.1
  have : SigmaFinite μG := hG.1
  have hm := measurable_lmul_swap (k := k) (r := r)

  obtain ⟨f0, hf0pos, hf0m, hf0int⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG one_ne_zero
  set g : Mt k r → ENNReal := fun x => ∫⁻ s, (f0 (lmulM (Matrix.of s) x) : ENNReal) ∂μS with hg
  have hgm : Measurable g := by
    have : Measurable (fun p : Mt k r × Mt k r => (f0 (lmulM (Matrix.of p.2) p.1) : ENNReal)) :=
      (measurable_coe_nnreal_ennreal.comp hf0m).comp hm
    exact this.lintegral_prod_right'
  have hgpos : ∀ x, 0 < g x := by
    intro x
    rw [pos_iff_ne_zero]
    intro h0
    have hmx : Measurable (fun s : Mt k r => (f0 (lmulM (Matrix.of s) x) : ENNReal)) :=
      (measurable_coe_nnreal_ennreal.comp hf0m).comp (hm.comp measurable_prodMk_left)
    change ∫⁻ s, (f0 (lmulM (Matrix.of s) x) : ENNReal) ∂μS = 0 at h0
    rw [lintegral_eq_zero_iff hmx] at h0
    have hall : ∀ᵐ s ∂μS, False := by
      filter_upwards [h0] with s hs
      simp only [Pi.zero_apply, ENNReal.coe_eq_zero] at hs
      exact (hf0pos _).ne' hs
    exact hμS.2.1 (Measure.measure_univ_eq_zero.mp (by simpa using hall))
  have hgint : ∫⁻ x, g x ∂ν < ⊤ := by
    have := hq (fun x => (f0 x : ENNReal)) (measurable_coe_nnreal_ennreal.comp hf0m)
    have h2 : ∫⁻ x, g x ∂ν = ∫⁻ x, (f0 x : ENNReal) ∂μG := by rw [this]; rfl
    rw [h2]
    exact hf0int.trans ENNReal.one_lt_top

  have hsig : SigmaFinite ν := by
    refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ENNReal) + 1)⁻¹ ≤ g x})
      (Set.countable_range _) ?_ ?_
    · rintro _ ⟨n, rfl⟩
      have hne : ((n : ENNReal) + 1)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
      have hnt : ((n : ENNReal) + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simp)
      calc ν {x | ((n : ENNReal) + 1)⁻¹ ≤ g x} ≤ (∫⁻ x, g x ∂ν) / ((n : ENNReal) + 1)⁻¹ :=
            meas_ge_le_lintegral_div hgm.aemeasurable hne hnt
        _ < ⊤ := ENNReal.div_lt_top hgint.ne hne
    · rw [Set.sUnion_range, Set.eq_univ_iff_forall]
      intro x
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hgpos x).ne'
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      show ((n : ENNReal) + 1)⁻¹ ≤ g x
      refine le_trans ?_ hn.le
      exact ENNReal.inv_le_inv.mpr le_self_add
  have hmap := eq_map_prod_of_isQuotMeas (μG := μG) (μS := μS) (ν := ν) hq
  refine ⟨hsig, ?_, hmap, ?_, ?_⟩
  · have hae := GlobalTheory.QuotRightInv.ae_mem_of_quot hset
    rw [ae_iff] at hae
    simpa using hae
  · intro B _ _ _ f hf
    rw [hmap] at hf
    have hf' : Integrable (fun p : Mt k r × Mt k r => f (lmulM (Matrix.of p.2) p.1)) (ν.prod μS) :=
      (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp hf
    refine ⟨hf'.integral_prod_left, ?_⟩
    rw [hmap, integral_map hm.aemeasurable hf.aestronglyMeasurable, integral_prod _ hf']
  · intro F hF hFS y hy
    exact GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset F hF (fun s hs x _ => hFS s hs x) y hy

end GlobalTheory.SgInf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrableStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_besselUnitary_integrable : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν → SigmaFinite ν ∧ ν {x | Matrix.of x ∉ GG k r} = 0 ∧ μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) ∧ (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (f : Mt k r → B), Integrable f μG → Integrable (fun x => ∫ s, f (lmulM (Matrix.of s) x) ∂μS) ν ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (lmulM (Matrix.of s) x) ∂μS) ∂ν) ∧ (∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∀ y ∈ GG k r, ∫⁻ x, F (rmulM y x) ∂ν = ∫⁻ x, F x ∂ν) := by
  first | exact @GlobalTheory.SgInf.weil_integrable | exact GlobalTheory.SgInf.weil_integrable | (intros; apply GlobalTheory.SgInf.weil_integrable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLattice
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.PoissonV

variable (ι κ : Type) [Fintype ι] [Fintype κ]

theorem _root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_curry :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : MeasurePreserving (MeasurableEquiv.curry ι κ ℂ).symm volume volume := by
    refine ⟨(MeasurableEquiv.curry ι κ ℂ).symm.measurable, ?_⟩
    have hv : (volume : Measure (ι × κ → ℂ)) = Measure.pi fun _ => volume := rfl
    rw [hv]
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have hpre : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Set.univ.pi fun k => s (i, k) := by
      ext x
      simp [MeasurableEquiv.curry, Set.mem_pi, Prod.forall]
    rw [hpre, volume_pi_pi]
    simp_rw [volume_pi_pi]
    rw [Fintype.prod_prod_type]
  simpa using h.symm

def coords : EuclideanSpace ℂ (ι × κ) ≃L[ℝ] (ι → κ → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x w a => x (w, a)
      invFun := fun y => WithLp.toLp 2 fun p => y p.1 p.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem _root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords :
    MeasurePreserving (_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ) volume volume :=
  (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_curry ι κ).comp (_root_.GlobalTheory.volume_preserving_ofLp_complex _)

theorem _root_.GlobalTheory.FlagBase.PoissonV.norm_sq_coords (x : EuclideanSpace ℂ (ι × κ)) :
    ∑ w, ∑ a, ‖_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ x w a‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

end GlobalTheory.FlagBase.PoissonV

namespace GlobalTheory.FlagBase

open PoissonV

variable (ι κ : Type) [Fintype ι] [Fintype κ] in
private theorem inner_toLp_conj_eq_sum_re_dotProduct (u : EuclideanSpace ℂ (ι × κ))
    (y : ι → κ → ℂ) :
    inner ℝ u (WithLp.toLp 2 fun p => starRingEnd ℂ (y p.1 p.2) : EuclideanSpace ℂ (ι × κ)) =
      ∑ w, (_root_.GlobalTheory.FlagBase.PoissonV.coords ι κ u w ⬝ᵥ y w).re := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp [_root_.GlobalTheory.FlagBase.PoissonV.coords, dotProduct, Complex.re_sum, Complex.mul_re]
  congr 1 <;> exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem _root_.GlobalTheory.FlagBase.poisson_gaussV (E : Type) [Field E] [NumberField E] (j : ℕ)
    (L : Submodule ℤ (_root_.GlobalTheory.FlagBase.VecInf E j))
    [DiscreteTopology L] (hL : IsZLattice ℝ L) :
    Summable (fun x : L => _root_.GlobalTheory.FlagBase.gaussV E j x) ∧
      Summable (fun y : _root_.GlobalTheory.FlagBase.dualAt E j L => _root_.GlobalTheory.FlagBase.gaussV E j y) ∧
      ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x =
        (_root_.GlobalTheory.FlagBase.covAt E j L)⁻¹ *
          ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y ∧
      ∫ x, _root_.GlobalTheory.FlagBase.gaussV E j x = 1 := by
  classical
  haveI := hL
  let e := _root_.GlobalTheory.FlagBase.PoissonV.coords (InfinitePlace E) (Fin j)
  let L' := ZLattice.comap ℝ L
    (e : EuclideanSpace ℂ (InfinitePlace E × Fin j) →ₗ[ℝ] _root_.GlobalTheory.FlagBase.VecInf E j)
  have hmemL : ∀ u, u ∈ L' ↔ e u ∈ L := fun u => Iff.rfl
  have hg : ∀ u, _root_.GlobalTheory.FlagBase.gaussV E j (e u) = Real.exp (-Real.pi * ‖u‖ ^ 2) := by
    intro u
    show Real.exp (-Real.pi * ∑ w, ∑ a, ‖e u w a‖ ^ 2) = _
    rw [_root_.GlobalTheory.FlagBase.PoissonV.norm_sq_coords]
  have hg' : ∀ x, _root_.GlobalTheory.FlagBase.gaussV E j x = Real.exp (-Real.pi * ‖e.symm x‖ ^ 2) := by
    intro x
    rw [← hg, ContinuousLinearEquiv.apply_symm_apply]
  let eL : L ≃ L' :=
    { toFun := fun y => ⟨e.symm y, by rw [hmemL, ContinuousLinearEquiv.apply_symm_apply]; exact y.2⟩
      invFun := fun x => ⟨e x, (hmemL x).1 x.2⟩
      left_inv := fun y => by ext; simp
      right_inv := fun x => by ext; simp }
  let ψ : _root_.GlobalTheory.FlagBase.VecInf E j ≃ EuclideanSpace ℂ (InfinitePlace E × Fin j) :=
    { toFun := fun y => WithLp.toLp 2 fun p => starRingEnd ℂ (y p.1 p.2)
      invFun := fun z w a => starRingEnd ℂ (z (w, a))
      left_inv := fun y => by funext w a; simp
      right_inv := fun z => by ext p; simp }
  have hψ : ∀ y, _root_.GlobalTheory.FlagBase.gaussV E j y = Real.exp (-Real.pi * ‖ψ y‖ ^ 2) := by
    intro y
    show Real.exp (-Real.pi * ∑ w, ∑ a, ‖y w a‖ ^ 2) = _
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp [ψ]
  have hinner : ∀ u y, inner ℝ u (ψ y) = ∑ w, (e u w ⬝ᵥ y w).re :=
    fun u y => inner_toLp_conj_eq_sum_re_dotProduct _ _ u y
  have hdual : ∀ y, y ∈ _root_.GlobalTheory.FlagBase.dualAt E j L ↔
      ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z := by
    intro y
    unfold _root_.GlobalTheory.FlagBase.dualAt
    constructor
    · intro hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact hy
      | zero => intro x _; exact ⟨0, by simp⟩
      | add y y' _ _ h h' =>
        intro x hx
        obtain ⟨z, hz⟩ := h x hx
        obtain ⟨z', hz'⟩ := h' x hx
        refine ⟨z + z', ?_⟩
        simp only [Pi.add_apply, dotProduct_add, Complex.add_re, Finset.sum_add_distrib, hz, hz']
        push_cast
        ring
      | smul n y _ h =>
        intro x hx
        obtain ⟨z, hz⟩ := h x hx
        refine ⟨n * z, ?_⟩
        simp only [Pi.smul_apply, dotProduct_smul, Complex.smul_re]
        rw [← Finset.smul_sum, hz, zsmul_eq_mul]
        push_cast
        ring
    · intro hy
      exact Submodule.subset_span hy
  have hmem : ∀ y, y ∈ _root_.GlobalTheory.FlagBase.dualAt E j L ↔ ψ y ∈ _root_.GlobalTheory.dualLattice L' := by
    intro y
    rw [hdual, _root_.GlobalTheory.mem_dualLattice]
    constructor
    · intro h u hu
      obtain ⟨z, hz⟩ := h (e u) ((hmemL u).1 hu)
      exact ⟨z, by rw [hinner, hz]⟩
    · intro h x hx
      obtain ⟨m, hm⟩ := h (e.symm x) (by rw [hmemL, ContinuousLinearEquiv.apply_symm_apply]; exact hx)
      refine ⟨m, ?_⟩
      rw [hm, hinner, ContinuousLinearEquiv.apply_symm_apply]
  let dL : _root_.GlobalTheory.FlagBase.dualAt E j L ≃ _root_.GlobalTheory.dualLattice L' := ψ.subtypeEquiv hmem
  let f : EuclideanSpace ℂ (InfinitePlace E × Fin j) → ℝ := fun u => Real.exp (-Real.pi * ‖u‖ ^ 2)
  have hsL : Summable (fun x : L => _root_.GlobalTheory.FlagBase.gaussV E j x) :=
    ((eL.summable_iff (f := fun x : L' => f x)).2
      (_root_.GlobalTheory.summable_lattice_exp_neg_mul_norm_sq L' Real.pi_pos)).congr fun x => by rw [hg']; rfl
  have hsD : Summable (fun y : _root_.GlobalTheory.FlagBase.dualAt E j L => _root_.GlobalTheory.FlagBase.gaussV E j y) :=
    ((dL.summable_iff (f := fun z : _root_.GlobalTheory.dualLattice L' => f z)).2
      (_root_.GlobalTheory.summable_lattice_exp_neg_mul_norm_sq _ Real.pi_pos)).congr fun y => by rw [hψ]; rfl
  have hT1 : ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x = ∑' x : L', f x :=
    calc ∑' x : L, _root_.GlobalTheory.FlagBase.gaussV E j x = ∑' x : L, f (eL x) :=
          tsum_congr fun x => by rw [hg']; rfl
      _ = ∑' x : L', f x := eL.tsum_eq (fun x : L' => f x)
  have hT2 : ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y =
      ∑' z : _root_.GlobalTheory.dualLattice L', f z :=
    calc ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, _root_.GlobalTheory.FlagBase.gaussV E j y =
          ∑' y : _root_.GlobalTheory.FlagBase.dualAt E j L, f (dL y) :=
          tsum_congr fun y => by rw [hψ]; rfl
      _ = ∑' z : _root_.GlobalTheory.dualLattice L', f z := dL.tsum_eq (fun z : _root_.GlobalTheory.dualLattice L' => f z)
  haveI : (volume : Measure (_root_.GlobalTheory.FlagBase.VecInf E j)).IsAddHaarMeasure := by
    rw [← (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords (InfinitePlace E) (Fin j)).map_eq]
    exact e.isAddHaarMeasure_map volume
  have hcov : _root_.GlobalTheory.FlagBase.covAt E j L = ZLattice.covolume L' volume := by
    show ZLattice.covolume L volume = _
    exact (ZLattice.covolume_comap L volume volume
      (_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords _ _)).symm
  have hP := _root_.GlobalTheory.tsum_gaussian_lattice_eq_dualLattice L' one_pos
  simp only [mul_one, Real.one_rpow, div_one] at hP
  refine ⟨hsL, hsD, ?_, ?_⟩
  · rw [hT1, hT2, hcov]
    exact hP
  · have hI : ∫ x, _root_.GlobalTheory.FlagBase.gaussV E j x = ∫ u, f u :=
      ((_root_.GlobalTheory.FlagBase.PoissonV.measurePreserving_coords (InfinitePlace E) (Fin j)).integral_comp
        e.toHomeomorph.measurableEmbedding (_root_.GlobalTheory.FlagBase.gaussV E j)).symm.trans
        (integral_congr_ae (Filter.Eventually.of_forall fun u => hg u))
    rw [hI]
    show ∫ u, Real.exp (-Real.pi * ‖u‖ ^ 2) = 1
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm Real.pi_pos, div_self Real.pi_ne_zero,
      Real.one_rpow]

end GlobalTheory.FlagBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PoissonSummationInfinitePlaceGaussianLatticeStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poisson_summation_infinitePlaceGaussian_lattice : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (L : Submodule ℤ (VecInf E j)) [DiscreteTopology L], IsZLattice ℝ L → Summable (fun x : L => gaussV E j x) ∧ Summable (fun y : dualAt E j L => gaussV E j y) ∧ ∑' x : L, gaussV E j x = (covAt E j L)⁻¹ * ∑' y : dualAt E j L, gaussV E j y ∧ ∫ x, gaussV E j x = 1 := by
  first | exact @GlobalTheory.FlagBase.poisson_gaussV | exact GlobalTheory.FlagBase.poisson_gaussV | (intros; apply GlobalTheory.FlagBase.poisson_gaussV <;> assumption)
end
end
