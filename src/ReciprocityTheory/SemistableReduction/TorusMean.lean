module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.TorusMeanD
section -- merged from ReciprocityTheory.SemistableReduction.TorusMeanC
section -- merged from ReciprocityTheory.SemistableReduction.TorusMeanB
section -- merged from ReciprocityTheory.SemistableReduction.TorusMeanA
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Polynomial Real

def circPt (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * (t : ℂ))

lemma circPt_eq (t : ℝ) : circPt t = circleMap 0 1 (2 * π * t) := by
  rw [circleMap_zero, circPt]; push_cast; ring_nf

lemma norm_circPt (t : ℝ) : ‖circPt t‖ = 1 := by
  rw [circPt_eq, norm_circleMap_zero]; simp

instance isProbabilityMeasure_restrict_Ioc :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
  ⟨by simp⟩

lemma integrableOn_log_circ (p : ℂ[X]) :
    IntegrableOn (fun t => Real.log ‖p.eval (circPt t)‖) (Set.Ioc (0 : ℝ) 1) := by
  have h := (p.intervalIntegrable_mahlerMeasure).comp_mul_left (c := 2 * π) enorm_ne_top
    enorm_ne_top
  have h2 : IntervalIntegrable (fun t => Real.log ‖p.eval (circPt t)‖) volume 0 1 := by
    simp only [circPt_eq]
    convert h using 2 <;> simp
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h2

lemma integral_log_circ (p : ℂ[X]) :
    ∫ t in Set.Ioc (0 : ℝ) 1, Real.log ‖p.eval (circPt t)‖ = p.logMahlerMeasure := by
  rw [← intervalIntegral.integral_of_le zero_le_one, logMahlerMeasure_def, circleAverage_def]
  simp only [circPt_eq]
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.log ‖p.eval (circleMap 0 1 x)‖)
    (by positivity : (2 * π) ≠ 0)]
  simp

lemma log_norm_leadingCoeff_le (p : ℂ[X]) : Real.log ‖p.leadingCoeff‖ ≤ p.logMahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  rw [logMahlerMeasure_eq_log_MahlerMeasure]
  exact Real.log_le_log (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp))
    (leadingCoeff_le_mahlerMeasure p)

lemma log_norm_coeff_top_le (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (htop : ∀ k', k < k' → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by
  have hd : p.natDegree = k := by
    apply le_antisymm
    · exact natDegree_le_iff_coeff_eq_zero.mpr fun k' hk' => htop k' (by exact_mod_cast hk')
    · exact le_natDegree_of_ne_zero hk
  have := log_norm_leadingCoeff_le p
  rwa [leadingCoeff, hd] at this

lemma log_norm_coeff_bot_le (p : ℂ[X]) (k : ℕ) (hk : p.coeff k ≠ 0)
    (hbot : ∀ k', k' < k → p.coeff k' = 0) : Real.log ‖p.coeff k‖ ≤ p.logMahlerMeasure := by
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.mpr hbot
  have hp : p ≠ 0 := fun h => hk (by simp [h])
  have hq0 : q ≠ 0 := fun h => hp (by simp [hq, h])
  have hc : p.coeff k = q.coeff 0 := by
    rw [hq, coeff_X_pow_mul']; simp
  have hM : p.logMahlerMeasure = q.logMahlerMeasure := by
    rw [hq, logMahlerMeasure_mul_eq_add_logMahlerMeasure (by rw [← hq]; exact hp),
      X_pow_eq_monomial, logMahlerMeasure_monomial]
    simp
  rw [hc, hM, logMahlerMeasure_eq_log_MahlerMeasure]
  rw [hc] at hk
  apply Real.log_le_log (norm_pos_iff.mpr hk)
  simpa using norm_coeff_le_choose_mul_mahlerMeasure 0 q

lemma circPt_injOn : Set.InjOn circPt (Set.Ioc (0 : ℝ) 1) := by
  intro a ha b hb h
  simp only [circPt_eq] at h
  have hinj := injOn_circleMap_of_abs_sub_le (c := (0 : ℂ)) (R := 1) one_ne_zero
    (a := 0) (b := 2 * π) (by rw [zero_sub, abs_neg, abs_of_pos (by positivity)])
  rw [Set.uIoc_of_le (by positivity)] at hinj
  have : 2 * π * a = 2 * π * b := by
    apply hinj
    · constructor <;> nlinarith [ha.1, ha.2, pi_pos]
    · constructor <;> nlinarith [hb.1, hb.2, pi_pos]
    · exact h
  have hpi : (2 * π) ≠ 0 := by positivity
  exact mul_left_cancel₀ hpi this

lemma zero_set_circ_null (p : ℂ[X]) (hp : p ≠ 0) :
    volume.restrict (Set.Ioc (0 : ℝ) 1) {t | p.eval (circPt t) = 0} = 0 := by
  rw [Measure.restrict_apply' measurableSet_Ioc]
  apply Set.Finite.measure_zero _ volume
  apply Set.Finite.of_finite_image (f := circPt) _
    (Set.InjOn.mono
      (s₁ := {t | p.eval (circPt t) = 0} ∩ Set.Ioc (0 : ℝ) 1)
      (s₂ := Set.Ioc (0 : ℝ) 1) (fun _ h => h.2) circPt_injOn)
  apply p.roots.finite_toSet.subset
  rintro _ ⟨t, ⟨ht, _⟩, rfl⟩
  simpa [mem_roots hp] using ht

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

instance isProbabilityMeasure_torusProb (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (torusProb ι) := by
  unfold torusProb; infer_instance

def tmUpd (i : ι) : (ι → ℝ) × ℝ → (ι → ℝ) := fun p => update p.1 i p.2

lemma measurable_tmUpd (i : ι) : Measurable (tmUpd i) := by
  first
  | exact measurable_update' (a := i)
  | exact measurable_pi_iff.mpr fun j => by
      by_cases h : j = i
      · subst h; simpa [tmUpd] using measurable_snd
      · simpa [tmUpd, Function.update_of_ne h] using (measurable_pi_apply j).comp measurable_fst

lemma tmUpd_preimage_pi (i : ι) (s : ι → Set ℝ) :
    tmUpd i ⁻¹' (Set.univ.pi s) = (Set.univ.pi (update s i Set.univ)) ×ˢ s i := by
  ext ⟨θ, t⟩
  simp only [Set.mem_preimage, tmUpd, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
  constructor
  · intro h
    refine ⟨fun j => ?_, by simpa using h i⟩
    by_cases hj : j = i
    · subst hj; simp
    · simpa [hj] using h j
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j = i
    · subst hj; simpa using h2
    · simpa [hj] using h1 j

lemma measurePreserving_tmUpd (i : ι) :
    MeasurePreserving (tmUpd i) ((torusProb ι).prod unitIntervalMeasure) (torusProb ι) := by
  refine ⟨measurable_tmUpd i, ?_⟩
  have h1 : (volume.restrict (Set.Ioc (0 : ℝ) 1)) Set.univ = 1 := by simp
  unfold torusProb
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply (measurable_tmUpd i) (MeasurableSet.univ_pi hs), tmUpd_preimage_pi,
    Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => volume.restrict (Set.Ioc (0 : ℝ) 1) (s j))
      (Finset.mem_univ i)]
  have hp : ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (update s i Set.univ j) =
      ∏ j ∈ Finset.univ.erase i, volume.restrict (Set.Ioc (0 : ℝ) 1) (s j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hp, Function.update_self, h1, one_mul, mul_comm]

lemma tm_integrable_comp (i : ι) {F : (ι → ℝ) → ℝ} (hF : AEStronglyMeasurable F (torusProb ι)) :
    Integrable (F ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) ↔ Integrable F (torusProb ι) := by
  exact (measurePreserving_tmUpd i).integrable_comp hF

lemma tm_integral_comp (i : ι) {F : (ι → ℝ) → ℝ} (hF : AEStronglyMeasurable F (torusProb ι)) :
    ∫ θ, F θ ∂(torusProb ι) = ∫ p, F (tmUpd i p) ∂((torusProb ι).prod unitIntervalMeasure) := by
  have hmap := (measurePreserving_tmUpd i).map_eq
  conv_lhs => rw [← hmap]
  exact integral_map (measurable_tmUpd i).aemeasurable (by rwa [hmap])

lemma tm_measure_null (i : ι) {S : Set (ι → ℝ)} (hS : MeasurableSet S)
    (h : ∀ᵐ θ ∂(torusProb ι), unitIntervalMeasure {t | update θ i t ∈ S} = 0) : torusProb ι S = 0 := by
  rw [← (measurePreserving_tmUpd i).measure_preimage hS.nullMeasurableSet,
    Measure.prod_apply ((measurable_tmUpd i) hS)]
  have h2 : (fun θ => unitIntervalMeasure (Prod.mk θ ⁻¹' (tmUpd i ⁻¹' S))) =ᵐ[torusProb ι] 0 :=
    h.mono fun θ hθ => hθ
  rw [lintegral_congr_ae h2]
  simp

def tmSlice (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) : Polynomial ℂ :=
  ∑ s ∈ f.support, Polynomial.monomial (s i)
    (MvPolynomial.eval x (MvPolynomial.monomial (s.erase i) (f.coeff s)))

lemma tmSlice_coeff (i : ι) (x : ι → ℂ) (f : MvPolynomial ι ℂ) (k : ℕ) :
    (tmSlice i x f).coeff k = MvPolynomial.eval x (coeffIn i k f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tmSlice, coeffIn, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial_apply, map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs <;> simp

lemma tm_eval_update (i : ι) (x : ι → ℂ) (z : ℂ) (f : MvPolynomial ι ℂ) :
    MvPolynomial.eval (update x i z) f = (tmSlice i x f).eval z := by
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [tmSlice, map_sum, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i, Function.update_self,
    Finsupp.erase_same, pow_zero, one_mul]
  have hp : ∏ j ∈ ({i}ᶜ : Finset ι), update x i z j ^ s j =
      ∏ j ∈ ({i}ᶜ : Finset ι), x j ^ (Finsupp.erase i s) j :=
    Finset.prod_congr rfl fun j hj => by
      have hji : j ≠ i := by simpa using hj
      rw [Function.update_of_ne hji, Finsupp.erase_ne hji]
  rw [hp]
  ring

lemma torusPoint_update (θ : ι → ℝ) (i : ι) (t : ℝ) :
    torusPoint (update θ i t) = update (torusPoint θ) i (circPt t) := by
  funext j
  by_cases h : j = i
  · subst h; simp [torusPoint, circPt]
  · simp [torusPoint, Function.update_of_ne h]

lemma norm_torusPoint (θ : ι → ℝ) (j : ι) : ‖torusPoint θ j‖ = 1 := by simp [torusPoint, Complex.norm_exp]

lemma norm_eval_torus_le (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by
  rw [MvPolynomial.eval_eq]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => ?_))
  rw [norm_mul, norm_prod]
  simp [norm_pow, norm_torusPoint]

lemma continuous_eval_torus (f : MvPolynomial ι ℂ) :
    Continuous fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f := by
  exact (MvPolynomial.continuous_eval f).comp (continuous_pi fun j => by unfold torusPoint; fun_prop)

lemma measurable_logEval (f : MvPolynomial ι ℂ) :
    Measurable fun θ : ι → ℝ => Real.log ‖MvPolynomial.eval (torusPoint θ) f‖ := Real.measurable_log.comp (continuous_eval_torus f).norm.measurable

lemma vars_coeffIn_subset (i : ι) (k : ℕ) (f : MvPolynomial ι ℂ) :
    (coeffIn i k f).vars ⊆ f.vars.erase i := by
  intro j hj
  unfold coeffIn at hj
  have h1 := MvPolynomial.vars_sum_subset _ _ hj
  rw [Finset.mem_biUnion] at h1
  obtain ⟨s, hs, hjs⟩ := h1
  have hsf : s ∈ f.support := (Finset.mem_filter.mp hs).1
  rw [MvPolynomial.vars_monomial (MvPolynomial.mem_support_iff.mp hsf), Finsupp.support_erase,
    Finset.mem_erase] at hjs
  exact Finset.mem_erase.mpr ⟨hjs.1, (MvPolynomial.mem_vars_iff_mem_support j).mpr ⟨s, hsf, hjs.2⟩⟩

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def tmLog (f : MvPolynomial ι ℂ) (θ : ι → ℝ) : ℝ := Real.log ‖MvPolynomial.eval (torusPoint θ) f‖

lemma measurable_tmLog (f : MvPolynomial ι ℂ) : Measurable (tmLog f) := measurable_logEval f

lemma tmLog_update (f : MvPolynomial ι ℂ) (θ : ι → ℝ) (i : ι) (t : ℝ) :
    tmLog f (update θ i t) = Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := by
  rw [tmLog, torusPoint_update, tm_eval_update]

lemma tmLog_le (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    tmLog f θ ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := by
  unfold tmLog
  rcases eq_or_ne ‖MvPolynomial.eval (torusPoint θ) f‖ 0 with h | h
  · rw [h, Real.log_zero]; exact posLog_nonneg
  · exact (Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))
      (norm_eval_torus_le f θ)).trans (le_max_right _ _)

lemma coeffIn_eq_zero_of_lt (i : ι) (f : MvPolynomial ι ℂ) (k : ℕ)
    (hk : f.support.sup (fun s => s i) < k) : coeffIn i k f = 0 := by
  unfold coeffIn
  rw [Finset.filter_false_of_mem, Finset.sum_empty]
  intro s hs hsk
  have := Finset.le_sup (f := fun s : ι →₀ ℕ => s i) hs
  omega

lemma exists_coeffIn_ne_zero (i : ι) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∃ k, coeffIn i k f ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hf
  apply MvPolynomial.funext
  intro x
  have hs : tmSlice i x f = 0 := by
    ext k
    rw [tmSlice_coeff, h k]
    simp
  rw [← update_eq_self i x, tm_eval_update, hs]
  simp

lemma exists_top_coeffIn (i : ι) (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∃ d, coeffIn i d f ≠ 0 ∧ ∀ k, d < k → coeffIn i k f = 0 := by
  classical
  set T := (Finset.range (f.support.sup (fun s => s i) + 1)).filter (fun k => coeffIn i k f ≠ 0)
  have hT : T.Nonempty := by
    obtain ⟨k, hk⟩ := exists_coeffIn_ne_zero i f hf
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hk⟩⟩
    by_contra hlt
    exact hk (coeffIn_eq_zero_of_lt i f k (by omega))
  refine ⟨T.max' hT, (Finset.mem_filter.mp (T.max'_mem hT)).2, fun k hk => ?_⟩
  by_contra hne
  by_cases hkN : k < f.support.sup (fun s => s i) + 1
  · have : k ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkN, hne⟩
    exact absurd (T.le_max' k this) (by omega)
  · exact hne (coeffIn_eq_zero_of_lt i f k (by omega))

lemma eval_const_of_vars_empty (f : MvPolynomial ι ℂ) (hf : f.vars ⊆ ∅) (x : ι → ℂ) :
    MvPolynomial.eval x f = MvPolynomial.constantCoeff f := by
  have := MvPolynomial.eval₂Hom_eq_constantCoeff_of_vars (RingHom.id ℂ) (g := x) (p := f)
    (fun i hi => absurd (hf hi) (by simp))
  simpa using this

lemma measurableSet_zeroTorus (f : MvPolynomial ι ℂ) :
    MeasurableSet {θ : ι → ℝ | MvPolynomial.eval (torusPoint θ) f = 0} :=
  (continuous_eval_torus f).measurable (measurableSet_singleton 0)

lemma torus_zero_set_measure_zero (S : Finset ι) : ∀ f : MvPolynomial ι ℂ, f.vars ⊆ S → f ≠ 0 →
    torusProb ι {θ | MvPolynomial.eval (torusPoint θ) f = 0} = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hS hf
    have hc : MvPolynomial.constantCoeff f ≠ 0 := by
      intro h0
      apply hf
      apply MvPolynomial.funext
      intro x
      rw [eval_const_of_vars_empty f hS, h0]
      simp
    have : {θ : ι → ℝ | MvPolynomial.eval (torusPoint θ) f = 0} = ∅ := by
      ext θ
      simp [eval_const_of_vars_empty f hS, hc]
    rw [this, measure_empty]
  | insert i S' hi ih =>
    intro f hS hf
    obtain ⟨d, hd, htop⟩ := exists_top_coeffIn i f hf
    have hg : torusProb ι {θ | MvPolynomial.eval (torusPoint θ) (coeffIn i d f) = 0} = 0 := by
      apply ih _ _ hd
      intro j hj
      have h1 := vars_coeffIn_subset i d f hj
      rw [Finset.mem_erase] at h1
      have h2 := hS h1.2
      rw [Finset.mem_insert] at h2
      exact h2.resolve_left h1.1
    apply tm_measure_null i (measurableSet_zeroTorus f)
    have hae : ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) (coeffIn i d f) ≠ 0 := by
      rw [ae_iff]; simpa using hg
    filter_upwards [hae] with θ hθ
    have hp : tmSlice i (torusPoint θ) f ≠ 0 := by
      intro h0
      apply hθ
      rw [← tmSlice_coeff, h0, Polynomial.coeff_zero]
    have := zero_set_circ_null _ hp
    convert this using 3 with t
    simp only [torusPoint_update, tm_eval_update]

lemma tm_null (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    torusProb ι {θ | MvPolynomial.eval (torusPoint θ) f = 0} = 0 :=
  torus_zero_set_measure_zero Finset.univ f (Finset.subset_univ _) hf

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma slice_abs_integral_le (f : MvPolynomial ι ℂ) (i : ι) (θ : ι → ℝ) :
    ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
        ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
  have hu : ∀ t, tmLog f (update θ i t) =
      Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := tmLog_update f θ i
  have hL : 0 ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := posLog_nonneg
  have hI : Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure := by
    simp_rw [hu]; exact integrableOn_log_circ _
  have h1 : ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure := by
    refine integral_mono hI.norm ((integrable_const _).sub hI) fun t => ?_
    have := tmLog_le f (update θ i t)
    simp only [Real.norm_eq_abs]
    rcases abs_cases (tmLog f (update θ i t)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h2 : ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure =
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) -
        (tmSlice i (torusPoint θ) f).logMahlerMeasure := by
    rw [integral_sub (integrable_const _) hI, integral_const]
    simp_rw [hu]
    rw [integral_log_circ]
    simp
  have h3 : |Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖| ≤
      ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
    rw [Polynomial.leadingCoeff, tmSlice_coeff]
    by_cases hn : (tmSlice i (torusPoint θ) f).natDegree < f.support.sup (fun s => s i) + 1
    · exact Finset.single_le_sum (f := fun k => |tmLog (coeffIn i k f) θ|)
        (fun k _ => abs_nonneg _) (Finset.mem_range.mpr hn)
    · rw [coeffIn_eq_zero_of_lt i f _ (by omega)]
      simp only [map_zero, norm_zero, Real.log_zero, abs_zero]
      exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have h4 := log_norm_leadingCoeff_le (tmSlice i (torusPoint θ) f)
  have h5 := neg_abs_le (Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖)
  linarith

lemma integrable_log_abs_on_torus (S : Finset ι) :
    ∀ f : MvPolynomial ι ℂ, f.vars ⊆ S → Integrable (tmLog f) (torusProb ι) := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hS
    have : tmLog f = fun _ => Real.log ‖MvPolynomial.constantCoeff f‖ := by
      funext θ; simp [tmLog, eval_const_of_vars_empty f hS]
    rw [this]; exact integrable_const _
  | insert i S' hi ih =>
    intro f hS
    have hsub : ∀ k, (coeffIn i k f).vars ⊆ S' := by
      intro k j hj
      have h1 := vars_coeffIn_subset i k f hj
      rw [Finset.mem_erase] at h1
      have h2 := hS h1.2
      rw [Finset.mem_insert] at h2
      exact h2.resolve_left h1.1
    have hmeas : AEStronglyMeasurable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      ((measurable_tmLog f).comp (measurable_tmUpd i)).aestronglyMeasurable
    rw [← tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable,
      integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun θ => ?_, ?_⟩
    · show Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure
      simp_rw [tmLog_update]
      exact integrableOn_log_circ _
    · have hG : Integrable (fun θ => 2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
          ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ|)
          (torusProb ι) :=
        (integrable_const _).add (integrable_finsetSum _ fun k _ => (ih _ (hsub k)).abs)
      refine hG.mono' hmeas.norm.integral_prod_right' (Filter.Eventually.of_forall fun θ => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact slice_abs_integral_le f i θ

lemma tm_int (f : MvPolynomial ι ℂ) : Integrable (tmLog f) (torusProb ι) :=
  integrable_log_abs_on_torus Finset.univ f (Finset.subset_univ _)

lemma tm_ae_ne (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) f ≠ 0 := by
  rw [ae_iff]; simpa using tm_null f hf

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

theorem torusMean_holds : TorusMeanBasicStatement ∧ TorusCoeffStatement := by
  classical
  refine ⟨fun ι _ => ⟨fun f _ => tm_int f, fun f g hf hg => ?_, fun s c => ?_⟩,
    fun ι _ f i k hk hext => ?_⟩
  · show ∫ θ, tmLog (f * g) θ ∂(torusProb ι) =
      ∫ θ, tmLog f θ ∂(torusProb ι) + ∫ θ, tmLog g θ ∂(torusProb ι)
    rw [← integral_add (tm_int f) (tm_int g)]
    apply integral_congr_ae
    filter_upwards [tm_ae_ne f hf, tm_ae_ne g hg] with θ h1 h2
    simp only [tmLog, map_mul, norm_mul]
    exact Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)
  · have hm : ∀ θ, tmLog (MvPolynomial.monomial s c) θ = Real.log ‖c‖ := by
      intro θ
      simp [tmLog, MvPolynomial.eval_monomial, Finsupp.prod, norm_prod, norm_pow,
        norm_torusPoint]
    show ∫ θ, tmLog (MvPolynomial.monomial s c) θ ∂(torusProb ι) = Real.log ‖c‖
    simp_rw [hm]
    simp
  · show ∫ θ, tmLog (coeffIn i k f) θ ∂(torusProb ι) ≤ ∫ θ, tmLog f θ ∂(torusProb ι)
    have hFi : Integrable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      (tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable).mpr (tm_int f)
    rw [tm_integral_comp i (measurable_tmLog f).aestronglyMeasurable,
      integral_prod (fun p => tmLog f (tmUpd i p)) hFi]
    refine integral_mono_ae (tm_int _) hFi.integral_prod_left ?_
    filter_upwards [tm_ae_ne _ hk] with θ hθ
    show tmLog (coeffIn i k f) θ ≤ ∫ t, tmLog f (update θ i t) ∂unitIntervalMeasure
    simp_rw [tmLog_update]
    rw [integral_log_circ]
    have hc : (tmSlice i (torusPoint θ) f).coeff k = MvPolynomial.eval (torusPoint θ) (coeffIn i k f) :=
      tmSlice_coeff i _ f k
    have hk' : (tmSlice i (torusPoint θ) f).coeff k ≠ 0 := hc ▸ hθ
    show Real.log ‖MvPolynomial.eval (torusPoint θ) (coeffIn i k f)‖ ≤ _
    rw [← hc]
    rcases hext with htop | hbot
    · exact log_norm_coeff_top_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, htop k' hk'', map_zero]
    · exact log_norm_coeff_bot_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, hbot k' hk'', map_zero]

end ReciprocityTheory.MultiplicativeHeights
