module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushR
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushV
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k : ℕ}

theorem normSq_real_smul (t : ℝ) (z : ℂ) : Complex.normSq (t • z) = t ^ 2 * Complex.normSq z := by
  rw [Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem qf_smul (t : ℝ) (p : (Fin k → ℂ) × ℂ) : qf k (t • p) = t ^ 2 * qf k p := by
  unfold qf
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, normSq_real_smul, ← Finset.mul_sum]
  ring

theorem continuous_qf : Continuous (qf k) := by
  unfold qf
  exact (continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp
    ((continuous_apply i).comp continuous_fst)).sub (Complex.continuous_normSq.comp continuous_snd)

def tau (k : ℕ) (T' : ℝ) (p : (Fin k → ℂ) × ℂ) : ℝ := Real.sqrt (-qf k p / T')

theorem continuous_tau (T' : ℝ) : Continuous (tau k T') :=
  Real.continuous_sqrt.comp (continuous_qf.neg.div_const _)

theorem coneSh_eq {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) :
    coneSh k T' E = {p | qf k p < 0 ∧ 1 < tau k T' p ∧ tau k T' p < 2 ∧ (tau k T' p)⁻¹ • p ∈ E} := by
  ext p
  constructor
  · rintro ⟨⟨v, t⟩, ⟨⟨hvE, hvS⟩, ht1, ht2⟩, rfl⟩
    have hv : qf k v = -T' := hvS
    have hq : qf k (t • v) = -(t ^ 2 * T') := by rw [qf_smul, hv]; ring
    have htau : tau k T' (t • v) = t := by
      unfold tau
      rw [hq, neg_neg, mul_div_assoc, div_self hT'.ne', mul_one, Real.sqrt_sq (by have : 1 < t := ht1; linarith)]
    have ht1' : 1 < t := ht1
    have hpos : 0 < t ^ 2 * T' := mul_pos (pow_pos (by linarith) 2) hT'
    refine ⟨by rw [hq]; linarith, by rw [htau]; exact ht1, by rw [htau]; exact ht2, ?_⟩
    rw [htau, smul_smul, inv_mul_cancel₀ (by linarith : t ≠ 0), one_smul]
    exact hvE
  · rintro ⟨hneg, h1, h2, hE⟩
    have hq0 : qf k p ≠ 0 := hneg.ne
    have ht2 : tau k T' p ^ 2 = -qf k p / T' := by
      unfold tau
      rw [Real.sq_sqrt (div_nonneg (by linarith) hT'.le)]
    refine ⟨((tau k T' p)⁻¹ • p, tau k T' p), ⟨⟨hE, ?_⟩, h1, h2⟩, ?_⟩
    · show qf k ((tau k T' p)⁻¹ • p) = -T'
      rw [qf_smul, inv_pow, ht2, inv_div, div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.2 hq0)]
      ring
    · show tau k T' p • ((tau k T' p)⁻¹ • p) = p
      rw [smul_smul, mul_inv_cancel₀ (by linarith : tau k T' p ≠ 0), one_smul]

theorem measurableSet_coneSh {T' : ℝ} (hT' : 0 < T') {E : Set ((Fin k → ℂ) × ℂ)} (hE : MeasurableSet E) :
    MeasurableSet (coneSh k T' E) := by
  rw [coneSh_eq hT']
  have hq := (continuous_qf (k := k)).measurable
  have htau := (continuous_tau (k := k) T').measurable
  simp only [Set.ofPred_and]
  refine (measurableSet_lt hq measurable_const).inter ((measurableSet_lt measurable_const htau).inter
    ((measurableSet_lt htau measurable_const).inter ?_))
  exact (htau.inv.smul measurable_id) hE

def phiR (a T' t : ℝ) : ℝ := Real.sqrt (a + t ^ 2 * T')

theorem slice_mem {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (y : Fin k → ℂ) (θ t : ℝ) (ht : 0 < t) :
    (y, ((phiR (∑ i, Complex.normSq (y i)) T' t : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) ∈ coneSh k T' E ↔
      (1 < t ∧ t < 2 ∧ hq k T' (t⁻¹ • y) θ ∈ E) := by
  set a := ∑ i, Complex.normSq (y i) with ha_def
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  set φ := phiR a T' t with hφdef
  have hφ0 : 0 ≤ φ := Real.sqrt_nonneg _
  have hφ2 : φ ^ 2 = a + t ^ 2 * T' := Real.sq_sqrt (by positivity)
  have hqv : qf k (y, (φ : ℂ) * Complex.exp (θ * Complex.I)) = -(t ^ 2 * T') := by
    unfold qf
    simp only
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (Complex.exp _),
      Complex.norm_exp_ofReal_mul_I, ← ha_def]
    linear_combination (-1 : ℝ) * hφ2
  have htau : tau k T' (y, (φ : ℂ) * Complex.exp (θ * Complex.I)) = t := by
    unfold tau
    rw [hqv, neg_neg, mul_div_assoc, div_self hT'.ne', mul_one, Real.sqrt_sq ht.le]
  have hsc : (t⁻¹ : ℝ) • ((y, (φ : ℂ) * Complex.exp (θ * Complex.I)) : (Fin k → ℂ) × ℂ) =
      hq k T' (t⁻¹ • y) θ := by
    unfold hq
    have hs : ∑ i, Complex.normSq ((t⁻¹ • y) i) = t⁻¹ ^ 2 * a := by
      simp only [Pi.smul_apply, normSq_real_smul, ← Finset.mul_sum, ha_def]
    have hr : Real.sqrt (∑ i, Complex.normSq ((t⁻¹ • y) i) + T') = t⁻¹ * φ := by
      rw [hs, show t⁻¹ ^ 2 * a + T' = (t⁻¹ * φ) ^ 2 by
        rw [mul_pow, hφ2]; field_simp]
      exact Real.sqrt_sq (mul_nonneg (inv_nonneg.2 ht.le) hφ0)
    rw [hr, Prod.smul_mk, Complex.real_smul]
    push_cast
    ring_nf
  rw [coneSh_eq hT']
  simp only [Set.mem_ofPred_eq]
  rw [htau, hsc]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    rw [hqv]
    have : 0 < t ^ 2 * T' := by positivity
    linarith

end PI.RhsWLim.W
end
end

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k : ℕ}

theorem radial {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E) (y : Fin k → ℂ)
    (θ : ℝ) :
    ∫⁻ R in Set.Ioi (0 : ℝ), ENNReal.ofReal R *
        (coneSh k T' E).indicator 1 (y, (R : ℂ) * Complex.exp (θ * Complex.I)) =
      ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * E.indicator 1 (hq k T' (t⁻¹ • y) θ) := by
  set a := ∑ i, Complex.normSq (y i) with ha_def
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hS := measurableSet_coneSh hT' hE
  set g : ℝ → ℝ≥0∞ := fun R => ENNReal.ofReal R *
    (coneSh k T' E).indicator 1 (y, (R : ℂ) * Complex.exp (θ * Complex.I)) with hgdef
  have hsupp : ((Set.Ioi (0 : ℝ)).indicator g).support ⊆ phiR a T' '' Set.Ioo 1 2 := by
    intro R hR
    rw [Function.mem_support] at hR
    have hR0 : R ∈ Set.Ioi (0 : ℝ) := by
      by_contra h
      exact hR (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hR0] at hR
    have hR0' : 0 < R := hR0
    have hmem : (y, (R : ℂ) * Complex.exp (θ * Complex.I)) ∈ coneSh k T' E := by
      by_contra h
      apply hR
      simp only [hgdef, Set.indicator_of_notMem h, mul_zero]
    rw [coneSh_eq hT'] at hmem
    obtain ⟨hneg, h1, h2, -⟩ := hmem
    refine ⟨tau k T' (y, (R : ℂ) * Complex.exp (θ * Complex.I)), ⟨h1, h2⟩, ?_⟩
    have hqv : qf k (y, (R : ℂ) * Complex.exp (θ * Complex.I)) = a - R ^ 2 := by
      unfold qf
      simp only
      rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (Complex.exp _),
        Complex.norm_exp_ofReal_mul_I, ← ha_def]
      ring
    have htau2 : tau k T' (y, (R : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 = (R ^ 2 - a) / T' := by
      unfold tau
      rw [Real.sq_sqrt (div_nonneg (by linarith) hT'.le), hqv]
      ring
    unfold phiR
    rw [htau2, div_mul_cancel₀ _ hT'.ne', show a + (R ^ 2 - a) = R ^ 2 by ring, Real.sqrt_sq hR0'.le]
  rw [← lintegral_indicator measurableSet_Ioi, ← setLIntegral_eq_of_support_subset hsupp]
  have hpos : ∀ t : ℝ, 0 < t → 0 < a + t ^ 2 * T' := fun t ht =>
    add_pos_of_nonneg_of_pos ha (mul_pos (pow_pos ht 2) hT')
  have hderiv : ∀ t ∈ Set.Ioo (1 : ℝ) 2, HasDerivWithinAt (phiR a T')
      (2 * t * T' / (2 * Real.sqrt (a + t ^ 2 * T'))) (Set.Ioo 1 2) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : HasDerivAt (fun t => a + t ^ 2 * T') (2 * t * T') t := by
      have := ((hasDerivAt_pow 2 t).mul_const T').const_add a
      exact this.congr_deriv (by ring)
    exact (h1.sqrt (hpos t ht0).ne').hasDerivWithinAt
  have hinj : Set.InjOn (phiR a T') (Set.Ioo 1 2) := by
    intro t1 h1 t2 h2 he
    have h10 : 0 < t1 := by linarith [h1.1]
    have h20 : 0 < t2 := by linarith [h2.1]
    unfold phiR at he
    rw [Real.sqrt_inj (hpos t1 h10).le (hpos t2 h20).le] at he
    have e2 : t1 ^ 2 = t2 ^ 2 := mul_right_cancel₀ hT'.ne' (by linarith)
    exact (pow_left_inj₀ h10.le h20.le two_ne_zero).1 e2
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have ht0 : 0 < t := by linarith [ht.1]
  have hφpos : 0 < Real.sqrt (a + t ^ 2 * T') := Real.sqrt_pos.2 (hpos t ht0)
  have hφ : phiR a T' t = Real.sqrt (a + t ^ 2 * T') := rfl
  rw [Set.indicator_of_mem (show phiR a T' t ∈ Set.Ioi (0 : ℝ) from hφ ▸ hφpos)]
  have hm := slice_mem hT' E y θ t ht0
  have hfac : ENNReal.ofReal |2 * t * T' / (2 * Real.sqrt (a + t ^ 2 * T'))| *
      ENNReal.ofReal (phiR a T' t) = ENNReal.ofReal (T' * t) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (div_pos (mul_pos (mul_pos two_pos ht0) hT')
      (mul_pos two_pos hφpos)), hφ]
    congr 1
    field_simp
  by_cases hE' : hq k T' (t⁻¹ • y) θ ∈ E
  · rw [Set.indicator_of_mem hE']
    simp only [hgdef]
    rw [Set.indicator_of_mem (hm.2 ⟨ht.1, ht.2, hE'⟩)]
    simp only [Pi.one_apply, mul_one]
    exact hfac
  · rw [Set.indicator_of_notMem hE']
    simp only [hgdef]
    rw [Set.indicator_of_notMem (fun h => hE' (hm.1 h).2.2)]
    simp

end PI.RhsWLim.W
end
end

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k : ℕ}

theorem lintegral_inv_smul {t : ℝ} (ht : 0 < t) {G : (Fin k → ℂ) → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ y, G (t⁻¹ • y) = ENNReal.ofReal (t ^ Module.finrank ℝ (Fin k → ℂ)) * ∫⁻ y, G y := by
  have hH : (volume : Measure (Fin k → ℂ)).IsAddHaarMeasure := inferInstance
  set f : (Fin k → ℂ) →ₗ[ℝ] (Fin k → ℂ) := t⁻¹ • LinearMap.id with hfdef
  have hdet : LinearMap.det f = (t⁻¹) ^ Module.finrank ℝ (Fin k → ℂ) := by
    rw [hfdef, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdet0 : LinearMap.det f ≠ 0 := by rw [hdet]; exact pow_ne_zero _ (inv_ne_zero ht.ne')
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure (Fin k → ℂ))) hdet0
  rw [hdet, inv_pow, inv_inv, abs_of_pos (pow_pos ht _)] at hmap
  have hfm : Measurable f := f.continuous_of_finiteDimensional.measurable
  have e : (fun y : Fin k → ℂ => G (t⁻¹ • y)) = fun y => G (f y) := by
    funext y
    simp [hfdef]
  rw [e, ← lintegral_map hG hfm, hmap, lintegral_smul_measure, smul_eq_mul]

theorem polar_symm_exp (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (p.2 * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem coneVol : ConeVol := by
  intro k T' hT'
  set d := Module.finrank ℝ (Fin k → ℂ) with hd
  set C : ℝ≥0∞ := ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) with hC
  refine ⟨C, ?_, ?_, fun E hE => ?_⟩
  · apply ne_of_gt
    calc (0 : ℝ≥0∞) < ENNReal.ofReal T' * volume (Set.Ioo (1 : ℝ) 2) := by
          rw [Real.volume_Ioo]
          exact ENNReal.mul_pos (by simpa using hT') (by norm_num)
      _ = ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal T' := (setLIntegral_const _ _).symm
      _ ≤ C := setLIntegral_mono' measurableSet_Ioo fun t ht => by
          have ht1 : 1 < t := ht.1
          rw [← ENNReal.ofReal_mul (by nlinarith)]
          apply ENNReal.ofReal_le_ofReal
          have h1 : 1 ≤ t ^ d := one_le_pow₀ ht1.le
          have h2 : 1 ≤ t * t ^ d := one_le_mul_of_one_le_of_one_le ht1.le h1
          calc T' = T' * 1 := (mul_one _).symm
            _ ≤ T' * (t * t ^ d) := mul_le_mul_of_nonneg_left h2 hT'.le
            _ = T' * t * t ^ d := by ring
  · apply ne_of_lt
    calc C ≤ ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * 2 * 2 ^ d) :=
          setLIntegral_mono' measurableSet_Ioo fun t ht => by
            have ht1 : 1 < t := ht.1
            have ht2 : t < 2 := ht.2
            rw [← ENNReal.ofReal_mul (by nlinarith)]
            apply ENNReal.ofReal_le_ofReal
            have h1 : t ^ d ≤ 2 ^ d := pow_le_pow_left₀ (by linarith) ht2.le d
            have h2 : 0 ≤ t ^ d := pow_nonneg (by linarith) d
            have h3 : T' * t ≤ T' * 2 := by nlinarith
            calc T' * t * t ^ d ≤ T' * 2 * t ^ d := by nlinarith
              _ ≤ T' * 2 * 2 ^ d := by nlinarith
      _ < ⊤ := by
          rw [setLIntegral_const, Real.volume_Ioo]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hS := measurableSet_coneSh hT' hE
  have hf : Measurable (E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)) := measurable_one.indicator hE
  set F3 : (Fin k → ℂ) → ℝ → ℝ → ℝ≥0∞ := fun y θ t =>
    ENNReal.ofReal (T' * t) * E.indicator 1 (hq k T' (t⁻¹ • y) θ) with hF3
  have hF3m : Measurable (fun p : ((Fin k → ℂ) × ℝ) × ℝ => F3 p.1.1 p.1.2 p.2) := by
    refine (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_snd)).mul ?_
    exact hf.comp ((continuous_hq k T').measurable.comp
      ((measurable_snd.inv.smul (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)))

  have hfib : ∀ y : Fin k → ℂ, volume (Prod.mk y ⁻¹' coneSh k T' E) =
      ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 y θ t := by
    intro y
    have hSy : MeasurableSet (Prod.mk y ⁻¹' coneSh k T' E) := measurable_prodMk_left hS
    have hg : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 •
        (Prod.mk y ⁻¹' coneSh k T' E).indicator (1 : ℂ → ℝ≥0∞) ((p.1 : ℂ) * Complex.exp (p.2 * Complex.I))) := by
      refine (ENNReal.measurable_ofReal.comp measurable_fst).smul ?_
      exact (measurable_one.indicator hSy).comp ((Complex.continuous_ofReal.comp continuous_fst).mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))).measurable
    rw [← lintegral_indicator_one hSy, ← Complex.lintegral_comp_polarCoord_symm]
    simp_rw [polar_symm_exp]
    rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hg.aemeasurable,
      lintegral_lintegral_swap hg.aemeasurable]
    refine lintegral_congr fun θ => ?_
    rw [hF3]
    dsimp only
    rw [← radial hT' E hE y θ]
    refine lintegral_congr fun R => ?_
    rw [smul_eq_mul]
    rfl
  rw [Measure.volume_eq_prod, Measure.prod_apply hS]
  simp_rw [hfib]

  have hm2 : Measurable (fun p : (Fin k → ℂ) × ℝ => ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 p.1 p.2 t) :=
    hF3m.lintegral_prod_right'
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have hm3 : ∀ θ : ℝ, Measurable (fun p : (Fin k → ℂ) × ℝ => F3 p.1 θ p.2) := fun θ =>
    hF3m.comp (((measurable_fst).prodMk measurable_const).prodMk measurable_snd)
  have step : ∀ θ : ℝ, ∫⁻ y, ∫⁻ t in Set.Ioo (1 : ℝ) 2, F3 y θ t =
      ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) *
        ∫⁻ y, E.indicator 1 (hq k T' y θ) := by
    intro θ
    rw [lintegral_lintegral_swap (hm3 θ).aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    rw [hF3]
    dsimp only
    have hGm : Measurable (fun y : Fin k → ℂ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
      hf.comp ((continuous_hq k T').measurable.comp (measurable_id.prodMk measurable_const))
    rw [lintegral_const_mul (ENNReal.ofReal (T' * t)) (f := fun x => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞)
      (hq k T' (t⁻¹ • x) θ)) (hGm.comp (measurable_const_smul _))]
    have hsc := lintegral_inv_smul ht0 hGm
    rw [hsc, mul_assoc]
  simp_rw [step]
  have hP : Measurable (fun θ : ℝ => ∫⁻ y, E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) := by
    have : Measurable (fun p : (Fin k → ℂ) × ℝ => E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' p.1 p.2)) :=
      hf.comp (continuous_hq k T').measurable
    exact this.lintegral_prod_left'
  have hct : Measurable (fun t : ℝ => ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d)) :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const d))
  have hprod : Measurable (Function.uncurry fun (θ : ℝ) (t : ℝ) =>
      ENNReal.ofReal (T' * t) * ENNReal.ofReal (t ^ d) * ∫⁻ y, E.indicator (1 : (Fin k → ℂ) × ℂ → ℝ≥0∞) (hq k T' y θ)) :=
    (hct.comp measurable_snd).mul (hP.comp measurable_fst)
  rw [lintegral_lintegral_swap hprod.aemeasurable]
  unfold hqI
  rw [hC, ← lintegral_mul_const _ hct]
  refine lintegral_congr fun t => ?_
  rw [lintegral_const_mul _ hP]

end PI.RhsWLim.W
