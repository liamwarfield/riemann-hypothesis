module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeB
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeA
noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.UnitA

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)

def pr (a b : G → ℂ) : ℂ := ∫ x, star (a x) * b x ∂μ

def nrm (a : G → ℂ) : ℝ := (eLpNorm a 2 μ).toReal

variable {μ}

theorem pr_int {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun x => star (a x) * b x) μ := by
  have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)
  refine h.congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx1 hx2
  rw [hx1, hx2, RCLike.inner_apply, starRingEnd_apply, mul_comm]

theorem pr_eq_inner {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    pr μ a b = inner ℂ (ha.toLp a) (hb.toLp b) := by
  rw [MeasureTheory.L2.inner_def]
  unfold pr
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hx1 hx2
  rw [hx1, hx2, RCLike.inner_apply, starRingEnd_apply, mul_comm]

theorem pr_bound {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ‖pr μ a b‖ ≤ nrm μ a * nrm μ b := by
  rw [pr_eq_inner ha hb]
  have h := norm_inner_le_norm (𝕜 := ℂ) (ha.toLp a) (hb.toLp b)
  simpa only [nrm, Lp.norm_toLp] using h

theorem pr_star (a b : G → ℂ) : star (pr μ a b) = pr μ b a := by
  unfold pr
  have h : ∫ x, (starRingEnd ℂ) (star (a x) * b x) ∂μ =
      (starRingEnd ℂ) (∫ x, star (a x) * b x ∂μ) := integral_conj
  simp only [starRingEnd_apply] at h
  rw [← h]
  congr 1
  funext x
  rw [star_mul, star_star]

theorem pr_sub_left {a a₁ b : G → ℂ} (ha : MemLp a 2 μ) (ha₁ : MemLp a₁ 2 μ) (hb : MemLp b 2 μ) :
    pr μ (fun x => a x - a₁ x) b = pr μ a b - pr μ a₁ b := by
  unfold pr
  rw [← integral_sub (pr_int ha hb) (pr_int ha₁ hb)]
  congr 1
  funext x
  rw [star_sub, sub_mul]

theorem pr_neg_right (a b : G → ℂ) : pr μ a (fun x => -b x) = -pr μ a b := by
  unfold pr
  rw [← integral_neg]
  congr 1
  funext x
  rw [mul_neg]

theorem int_norm_le {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ x, ‖star (a x) * b x‖ ∂μ ≤ nrm μ a * nrm μ b := by
  have hA : MemLp (fun x => ‖a x‖) 2 μ := ha.norm
  have hB : MemLp (fun x => ‖b x‖) 2 μ := hb.norm
  have h1 : ∫ x, ‖star (a x) * b x‖ ∂μ = inner ℝ (hA.toLp _) (hB.toLp _) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply, norm_mul, norm_star]
    simp only [starRingEnd_apply, star_trivial]
    ring
  rw [h1]
  calc inner ℝ (hA.toLp _) (hB.toLp _) ≤ ‖hA.toLp _‖ * ‖hB.toLp _‖ := real_inner_le_norm _ _
    _ = nrm μ a * nrm μ b := by
      simp only [nrm, Lp.norm_toLp, eLpNorm_norm]
      rw [eLpNorm_norm a ha.aestronglyMeasurable, eLpNorm_norm b hb.aestronglyMeasurable]

theorem pr_add_left {a a₁ b : G → ℂ} (ha : MemLp a 2 μ) (ha₁ : MemLp a₁ 2 μ) (hb : MemLp b 2 μ) :
    pr μ (a + a₁) b = pr μ a b + pr μ a₁ b := by
  unfold pr
  rw [← integral_add (pr_int ha hb) (pr_int ha₁ hb)]
  congr 1
  funext x
  simp [Pi.add_apply, star_add]
  ring

theorem pr_add_right {a b b₁ : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hb₁ : MemLp b₁ 2 μ) :
    pr μ a (b + b₁) = pr μ a b + pr μ a b₁ := by
  unfold pr
  rw [← integral_add (pr_int ha hb) (pr_int ha hb₁)]
  congr 1
  funext x
  simp [Pi.add_apply]
  ring

theorem pr_smul_left (c : ℂ) (a b : G → ℂ) : pr μ (c • a) b = star c * pr μ a b := by
  unfold pr
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [smul_eq_mul, star_mul]
  ring

theorem pr_smul_right (c : ℂ) (a b : G → ℂ) : pr μ a (c • b) = c * pr μ a b := by
  unfold pr
  rw [← integral_const_mul]
  congr 1
  funext x
  simp [smul_eq_mul]
  ring

theorem pr_self_re {a : G → ℂ} (ha : MemLp a 2 μ) :
    pr μ a a = ((∫ x, ‖a x‖ ^ 2 ∂μ : ℝ) : ℂ) ∧ Integrable (fun x => ‖a x‖ ^ 2) μ := by
  have hI : Integrable (fun x => ‖a x‖ ^ 2) μ := by
    refine (pr_int ha ha).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, norm_star, sq]
  refine ⟨?_, hI⟩
  unfold pr
  rw [← integral_complex_ofReal]
  congr 1
  funext x
  rw [Complex.ofReal_pow]
  exact Complex.conj_mul' (a x)

section Invariant

variable [μ.IsMulRightInvariant]

theorem memLp_rt {a : G → ℂ} (ha : MemLp a 2 μ) (g : G) : MemLp (fun x => a (x * g)) 2 μ := by
  exact ha.comp_measurePreserving (measurePreserving_mul_right μ g)

theorem nrm_rt {a : G → ℂ} (ha : AEStronglyMeasurable a μ) (g : G) :
    nrm μ (fun x => a (x * g)) = nrm μ a := by
  unfold nrm
  have h := eLpNorm_comp_measurePreserving (p := 2) ha (measurePreserving_mul_right μ g)
  exact congrArg ENNReal.toReal h

theorem pr_rt (a b : G → ℂ) (g : G) :
    pr μ (fun x => a (x * g)) (fun x => b (x * g)) = pr μ a b := by
  unfold pr
  exact integral_mul_right_eq_self (fun x => star (a x) * b x) g

theorem pr_shift (a b : G → ℂ) (g : G) :
    pr μ (fun x => a (x * g)) b = pr μ a (fun x => b (x * g⁻¹)) := by
  rw [← pr_rt (fun x => a (x * g)) b g⁻¹]
  simp only [inv_mul_cancel_right, mul_inv_cancel_right]

end Invariant

theorem ftc {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) {a a' : G → ℂ} (ha' : Continuous a')
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) (x : G) (t : ℝ) :
    ∫ s in (0:ℝ)..t, a' (x * φ s) = a (x * φ t) - a x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => a (x * φ s))
    (f' := fun s => a' (x * φ s)) (a := 0) (b := t) (fun s _ => hd x s)
    ((ha'.comp (continuous_const.mul hφc)).intervalIntegrable 0 t)
  simpa only [hφ0, mul_one] using h

section Flow

variable [μ.IsMulRightInvariant] [SFinite μ]

theorem incr {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) {a a' b : G → ℂ}
    (ha' : Continuous a') (hb : Continuous b)
    (haL : MemLp a 2 μ) (ha'L : MemLp a' 2 μ) (hbL : MemLp b 2 μ)
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => pr μ (fun x => a' (x * φ s)) b) MeasureTheory.volume 0 t ∧
    pr μ (fun x => a (x * φ t)) b - pr μ a b =
      ∫ s in (0:ℝ)..t, pr μ (fun x => a' (x * φ s)) b := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0:ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hFc : Continuous (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2) :=
    (continuous_star.comp (ha'.comp (continuous_snd.mul (hφc.comp continuous_fst)))).mul
      (hb.comp continuous_snd)
  have hm : AEStronglyMeasurable (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2)
      ((volume.restrict (Set.Ioc (0:ℝ) t)).prod μ) := hFc.aestronglyMeasurable
  have hFint : Integrable (fun p : ℝ × G => star (a' (p.2 * φ p.1)) * b p.2)
      ((volume.restrict (Set.Ioc (0:ℝ) t)).prod μ) := by
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall fun s => pr_int (memLp_rt ha'L (φ s)) hbL, ?_⟩
    refine Integrable.mono' (integrable_const (nrm μ a' * nrm μ b)) hm.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have h := int_norm_le (memLp_rt ha'L (φ s)) hbL
    rwa [nrm_rt ha'L.aestronglyMeasurable] at h
  have hInner := hFint.integral_prod_left
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hInner, ?_⟩
  have h1 : ∀ x, star (a (x * φ t) - a x) * b x =
      ∫ s in Set.Ioc 0 t, star (a' (x * φ s)) * b x := by
    intro x
    rw [← ftc hφc hφ0 ha' hd x t, intervalIntegral.integral_of_le ht, integral_mul_const]
    congr 1
    have h := integral_conj (μ := volume.restrict (Set.Ioc (0:ℝ) t)) (f := fun s => a' (x * φ s))
    simp only [starRingEnd_apply] at h
    exact h.symm
  have hL : pr μ (fun x => a (x * φ t)) b - pr μ a b = ∫ x, star (a (x * φ t) - a x) * b x ∂μ := by
    rw [← pr_sub_left (memLp_rt haL (φ t)) haL hbL]
    rfl
  rw [hL, intervalIntegral.integral_of_le ht]
  simp_rw [h1]
  exact (integral_integral_swap (f := fun s x => star (a' (x * φ s)) * b x) hFint).symm

theorem small_zero {D : ℂ} {C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖D‖ ≤ t * C) : D = 0 := by
  by_contra hD
  have hpos : 0 < ‖D‖ := norm_pos_iff.mpr hD
  have h1 := h 1 one_pos le_rfl
  have hC : 0 < C := by linarith
  have hC0 : C ≠ 0 := hC.ne'
  have ht0 : 0 < min 1 (‖D‖ / (2 * C)) := lt_min one_pos (div_pos hpos (by linarith))
  have ht1 : min 1 (‖D‖ / (2 * C)) ≤ 1 := min_le_left _ _
  have ht2 : min 1 (‖D‖ / (2 * C)) ≤ ‖D‖ / (2 * C) := min_le_right _ _
  have h2 := h _ ht0 ht1
  have h3 : min 1 (‖D‖ / (2 * C)) * C ≤ ‖D‖ / 2 := by
    calc min 1 (‖D‖ / (2 * C)) * C ≤ ‖D‖ / (2 * C) * C := mul_le_mul_of_nonneg_right ht2 hC.le
      _ = ‖D‖ / 2 := by field_simp <;> ring
  linarith

private theorem negder_lemma {φ : ℝ → G} {a a' : G → ℂ}
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t) :
    ∀ x t, HasDerivAt (fun s => a (x * φ (-s))) (-a' (x * φ (-t))) t := by
  intro x t
  have h := (hd x (-t)).scomp t (hasDerivAt_id t).neg
  simpa [Function.comp_def] using h

private theorem inv_lemma_2 {φ : ℝ → G} (hφ0 : φ 0 = 1) (hφa : ∀ s t, φ (s + t) = φ s * φ t) (s : ℝ) :
    (φ s)⁻¹ = φ (-s) := by
  have h : φ s * φ (-s) = 1 := by
    rw [← hφa]
    simp [hφ0]
  exact (eq_inv_of_mul_eq_one_right h).symm

private theorem lin_lemma_3 {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1)
    (hφa : ∀ s t, φ (s + t) = φ s * φ t) {a a' b b' : G → ℂ}
    (ha' : Continuous a') (hb : Continuous b) (hb' : Continuous b')
    (haL : MemLp a 2 μ) (ha'L : MemLp a' 2 μ) (hbL : MemLp b 2 μ) (hb'L : MemLp b' 2 μ)
    (hd : ∀ x t, HasDerivAt (fun s => a (x * φ s)) (a' (x * φ t)) t)
    (hdb : ∀ x t, HasDerivAt (fun s => b (x * φ s)) (b' (x * φ t)) t) {t : ℝ} (ht : 0 ≤ t) :
    ‖(pr μ (fun x => a (x * φ t)) b - pr μ a b) - (t : ℂ) * pr μ a' b‖ ≤
      t * (t * (nrm μ a' * nrm μ b')) := by
  have hψc : Continuous fun s => φ (-s) := hφc.comp continuous_neg
  obtain ⟨hI, hE⟩ := incr hφc hφ0 ha' hb haL ha'L hbL hd ht
  have hbd : ∀ s ∈ Set.uIoc 0 t,
      ‖pr μ (fun x => a' (x * φ s)) b - pr μ a' b‖ ≤ t * (nrm μ a' * nrm μ b') := by
    intro s hs
    rw [Set.uIoc_of_le ht] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have e1 : pr μ (fun x => a' (x * φ s)) b = pr μ a' (fun x => b (x * φ (-s))) := by
      rw [pr_shift, inv_lemma_2 hφ0 hφa]
    have e2 : pr μ (fun x => b (x * φ (-s))) a' - pr μ b a' =
        ∫ r in (0:ℝ)..s, pr μ (fun x => -b' (x * φ (-r))) a' :=
      (incr (φ := fun s => φ (-s)) hψc (by simp [hφ0]) (a' := fun y => -b' y) hb'.neg ha' hbL
        hb'L.neg ha'L (negder_lemma hdb) hs0).2
    have e3 : pr μ (fun x => a' (x * φ s)) b - pr μ a' b =
        star (pr μ (fun x => b (x * φ (-s))) a' - pr μ b a') := by
      rw [e1, star_sub, pr_star, pr_star]
    have hC : ∀ r ∈ Set.uIoc 0 s, ‖pr μ (fun x => -b' (x * φ (-r))) a'‖ ≤ nrm μ b' * nrm μ a' := by
      intro r _
      have h := pr_bound (memLp_rt hb'L.neg (φ (-r))) ha'L
      have hn : nrm μ (fun x => (-b') (x * φ (-r))) = nrm μ b' := by
        rw [nrm_rt hb'L.neg.aestronglyMeasurable]
        unfold nrm
        rw [eLpNorm_neg]
      rw [hn] at h
      exact h
    rw [e3, norm_star, e2]
    calc _ ≤ (nrm μ b' * nrm μ a') * |s - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hC
      _ ≤ t * (nrm μ a' * nrm μ b') := by
        rw [sub_zero, abs_of_nonneg hs0]
        have h1 : 0 ≤ nrm μ a' := ENNReal.toReal_nonneg
        have h2 : 0 ≤ nrm μ b' := ENNReal.toReal_nonneg
        have h3 : 0 ≤ nrm μ a' * nrm μ b' := mul_nonneg h1 h2
        nlinarith [hs.2]
  have hmain : pr μ (fun x => a (x * φ t)) b - pr μ a b - (t : ℂ) * pr μ a' b =
      ∫ s in (0:ℝ)..t, (pr μ (fun x => a' (x * φ s)) b - pr μ a' b) := by
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const, intervalIntegral.integral_const, ← hE,
      sub_zero, Complex.real_smul]
  rw [hmain]
  calc _ ≤ (t * (nrm μ a' * nrm μ b')) * |t - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = _ := by rw [sub_zero, abs_of_nonneg ht]; ring

theorem skew {φ : ℝ → G} (hφc : Continuous φ) (hφ0 : φ 0 = 1) (hφa : ∀ s t, φ (s + t) = φ s * φ t)
    {u u' v v' : G → ℂ} (hu : Continuous u) (hu' : Continuous u') (hv : Continuous v)
    (hv' : Continuous v')
    (huL : MemLp u 2 μ) (hu'L : MemLp u' 2 μ) (hvL : MemLp v 2 μ) (hv'L : MemLp v' 2 μ)
    (hdu : ∀ x t, HasDerivAt (fun s => u (x * φ s)) (u' (x * φ t)) t)
    (hdv : ∀ x t, HasDerivAt (fun s => v (x * φ s)) (v' (x * φ t)) t) :
    pr μ u' v = -pr μ u v' := by
  have hψc : Continuous fun s => φ (-s) := hφc.comp continuous_neg
  have hψa : ∀ s t, φ (-(s + t)) = φ (-s) * φ (-t) := fun s t => by rw [neg_add, hφa]
  have hnv : nrm μ (fun y => -v' y) = nrm μ v' := by
    unfold nrm
    rw [show (fun y => -v' y) = -v' from rfl, eLpNorm_neg]
  have hnu : nrm μ (fun y => -u' y) = nrm μ u' := by
    unfold nrm
    rw [show (fun y => -u' y) = -u' from rfl, eLpNorm_neg]
  suffices h : pr μ u' v + pr μ u v' = 0 by linear_combination h
  apply small_zero (C := 2 * (nrm μ u' * nrm μ v'))
  intro t ht0 ht1
  have E1 : ‖(pr μ (fun x => u (x * φ t)) v - pr μ u v) - (t : ℂ) * pr μ u' v‖ ≤
      t * (t * (nrm μ u' * nrm μ v')) :=
    lin_lemma_3 hφc hφ0 hφa hu' hv hv' huL hu'L hvL hv'L hdu hdv ht0.le
  have E2 : ‖(pr μ (fun x => v (x * φ (-t))) u - pr μ v u) - (t : ℂ) * pr μ (fun y => -v' y) u‖ ≤
      t * (t * (nrm μ (fun y => -v' y) * nrm μ (fun y => -u' y))) :=
    lin_lemma_3 (φ := fun s => φ (-s)) hψc (by simp [hφ0]) hψa hv'.neg hu hu'.neg hvL hv'L.neg huL
      hu'L.neg (negder_lemma hdv) (negder_lemma hdu) ht0.le
  rw [hnv, hnu] at E2
  have e1 : pr μ (fun x => u (x * φ t)) v = pr μ u (fun x => v (x * φ (-t))) := by
    rw [pr_shift, inv_lemma_2 hφ0 hφa]
  have e2 : star ((pr μ (fun x => v (x * φ (-t))) u - pr μ v u) - (t : ℂ) * pr μ (fun y => -v' y) u) =
      (pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v' := by
    rw [star_sub, star_sub, star_mul', pr_star, pr_star, pr_star, e1, Complex.star_def,
      Complex.conj_ofReal, pr_neg_right]
    ring
  have E3 : ‖(pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v'‖ ≤
      t * (t * (nrm μ u' * nrm μ v')) := by
    rw [← e2, norm_star]
    linarith [E2]
  have key : (t : ℂ) * (pr μ u' v + pr μ u v') =
      ((pr μ (fun x => u (x * φ t)) v - pr μ u v) + (t : ℂ) * pr μ u v') -
        ((pr μ (fun x => u (x * φ t)) v - pr μ u v) - (t : ℂ) * pr μ u' v) := by ring
  have hn : ‖(t : ℂ) * (pr μ u' v + pr μ u v')‖ ≤ 2 * (t * (t * (nrm μ u' * nrm μ v'))) := by
    rw [key]
    exact (norm_sub_le _ _).trans (by linarith)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le] at hn
  exact le_of_mul_le_mul_left (by linarith : t * ‖pr μ u' v + pr μ u v'‖ ≤
    t * (t * (2 * (nrm μ u' * nrm μ v')))) ht0

end Flow

end ReciprocityTheory.ChartRestriction.DS.UnitA
end
end

noncomputable section

open Finset MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.UnitB

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def sg (ε : Fin n → Bool) (c : Fin n) : ℂ := if ε c then 1 else -1

theorem sg_mul_self (ε : Fin n → Bool) (c : Fin n) : sg ε c * sg ε c = 1 := by
  unfold sg
  split_ifs <;> norm_num

theorem star_sg (ε : Fin n → Bool) (c : Fin n) : star (sg ε c) = sg ε c := by
  unfold sg
  split_ifs <;> simp

theorem norm_sg (ε : Fin n → Bool) (c : Fin n) : ‖sg ε c‖ = 1 := by
  unfold sg
  split_ifs <;> simp

theorem Jm_eq (ε : Fin n → Bool) : Jm ε = Matrix.diagonal (sg ε) := rfl

def wt (dual : Bool) (ε : Fin n → Bool) (ξ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : ℂ :=
  cond dual (sg ε c * star (x ξ c)) (x ξ c)

theorem norm_wt (dual : Bool) (ε : Fin n → Bool) (ξ : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) :
    ‖wt dual ε ξ x c‖ = ‖x ξ c‖ := by
  cases dual
  · rfl
  · simp only [wt, cond_true, norm_mul, norm_sg, norm_star, one_mul]

theorem norm_entry_le (x : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖x i j‖ ≤ Real.sqrt (S7.hs x) := by
  have h1 : ‖x i j‖ ^ 2 ≤ ∑ j', ‖x i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖x i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
  have h2 : ∑ j', ‖x i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖x i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖x i' j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i)
  have h3 : ‖x i j‖ ^ 2 ≤ S7.hs x := by
    simp only [S7.hs, Formalism.REAL.hs]
    exact h1.trans h2
  have h4 := Real.abs_le_sqrt h3
  rwa [abs_of_nonneg (norm_nonneg _)] at h4

theorem continuous_wt (dual : Bool) (ε : Fin n → Bool) (ξ c : Fin n) :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => wt dual ε ξ x c) := by
  have he : Continuous (fun x : Matrix (Fin n) (Fin n) ℂ => x ξ c) :=
    (continuous_apply c).comp (continuous_apply ξ)
  cases dual
  · exact he
  · exact continuous_const.mul he.star

def wtLin (dual : Bool) (ε : Fin n → Bool) (ξ c : Fin n) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ where
  toFun x := wt dual ε ξ x c
  map_add' x y := by cases dual <;> simp [wt, mul_add]
  map_smul' r x := by
    cases dual <;> simp [wt, Complex.real_smul, Complex.conj_ofReal]; ring

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def cf (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H) (ξ : Fin n)
    (F : Fin n → H) : Formalism.REAL.UJ ε → ℂ :=
  fun g => ∑ c, wt dual ε ξ (Formalism.MainNotions.S.umat g) c * inner ℂ y (σ (Formalism.MainNotions.S.umat g) (F c))

theorem cf_add (dual : Bool) (y : H) (ξ : Fin n) (F F' : Fin n → H) :
    cf dual ε σ y ξ (F + F') = cf dual ε σ y ξ F + cf dual ε σ y ξ F' := by
  funext g
  simp only [cf, Pi.add_apply, map_add (f := _), inner_add_right, mul_add, Finset.sum_add_distrib]

theorem cf_smul (dual : Bool) (y : H) (ξ : Fin n) (a : ℂ) (F : Fin n → H) :
    cf dual ε σ y ξ (a • F) = a • cf dual ε σ y ξ F := by
  funext g
  simp only [cf, Pi.smul_apply, map_smul, inner_smul_right, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem continuous_umat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_orbit (hσ : IsURepOn (UJset ε) σ) (v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) := (hσ.2.2 v).comp_continuous continuous_umat fun g => g.2

theorem continuous_cf (hσ : IsURepOn (UJset ε) σ) (dual : Bool) (y : H) (ξ : Fin n) (F : Fin n → H) :
    Continuous (cf dual ε σ y ξ F) := by
  unfold cf
  exact continuous_finsetSum _ fun c _ => ((continuous_wt dual ε ξ c).comp continuous_umat).mul
    (continuous_const.inner (continuous_orbit hσ (F c)))

theorem memLp_cf (hσ : IsURepOn (UJset ε) σ) (dual : Bool) (y : H) (ξ : Fin n) (F : Fin n → H)
    (hW : ∀ c, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ y (σ (Formalism.MainNotions.S.umat g) (F c)))
      2 (Formalism.REAL.muG ε)) :
    MemLp (cf dual ε σ y ξ F) 2 (Formalism.REAL.muG ε) := by
  unfold cf
  refine MeasureTheory.memLp_finsetSum _ fun c _ => ?_
  refine MemLp.of_le (hW c) ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact (((continuous_wt dual ε ξ c).comp continuous_umat).mul
      (continuous_const.inner (continuous_orbit hσ (F c)))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_wt]
    exact mul_le_mul_of_nonneg_right (norm_entry_le _ ξ c) (norm_nonneg _)

end Rep

end ReciprocityTheory.ChartRestriction.DS.UnitB
end
end

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.UnitB

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {ε : Fin n → Bool}

def toG (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset ε) : Formalism.REAL.UJ ε :=
  ⟨⟨g, Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε, (Formalism.REAL.indefinite_unitary_inv_closed n ε g hg).1,
    (Formalism.REAL.indefinite_unitary_inv_closed n ε g hg).2⟩, hg⟩

theorem umat_mul (a b : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.umat (a * b) = Formalism.MainNotions.S.umat a * Formalism.MainNotions.S.umat b := rfl

theorem umat_one : Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε) = 1 := rfl

def ex (X : Matrix (Fin n) (Fin n) ℂ) (hX : inG ε X) (s : ℝ) : Formalism.REAL.UJ ε :=
  toG (NormedSpace.exp ((s : ℂ) • X)) (exp_smul_mem_UJset hX s)

theorem umat_ex {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s : ℝ) :
    Formalism.MainNotions.S.umat (ex X hX s) = NormedSpace.exp ((s : ℂ) • X) := rfl

theorem ex_zero {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : ex X hX 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  show Formalism.MainNotions.S.umat (ex X hX 0) = Formalism.MainNotions.S.umat (1 : Formalism.REAL.UJ ε)
  rw [umat_ex, umat_one, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]

theorem ex_add {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (s t : ℝ) :
    ex X hX (s + t) = ex X hX s * ex X hX t := by
  apply Subtype.ext
  apply Units.ext
  show Formalism.MainNotions.S.umat (ex X hX (s + t)) = Formalism.MainNotions.S.umat (ex X hX s * ex X hX t)
  rw [umat_mul, umat_ex, umat_ex, umat_ex, Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem hasDerivAt_expm (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (NormedSpace.exp ((t : ℂ) • X) * X) t := by
  have h := hasDerivAt_exp_smul_const X t
  rw [show (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X)) = fun s : ℝ => NormedSpace.exp (s • X) from
    funext fun s => by rw [Complex.coe_smul], Complex.coe_smul]
  exact h

theorem continuous_ex {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : Continuous (ex X hX) := by
  have h1 : Continuous (fun s : ℝ => NormedSpace.exp ((s : ℂ) • X)) :=
    continuous_iff_continuousAt.2 fun s => (hasDerivAt_expm X s).continuousAt
  unfold ex toG
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨h1, ?_⟩) _
  show Continuous fun s : ℝ => Formalism.REAL.Jm ε * (NormedSpace.exp ((s : ℂ) • X))ᴴ * Formalism.REAL.Jm ε
  exact (continuous_const.mul h1.matrix_conjTranspose).mul continuous_const

theorem hasDerivAt_wt (dual : Bool) (ξ c : Fin n) (Y X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => wt dual ε ξ (Y * NormedSpace.exp ((t : ℂ) • X)) c) (wt dual ε ξ (Y * X) c) 0 := by
  have h1 := (hasDerivAt_expm X 0).const_mul Y
  rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, one_mul] at h1
  exact (LinearMap.toContinuousLinearMap (wtLin dual ε ξ c)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

end Deriv

theorem inG_entry {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (a b : Fin n) :
    sg ε a * star (X b a) = -(sg ε b * X a b) := by
  have hX' : Xᴴ * Jm ε + Jm ε * X = 0 := hX
  have h := congrFun (congrFun hX' a) b
  simp only [Matrix.add_apply, Matrix.zero_apply, Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.conjTranspose_apply] at h
  have ha := sg_mul_self ε a
  have hb := sg_mul_self ε b
  linear_combination (sg ε a * sg ε b) * h - (sg ε a * star (X b a)) * hb - (sg ε b * X a b) * ha

theorem wt_deriv_id (dual : Bool) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (ξ : Fin n)
    (Y : Matrix (Fin n) (Fin n) ℂ) (I : Fin n → ℂ) :
    ∑ c, wt dual ε ξ (Y * X) c * I c =
      ∑ c, wt dual ε ξ Y c * cond dual (-∑ a, X a c * I a) (∑ b, X c b * I b) := by
  cases dual
  · simp only [wt, cond_false, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
  · have key : ∀ b c, sg ε c * star (X b c) = -(sg ε b * X c b) := fun b c => inG_entry hX c b
    simp only [wt, cond_true, Matrix.mul_apply, star_sum, star_mul', Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    linear_combination (star (Y ξ b) * I c) * key b c

def mx {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Fin n → Fin n → Module.End ℂ W)
    (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ W := ∑ a, ∑ b, X a b • T a b

theorem mx_apply_tensF {M : Type*} [AddCommGroup M] [Module ℂ M] (dual : Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (X : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → M) (c : Fin n) :
    mx (tensF dual E) X f c = actM E X (f c) + cond dual (-∑ a, X a c • f a) (∑ b, X c b • f b) := by
  cases dual
  · simp [mx, tensF, tensV, actM, coordV, Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_ite,
      Finset.sum_apply, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ ha
      rw [if_neg (Ne.symm ha)]
      simp
    · intro h
      exact absurd (Finset.mem_univ c) h
  · simp [mx, tensF, tensVd, actM, coordV, Finset.smul_sum, smul_sub, Finset.sum_sub_distrib, smul_ite,
      Finset.sum_apply, LinearMap.sum_apply, sub_eq_add_neg]
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ite_apply, LinearMap.proj_apply,
      LinearMap.zero_apply, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 2
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
      simp
    · intro h
      exact absurd (Finset.mem_univ c) h

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem sig_mul (hσ : IsURepOn (UJset ε) σ) (a b : Formalism.REAL.UJ ε) :
    σ (Formalism.MainNotions.S.umat (a * b)) = (σ (Formalism.MainNotions.S.umat a)).comp (σ (Formalism.MainNotions.S.umat b)) := by
  rw [umat_mul]
  exact hσ.1.2 _ a.2 _ b.2

theorem sig_inv_apply (hσ : IsURepOn (UJset ε) σ) (g : Formalism.REAL.UJ ε) (v : H) :
    σ (Formalism.MainNotions.S.umat g) (σ (Formalism.MainNotions.S.umat g⁻¹) v) = v := by
  have h := (sig_mul hσ g g⁻¹).symm
  rw [mul_inv_cancel, umat_one, hσ.1.1] at h
  have h2 := congrArg (fun L : H →L[ℂ] H => L v) h
  simpa using h2

theorem sig_inner (hσ : IsURepOn (UJset ε) σ) (g : Formalism.REAL.UJ ε) (a b : H) :
    inner ℂ (σ (Formalism.MainNotions.S.umat g) a) (σ (Formalism.MainNotions.S.umat g) b) = inner ℂ a b := by
  let L : H →ₗᵢ[ℂ] H :=
    { toLinearMap := (σ (Formalism.MainNotions.S.umat g) : H →ₗ[ℂ] H), norm_map' := hσ.2.1 _ g.2 }
  exact L.inner_map_map a b

theorem inner_sig (hσ : IsURepOn (UJset ε) σ) (g : Formalism.REAL.UJ ε) (y u : H) :
    inner ℂ y (σ (Formalism.MainNotions.S.umat g) u) = inner ℂ (σ (Formalism.MainNotions.S.umat g⁻¹) y) u := by
  rw [← sig_inner hσ g (σ (Formalism.MainNotions.S.umat g⁻¹) y) u, sig_inv_apply hσ g y]

theorem wt_K (dual : Bool) (ξ : Fin n) (x k : Matrix (Fin n) (Fin n) ℂ) (hk : k * Jm ε = Jm ε * k)
    (d : Fin n) : ∑ c, wt dual ε ξ x c * cond dual (star (k c d)) (k c d) = wt dual ε ξ (x * k) d := by
  cases dual
  · simp [wt, Matrix.mul_apply]
  · have hkc : ∀ c, sg ε c * star (k c d) = sg ε d * star (k c d) := by
      intro c
      have h := congrFun (congrFun hk c) d
      simp only [Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
      have h2 := congrArg star h
      simp only [star_mul', star_sg] at h2
      linear_combination (-1 : ℂ) * h2
    simp only [wt, cond_true, Matrix.mul_apply, star_sum, star_mul', Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    linear_combination (star (x ξ c)) * hkc c

theorem cf_kDiag (hσ : IsURepOn (UJset ε) σ) (dual : Bool) (y : H) (ξ : Fin n) (F : Fin n → H)
    (κ : Formalism.REAL.UJ ε) (hk : Formalism.MainNotions.S.umat κ * Jm ε = Jm ε * Formalism.MainNotions.S.umat κ) (g : Formalism.REAL.UJ ε) :
    cf dual ε σ y ξ (kDiag dual σ (Formalism.MainNotions.S.umat κ) F) g = cf dual ε σ y ξ F (g * κ) := by
  unfold cf kDiag
  rw [sig_mul hσ g κ, umat_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.comp_apply, map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← wt_K dual ξ _ _ hk d, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

end Rep

section DerivRep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem inner_exp_deriv (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (y : H) (z : Formalism.REAL.UJ ε) (v : D) :
    HasDerivAt (fun t : ℝ => inner ℂ y (σ (Formalism.MainNotions.S.umat z * NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((actM E X v : D) : H))) 0 := by
  have h1 := hD.deriv X hX v
  have hfun : (fun t : ℝ => inner ℂ y (σ (Formalism.MainNotions.S.umat z * NormedSpace.exp ((t : ℂ) • X)) (v : H))) =
      fun t : ℝ => inner ℂ y (σ (Formalism.MainNotions.S.umat z) (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H))) := by
    funext t
    simp only [hσ.1.2 _ z.2 _ (exp_smul_mem_UJset hX t), ContinuousLinearMap.comp_apply]
  rw [hfun]
  exact (((innerSL ℂ y).comp (σ (Formalism.MainNotions.S.umat z))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

theorem hasDerivAt_matrixCoeff_flow (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (dual : Bool) (y : H) (ξ : Fin n) (f : Fin n → D)
    (z : Formalism.REAL.UJ ε) :
    HasDerivAt (fun s => cf dual ε σ y ξ (fun c => ((f c : D) : H)) (z * ex X hX s))
      (cf dual ε σ y ξ (fun c => ((mx (tensF dual E) X f c : D) : H)) z) 0 := by
  have hterm : ∀ c, HasDerivAt (fun s : ℝ => wt dual ε ξ (Formalism.MainNotions.S.umat z * NormedSpace.exp ((s : ℂ) • X)) c *
      inner ℂ y (σ (Formalism.MainNotions.S.umat z * NormedSpace.exp ((s : ℂ) • X)) ((f c : D) : H)))
      (wt dual ε ξ (Formalism.MainNotions.S.umat z * X) c * inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((f c : D) : H)) +
        wt dual ε ξ (Formalism.MainNotions.S.umat z) c * inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((actM E X (f c) : D) : H))) 0 := by
    intro c
    refine ((hasDerivAt_wt dual ξ c _ X).mul (inner_exp_deriv hσ hD hX y z (f c))).congr_deriv ?_
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
  have hs := HasDerivAt.sum (u := (univ : Finset (Fin n))) (fun c _ => hterm c)
  rw [Finset.sum_fn] at hs
  have hv : cf dual ε σ y ξ (fun c => ((mx (tensF dual E) X f c : D) : H)) z =
      ∑ c, (wt dual ε ξ (Formalism.MainNotions.S.umat z * X) c * inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((f c : D) : H)) +
        wt dual ε ξ (Formalism.MainNotions.S.umat z) c * inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((actM E X (f c) : D) : H))) := by
    unfold cf
    simp only [mx_apply_tensF, Submodule.coe_add, map_add (f := _), inner_add_right, mul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    rw [wt_deriv_id dual hX ξ (Formalism.MainNotions.S.umat z) (fun c => inner ℂ y (σ (Formalism.MainNotions.S.umat z) ((f c : D) : H)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    cases dual
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, inner_sum, inner_smul_right]
    set_option synthInstance.maxHeartbeats 100000 in
      · simp [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_neg, map_sum, map_smul, map_neg, inner_sum,
        inner_smul_right, inner_neg_right]
  rw [hv]
  exact hs

theorem hasDerivAt_cf (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (dual : Bool) (y : H) (ξ : Fin n) (f : Fin n → D)
    (x : Formalism.REAL.UJ ε) (t : ℝ) :
    HasDerivAt (fun s => cf dual ε σ y ξ (fun c => ((f c : D) : H)) (x * ex X hX s))
      (cf dual ε σ y ξ (fun c => ((mx (tensF dual E) X f c : D) : H)) (x * ex X hX t)) t := by
  have h0 := hasDerivAt_matrixCoeff_flow hσ hD hX dual y ξ f (x * ex X hX t)
  have h0' : HasDerivAt (fun u => cf dual ε σ y ξ (fun c => ((f c : D) : H)) (x * ex X hX t * ex X hX u))
      (cf dual ε σ y ξ (fun c => ((mx (tensF dual E) X f c : D) : H)) (x * ex X hX t)) (t - t) := by
    rw [sub_self]
    exact h0
  have h1 := h0'.comp_sub_const t t
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  beta_reduce
  rw [mul_assoc, ← ex_add, add_sub_cancel]

end DerivRep

end ReciprocityTheory.ChartRestriction.DS.UnitB
