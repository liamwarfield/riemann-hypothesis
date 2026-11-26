module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfKapInt
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk

theorem lint_prod {I : Type} [Fintype I] [SigmaFinite (volume : Measure P)]
    (f : I → P → ℝ) (hf0 : ∀ v x, 0 ≤ f v x) (hm : ∀ v, Measurable (f v))
    (C : I → ℝ≥0) (hC : ∀ v, ∫⁻ x, ENNReal.ofReal (f v x) ≤ C v) :
    ∫⁻ w : I → P, ENNReal.ofReal (∏ v, f v (w v)) ≤ ((∏ v, C v : ℝ≥0) : ℝ≥0∞) := by
  have hint : ∀ v, Integrable (f v) := by
    intro v
    refine ⟨(hm v).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hf0 v))]
    exact lt_of_le_of_lt (hC v) ENNReal.coe_lt_top
  have hnn : ∀ w : I → P, 0 ≤ ∏ v, f v (w v) :=
    fun w => Finset.prod_nonneg fun v _ => hf0 v (w v)
  have hP : Integrable (fun w : I → P => ∏ v, f v (w v)) := by
    rw [volume_pi]
    exact Integrable.fintype_prod hint
  rw [← ofReal_integral_eq_lintegral_ofReal hP (ae_of_all _ hnn),
    integral_fintype_prod_volume_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg (hf0 v)), ENNReal.ofNNReal_finsetProd]
  refine Finset.prod_le_prod' fun v _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hint v) (ae_of_all _ (hf0 v))]
  exact hC v

theorem har1 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') (e : ℝ) (he : 0 ≤ e) :
    kap z w ^ e ≤ (8 : ℝ) ^ e * kap z w' ^ e := by
  unfold B1c at hB
  obtain ⟨h1, -, h3, -⟩ := hB
  have hzw := (h1 z w).1
  have hzw' := (h1 z w').1
  have key : kap z w ≤ 8 * kap z w' := by
    nlinarith [h3 z w w', mul_le_mul_of_nonneg_left h hzw]
  calc kap z w ^ e ≤ (8 * kap z w') ^ e := Real.rpow_le_rpow hzw key he
    _ = (8 : ℝ) ^ e * kap z w' ^ e := Real.mul_rpow (by norm_num) hzw'

theorem har2 (hB : B1c) (z w w' : P) (h : 1 / 2 ≤ kap w w') :
    (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) := by
  unfold B1c at hB
  obtain ⟨-, -, -, h4, -⟩ := hB
  have hw : 0 < |w.1.im| := abs_pos.mpr w.2
  have hw' : 0 < |w'.1.im| := abs_pos.mpr w'.2
  have hz : 0 ≤ |z.1.im| := abs_nonneg _
  have hww : |w'.1.im| ≤ 8 * |w.1.im| := by
    nlinarith [h4 w w', mul_le_mul_of_nonneg_right h hw'.le]
  have key : |z.1.im| / |w.1.im| ≤ 8 * (|z.1.im| / |w'.1.im|) := by
    rw [mul_div_assoc', div_le_div_iff₀ hw hw']
    nlinarith [mul_le_mul_of_nonneg_left hww hz]
  calc (|z.1.im| / |w.1.im|) ^ ((1 : ℝ) / 2) ≤ (8 * (|z.1.im| / |w'.1.im|)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow (div_nonneg hz hw.le) key (by norm_num)
    _ = (8 : ℝ) ^ ((1 : ℝ) / 2) * (|z.1.im| / |w'.1.im|) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num) (div_nonneg hz hw'.le)

theorem meas_abs_im : Measurable fun x : P => |x.1.im| := by
  exact (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable

end UpperTheory.Esk.KappaIntegralLemmas

open UpperTheory.Esk.KappaIntegralLemmas in
theorem UpperTheory.Esk.pf_KapInt : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.B6 → UpperTheory.Esk.KapInt := by
  intro hA _ hB h6
  unfold KapInt
  intro I _ k hk
  have hσ : SigmaFinite (volume : Measure P) := by
    unfold B1a at hA
    exact hA.1
  haveI := hσ
  have hB' := hB
  unfold B1c at hB'
  obtain ⟨h1, -, -, -, h5, -⟩ := hB'
  unfold B6 at h6
  choose Cv hCv using fun v => h6 (k v) (hk v)
  have ha : ∀ v, 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := fun v => by positivity
  have hA' : ((∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) : ℝ≥0) : ℝ)
      = ∏ v, (8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [NNReal.coe_prod]
    exact Finset.prod_congr rfl fun v _ => Real.coe_toNNReal _ (ha v)
  refine ⟨∏ v, Cv v, ∏ v, Real.toNNReal ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)), fun z => ?_⟩
  have hkm : ∀ v, Measurable (fun t : P => kap (z v) t) := fun v =>
    h5.measurable.comp (measurable_const.prodMk measurable_id)
  have hsplit : ∀ w : X I, Kap k z w * ∏ v, (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
      = ∏ v, (kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)) := by
    intro w
    rw [Finset.prod_mul_distrib]
    rfl
  refine ⟨?_, ?_, ?_, fun w w' hn => ⟨?_, ?_⟩⟩
  · unfold Kap
    exact Finset.measurable_prod _ fun v _ => ((hkm v).comp (measurable_pi_apply v)).pow_const _
  · unfold Kap
    exact lint_prod (fun v t => kap (z v) t ^ ((k v : ℝ) / 2))
      (fun v t => Real.rpow_nonneg (h1 _ _).1 _) (fun v => (hkm v).pow_const _) Cv
      (fun v => (hCv v (z v)).1)
  · simp only [hsplit]
    exact lint_prod
      (fun v t => kap (z v) t ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |t.1.im|) ^ ((1 : ℝ) / 2))
      (fun v t => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
        (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _))
      (fun v => ((hkm v).pow_const _).mul ((measurable_const.div meas_abs_im).pow_const _)) Cv
      (fun v => (hCv v (z v)).2)
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    unfold Kap
    rw [hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => Real.rpow_nonneg (h1 _ _).1 _) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have h8 : (1 : ℝ) ≤ (8 : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hp : 0 ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2)
        ≤ (8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := e1
      _ ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) * kap (z v) (w' v) ^ ((k v : ℝ) / 2) := by
        nlinarith [mul_le_mul_of_nonneg_left h8 hp]
  · have hn' : ∀ v, 1 / 2 ≤ kap (w v) (w' v) := hn
    rw [hsplit w, hsplit w', hA', ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ => mul_nonneg (Real.rpow_nonneg (h1 _ _).1 _)
      (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)) fun v _ => ?_
    have e1 := har1 hB (z v) (w v) (w' v) (hn' v) ((k v : ℝ) / 2) (by positivity)
    have e2 := har2 hB (z v) (w v) (w' v) (hn' v)
    calc kap (z v) (w v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w v).1.im|) ^ ((1 : ℝ) / 2)
        ≤ ((8 : ℝ) ^ ((k v : ℝ) / 2) * kap (z v) (w' v) ^ ((k v : ℝ) / 2)) *
            ((8 : ℝ) ^ ((1 : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) :=
          mul_le_mul e1 e2 (Real.rpow_nonneg (div_nonneg (abs_nonneg _) (abs_nonneg _)) _)
            (mul_nonneg (by positivity) (Real.rpow_nonneg (h1 _ _).1 _))
      _ = ((8 : ℝ) ^ ((k v : ℝ) / 2) * (8 : ℝ) ^ ((1 : ℝ) / 2)) *
            (kap (z v) (w' v) ^ ((k v : ℝ) / 2) * (|(z v).1.im| / |(w' v).1.im|) ^ ((1 : ℝ) / 2)) := by
        ring
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.CuspRegionVolumeFiniteProof
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk

def B1 (C c : ℝ) : Set {z : ℂ // z.im ≠ 0} := {w | |w.1.re| ≤ C ∧ c ≤ |w.1.im|}

theorem measurableSet_cusp_region (C c : ℝ) : MeasurableSet (B1 C c) := by
  have h1 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.re| :=
    (continuous_abs.comp (Complex.continuous_re.comp continuous_subtype_val)).measurable
  have h2 : Measurable fun w : {z : ℂ // z.im ≠ 0} => |w.1.im| :=
    (continuous_abs.comp (Complex.continuous_im.comp continuous_subtype_val)).measurable
  exact (measurableSet_le h1 measurable_const).inter (measurableSet_le measurable_const h2)

theorem pt_bound (C c : ℝ) (hc : 0 < c) (t : ℂ) (h1 : |t.re| ≤ C) (h2 : c ≤ |t.im|) :
    1 / t.im ^ 2 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hb : c ^ 2 ≤ t.im ^ 2 := by
    nlinarith [sq_abs t.im, mul_nonneg (sub_nonneg.2 h2) (add_nonneg (abs_nonneg t.im) hc.le)]
  have ha : t.re ^ 2 ≤ C ^ 2 := by
    nlinarith [sq_abs t.re, mul_nonneg (sub_nonneg.2 h1) (by linarith [abs_nonneg t.re] : 0 ≤ C + |t.re|)]
  have hbpos : 0 < t.im ^ 2 := lt_of_lt_of_le hc2 hb
  have e1 : 1 ≤ (1 + C ^ 2) * (1 + t.re ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    linarith
  have e2 : 1 / t.im ^ 2 ≤ (1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹ := by
    have h3 : 1 ≤ t.im ^ 2 / c ^ 2 := by
      rw [le_div_iff₀ hc2]
      linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hbpos (by positivity), add_mul, one_mul, one_div, inv_mul_eq_div]
    linarith
  calc 1 / t.im ^ 2 = 1 * (1 / t.im ^ 2) := (one_mul _).symm
    _ ≤ ((1 + C ^ 2) * (1 + t.re ^ 2)⁻¹) * ((1 + 1 / c ^ 2) * (1 + t.im ^ 2)⁻¹) :=
        mul_le_mul e1 e2 (by positivity) (by positivity)
    _ = (1 + C ^ 2) * (1 + 1 / c ^ 2) * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) := by ring

theorem integ_G : ∫⁻ t : ℂ, ENNReal.ofReal ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) < ⊤ := by
  have h1 : Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq
  have h2 : Integrable (fun p : ℝ × ℝ => (1 + p.1 ^ 2)⁻¹ * (1 + p.2 ^ 2)⁻¹) :=
    h1.mul_prod h1
  have h3 : Integrable (fun t : ℂ => (1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹) :=
    (Complex.volume_preserving_equiv_real_prod.integrable_comp h2.aestronglyMeasurable).2 h2
  exact h3.lintegral_lt_top

private theorem volume_eq_lintegral_inv_im_sq_comap (s : Set {z : ℂ // z.im ≠ 0}) (hs : MeasurableSet s) :
    (volume : Measure P) (show Set P from s) = ∫⁻ z in s, ENNReal.ofReal (1 / z.1.im ^ 2)
      ∂(Measure.comap (Subtype.val : {z : ℂ // z.im ≠ 0} → ℂ) volume) :=
  withDensity_apply _ hs

private theorem lintegral_comap_im_ne_zero_le_lintegral (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume) ≤ ∫⁻ t, f t := by
  have hs : MeasurableSet {z : ℂ | z.im ≠ 0} :=
    (isOpen_ne_fun Complex.continuous_im continuous_const).measurableSet
  calc ∫⁻ z : {z : ℂ // z.im ≠ 0}, f z.1 ∂(Measure.comap Subtype.val volume)
      = ∫⁻ t in {z : ℂ | z.im ≠ 0}, f t := lintegral_subtype_comap hs f
    _ ≤ ∫⁻ t, f t := setLIntegral_le_lintegral _ _

private theorem lintegral_mul_inv_one_add_sq_lt_top (K : ℝ) (hK : 0 ≤ K) :
    ∫⁻ t : ℂ, ENNReal.ofReal (K * ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹)) < ⊤ := by
  simp_rw [ENNReal.ofReal_mul hK]
  rw [lintegral_const_mul _ (by fun_prop)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top integ_G

private theorem lintegral_B1_inv_im_sq_le_lintegral (C c : ℝ) (hc : 0 < c) :
    ∫⁻ z in B1 C c, ENNReal.ofReal (1 / z.1.im ^ 2) ∂(Measure.comap Subtype.val volume) ≤
      ∫⁻ z : {z : ℂ // z.im ≠ 0}, ENNReal.ofReal ((1 + C ^ 2) * (1 + 1 / c ^ 2) *
          ((1 + z.1.re ^ 2)⁻¹ * (1 + z.1.im ^ 2)⁻¹)) ∂(Measure.comap Subtype.val volume) := by
  refine le_trans (setLIntegral_mono' (measurableSet_cusp_region C c) fun z hz => ?_) (setLIntegral_le_lintegral _ _)
  exact ENNReal.ofReal_le_ofReal (pt_bound C c hc z.1 hz.1 hz.2)

theorem volume_cusp_region_lt_top (C c : ℝ) (hc : 0 < c) : (volume : Measure P) (show Set P from B1 C c) < ⊤ := by
  have hK0 : 0 ≤ (1 + C ^ 2) * (1 + 1 / c ^ 2) := by positivity
  rw [volume_eq_lintegral_inv_im_sq_comap _ (measurableSet_cusp_region C c)]
  exact lt_of_le_of_lt ((lintegral_B1_inv_im_sq_le_lintegral C c hc).trans (lintegral_comap_im_ne_zero_le_lintegral
    (fun t : ℂ => ENNReal.ofReal ((1 + C ^ 2) * (1 + 1 / c ^ 2) *
      ((1 + t.re ^ 2)⁻¹ * (1 + t.im ^ 2)⁻¹))))) (lintegral_mul_inv_one_add_sq_lt_top _ hK0)

end UpperTheory.Esk.CuspRegionVolume

open UpperTheory.Esk.CuspRegionVolume in
theorem UpperTheory.Esk.cusp_region_volume_finite_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.UpperHalfPlaneMeasureCoordinates → UpperTheory.Esk.C2 → UpperTheory.Esk.E0a → UpperTheory.Esk.E0d → UpperTheory.Esk.E3 := by
  intro hB1a _ hC2 hE0a hE0d
  intro F I Gf _ _ _ D hD b hb
  obtain ⟨hcnt, hsf, -, hPY, -, -, -, -⟩ := hE0a F I Gf D hD
  obtain ⟨-, hsm, -, -, -, -, -, -, -, hsurj, -⟩ := hE0d F I Gf D hD
  haveI : Countable (PG F) := hcnt
  haveI : SigmaFinite (volume : Measure D.Xs) := hsf
  haveI : SigmaFinite (volume : Measure P) := hB1a.1
  haveI : Countable D.Om := hD.cO
  obtain ⟨c₀, hc₀, hmink⟩ := hD.mink
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have h01 : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1
  let T : Set D.Om := (fun x : Gf => (show D.Om from ((x : Gf) : Gf ⧸ D.H))) '' (S : Set Gf)
  let U : Set D.Xs := Set.univ.pi fun _ : I => (show Set P from B1 C c)
  have hT : T.Finite := S.finite_toSet.image _
  have hU : MeasurableSet U := MeasurableSet.univ_pi fun _ => measurableSet_cusp_region C c
  have hS : MeasurableSet (T ×ˢ U) := (MeasurableSet.of_discrete).prod hU
  have hcover : ∀ y : D.Y, ∃ g : PG F, g • y ∈ T ×ˢ U := by
    intro y
    obtain ⟨s, hs0, hs⟩ := hmink y.2 (D.rep y.1)
    obtain ⟨γ, hγ⟩ := hsurj s hs0
    set y' : D.Y := (γ : PG F) • y with hy'
    have h1 : c₀ ≤ D.Ht ![0, 1] y'.2 (D.rep y'.1) := by
      change c₀ ≤ D.HtY ![0, 1] ((γ : PG F) • y)
      rw [hsm ![0, 1] h01 γ y, hγ]
      exact hs
    obtain ⟨bb, -, ⟨x', hx'S, h, hhH, hjx⟩, hSg⟩ := hnorm y'.2 (D.rep y'.1) h1
    refine ⟨(bb : PG F) * (γ : PG F), ?_⟩
    rw [mul_smul, ← hy']
    refine ⟨?_, ?_⟩
    · have hy1 : ((D.rep y'.1 : Gf) : Gf ⧸ D.H) = y'.1 := Quotient.out_eq _
      have hm := D.mk_smulO bb (D.rep y'.1)
      rw [hy1] at hm
      refine ⟨x', hx'S, ?_⟩
      show (show D.Om from ((x' : Gf) : Gf ⧸ D.H)) = (bb : PG F) • y'.1
      rw [hm, hjx]
      refine (QuotientGroup.eq.2 ?_).symm
      rw [_root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact inv_mem hhH
    · show (bb : PG F) • y'.2 ∈ U
      rw [D.mk_smulX]
      intro v _
      exact ⟨(hSg v).1, (hSg v).2.1⟩
  have hfin : D.μY (T ×ˢ U) < ⊤ := by
    unfold Dat.μY
    rw [Measure.prod_prod]
    refine ENNReal.mul_lt_top (Measure.count_apply_lt_top.2 hT) ?_
    change (Measure.pi fun _ : I => (volume : Measure P)) (Set.univ.pi fun _ : I => (show Set P from B1 C c)) < ⊤
    rw [Measure.pi_pi]
    exact ENNReal.prod_lt_top fun _ _ => volume_cusp_region_lt_top C c hc
  exact lt_of_le_of_lt ((hC2 (PG F) D.Y).2 D.μY hPY b hb _ hS hcover) hfin
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.UnipotentTermsContributionProof
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.UnipotentTermsContribution

open UpperTheory.Esk

theorem diag {F : Type} [Field F] (g : GL (Fin 2) F) (s : Fin 2 → F) (c : F)
    (hs : s ᵥ* (g : Matrix (Fin 2) (Fin 2) F) = c • s)
    (hd : (g : Matrix (Fin 2) (Fin 2) F).trace ^ 2 ≠ 4 * (g : Matrix (Fin 2) (Fin 2) F).det)
    (δ1 : GL (Fin 2) F) (h1 : ![0, 1] ᵥ* (δ1 : Matrix (Fin 2) (Fin 2) F) = s) :
    ∃ δ : GL (Fin 2) F, (δ * g * δ⁻¹) 0 1 = 0 ∧ (δ * g * δ⁻¹) 1 0 = 0 := by
  obtain ⟨h, hh⟩ : ∃ h : GL (Fin 2) F, h = δ1 * g * δ1⁻¹ := ⟨_, rfl⟩
  have hv : ![0, 1] ᵥ* (h : Matrix (Fin 2) (Fin 2) F) = c • ![0, 1] := by
    rw [hh, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, h1, hs,
      Matrix.smul_vecMul, ← h1, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.vecMul_one]
  have e10 : h 1 0 = 0 := by
    have := congrFun hv 0
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using this
  have htr : (h : Matrix (Fin 2) (Fin 2) F).trace = (g : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [hh, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  have hdet : (h : Matrix (Fin 2) (Fin 2) F).det = (g : Matrix (Fin 2) (Fin 2) F).det := by
    rw [hh, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  have hne : h 0 0 - h 1 1 ≠ 0 := by
    intro e
    apply hd
    rw [← htr, ← hdet, Matrix.trace_fin_two, Matrix.det_fin_two]
    change (h 0 0 + h 1 1) ^ 2 = 4 * (h 0 0 * h 1 1 - h 0 1 * h 1 0)
    rw [e10]
    linear_combination (h 0 0 - h 1 1) * e
  obtain ⟨t, ht0⟩ : ∃ t : F, t = h 0 1 / (h 0 0 - h 1 1) := ⟨_, rfl⟩
  have ht : t * (h 0 0 - h 1 1) = h 0 1 := by rw [ht0]; exact div_mul_cancel₀ _ hne
  obtain ⟨u, hu, hu'⟩ : ∃ u : GL (Fin 2) F, (u : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] ∧
      ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, -t; 0, 1] :=
    ⟨⟨!![1, t; 0, 1], !![1, -t; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, rfl, rfl⟩
  have hc : u * δ1 * g * (u * δ1)⁻¹ = u * h * u⁻¹ := by rw [hh]; group
  have hM : ((u * δ1 * g * (u * δ1)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, t; 0, 1] * !![h 0 0, h 0 1; 0, h 1 1] * !![1, -t; 0, 1] := by
    rw [hc, Units.val_mul, Units.val_mul, hu, hu', Matrix.eta_fin_two (h : Matrix (Fin 2) (Fin 2) F), e10]
    rfl
  refine ⟨u * δ1, ?_, ?_⟩
  · rw [hM]
    simp
    linear_combination -ht
  · rw [hM]
    simp

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

theorem transport (hP : Pres (PG F) (volume : Measure D.Xs))
    {ι : Type} [Fintype ι] (k : I → ℕ) (a : ι → Gf) (T : ℝ)
    (hkk : ∀ (δ γ : PG F) y, D.kk k a (δ * γ * δ⁻¹) (δ • y) = D.kk k a γ y)
    (hLam : ∀ (γ δ : PG F) y, δ • y ∈ D.LamF T (δ * γ * δ⁻¹) ↔ y ∈ D.LamF T γ)
    (γ : PG F) (ω : D.Om) (δ γ' : PG F) (hγ' : δ * γ * δ⁻¹ = γ')
    (h : ∀ β : D.Xs → ℝ, IsCut (MulAction.stabilizer (PG F) ((γ', δ • ω) : D.Cj × D.Om)) β →
      Integrable (fun z => β z • (D.LamF T γ').indicator (D.kk k a γ') (δ • ω, z)) →
      ∫ z, β z • (D.LamF T γ').indicator (D.kk k a γ') (δ • ω, z) = 0)
    (β : D.Xs → ℝ) (hβ : IsCut (MulAction.stabilizer (PG F) ((γ, ω) : D.Cj × D.Om)) β)
    (hint : Integrable (fun z => β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z))) :
    ∫ z, β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z) = 0 := by
  subst hγ'
  set p : D.Cj × D.Om := (γ, ω) with hp
  have hq : δ • p = ((δ * γ * δ⁻¹ : PG F), δ • ω) := rfl
  have mem : ∀ g : PG F, g ∈ MulAction.stabilizer (PG F) (δ • p) ↔ δ⁻¹ * g * δ ∈ MulAction.stabilizer (PG F) p := by
    intro g
    simp only [MulAction.mem_stabilizer_iff, mul_smul]
    rw [inv_smul_eq_iff]
  let φ : MulAction.stabilizer (PG F) p ≃ MulAction.stabilizer (PG F) (δ • p) :=
    { toFun := fun x => ⟨δ * x * δ⁻¹, (mem _).2 (by
        have e : δ⁻¹ * (δ * (x : PG F) * δ⁻¹) * δ = x := by group
        rw [e]; exact x.2)⟩
      invFun := fun g => ⟨δ⁻¹ * g * δ, (mem _).1 g.2⟩
      left_inv := fun x => Subtype.ext (by change δ⁻¹ * (δ * (x : PG F) * δ⁻¹) * δ = x; group)
      right_inv := fun g => Subtype.ext (by change δ * (δ⁻¹ * (g : PG F) * δ) * δ⁻¹ = g; group) }
  let e : D.Xs ≃ᵐ D.Xs :=
    { toEquiv := MulAction.toPerm δ⁻¹
      measurable_toFun := (hP δ⁻¹).measurable
      measurable_invFun := (hP δ⁻¹⁻¹).measurable }
  have hme : MeasurePreserving e volume volume := hP δ⁻¹
  have he : ∀ w, e w = δ⁻¹ • w := fun _ => rfl
  set f : D.Xs → ℂ := fun z => β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z) with hf
  have key : ∀ w, f (e w) = β (δ⁻¹ • w) • (D.LamF T (δ * γ * δ⁻¹)).indicator (D.kk k a (δ * γ * δ⁻¹)) (δ • ω, w) := by
    intro w
    have hy : ((δ • ω, w) : D.Y) = δ • ((ω, δ⁻¹ • w) : D.Y) := by
      rw [Prod.smul_mk, smul_inv_smul]
    rw [hy, hf, he]
    beta_reduce
    congr 1
    by_cases hm : ((ω, δ⁻¹ • w) : D.Y) ∈ D.LamF T γ
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((hLam γ δ _).2 hm), hkk]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h' => hm ((hLam γ δ _).1 h'))]
  let β' : D.Xs → ℝ := fun w => β (δ⁻¹ • w)
  have hβ' : IsCut (MulAction.stabilizer (PG F) (δ • p)) β' := by
    refine ⟨hβ.meas.comp (hP δ⁻¹).measurable, fun w => hβ.nonneg _, fun w => ?_⟩
    rw [← φ.hasSum_iff]
    convert hβ.sum (δ⁻¹ • w) using 2 with x
    change β (δ⁻¹ • (δ * (x : PG F) * δ⁻¹) • w) = β ((x : PG F) • δ⁻¹ • w)
    simp only [smul_smul, show δ⁻¹ * (δ * (x : PG F) * δ⁻¹) = (x : PG F) * δ⁻¹ by group]
  have hint' : Integrable (fun w => β' w • (D.LamF T (δ * γ * δ⁻¹)).indicator (D.kk k a (δ * γ * δ⁻¹)) (δ • ω, w)) := by
    have := (hme.integrable_comp_emb e.measurableEmbedding).2 hint
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    exact key w
  have h0 := h β' (hq ▸ hβ') hint'
  rw [← hme.integral_comp' f]
  rw [← h0]
  exact integral_congr_ae (Filter.Eventually.of_forall key)

end UpperTheory.Esk.UnipotentTermsContribution

open UpperTheory.Esk.UnipotentTermsContribution in
theorem UpperTheory.Esk.unipotent_terms_contribution_proof : UpperTheory.Esk.C1 → UpperTheory.Esk.E0a → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.DiagonalTruncatedIntegralZero → UpperTheory.Esk.F6 := by
  intro _ hE0a hE0c hE0d hF6b F I Gf ι _ _ _ _ D k a hH T hT γ ω hγ β hβ hint
  by_cases hTe : D.Te a γ.out (D.rep ω) = 0
  · have hz : ∀ z, β z • (D.LamF T γ).indicator (D.kk k a γ) (ω, z) = 0 := by
      intro z
      simp [Dat.kk, Dat.kt, hTe]
    simp [hz]
  obtain ⟨-, -, hP, -⟩ := hE0a F I Gf D hH.ax
  obtain ⟨-, hkk, -, -, h5, h6⟩ := hE0c F I Gf ι D k a hH
  obtain ⟨-, -, -, -, -, -, -, hLamF, -, hex, -⟩ := hE0d F I Gf D hH.ax
  obtain ⟨i, hi⟩ := h5 γ ω hTe
  obtain ⟨-, hdisc⟩ := h6 γ ω i hi
  simp only [IsEll, not_forall, not_not] at hγ
  obtain ⟨s, hs0, c, hc⟩ := hγ
  obtain ⟨δ1, hδ1⟩ := hex s hs0
  obtain ⟨δ0, h01, h10⟩ := diag γ.out s c hc hdisc δ1 hδ1
  refine transport D hP k a T hkk (fun γ δ y => (hLamF T γ).2 δ y) γ ω (δ0 : PG F)
    ((δ0 * γ.out * δ0⁻¹ : GL (Fin 2) F) : PG F) ?_ ?_ β hβ hint
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']
  · intro β' hβ' hint'
    exact hF6b F I Gf ι D k a hH T hT (δ0 * γ.out * δ0⁻¹) ((δ0 : PG F) • ω) h01 h10 β' hβ' hint'
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.E5OfReproducingFormula
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

theorem rep_eq (ω : D.Om) (u : Gf) (hu : (u : Gf ⧸ D.H) = ω) : ∃ h : D.H, D.rep ω = u * h := by
  have h1 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  refine ⟨⟨u⁻¹ * D.rep ω, QuotientGroup.eq.1 (hu.trans h1.symm)⟩, ?_⟩
  simp

theorem ee_mul (h : D.H) (u : Gf) : D.ee ((h : Gf)⁻¹ * u) * (D.χ h : ℂ) = D.ee u := by
  unfold Dat.ee
  by_cases hu : u ∈ D.H
  · have hu' : (h : Gf)⁻¹ * u ∈ D.H := D.H.mul_mem (D.H.inv_mem h.2) hu
    rw [dite_eq_left hu', dite_eq_left hu, mul_comm, ← Units.val_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp
  · have hu' : (h : Gf)⁻¹ * u ∉ D.H := fun hh => hu (by simpa using D.H.mul_mem h.2 hh)
    rw [dite_eq_right hu', dite_eq_right hu, zero_mul]

theorem ee_one : D.ee 1 = 1 := by
  unfold Dat.ee
  rw [dite_eq_left D.H.one_mem]
  exact congrArg Units.val (map_one D.χ)

theorem smul_fst (γ : PG F) (ω : D.Om) : γ • ω = (((D.j γ.out * D.rep ω : Gf)) : Gf ⧸ D.H) := by
  have h2 : ((D.rep ω : Gf) : Gf ⧸ D.H) = ω := QuotientGroup.out_eq' _
  conv_lhs => rw [← QuotientGroup.out_eq' γ, ← h2]
  exact D.mk_smulO γ.out (D.rep ω)

theorem smul_snd (γ : PG F) (w : D.Xs) : γ • w = D.act γ.out w := by
  conv_lhs => rw [← QuotientGroup.out_eq' γ]
  exact D.mk_smulX γ.out w

variable [Fintype I]

theorem term (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (γ : PG F) (y : D.Y) :
    D.ee ((D.rep (γ • y).1)⁻¹ * x) * (qq k z (γ • y).2 * f ((γ • y).2, D.rep (γ • y).1)) =
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) * (qq k z (D.act γ.out y.2) * D.J k γ.out y.2) * f (y.2, D.rep y.1) := by
  obtain ⟨h, hh⟩ := rep_eq D (γ • y).1 (D.j γ.out * D.rep y.1) (by rw [Prod.smul_fst, smul_fst])
  have hs2 : (γ • y).2 = D.act γ.out y.2 := by rw [Prod.smul_snd, smul_snd]
  have key : (D.j γ.out * D.rep y.1 * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ * ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x) := by
    group
  rw [hh, hs2, hf.lev, show f (D.act γ.out y.2, D.j γ.out * D.rep y.1) = D.J k γ.out y.2 * f (y.2, D.rep y.1) from hf.aut _ _ _, key, ← ee_mul D h ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * x)]
  ring

open Classical in
theorem supp (k : I → ℕ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) (z : X I) (x : Gf) (y : D.Y) :
    D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) =
      if y.1 = ((x : Gf) : Gf ⧸ D.H) then qq k z y.2 * f (y.2, x) else 0 := by
  split_ifs with hy
  · obtain ⟨h, hh⟩ := rep_eq D y.1 x hy.symm
    have he := ee_mul D h 1
    rw [ee_one, mul_one] at he
    have key : (x * (h : Gf))⁻¹ * x = (h : Gf)⁻¹ := by group
    rw [hh, show f (y.2, x * (h : Gf)) = (D.χ h : ℂ) * f (y.2, x) from hf.lev _ _ _, key]
    calc _ = (D.ee ((h : Gf)⁻¹) * (D.χ h : ℂ)) * (qq k z y.2 * f (y.2, x)) := by ring
      _ = _ := by rw [he, one_mul]
  · have hn : (D.rep y.1)⁻¹ * x ∉ D.H := by
      intro hm
      apply hy
      have h1 : ((D.rep y.1 : Gf) : Gf ⧸ D.H) = y.1 := QuotientGroup.out_eq' _
      exact h1.symm.trans (QuotientGroup.eq.2 hm)
    have h0 : D.ee ((D.rep y.1)⁻¹ * x) = 0 := by
      unfold Dat.ee
      rw [dite_eq_right hn]
    rw [h0, zero_mul]

end UpperTheory.Esk.ReproducingKernelExpansion

open UpperTheory.Esk UpperTheory.Esk.ReproducingKernelExpansion in
theorem UpperTheory.Esk.e5_of_reproducing_formula : UpperTheory.Esk.B1b → UpperTheory.Esk.C3 → UpperTheory.Esk.E0a → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.MultivariableReproducingFormula → UpperTheory.Esk.E5 := by
  intro hB1 hC3 hE0 _hE4 hB3 F I Gf _ _ _ D hAx k hk _hcomp b hb f hf p
  obtain ⟨z, x⟩ := p
  obtain ⟨hcount, hsf, -, hpres, -, -, hborel, -⟩ := hE0 F I Gf D hAx
  have := hcount
  have := hsf
  have := hborel
  have := hAx.cO
  let ω₀ : D.Om := ((x : Gf) : Gf ⧸ D.H)
  let a : D.Om → ℂ := ({ω₀} : Set D.Om).indicator fun _ => (1 : ℂ)
  let h0 : D.Xs → ℂ := fun w => qq k z w * f (w, x)
  let G : D.Y → ℂ := fun y => D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1))
  have hG : G = fun y => a y.1 * h0 y.2 := by
    funext y
    change D.ee ((D.rep y.1)⁻¹ * x) * (qq k z y.2 * f (y.2, D.rep y.1)) = a y.1 * h0 y.2
    rw [supp D k f hf z x y]
    by_cases hy : y.1 = ((x : Gf) : Gf ⧸ D.H)
    · rw [if_pos hy]
      have ha : a y.1 = 1 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_pos (show y.1 ∈ ({ω₀} : Set D.Om) from hy)]
      rw [ha, one_mul]
    · rw [if_neg hy]
      have ha : a y.1 = 0 := by
        classical
        simp only [a]
        rw [Set.indicator_apply, if_neg (show y.1 ∉ ({ω₀} : Set D.Om) from hy)]
      rw [ha, zero_mul]
  have hqc : Continuous fun w : X I => qq k z w := by
    unfold qq
    exact continuous_finsetProd _ fun v _ =>
      (hB1.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))
  have hh0c : Continuous fun w : X I => qq k z w * f (w, x) := hqc.mul (hf.hol x).1
  have hh0m : Measurable h0 := hh0c.measurable
  obtain ⟨C, hC⟩ := hf.bdd
  have hB := hB3 I k hk (fun w => f (w, x)) (hf.hol x) ⟨C, fun w => hC w x⟩ z
  have hh0i : Integrable h0 := hB.1
  have ham : Measurable a := measurable_const.indicator (MeasurableSet.of_discrete)
  have hai : Integrable a Measure.count :=
    (integrable_indicator_iff (MeasurableSet.of_discrete)).2
      ((integrableOn_singleton_iff (by simp)).2 (Or.inr (by simp)))
  have ha1 : ∫ ω, a ω ∂Measure.count = 1 := by
    simp only [a]
    rw [integral_indicator (MeasurableSet.of_discrete)]
    simp
  have hGm : Measurable G := by
    rw [hG]
    exact (ham.comp measurable_fst).mul (hh0m.comp measurable_snd)
  have hGi : Integrable G D.μY := by
    rw [hG]
    unfold Dat.μY
    exact MeasureTheory.Integrable.mul_prod hai hh0i
  have hKf : ∀ y : D.Y, D.Kern k y (z, x) * f (y.2, D.rep y.1) = ∑' γ : PG F, G (γ • y) := by
    intro y
    unfold Dat.Kern
    rw [← tsum_mul_right]
    refine tsum_congr fun γ => ?_
    exact (term D k f hf z x γ y).symm
  have hCC := hC3 (PG F) D.Y D.μY hpres b hb G hGm hGi
  calc ∫ y, b y • (D.Kern k y (z, x) * f (y.2, D.rep y.1)) ∂D.μY
      = ∫ y, b y • ∑' γ : PG F, G (γ • y) ∂D.μY := by simp_rw [hKf]
    _ = ∫ y, G y ∂D.μY := hCC.2
    _ = ∫ y, a y.1 * h0 y.2 ∂(Measure.count.prod volume) := by rw [hG]; rfl
    _ = (∫ ω, a ω ∂Measure.count) * ∫ w, h0 w := integral_prod_mul _ _
    _ = f (z, x) := by rw [ha1, one_mul]; exact hB.2
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HolomorphicOnHalfPlaneFinsetSum
open MeasureTheory Matrix

namespace UpperTheory.Esk.FormsStableLemmas

open UpperTheory.Esk

theorem extendHalfPlane_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) :
    ext1 (fun t => ∑ i ∈ s, g i t) = fun t => ∑ i ∈ s, ext1 (g i) t := by
  funext t
  unfold ext1
  split_ifs <;> simp

theorem holomorphic_on_half_plane_finset_sum {ι : Type} (s : Finset ι) (g : ι → P → ℂ) (h : ∀ i ∈ s, Hol1 (g i)) :
    Hol1 (fun t => ∑ i ∈ s, g i t) := by
  unfold Hol1
  rw [extendHalfPlane_finset_sum]
  exact (DifferentiableOn.sum h).congr fun t _ => by simp [Finset.sum_apply]

theorem holomorphic_on_half_plane_add (f g : P → ℂ) (hf : Hol1 f) (hg : Hol1 g) : Hol1 (fun t => f t + g t) := by
  have : ext1 (fun t => f t + g t) = fun t => ext1 f t + ext1 g t := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1 at *
  rw [this]
  exact hf.add hg

theorem holomorphic_on_half_plane_const_mul (c : ℂ) (f : P → ℂ) (hf : Hol1 f) : Hol1 (fun t => c * f t) := by
  have : ext1 (fun t => c * f t) = fun t => c * ext1 f t := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1 at *
  rw [this]
  exact hf.const_mul c

theorem holomorphic_on_half_plane_zero : Hol1 (fun _ : P => (0 : ℂ)) := by
  have : ext1 (fun _ : P => (0 : ℂ)) = fun _ => 0 := by
    funext t; unfold ext1; split_ifs <;> simp
  unfold Hol1
  rw [this]
  exact differentiableOn_const 0

theorem nrm_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 ≤ nrm k z := by
  unfold nrm
  exact Finset.prod_nonneg fun v _ => Real.rpow_nonneg (abs_nonneg _) _

variable {F I Gf : Type} [Field F] [Group Gf] [Fintype I] (D : Dat F I Gf)

omit [Fintype I] in
theorem op_apply {ι : Type} [Fintype ι] (a : ι → Gf) (f : X I × Gf → ℂ) (p : X I × Gf) :
    Dat.Op a f p = ∑ i, f (p.1, p.2 * a i) := rfl

theorem isForm_zero (k : I → ℕ) : D.IsForm k 0 := by
  refine ⟨fun _ => ⟨continuous_const, fun _ _ => holomorphic_on_half_plane_zero⟩, ?_, ?_, ?_⟩
  · intro γ z x
    simp
  · intro z x h
    simp
  · exact ⟨0, fun z x => by simp⟩

theorem isForm_add (k : I → ℕ) (f g : X I × Gf → ℂ) (hf : D.IsForm k f) (hg : D.IsForm k g) :
    D.IsForm k (f + g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun x => ⟨(hf.hol x).1.add (hg.hol x).1,
      fun z v => holomorphic_on_half_plane_add _ _ ((hf.hol x).2 z v) ((hg.hol x).2 z v)⟩
  · intro γ z x
    simp [Pi.add_apply, hf.aut, hg.aut, mul_add]
  · intro z x h
    simp [Pi.add_apply, hf.lev, hg.lev, mul_add]
  · obtain ⟨C₁, h₁⟩ := hf.bdd
    obtain ⟨C₂, h₂⟩ := hg.bdd
    refine ⟨C₁ + C₂, fun z x => ?_⟩
    have hn := nrm_nonneg k z
    calc ‖(f + g) (z, x)‖ * nrm k z ≤ (‖f (z, x)‖ + ‖g (z, x)‖) * nrm k z :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hn
      _ = ‖f (z, x)‖ * nrm k z + ‖g (z, x)‖ * nrm k z := add_mul _ _ _
      _ ≤ C₁ + C₂ := add_le_add (h₁ z x) (h₂ z x)

theorem isForm_smul (k : I → ℕ) (c : ℂ) (f : X I × Gf → ℂ) (hf : D.IsForm k f) :
    D.IsForm k (c • f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun x => ⟨continuous_const.mul (hf.hol x).1,
      fun z v => holomorphic_on_half_plane_const_mul c _ ((hf.hol x).2 z v)⟩
  · intro γ z x
    simp [Pi.smul_apply, hf.aut]
    ring
  · intro z x h
    simp [Pi.smul_apply, hf.lev]
    ring
  · obtain ⟨C, h⟩ := hf.bdd
    refine ⟨‖c‖ * C, fun z x => ?_⟩
    have := h z x
    have hc := norm_nonneg c
    calc ‖(c • f) (z, x)‖ * nrm k z = ‖c‖ * (‖f (z, x)‖ * nrm k z) := by
          rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
      _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left this hc

def S (k : I → ℕ) : Submodule ℂ (X I × Gf → ℂ) where
  carrier := {f | D.IsForm k f}
  add_mem' {f g} hf hg := isForm_add D k f g hf hg
  zero_mem' := isForm_zero D k
  smul_mem' c f hf := isForm_smul D k c f hf

theorem M_eq (k : I → ℕ) : D.M k = S D k := Submodule.span_eq (S D k)

theorem mem_M (k : I → ℕ) (f : X I × Gf → ℂ) : f ∈ D.M k ↔ D.IsForm k f := by
  rw [M_eq]; rfl

open Classical in
theorem isForm_op (k : I → ℕ) {ι : Type} [Fintype ι] (a : ι → Gf) (ha : D.Good a)
    (f : X I × Gf → ℂ) (hf : D.IsForm k f) : D.IsForm k (Dat.Op a f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    refine ⟨?_, fun z v => ?_⟩
    · simp only [op_apply]
      exact continuous_finsetSum _ fun i _ => (hf.hol (x * a i)).1
    · simp only [op_apply]
      exact holomorphic_on_half_plane_finset_sum Finset.univ (fun i t => f (Function.update z v t, x * a i))
        (fun i _ => (hf.hol (x * a i)).2 z v)
  · intro γ z x
    simp only [op_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, hf.aut]
  · intro z x h
    simp only [op_apply]
    exact ha (fun y => f (z, y)) (fun y h' => hf.lev z y h') x h
  · obtain ⟨C, hC⟩ := hf.bdd
    refine ⟨Fintype.card ι * C, fun z x => ?_⟩
    have hn := nrm_nonneg k z
    simp only [op_apply]
    calc ‖∑ i, f (z, x * a i)‖ * nrm k z ≤ (∑ i, ‖f (z, x * a i)‖) * nrm k z :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) hn
      _ = ∑ i, ‖f (z, x * a i)‖ * nrm k z := Finset.sum_mul _ _ _
      _ ≤ ∑ _i : ι, C := Finset.sum_le_sum fun i _ => hC z (x * a i)
      _ = Fintype.card ι * C := by simp

theorem main (k : I → ℕ) : (∀ f, f ∈ D.M k ↔ D.IsForm k f) ∧
    ∀ (ι : Type) [Fintype ι] (a : ι → Gf), D.Good a → ∀ f ∈ D.M k, Dat.Op a f ∈ D.M k := by
  refine ⟨mem_M D k, fun ι _ a ha f hf => ?_⟩
  rw [mem_M] at hf ⊢
  exact isForm_op D k a ha f hf

end UpperTheory.Esk.FormsStableLemmas

theorem UpperTheory.Esk.forms_stable_under_operators_proof : UpperTheory.Esk.FormsStableUnderOperators :=
  fun _ _ _ _ _ _ D _ k => UpperTheory.Esk.FormsStableLemmas.main D k
end
