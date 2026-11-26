module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolumeOpenPosUpperHalfPlane
open MeasureTheory Set UpperHalfPlane in
private theorem UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane (U : Set ℍ) (hU : IsOpen U) (hne : U.Nonempty) :
    0 < (volume : Measure ℍ) U := by
  rw [pos_iff_ne_zero]
  intro h0
  have hac : (volume.comap UpperHalfPlane.coe : Measure ℍ) ≪ (volume : Measure ℍ) := by
    rw [volume_def]
    refine withDensity_absolutelyContinuous' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · refine Measurable.aemeasurable (Measurable.coe_nnreal_ennreal ?_)
      refine Continuous.measurable ?_
      refine .pow (.div₀ continuous_const ?_ ?_) _
      · exact continuous_im.subtype_mk _
      · exact fun x ↦ NNReal.ne_iff.mp x.im_ne_zero
    · have hz : NNReal.mk z.im z.im_pos.le ≠ 0 := NNReal.ne_iff.mp z.im_ne_zero
      exact ENNReal.coe_ne_zero.mpr (pow_ne_zero _ (one_div_ne_zero hz))
  have h1 := hac h0
  rw [measurableEmbedding_coe.comap_apply] at h1
  exact ((isOpenEmbedding_coe.isOpenMap U hU).measure_pos volume (hne.image _)).ne' h1

open MeasureTheory Set UpperHalfPlane in
theorem UpperTheory.V.Af.Rs.fdPos :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdPos := by
  intro _ φ hc h0 hint z hz hpos
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hint]
  have hV : IsOpen {w : ℍ | 0 < φ w} := isOpen_lt continuous_const hc
  rw [ModularGroup.fd_eq_closure_fdo] at hz
  have hne : ({w : ℍ | 0 < φ w} ∩ ModularGroup.fdo).Nonempty :=
    mem_closure_iff.mp hz _ hV hpos
  refine (UpperTheory.V.Af.Rs.volume_open_pos_upper_half_plane _ (hV.inter ModularGroup.isOpen_fdo) hne).trans_le
    (measure_mono ?_)
  rintro w ⟨hw, hw'⟩
  exact ⟨ne_of_gt hw, ModularGroup.fdo_subset_fd hw'⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TailFin
open MeasureTheory Set
open UpperHalfPlane hiding I
open scoped ENNReal

private lemma fd_meas : MeasurableSet ModularGroup.fd := by
  apply IsClosed.measurableSet
  have h1 : IsClosed {z : ℍ | 1 ≤ Complex.normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ (1 : ℝ) / 2} :=
    isClosed_le (UpperHalfPlane.continuous_re.abs) continuous_const
  exact h1.inter h2

private lemma tail_fin :
    ∫⁻ y in Ioi (1 / 2 : ℝ), ENNReal.ofReal (1 / y ^ 2) < ∞ := by
  have h : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioi (1 / 2 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
  have h' : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Ioi (1 / 2 : ℝ)) := by
    refine h.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) ≤ y := le_trans (by norm_num) (le_of_lt hy)
    simp only
    rw [Real.rpow_neg hy0, Real.rpow_two, one_div]
  exact h'.lintegral_lt_top

theorem UpperTheory.V.Af.Rs.fdFin :
    UpperTheory.V.Af.Rs.StripIm → UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdFin := by
  rintro - ⟨hm, hv⟩
  refine ⟨fd_meas, ?_⟩
  rw [hv, Measure.map_apply hm fd_meas]
  have hsub : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' ModularGroup.fd ⊆
      (Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Ioi (1 / 2 : ℝ)) ∪ ((univ : Set ℝ) ×ˢ Iic (0 : ℝ)) := by
    rintro ⟨x, y⟩ hp
    rcases le_or_gt y 0 with hy | hy
    · exact Or.inr ⟨mem_univ _, hy⟩
    · left
      have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
      have hp' : UpperTheory.V.Af.Rs.pt x y ∈ ModularGroup.fd := hp
      have e : UpperTheory.V.Af.Rs.pt x y = ⟨_, him⟩ := ofComplex_apply_of_im_pos him
      have hre : (UpperTheory.V.Af.Rs.pt x y).re = x := by rw [e]; simp [UpperHalfPlane.re]
      have hi : (UpperTheory.V.Af.Rs.pt x y).im = y := by rw [e]; simp [UpperHalfPlane.im]
      have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hp'
      have h2 := hp'.2
      rw [hre] at h2
      rw [hi] at h3
      refine ⟨abs_le.1 h2, ?_⟩
      show (1 / 2 : ℝ) < y
      nlinarith
  refine lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt (measure_union_le _ _) ?_)
  rw [ENNReal.add_lt_top]
  constructor
  · rw [withDensity_apply _ (measurableSet_Icc.prod measurableSet_Ioi), ← Measure.prod_restrict,
      lintegral_prod _ (by fun_prop)]
    simp only [lintegral_const]
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.2 (Ioi_subset_Ioi (by norm_num))]
    exact ENNReal.mul_lt_top tail_fin (by simp)
  · rw [withDensity_absolutelyContinuous _ _ (by simp [Measure.prod_prod, Iic_inter_Ioi])]
    exact ENNReal.zero_lt_top
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolMap
noncomputable section

open MeasureTheory Set
open UpperHalfPlane hiding I

namespace UpperTheory.V.Af.Rs

private lemma measurable_ofComplex : Measurable (ofComplex : ℂ → ℍ) := by
  classical
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have h : (UpperHalfPlane.coe ∘ (ofComplex : ℂ → ℍ)) =
      fun w : ℂ => if 0 < w.im then w else ((ofComplex 0 : ℍ) : ℂ) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [hw, ofComplex_apply_of_im_pos hw]
    · simp only [Function.comp, hw, if_false]
      rw [ofComplex_apply_of_im_nonpos (not_lt.mp hw), ofComplex_apply_of_im_nonpos (le_refl _ : (0 : ℂ).im ≤ 0)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const Complex.measurable_im) measurable_id measurable_const

private lemma pt_eq (p : ℝ × ℝ) : pt p.1 p.2 = ofComplex (Complex.measurableEquivRealProd.symm p) := by
  unfold pt
  congr 1
  apply Complex.ext <;> simp

theorem volMap : VolMap := by
  have hm : Measurable (fun p : ℝ × ℝ => pt p.1 p.2) := by
    simp only [pt_eq]
    exact measurable_ofComplex.comp Complex.measurableEquivRealProd.symm.measurable
  refine ⟨hm, ?_⟩
  ext s hs
  have hp : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
      (volume : Measure (ℝ × ℝ)).restrict (univ ×ˢ Ioi 0) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hset : (fun p : ℝ × ℝ => pt p.1 p.2) ⁻¹' s ∩ univ ×ˢ Ioi 0 =
      Complex.measurableEquivRealProd.symm ⁻¹' (UpperHalfPlane.coe '' s) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_image, pt_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by simpa using h2
      refine ⟨_, h1, ?_⟩
      rw [ofComplex_apply_of_im_pos h3]
    · rintro ⟨z, hz, hzp⟩
      refine ⟨?_, ?_⟩
      · rw [← hzp, ofComplex_apply]; exact hz
      · have h3 : 0 < (Complex.measurableEquivRealProd.symm p).im := by
          rw [← hzp]; exact z.im_pos
        simpa using h3
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), hp, Measure.restrict_restrict (hm hs), hset,
    volume_eq_lintegral,
    ← (Complex.volume_preserving_equiv_real_prod.symm _).setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp

end UpperTheory.V.Af.Rs
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIm
open MeasureTheory Set
open UpperHalfPlane hiding I

private theorem pt_re_im (x y : ℝ) (hy : 0 < y) :
    (UpperTheory.V.Af.Rs.pt x y).re = x ∧ (UpperTheory.V.Af.Rs.pt x y).im = y := by
  rw [UpperTheory.V.Af.Rs.pt, ← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im,
    UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hy)]
  simp

private theorem measurableSet_strip' : MeasurableSet UpperTheory.V.Af.Rs.strip := by
  have hre : Continuous fun z : ℍ => z.re := Complex.continuous_re.comp UpperHalfPlane.continuous_coe
  exact (measurableSet_le measurable_const hre.measurable).inter
    (measurableSet_lt hre.measurable measurable_const)

private theorem volume_restrict_strip_eq_map_withDensity (hV : UpperTheory.V.Af.Rs.VolMap) :
    (volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip =
      Measure.map (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2)
      ((((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))).withDensity
        fun p => ENNReal.ofReal (1 / p.2 ^ 2)) := by
  obtain ⟨hf, hvol⟩ := hV
  have hs : MeasurableSet ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) :=
    hf measurableSet_strip'
  have hset : (fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip ∩ (univ ×ˢ Ioi 0)
      = Ico (0:ℝ) 1 ×ˢ Ioi 0 := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, mem_Ioi, mem_Ico,
      UpperTheory.V.Af.Rs.strip, mem_setOf_eq]
    constructor
    · rintro ⟨h, hy⟩
      rw [(pt_re_im x y hy).1] at h
      exact ⟨h, hy⟩
    · rintro ⟨h, hy⟩
      rw [(pt_re_im x y hy).1]
      exact ⟨h, hy⟩
  have h0 : (volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ))) =
      ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hbase : ((volume : Measure ℝ).prod (volume.restrict (Ioi (0:ℝ)))).restrict
      ((fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2) ⁻¹' UpperTheory.V.Af.Rs.strip) =
      ((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0)) := by
    rw [h0, Measure.restrict_restrict hs, hset, ← Measure.prod_restrict]
  rw [hvol, Measure.restrict_map hf measurableSet_strip', restrict_withDensity hs, hbase]

theorem UpperTheory.V.Af.Rs.stripIm :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.StripIm := by
  intro hV φ hφ hint
  have hf : Measurable fun p : ℝ × ℝ => UpperTheory.V.Af.Rs.pt p.1 p.2 := hV.1
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) := by fun_prop
  have hlt : ∀ᵐ p ∂(((volume : Measure ℝ).restrict (Ico 0 1)).prod (volume.restrict (Ioi 0))),
      ENNReal.ofReal (1 / p.2 ^ 2) < ⊤ := Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have him : Continuous fun z : ℍ => z.im := Complex.continuous_im.comp UpperHalfPlane.continuous_coe
  have hm : Measurable fun z : ℍ => φ z.im := hφ.comp him.measurable
  show Integrable (fun z : ℍ => φ z.im) ((volume : Measure ℍ).restrict UpperTheory.V.Af.Rs.strip)
  rw [volume_restrict_strip_eq_map_withDensity hV, integrable_map_measure hm.aestronglyMeasurable hf.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hg hlt]
  have h1 : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Ico (0:ℝ) 1)) := integrable_const 1
  have h2 : Integrable (fun y => φ y / y ^ 2) (volume.restrict (Ioi (0:ℝ))) := hint
  refine (h1.mul_prod h2).congr ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)]
    with p hp
  simp only [Function.comp_apply, (pt_re_im p.1 p.2 hp).2,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 1 / p.2 ^ 2), smul_eq_mul, one_mul]
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.FdNull
open MeasureTheory Set in
private theorem UpperTheory.V.Af.Rs.line_null (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have h : {z : ℂ | z.re = c} = Complex.measurableEquivRealProd ⁻¹' (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [h, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod]
  simp

open MeasureTheory Set in
theorem UpperTheory.V.Af.Rs.fdNull :
    UpperTheory.V.Af.Rs.VolMap → UpperTheory.V.Af.Rs.FdNull := by
  intro _
  unfold UpperTheory.V.Af.Rs.FdNull
  rw [UpperHalfPlane.volume_eq_lintegral]
  apply setLIntegral_measure_zero
  have h0 : volume (Metric.sphere (0 : ℂ) 1 ∪ ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)})) = 0 :=
    measure_union_null (Measure.addHaar_sphere _ _ _)
      (measure_union_null (UpperTheory.V.Af.Rs.line_null _) (UpperTheory.V.Af.Rs.line_null _))
  refine measure_mono_null ?_ h0
  rintro _ ⟨z, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
  by_cases hs : 1 < Complex.normSq (z : ℂ)
  · right
    have h4 : ¬ |z.re| < 1 / 2 := fun h => h3 ⟨hs, h⟩
    have h5 : |z.re| = 1 / 2 := le_antisymm h2 (not_lt.mp h4)
    exact (abs_eq (by norm_num)).mp h5
  · left
    have h5 : Complex.normSq (z : ℂ) = 1 := le_antisymm (not_lt.mp hs) h1
    rw [Complex.normSq_eq_norm_sq] at h5
    rw [mem_sphere_zero_iff_norm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h5
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.FdCount
open MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups ENNReal

theorem UpperTheory.V.Af.Rs.fdCount :
    UpperTheory.V.Af.Rs.FdNull → UpperTheory.V.Af.Rs.FdCount := by
  intro hN
  unfold UpperTheory.V.Af.Rs.FdNull at hN
  unfold UpperTheory.V.Af.Rs.FdCount
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hnull : ∀ γ : SL(2, ℤ),
      volume ((fun z : ℍ => γ • z) ⁻¹' (ModularGroup.fd \ ModularGroup.fdo)) = 0 := by
    intro γ
    have : (fun z : ℍ => γ • z) = fun z : ℍ => ((γ : GL (Fin 2) ℝ)) • z := rfl
    rw [this, measure_preimage_smul]
    exact hN
  have hB := measure_iUnion_null hnull
  rw [ae_iff]
  refine measure_mono_null ?_ hB
  intro z hz
  by_contra hzB
  simp only [mem_iUnion, mem_preimage, not_exists] at hzB
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  have hgo : g • z ∈ ModularGroup.fdo := by
    by_contra h
    exact hzB g ⟨hg, h⟩
  have hne : g ≠ -g := by
    intro h
    have h1 : (1 : SL(2, ℤ)) = -1 := by
      have := congrArg (fun A => A * g⁻¹) h
      simpa using this
    have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h1
    simp at this
  apply hz
  rw [tsum_eq_sum (s := {g, -g}) ?_]
  · rw [Finset.sum_pair hne]
    have hg' : (-g) • z ∈ ModularGroup.fd := by simpa using hg
    rw [indicator_of_mem hg, indicator_of_mem hg', one_add_one_eq_two]
  · intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hγ
    apply indicator_of_notMem
    intro hmem
    have heq : γ • z = (γ * g⁻¹) • (g • z) := by
      rw [smul_smul, inv_mul_cancel_right]
    rw [heq] at hmem
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hgo hmem with h | h
    · exact hγ.1 (mul_inv_eq_one.mp h)
    · apply hγ.2
      rw [mul_inv_eq_iff_eq_mul] at h
      rw [h]
      simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RowBij
open UpperHalfPlane hiding I
open scoped MatrixGroups

private theorem UpperTheory.V.Af.Rs.eq_T_zpow_mul_of_row_eq {γ δ : SL(2, ℤ)}
    (h : UpperTheory.V.Af.Rs.row γ = UpperTheory.V.Af.Rs.row δ) : ∃ n : ℤ, γ = ModularGroup.T ^ n * δ := by
  have hc : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := congrFun h 0
  have hd : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := congrFun h 1
  have hγ := γ.det_coe
  have hδ := δ.det_coe
  rw [Matrix.det_fin_two] at hγ hδ
  refine ⟨-(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
      + (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two, hc, hd]
  · rw [hc, hd] at hγ
    linear_combination (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hγ
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * hδ
  · rw [hc, hd] at hγ
    linear_combination (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hγ
      - (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * hδ

private theorem UpperTheory.V.Af.Rs.row_T_zpow_mul (n : ℤ) (δ : SL(2, ℤ)) :
    UpperTheory.V.Af.Rs.row (ModularGroup.T ^ n * δ) = UpperTheory.V.Af.Rs.row δ := by
  funext i
  simp [UpperTheory.V.Af.Rs.row, ModularGroup.coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.V.Af.Rs.rowBij :
    UpperTheory.V.Af.Rs.RowBij := by
  refine ⟨fun γ => ModularGroup.bottom_row_coprime γ, ?_⟩
  intro z x
  obtain ⟨g, -, hg⟩ := ModularGroup.bottom_row_surj (R := ℤ) (Set.mem_setOf_eq ▸ x.2 : x.1 ∈ _)
  have hrow : UpperTheory.V.Af.Rs.row g = x.1 := hg
  refine ⟨ModularGroup.T ^ (-⌊(g • z).re⌋) * g, ⟨?_, ?_⟩, ?_⟩
  · rw [UpperTheory.V.Af.Rs.row_T_zpow_mul, hrow]
  · show 0 ≤ (_ : ℍ).re ∧ (_ : ℍ).re < 1
    rw [mul_smul, ModularGroup.re_T_zpow_smul]
    push_cast
    constructor
    · linarith [Int.floor_le (g • z).re]
    · linarith [Int.lt_floor_add_one (g • z).re]
  · rintro γ' ⟨hr, hs⟩
    have hr' : UpperTheory.V.Af.Rs.row γ' = UpperTheory.V.Af.Rs.row g := by rw [hr, hrow]
    obtain ⟨m, rfl⟩ := UpperTheory.V.Af.Rs.eq_T_zpow_mul_of_row_eq hr'
    have hs' : 0 ≤ ((ModularGroup.T ^ m * g) • z).re ∧ ((ModularGroup.T ^ m * g) • z).re < 1 := hs
    rw [mul_smul, ModularGroup.re_T_zpow_smul] at hs'
    have h1 : ((m + ⌊(g • z).re⌋ : ℤ) : ℝ) < 1 := by
      push_cast
      linarith [Int.floor_le (g • z).re]
    have h2 : (-1 : ℝ) < ((m + ⌊(g • z).re⌋ : ℤ) : ℝ) := by
      push_cast
      linarith [Int.lt_floor_add_one (g • z).re]
    have h1' : m + ⌊(g • z).re⌋ < 1 := by exact_mod_cast h1
    have h2' : -1 < m + ⌊(g • z).re⌋ := by exact_mod_cast h2
    have hm : m = -⌊(g • z).re⌋ := by omega
    rw [hm]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TBdd
open MeasureTheory in
theorem UpperTheory.V.Af.Rs.tBdd :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.ZDiff → UpperTheory.V.Af.Rs.ZInt → UpperTheory.V.Af.Rs.TBdd := by
  intro hF hD _ L _ G hG h0
  obtain ⟨C, hC⟩ := hD L
  obtain ⟨-, D, hD⟩ := hG
  refine ⟨(∑ _v : Fin 2 → ZMod L, |C| * D) * (volume : Measure UpperHalfPlane).real ModularGroup.fd, fun s hs => ?_⟩
  unfold UpperTheory.V.Af.Rs.TT
  refine norm_setIntegral_le_of_norm_le_const hF.2 fun z hz => ?_
  have hy : 0 < z.im := z.im_pos
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have hy2 : 1 / 2 ≤ z.im := by nlinarith
  have he : ∑ v, G v z * (UpperTheory.V.Af.Rs.Zc L v s z : ℂ) =
      ∑ v, G v z * ((UpperTheory.V.Af.Rs.Zc L v s z - UpperTheory.V.Af.Rs.Zc L 0 s z : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h0 z, zero_mul, sub_zero]
  rw [he]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := hC v 0 s hs z hz
  have h2 := hD v z hy2
  have h4 : C * z.im ^ 3 ≤ |C| * z.im ^ 3 := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  calc _ ≤ ‖G v z‖ * (|C| * z.im ^ 3) := mul_le_mul_of_nonneg_left (h1.trans h4) (norm_nonneg _)
    _ = |C| * (‖G v z‖ * z.im ^ 3) := by ring
    _ ≤ |C| * D := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ZLow
theorem UpperTheory.V.Af.Rs.zLow :
    UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.KerLow → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZLow := by
  intro hB hL hW L _ s hs z hz
  have hs' : s ∈ Set.Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨-, h0, -, -, -, hub⟩ := hB s hs'
  have hsum : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  have hk : Summable fun x : Fin 2 → ℤ => UpperTheory.V.Af.Rs.ker s x z :=
    Summable.of_nonneg_of_le (fun x => h0 x z) (fun x => hub x z hz) (hsum.mul_left _)
  have hv : ∀ v ∈ (Finset.univ : Finset (Fin 2 → ZMod L)), Summable fun x : Fin 2 → ℤ =>
      if UpperTheory.V.Af.Rs.cls L x = v then UpperTheory.V.Af.Rs.ker s x z else 0 := by
    intro v _
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) hk
    · split_ifs
      · exact h0 x z
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact h0 x z
  have he : ∑ v, UpperTheory.V.Af.Rs.Zc L v s z = ∑' x : Fin 2 → ℤ, UpperTheory.V.Af.Rs.ker s x z := by
    unfold UpperTheory.V.Af.Rs.Zc
    rw [← Summable.tsum_finsetSum hv]
    refine tsum_congr fun x => ?_
    simp
  rw [he, UpperTheory.V.Af.Rs.Wsum, ← tsum_mul_left]
  exact (hsum.mul_left _).tsum_le_tsum (fun x => hL s hs' x z hz) hk
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.RowRep
open scoped MatrixGroups

theorem UpperTheory.V.Af.Rs.rowRep :
    UpperTheory.V.Af.Rs.RowRep := by
  intro x
  set g := (x 0).gcd (x 1) with hg
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · obtain ⟨h0', h1'⟩ := Int.gcd_eq_zero_iff.mp h0
    refine ⟨0, 1, ?_⟩
    funext i
    fin_cases i <;> simp [h0', h1']
  · have hc : IsCoprime (x 0 / (g : ℤ)) (x 1 / (g : ℤ)) :=
      Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
    obtain ⟨γ, -, hγ⟩ := ModularGroup.bottom_row_surj (R := ℤ)
      (show ![x 0 / (g : ℤ), x 1 / (g : ℤ)] ∈ {cd : Fin 2 → ℤ | IsCoprime (cd 0) (cd 1)} by simpa using hc)
    refine ⟨g, γ, ?_⟩
    funext i
    have hi := congrFun hγ i
    simp only [UpperTheory.V.Af.Rs.row, Pi.smul_apply, smul_eq_mul] at hi ⊢
    rw [hi]
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_left (x 0) (x 1))).symm
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact (Int.mul_ediv_cancel' (Int.gcd_dvd_right (x 0) (x 1))).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.CharEq2
theorem UpperTheory.V.Af.Rs.charEq2 :
    UpperTheory.V.Af.Rs.Core → UpperTheory.V.Af.Rs.Deplete → UpperTheory.V.Af.Rs.CharEq2 := by
  intro hCore hDep k N M _ _ hk χ ψ g h hev
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨B, hB⟩ := hev.bddAbove
  obtain ⟨L, hL⟩ : ∃ L, L = N * M * B.factorial := ⟨_, rfl⟩
  haveI : NeZero L := ⟨by
    rw [hL]
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne N) (NeZero.ne M)) (Nat.factorial_ne_zero B)⟩
  haveI : NeZero (L * L) := ⟨Nat.mul_ne_zero (NeZero.ne L) (NeZero.ne L)⟩
  have hNL : N ∣ L := ⟨M * B.factorial, by rw [hL]; ring⟩
  have hML : M ∣ L := ⟨N * B.factorial, by rw [hL]; ring⟩
  obtain ⟨χ1, g1, hg1⟩ := hDep k N L hk hNL χ g
  obtain ⟨χ2, h1, hh1⟩ := hDep k M L hk hML ψ h
  have good : ∀ p, Nat.Prime p → ¬ p ∣ L → (h.a p = g.a p ∧ (starRingEnd ℂ) (g.a p) * χ p = g.a p ∧
      (starRingEnd ℂ) (h.a p) * ψ p = h.a p) := by
    intro p hp hpL
    by_contra hbad
    have hle : p ≤ B := hB (by simp only [Set.mem_setOf_eq]; exact fun H => hbad (H hp))
    exact hpL (hL ▸ Dvd.dvd.mul_left (Nat.dvd_factorial hp.pos hle) _)
  have hcore := hCore k (L * L) hk χ1 χ2 g1 h1 ?_ ?_
  · rw [Filter.eventually_cofinite]
    apply ((Finset.range (L + 1)).finite_toSet).subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_cases hpL : p ∣ L
    · simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne L)) hpL)
    · exfalso
      apply hp
      intro hpp
      rw [← ((hg1 p hpp).1 hpL).1, ← ((hh1 p hpp).1 hpL).1, hcore]
  · intro p hp
    by_cases hpL : p ∣ L
    · rw [(hg1 p hp).2 hpL, (hh1 p hp).2 hpL]
    · rw [((hh1 p hp).1 hpL).2, ((hg1 p hp).1 hpL).2]
      exact (good p hp hpL).1
  · intro p hp hne
    by_cases hpL : p ∣ L
    · exact (hg1 p hp).2 hpL
    · obtain ⟨e1, e2, e3⟩ := good p hp hpL
      rw [((hg1 p hp).1 hpL).2]
      by_contra ha
      apply hne
      rw [((hg1 p hp).1 hpL).1, ((hh1 p hp).1 hpL).1]
      rw [e1] at e3
      have hc : (starRingEnd ℂ) (g.a p) ≠ 0 := by simpa using ha
      exact mul_left_cancel₀ hc (e2.trans e3.symm)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.Imports
open Set UpperTheory.V.Af UpperTheory.V.Sd
open scoped ComplexConjugate

theorem UpperTheory.V.Af.Rs.cmp :
    UpperTheory.V.Af.Rs.RankSum → UpperTheory.V.Af.Rs.Rankin → UpperTheory.V.Af.Rs.ArFact → UpperTheory.V.Af.Rs.ArSum → UpperTheory.V.Af.Rs.Cmp := by
  intro hRS hR hAF hAS k L _ hk χ ψ g h hap hχ s hs
  have hrec1 : Rs.Rec (fun p => χ (p : ZMod L) * (p:ℂ)^(k-1)) (coef g.f) :=
    ⟨g.one, fun p hp n hn => g.eig p hp n hn⟩
  have hrec2 : Rs.Rec (fun p => ψ (p : ZMod L) * (p:ℂ)^(k-1)) (coef h.f) :=
    ⟨h.one, fun p hp n hn => h.eig p hp n hn⟩
  have hba : ∀ p, Nat.Prime p → coef h.f p = coef g.f p := fun p hp => hap p hp
  have hz : ∀ p, Nat.Prime p → χ (p : ZMod L) * (p:ℂ)^(k-1) ≠ ψ (p : ZMod L) * (p:ℂ)^(k-1) →
      coef g.f p = 0 := by
    intro p hp hne
    apply hχ p hp
    intro heq
    apply hne
    rw [heq]
  have hbd : ∀ p, Nat.Prime p → ‖χ (p : ZMod L) * (p:ℂ)^(k-1)‖ ≤ (p:ℝ)^(k-1) ∧
      ‖ψ (p : ZMod L) * (p:ℂ)^(k-1)‖ ≤ (p:ℝ)^(k-1) := by
    intro p hp
    constructor <;>
    · rw [norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one _ _)
  obtain ⟨P, hPb, hP⟩ := hAF (k-1) _ _ (coef g.f) (coef h.f) hrec1 hrec2 hba hz hbd
  have hkt : ((k-1 : ℕ) : ℝ) + 1 ≤ (k:ℝ) + s - 1 := by
    rw [Nat.cast_sub hk]
    push_cast
    linarith [hs.1]
  have key := hAS (k-1) ((k:ℝ) + s - 1) (coef g.f) (coef h.f) P hkt hPb hP (hRS k L g.f s hs)
  rw [hR k L g.f g.f s hs, hR k L g.f h.f s hs, norm_mul, norm_mul]
  have hconv : (∑' n : ℕ, (starRingEnd ℂ) (coef g.f n) * coef g.f n / (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ))
      = ((∑' n : ℕ, ‖coef g.f n‖ ^ 2 / (n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.conj_mul']
    push_cast
    ring
  have hnn : 0 ≤ ∑' n : ℕ, ‖coef g.f n‖ ^ 2 / (n:ℝ) ^ ((k:ℝ) + s - 1) :=
    tsum_nonneg fun n => div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [hconv, Complex.norm_of_nonneg hnn]
  have hre := Complex.re_le_norm (∑' n : ℕ, (starRingEnd ℂ) (coef h.f n) * coef g.f n /
    (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ))
  have hg := norm_nonneg ((Rs.gam ((k:ℝ) + s - 1) : ℝ) : ℂ)
  calc _ ≤ ‖((Rs.gam ((k:ℝ) + s - 1) : ℝ) : ℂ)‖ * (7 * ‖∑' n : ℕ, (starRingEnd ℂ) (coef h.f n) * coef g.f n /
        (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hg
    _ = _ := by ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.PetRe
open UpperHalfPlane hiding I
open UpperTheory.V.Af UpperTheory.V.Sd

private lemma pet_re (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    (petersson (k : ℤ) f f z).re = Complex.normSq (f z) * z.im ^ k := by
  simp only [petersson]
  rw [zpow_natCast, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.sq_norm]

theorem UpperTheory.V.Af.Rs.core :
    UpperTheory.V.Af.Rs.TBdd → UpperTheory.V.Af.Rs.TTop → UpperTheory.V.Af.Rs.ClsEx → UpperTheory.V.Af.Rs.ClsProp → UpperTheory.V.Af.Rs.TEq → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.PetChar → UpperTheory.V.Af.Rs.Cmp → UpperTheory.V.Af.Rs.Core := by
  intro hTB hTT hCE hCP hTE hLB hNP hPC hCmp k L _ hk χ ψ g h hap hχ
  by_contra hne
  have hne' : χ * ψ⁻¹ ≠ 1 := fun e => hne (mul_inv_eq_one.mp e)
  obtain ⟨G, hG⟩ := hCE L (χ * ψ⁻¹) (petersson (k : ℤ) h.f g.f) (hPC k L χ ψ g.f h.f g.char h.char)
  have hNF := hNP k L g.f h.f
  obtain ⟨hP1, hP2, -⟩ := hCP L _ _ G hG
  obtain ⟨C, hC⟩ := hTB L G (hP1 hNF) (hP2 hne')
  have hchar0 := hPC k L χ χ g.f g.f g.char g.char
  simp only [mul_inv_cancel] at hchar0
  obtain ⟨G0, hG0⟩ := hCE L 1 (petersson (k : ℤ) g.f g.f) hchar0
  have hNF0 := hNP k L g.f g.f
  obtain ⟨hQ1, -, hQ3⟩ := hCP L _ _ G0 hG0
  have hfz : ∃ z, g.f z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h0 : (⇑g.f : ℍ → ℂ) = 0 := funext hall
    have := g.one
    rw [h0] at this
    simp [UpperTheory.V.Af.coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨z0, hz0⟩ := hfz
  have hpos : ∃ z, 0 < (petersson (k : ℤ) g.f g.f z).re := by
    refine ⟨z0, ?_⟩
    rw [pet_re]
    exact mul_pos (Complex.normSq_pos.mpr hz0) (pow_pos z0.im_pos k)
  have hnn : ∀ z, 0 ≤ (petersson (k : ℤ) g.f g.f z).re := by
    intro z
    rw [pet_re]
    exact mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg z.im_pos.le k)
  obtain ⟨hR1, hR2⟩ := hQ3 rfl hnn hpos
  obtain ⟨s, hs, hM⟩ := hTT L G0 (hQ1 hNF0) hR1 hR2 (56 * C + 1)
  have hs1 : (1 : ℝ) ≤ s := hs.1.le
  have e1 := hTE L _ _ G hG hNF (hP1 hNF) s hs
  have e0 := hTE L _ _ G0 hG0 hNF0 (hQ1 hNF0) s hs
  obtain ⟨-, hL1, -⟩ := hLB L (χ * ψ⁻¹) s hs1
  obtain ⟨-, -, hL0⟩ := hLB L 1 s hs1
  have hCs := hC s hs
  have hcmp := hCmp k L hk χ ψ g h hap hχ s hs
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e1, norm_mul, norm_mul, h2] at hCs
  have hre := Complex.re_le_norm (Rs.TT L G0 s)
  have hnorm : ‖Rs.TT L G0 s‖ = ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ *
      (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖) := by
    rw [e0, norm_mul, norm_mul, h2]
  have hA := norm_nonneg (Rs.stripI (petersson (k : ℤ) h.f g.f) s)
  have hB := norm_nonneg (Rs.stripI (petersson (k : ℤ) g.f g.f) s)
  have hX : ‖Rs.stripI (petersson (k : ℤ) h.f g.f) s‖ ≤ 2 * C := by nlinarith
  have hY : ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ * (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖)
      ≤ 2 * (2 * (7 * (2 * C))) := by
    apply mul_le_mul hL0 _ (by positivity) (by norm_num)
    linarith
  linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.MelSum
noncomputable section

open MeasureTheory Set

namespace UpperTheory.V.Af.Rs

private lemma melSum_int {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    IntegrableOn (fun y : ℝ => a * Real.exp (-r * y) * y ^ (t - 1)) (Ioi 0) := by
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := t - 1) (p := 1) (b := r) (by linarith) one_pos hr).const_mul a
  refine IntegrableOn.congr_fun h (fun y _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring

private lemma melSum_val {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    ∫ y in Ioi (0 : ℝ), a * Real.exp (-r * y) * y ^ (t - 1) = a * ((1 / r) ^ t * Real.Gamma t) := by
  have e : (fun y : ℝ => a * Real.exp (-r * y) * y ^ (t - 1)) =
      fun y => a * (y ^ (t - 1) * Real.exp (-(r * y))) := by
    funext y
    rw [neg_mul]
    ring
  rw [e, integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ht hr]

theorem melSum : MelSum := by
  intro c P t ht hc hP hI
  have hΓ : 0 < Real.Gamma t := Real.Gamma_pos_of_pos ht
  have h4 : 0 < 4 * Real.pi := by positivity
  have hCpos : 0 < (4 * Real.pi) ^ t / Real.Gamma t := div_pos (Real.rpow_pos_of_pos h4 t) hΓ
  have hr : ∀ n : ℕ, 0 < 4 * Real.pi * ((n + 1 : ℕ) : ℝ) := fun n => by positivity
  have hval : ∀ n : ℕ, c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t =
      (4 * Real.pi) ^ t / Real.Gamma t * ∫ y in Ioi (0 : ℝ),
        c (n + 1) * Real.exp (-(4 * Real.pi * ((n + 1 : ℕ) : ℝ)) * y) * y ^ (t - 1) := by
    intro n
    rw [melSum_val ht (hr n)]
    have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [Real.div_rpow zero_le_one (hr n).le, Real.one_rpow, Real.mul_rpow h4.le hm.le]
    have h5 : 0 < ((n + 1 : ℕ) : ℝ) ^ t := Real.rpow_pos_of_pos hm t
    have h6 : 0 < (4 * Real.pi) ^ t := Real.rpow_pos_of_pos h4 t
    field_simp
  have hbound : ∀ N, ∑ n ∈ Finset.range N, c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t ≤
      (4 * Real.pi) ^ t / Real.Gamma t * ∫ y in Ioi (0 : ℝ), P y * y ^ (t - 1) := by
    intro N
    simp_rw [hval]
    rw [← Finset.mul_sum, ← integral_finsetSum _ (fun n _ => melSum_int ht (hr n) _)]
    apply mul_le_mul_of_nonneg_left _ hCpos.le
    apply setIntegral_mono_on
    · exact integrable_finsetSum _ (fun n _ => melSum_int ht (hr n) _)
    · exact hI
    · exact measurableSet_Ioi
    · intro y hy
      have hy' : 0 < y := hy
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy'.le _)
      have h1 : ∑ n ∈ Finset.range (N + 1), c n * Real.exp (-(4 * Real.pi * n) * y) ≤ P y :=
        sum_le_hasSum _ (fun i _ => mul_nonneg (hc i) (Real.exp_pos _).le) (hP y hy')
      rw [Finset.sum_range_succ'] at h1
      have h0 : 0 ≤ c 0 * Real.exp (-(4 * Real.pi * ((0 : ℕ) : ℝ)) * y) :=
        mul_nonneg (hc 0) (Real.exp_pos _).le
      linarith
  have hs : Summable (fun n : ℕ => c (n + 1) / ((n + 1 : ℕ) : ℝ) ^ t) :=
    summable_of_sum_range_le
      (fun n => div_nonneg (hc _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hbound
  exact (summable_nat_add_iff 1 (f := fun n : ℕ => c n / (n : ℝ) ^ t)).mp hs

end UpperTheory.V.Af.Rs
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.ZInt
open MeasureTheory Set UpperHalfPlane

theorem UpperTheory.V.Af.Rs.zInt :
    UpperTheory.V.Af.Rs.FdFin → UpperTheory.V.Af.Rs.KerBd → UpperTheory.V.Af.Rs.WTop → UpperTheory.V.Af.Rs.ZInt := by
  intro hF hB hW L _ G hG s hs v v'
  obtain ⟨hGc, C0, hC0⟩ := hG
  have hs' : s ∈ Icc (1 : ℝ) 2 := ⟨hs.1.le, hs.2⟩
  obtain ⟨h1, h2, -, -, -, h6⟩ := hB s hs'
  have hW2 : Summable fun x : Fin 2 → ℤ => ‖x‖ ^ (-(2 * s)) := hW.1 (2 * s) (by linarith [hs.1])
  set W := ∑' x : Fin 2 → ℤ, ‖x‖ ^ (-(2 * s)) with hWdef
  set g : (Fin 2 → ℤ) → ℍ → ℝ := fun x z =>
    if UpperTheory.V.Af.Rs.cls L x = v' then UpperTheory.V.Af.Rs.ker s x z else 0 with hg
  have hg0 : ∀ x z, 0 ≤ g x z := fun x z => by
    simp only [hg]
    split_ifs
    exacts [h2 x z, le_rfl]
  have hgle : ∀ x z, g x z ≤ UpperTheory.V.Af.Rs.ker s x z := fun x z => by
    simp only [hg]
    split_ifs
    exacts [le_rfl, h2 x z]
  have hgm : ∀ x, Measurable (g x) := by
    intro x
    by_cases h : UpperTheory.V.Af.Rs.cls L x = v'
    · have e : g x = UpperTheory.V.Af.Rs.ker s x := by
        funext z
        simp [hg, h]
      rw [e]
      exact (h1 x).measurable
    · have e : g x = fun _ => 0 := by
        funext z
        simp [hg, h]
      rw [e]
      exact measurable_const
  have hgs : ∀ z ∈ ModularGroup.fd, Summable fun x => g x z := fun z hz =>
    Summable.of_nonneg_of_le (fun x => hg0 x z) (fun x => (hgle x z).trans (h6 x z hz))
      (hW2.mul_left _)
  have hEq : EqOn (fun z => G v z * (((∑' x, ENNReal.ofReal (g x z)).toReal : ℝ) : ℂ))
      (fun z => G v z * ((UpperTheory.V.Af.Rs.Zc L v' s z : ℝ) : ℂ)) ModularGroup.fd := by
    intro z hz
    have e : (∑' x, ENNReal.ofReal (g x z)).toReal = UpperTheory.V.Af.Rs.Zc L v' s z := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => hg0 x z) (hgs z hz),
        ENNReal.toReal_ofReal (tsum_nonneg fun x => hg0 x z)]
      rfl
    simp only [e]
  refine IntegrableOn.congr_fun ?_ hEq hF.1
  refine Measure.integrableOn_of_bounded (M := 8 * C0 * W) hF.2.ne ?_ ?_
  · exact ((hGc v).measurable.mul (Complex.measurable_ofReal.comp
      (Measurable.ennreal_toReal (Measurable.tsum fun x => (hgm x).ennreal_ofReal)))).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem hF.1 fun z hz => ?_
    have him0 : 0 < z.im := z.im_pos
    have him : 1 / 2 ≤ z.im := by
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
      nlinarith
    have e := hEq hz
    simp only at e
    rw [e]
    have hZ0 : 0 ≤ UpperTheory.V.Af.Rs.Zc L v' s z := tsum_nonneg fun x => hg0 x z
    have hZ : UpperTheory.V.Af.Rs.Zc L v' s z ≤ 4 * z.im ^ 2 * W := by
      calc UpperTheory.V.Af.Rs.Zc L v' s z = ∑' x, g x z := rfl
        _ ≤ ∑' x : Fin 2 → ℤ, 4 * z.im ^ 2 * ‖x‖ ^ (-(2 * s)) :=
          Summable.tsum_le_tsum (fun x => (hgle x z).trans (h6 x z hz)) (hgs z hz) (hW2.mul_left _)
        _ = 4 * z.im ^ 2 * W := tsum_mul_left
    have hGb := hC0 v z him
    have hW0 : 0 ≤ W := tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hZ0]
    have hG2 : ‖G v z‖ * z.im ^ 2 ≤ 2 * C0 := by
      nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (G v z)) (sq_nonneg z.im)) (sub_nonneg.mpr him)]
    calc ‖G v z‖ * UpperTheory.V.Af.Rs.Zc L v' s z ≤ ‖G v z‖ * (4 * z.im ^ 2 * W) :=
          mul_le_mul_of_nonneg_left hZ (norm_nonneg _)
      _ ≤ 8 * C0 * W := by nlinarith [mul_le_mul_of_nonneg_left hG2 hW0]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.GcdSum
open UpperTheory.V.Af.Rs in
private lemma gcdSum_inj :
    Function.Injective (fun p : ℕ × Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
  rintro ⟨n, a, ha⟩ ⟨m, b, hb⟩ h
  simp only at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1
  have ga : (a 0).gcd (a 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp ha
  have gb : (b 0).gcd (b 1) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hb
  have hk : (((n + 1 : ℕ) : ℤ) * a 0).gcd (((n + 1 : ℕ) : ℤ) * a 1)
      = (((m + 1 : ℕ) : ℤ) * b 0).gcd (((m + 1 : ℕ) : ℤ) * b 1) := by
    rw [h0, h1]
  rw [Int.gcd_mul_left, Int.gcd_mul_left, ga, gb] at hk
  simp only [Int.natAbs_natCast, mul_one] at hk
  have hnm : n = m := by omega
  subst hnm
  have hpos : ((n + 1 : ℕ) : ℤ) ≠ 0 := by positivity
  have e0 : a 0 = b 0 := mul_left_cancel₀ hpos h0
  have e1 : a 1 = b 1 := mul_left_cancel₀ hpos h1
  have hab : a = b := by
    funext i
    fin_cases i
    · exact e0
    · exact e1
  subst hab
  rfl

open UpperTheory.V.Af.Rs in
private lemma gcdSum_surj (v : Fin 2 → ℤ) (hv : v ≠ 0) :
    v ∈ Set.range (fun p : ℕ × Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
  set g := (v 0).gcd (v 1) with hg
  have hpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h
    · exfalso
      obtain ⟨a0, a1⟩ := Int.gcd_eq_zero_iff.mp h0
      apply hv
      funext i
      fin_cases i
      · exact a0
      · exact a1
    · exact h
  have hc : IsCoprime ((fun i => v i / (g : ℤ)) 0) ((fun i => v i / (g : ℤ)) 1) :=
    Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hpos)
  refine ⟨(g - 1, ⟨fun i => v i / (g : ℤ), hc⟩), ?_⟩
  have hg1 : g - 1 + 1 = g := Nat.sub_add_cancel hpos
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, hg1]
  fin_cases i
  · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))
  · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))

theorem UpperTheory.V.Af.Rs.gcdSum :
    UpperTheory.V.Af.Rs.GcdSum := by
  intro u c hu hc hu0 hc0 hmul
  have hsupp : Function.support u ⊆
      Set.range (fun p : ℕ × UpperTheory.V.Af.Rs.Cop => (((p.1 + 1 : ℕ) : ℤ)) • p.2.1) := by
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      exact hv hu0
    exact gcdSum_surj v hv0
  rw [← gcdSum_inj.tsum_eq hsupp]
  have hterm : ∀ p : ℕ × UpperTheory.V.Af.Rs.Cop,
      u ((((p.1 + 1 : ℕ) : ℤ)) • p.2.1) = c (p.1 + 1) * u p.2.1 := fun p => hmul (p.1 + 1) p.2
  have hprod : Summable fun p : ℕ × UpperTheory.V.Af.Rs.Cop => c (p.1 + 1) * u p.2.1 := by
    have := hu.comp_injective gcdSum_inj
    refine this.congr fun p => ?_
    exact hterm p
  simp only [hterm]
  rw [hc.tsum_eq_zero_add, hc0, zero_add]
  exact ((hc.comp_injective (add_left_injective 1)).tsum_mul_tsum
    (hu.comp_injective Subtype.val_injective) hprod).symm
end
