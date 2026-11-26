module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaFrameCubeConstantRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramified
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfPreservesFullLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPolarisedTopFormDbarExactEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowth
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_corrC : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (corrC ρ G₀ G₁) (offHyp S U) := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK
  obtain ⟨C, hC0, hCb⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  set c' : ℝ := |c| + C + C * (|c| + C) with hc'
  have hposition : ∀ v ∈ offHyp S U, v ∈ K → ∀ j : Fin n, ∀ i a b p q,
      ‖intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j i a b p q‖ *
        (poinWt S v a * poinWt S v b) ≤ c' := by
    intro v hv hvK j i a b p q
    obtain ⟨-, hdb, hcn, hcv⟩ := hCb v hvK
    have hw01 := (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).1
    have hwa := hw01 a
    have hwb := hw01 b
    have hab : poinWt S v a * poinWt S v b ≤ 1 := mul_le_one₀ hwa.2 hwb.1 hwb.2
    have hab0 : 0 ≤ poinWt S v a * poinWt S v b := mul_nonneg hwa.1 hwb.1
    have hca : 0 ≤ |c| := abs_nonneg c
    have hCc : 0 ≤ C * (|c| + C) := mul_nonneg hC0 (add_nonneg hca hC0)
    unfold intersection_update_fsHerm_neg_one
    split_ifs with h1 h2
    · have := hcurv v hv a b p q
      simp only [curvAt]
      linarith [le_abs_self c]
    · simp only [cutForm, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, norm_mul]
      have e1 := hconn v hv a p q
      have e2 := hcn a p q
      have e3 := hdb b
      have hxy := norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
      have hD0 := norm_nonneg (dbar (fun x => (ρ x : ℂ)) v (coordVec b))
      have hN0 := norm_nonneg (conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q)
      have hwab : poinWt S v a * poinWt S v b ≤ poinWt S v a := mul_le_of_le_one_right hwa.1 hwb.2
      have hY : ‖conn G₀ v (coordVec a) p q‖ * poinWt S v a ≤ C :=
        (mul_le_mul e2 hwa.2 hwa.1 hC0).trans (by rw [mul_one])
      have hS : (‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖) * poinWt S v a ≤ |c| + C := by
        calc _ ≤ (‖conn G₁ v (coordVec a) p q‖ + ‖conn G₀ v (coordVec a) p q‖) * poinWt S v a :=
              mul_le_mul_of_nonneg_right hxy hwa.1
          _ ≤ |c| + C := by rw [add_mul]; linarith [le_abs_self c]
      calc _ ≤ ‖dbar (fun x => (ρ x : ℂ)) v (coordVec b)‖ *
              ‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖ * poinWt S v a :=
            mul_le_mul_of_nonneg_left hwab (mul_nonneg hD0 hN0)
        _ = ‖dbar (fun x => (ρ x : ℂ)) v (coordVec b)‖ *
              (‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖ * poinWt S v a) := by ring
        _ ≤ C * (|c| + C) := mul_le_mul e3 hS (mul_nonneg hN0 hwa.1) hC0
        _ ≤ c' := by linarith
    · have := hcv a b p q
      simp only [curvAt]
      have : ‖curv G₀ v (coordVec a) (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ C :=
        (mul_le_mul this hab hab0 hC0).trans (by rw [mul_one])
      linarith
  refine GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K (corrC ρ G₀ G₁)
    ((n : ℝ) * ((Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c'| ^ n)) hU hK hKU hsmall ?_ ?_ ?_
  · intro v hv
    have hvU := hv.1
    have hρv : ContDiffAt ℝ 1 ρ v :=
      (hρ.contDiffAt (hU.mem_nhds hvU)).of_le (WithTop.coe_le_coe.2 le_top)
    exact (GlobalTheory.T.continuousAt_transgressionTopCoeffComplex hρv ((hG₀ v hvU).1.of_le (WithTop.coe_le_coe.2 le_top)) (hG₀ v hvU).2
      ((hG₁ v hv).1.of_le (WithTop.coe_le_coe.2 le_top)) (hG₁ v hv).2).continuousWithinAt
  · intro v hv hvK
    apply GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero
    have : U \ K ∈ 𝓝 v := (hU.sdiff hK.isClosed).mem_nhds ⟨hv.1, hvK⟩
    filter_upwards [this] with x hx
    exact hρK x hx.1 hx.2
  · intro v hv hvK
    have hwpos : ∀ a, 0 < poinWt S v a := (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).2 hv.2
    calc ‖corrC ρ G₀ G₁ v‖
        ≤ ∑ j : Fin n, ‖mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c'| ^ n *
            ∏ a, (poinWt S v a)⁻¹ ^ 2 :=
          Finset.sum_le_sum fun j _ => GlobalTheory.T.norm_polarisedTopChernCoeff_le_of_weighted_bound _ _ c' hwpos (hposition v hv hvK j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowthStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_chernTransgressionTerm_poincareGrowth : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (corrC ρ G₀ G₁) (offHyp S U) := by
  first | exact @GlobalTheory.GoodTop.integrableOn_corrC | exact GlobalTheory.GoodTop.integrableOn_corrC | (intros; apply GlobalTheory.GoodTop.integrableOn_corrC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGram
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGram
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma continuousAt_cutoff_mul_chern_form_coeff {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hG : _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G v) (hdet : IsUnit (G v).det) (hρ : ContinuousAt ρ v) :
    ContinuousAt (fun x => (ρ x : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G x)
      v := by
  refine ContinuousAt.mul (Complex.continuous_ofReal.continuousAt.comp (f := ρ) hρ) ?_
  refine _root_.GlobalTheory.GoodTop.continuousAt_mixTop (K := fun x _ => _root_.GlobalTheory.GoodTop.curvAt G x)
    fun i a b p q => ?_
  have h := hG.curv (j := 0) hdet
    (by rw [zero_add]; first | exact le_top | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤)) | exact WithTop.coe_le_coe.2 le_top)
    (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q
  exact h.continuousAt


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ),
      IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U →
      (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) U := by
  intro n r _ _ U K G₀ ρ hU hK hKU hG₀ hρ hρK
  have hcont : ContinuousOn
      (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) K :=
    fun v hv => (continuousAt_cutoff_mul_chern_form_coeff (hG₀ v (hKU hv)).1 (hG₀ v (hKU hv)).2
      (hρ.contDiffAt (hU.mem_nhds (hKU hv))).continuousAt).continuousWithinAt
  refine (hcont.integrableOn_compact hK).of_forall_diff_eq_zero hU.measurableSet
    fun v hv => ?_
  rw [hρK v hv.1 hv.2, Complex.ofReal_zero, zero_mul]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormSmoothGramStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (U K : Set (V n)) (G₀ : V n → Matrix r r ℂ) (ρ : V n → ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) U := by
  first | exact @GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | exact GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth | (intros; apply GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasEqChartMeasOfCompatOn
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem glueMeas_eq_chartMeas_of_compat_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ρ : κ → Y → ENNReal} (e' : OpenPartialHomeomorph Y (V n)) (ρ' : Y → ENNReal), S ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → (∀ i j y, y ∈ S → y ∈ (e i).source → y ∈ (e j).source → ρ i y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ρ j y) → (∀ j y, y ∈ S → y ∈ (e j).source → ρ' y = ENNReal.ofReal (‖transDet e' (e j) y‖ ^ 2) * ρ j y) → glueMeas e ρ S = chartMeas e' ρ' S := by
  intro n Y κ _ _ _ _ e hd hcov S hS ρ e' ρ' hSe hd' hρ hρ'
  have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := ρ) (ρ' := fun i => S.indicator (ρ i)) (c := 1)
    ENNReal.one_ne_top hS (fun i y _ hy => by rw [one_mul, Set.indicator_of_mem hy])
  rw [one_smul] at hm
  have cσ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      S.indicator (ρ i) y = ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * S.indicator (ρ j) y := by
    intro i j y hi hj
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact hρ i j y hy hi hj
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
  have key : (glueMeas e ρ).restrict S = (chartMeas e' ρ').restrict S := by
    rw [hm]
    refine ext_of_cover (fun i => (e i).source) (fun i => (e i).open_source) hcov fun i A hA hAi => ?_
    have hsub : A ∩ S ⊆ (e i).source := Set.inter_subset_left.trans hAi
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
      glueMeas_apply e (fun i => S.indicator (ρ i)) hd cσ i (hA.inter hS) hsub]
    refine (chartMeas_eq e' (e i) (hd' i) (hA.inter hS) (Set.inter_subset_right.trans hSe) hsub
      fun y hy => ?_).symm
    rw [Set.indicator_of_mem hy.2]
    exact hρ' i y hy.2 (hsub hy)
  have := congrArg (fun μ : Measure Y => μ S) key
  simpa only [Measure.restrict_apply_self] using this

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChart
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

theorem hasInt_of_chart : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d : κ → Y → ℝ} (e' : OpenPartialHomeomorph Y (V n)) (W : Set Y) (g : V n → ℝ), IsOpen W → W ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → IsTopForm e d S → (∀ i y, y ∈ S → y ∉ W → y ∈ (e i).source → d i y = 0) → (∀ j y, y ∈ S → y ∈ W → y ∈ (e j).source → g (e' y) = ‖transDet e' (e j) y‖ ^ 2 * d j y) → IntegrableOn g (e' '' (S ∩ W)) → HasInt e d S (∫ v in e' '' (S ∩ W), g v) := by
  intro n Y κ _ _ _ _ e hd hcov S hS d e' W g hW hWe hd' hT h0 hg hint
  have hSW : MeasurableSet (S ∩ W) := hS.inter hW.measurableSet
  have hsub : S ∩ W ⊆ e'.source := Set.inter_subset_right.trans hWe
  have key : ∀ ε : ℝ, glueMeas e (fun i y => ENNReal.ofReal (ε * d i y)) S =
      ∫⁻ v in e' '' (S ∩ W), ENNReal.ofReal (ε * g v) := by
    intro ε
    have hD : MeasurableSet (S \ W) := hS.diff hW.measurableSet
    have hz := GlobalTheory.ChernScale.glueMeas_restrict_eq e (ρ := fun i y => ENNReal.ofReal (ε * d i y))
      (ρ' := fun i y => ENNReal.ofReal (ε * d i y)) (c := 0) ENNReal.zero_ne_top hD
      (fun i y hi hy => by rw [h0 i y hy.1 hy.2 hi]; simp)
    have hz' : glueMeas e (fun i y => ENNReal.ofReal (ε * d i y)) (S \ W) = 0 := by
      have := congrArg (fun μ : Measure Y => μ (S \ W)) hz
      simpa only [Measure.restrict_apply_self, zero_smul, Measure.coe_zero, Pi.zero_apply] using this
    rw [← measure_inter_add_diff S hW.measurableSet, hz', add_zero,
      glueMeas_eq_chartMeas_of_compat_on e hd hcov hSW e' (fun y => ENNReal.ofReal (ε * g (e' y))) hsub hd'
        (fun i j y hy hi hj => by
          rw [hT.trans i j y hy.1 hi hj, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm])
        (fun j y hy hj => by
          rw [hg j y hy.1 hy.2 hj, ← ENNReal.ofReal_mul (sq_nonneg _), mul_left_comm]),
      chartMeas_apply_of_subset _ _ hSW hsub]
    refine setLIntegral_congr_fun (measurableSet_image e' hSW hsub) ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [e'.left_inv (hsub hy)]
  refine ⟨fun ε => ?_, ?_⟩
  · rw [key]
    exact (Integrable.const_mul hint _).lintegral_lt_top.ne
  · rw [measureReal_def, measureReal_def, key, key,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
    simp

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChartStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d : κ → Y → ℝ} (e' : OpenPartialHomeomorph Y (V n)) (W : Set Y) (g : V n → ℝ), IsOpen W → W ⊆ e'.source → (∀ j, DifferentiableOn ℂ (e j ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' (e j).source)) → IsTopForm e d S → (∀ i y, y ∈ S → y ∉ W → y ∈ (e i).source → d i y = 0) → (∀ j y, y ∈ S → y ∈ W → y ∈ (e j).source → g (e' y) = ‖transDet e' (e j) y‖ ^ 2 * d j y) → IntegrableOn g (e' '' (S ∩ W)) → HasInt e d S (∫ v in e' '' (S ∩ W), g v) := by
  first | exact @GlobalTheory.GoodTop.hasInt_of_chart | exact GlobalTheory.GoodTop.hasInt_of_chart | (intros; apply GlobalTheory.GoodTop.hasInt_of_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImageProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImageProperties
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem goodPatch_image : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → IsOpen (e '' W) ∧ e '' (ptsIn X.str σ O ∩ W) = offHyp S (e '' W) ∧ ∀ K : Set (CxPts X.str σ), IsClosed K → K ⊆ W → IsCompact (e '' K) := by
  intro F _ σ X m E O H e S A W c h
  refine ⟨e.isOpen_image_of_subset_source h.isOpen h.sub, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨z, ⟨hO, hW⟩, rfl⟩
      exact ⟨⟨z, hW, rfl⟩, (h.mem z hW).1 hO⟩
    · rintro ⟨⟨z, hW, rfl⟩, hv⟩
      exact ⟨z, ⟨(h.mem z hW).2 hv, hW⟩, rfl⟩
  · intro K hK hKW
    haveI : CompactSpace (CxPts X.str σ) := CxPts.compactSpace σ X.isProjOver
    exact hK.isCompact.image_of_continuousOn (e.continuousOn.mono (hKW.trans h.sub))

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImagePropertiesStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPatch_chart_image_properties : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ) {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → IsOpen (e '' W) ∧ e '' (ptsIn X.str σ O ∩ W) = offHyp S (e '' W) ∧ ∀ K : Set (CxPts X.str σ), IsClosed K → K ⊆ W → IsCompact (e '' K) := by
  first | exact @GlobalTheory.GoodTop.goodPatch_image | exact GlobalTheory.GoodTop.goodPatch_image | (intros; apply GlobalTheory.GoodTop.goodPatch_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTermDensityGoodPatch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTermDensityGoodPatch
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hsupp
  classical
  have := X.smooth_str
  obtain ⟨hUo, hUeq, hK⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  set g : V X.dim → ℝ := corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
    with hg
  have hKc : IsCompact (e '' tsupport ρ) := hK _ (isClosed_tsupport ρ) hsupp
  have hint : IntegrableOn (corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()))
      (offHyp S (e '' W)) := by
    refine GlobalTheory.T.integrableOn_chernTransgressionTerm_poincareGrowth S (e '' W) (e '' tsupport ρ) _ _ _ c hUo hKc (Set.image_mono hsupp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha
    · rintro _ ⟨z, hz, rfl⟩
      have htop : z ∈ ptsIn X.str σ (⊤ : X.X.Opens) := by
        simp [ptsIn]
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo htop (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)
    · intro v hv a i j
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO a i j
    · intro v hv a b i j
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO a b i j
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hP.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' (ptsIn X.str σ O ∩ W)) := by
    rw [hUeq]
    exact (hint.re).const_mul _
  have hval : (∫ v in e '' (ptsIn X.str σ O ∩ W), g v) = (Real.pi ^ X.dim)⁻¹ *
      (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re := by
    rw [hUeq, hg]
    simp only [corrTop]
    rw [integral_const_mul]
    congr 1
    exact integral_re hint
  rw [← hval]
  refine GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e) (fun i j => i.holo_trans j)
    (fun y => AlgChart.exists_mem_source y) (isOpen_ptsIn O).measurableSet e W g hP.isOpen hP.sub
    (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hP.holo j) (GlobalTheory.T.transgression_correction_isTopDegreeForm E O H H₀ hH hH₀ hρ) ?_ ?_ hgi
  · intro i y _ hyW hyi
    have hy : y ∉ tsupport ρ := fun h => hyW (hsupp h)
    have h0 : ρ =ᶠ[𝓝 y] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    have h1 : (fun v => ρ (i.e.symm v)) =ᶠ[𝓝 (i.e y)] fun _ => 0 := by
      have ht := (i.e.continuousAt_symm (i.e.map_source hyi)).tendsto
      rw [i.e.left_inv hyi] at ht
      exact ht.eventually h0
    simp only [corrDens, corrTop]
    rw [GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero _ _ h1]
    simp
  · intro j y hyS hyW hyj
    exact GlobalTheory.T.transgressionDensity_holomorphicChart_etale E O H H₀ hH hH₀ hρ hP.holo j hyS (hP.sub hyW) hyj (hP.frame y hyW)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTermDensityGoodPatchStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgression_term_density_good_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re) := by
  first | exact @GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch | exact GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch | (intros; apply GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothMetricCutTopChernDensityPatch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothMetricCutTopChernDensityPatch
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem hasInt_cut_topDens_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) ((Real.pi ^ X.dim)⁻¹ * (∫ v in e '' W, (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hp ρ hρ hsupp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hcont : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have htop : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v with hf
  set g : V X.dim → ℝ := fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re with hg
  obtain ⟨hUo, -, hK⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hp

  have hfi : IntegrableOn f (e '' W) := by
    refine GlobalTheory.T.integrableOn_cutoff_topChernForm_smoothGram (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => ρ (e.symm v)) hUo
      (hK _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp) ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hp.holo mem_ptsIn_top (hp.sub hz) (hp.frame z hz)
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hp.holo (hp.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hp.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' W) := hfi.re.const_mul _
  have key := GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e)
    (fun i j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart i.holo j) (fun y => AlgChart.exists_mem_source y)
    (S := ptsIn X.str σ ⊤) (isOpen_ptsIn _).measurableSet (d := fun c y => ρ y * topDens E H₀ c y) e W g
    hp.isOpen hp.sub (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hp.holo j) (GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E ⊤ H₀ hH₀ hcont) ?_ ?_
    (by rw [htop, Set.univ_inter]; exact hgi)
  · rw [htop, Set.univ_inter] at key
    convert key using 1
    rw [hg, integral_const_mul]
    congr 1
    exact (integral_re hfi).symm
  · intro i y _ hyW _
    have : ρ y = 0 := by
      by_contra h0
      exact hyW (hsupp (subset_tsupport ρ h0))
    simp [this]
  · intro j y _ hyW hyj
    have ht := GlobalTheory.T.top_chern_density_holomorphic_chart_etale E ⊤ H₀ hH₀ hp.holo j mem_ptsIn_top (hp.sub hyW) hyj (hp.frame y hyW)
    simp only [hg, hf, e.left_inv (hp.sub hyW), Complex.re_ofReal_mul]
    rw [← mul_assoc, mul_comm _ (ρ y), mul_assoc, ht]
    ring

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothMetricCutTopChernDensityPatchStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothMetric_cut_topChern_density_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) ((Real.pi ^ X.dim)⁻¹ * (∫ v in e '' W, (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v).re) := by
  first | exact @GlobalTheory.GoodTop.hasInt_cut_topDens_patch | exact GlobalTheory.GoodTop.hasInt_cut_topDens_patch | (intros; apply GlobalTheory.GoodTop.hasInt_cut_topDens_patch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricCutTopChernDensityPatch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricCutTopChernDensityPatch
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false
noncomputable section

theorem GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hρW
  obtain ⟨hU, himg, hcpt⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  have hS : MeasurableSet (ptsIn X.str σ O) := (isOpen_ptsIn O).measurableSet
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hρc : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have hρ0 : ∀ y, y ∉ W → ρ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hρW h))
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v with hf
  have hint : IntegrableOn f (offHyp S (e '' W)) := by
    refine GlobalTheory.T.integrableOn_cutoff_topChernForm_poincareGrowth S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
      (fun v => ρ (e.symm v)) c hU (hcpt _ (isClosed_tsupport ρ) hρW) (Set.image_mono hρW) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha
    · rintro _ ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO
    · intro v hv
      rw [← himg] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO
    · rintro _ ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK
      have hzK : z ∉ tsupport ρ := fun h => hK ⟨z, h, rfl⟩
      show ρ (e.symm (e z)) = 0
      rw [e.left_inv (hP.sub hz)]
      exact image_eq_zero_of_notMem_tsupport hzK
  have hre : IntegrableOn (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) (offHyp S (e '' W)) :=
    (Integrable.re hint).const_mul _
  have key := GlobalTheory.T.topFormIntegral_of_support_in_holomorphicChart (fun c : AlgChart X.str σ X.dim => c.e) hd hcov hS
    (d := fun c y => ρ y * topDens E H c y) e W (fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re) hP.isOpen hP.sub
    (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hP.holo j) (GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E O H hH hρc) ?_ ?_ (by rw [himg]; exact hre)
  · rw [himg, integral_const_mul] at key
    have h2 : ∫ v in offHyp S (e '' W), (f v).re = (∫ v in offHyp S (e '' W), f v).re := integral_re hint
    rw [h2] at key
    exact key
  · intro i y _ hy _
    simp [hρ0 y hy]
  · intro j y hyO hy hj
    have h1 := GlobalTheory.T.top_chern_density_holomorphic_chart_etale E O H hH hP.holo j hyO (hP.sub hy) hj (hP.frame y hy)
    simp only [hf, e.left_inv (hP.sub hy), Complex.re_ofReal_mul]
    rw [mul_left_comm, h1]
    ring
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricCutTopChernDensityPatchStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMetric_cut_topChern_density_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) v).re) := by
  first | exact @GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch | exact GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch | (intros; apply GlobalTheory.GoodTop.hasInt_mul_topDens_goodPatch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMixTopSlotEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDerivCutoffConnectionDifferenceEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDerivCutoffConnectionDifferenceEq
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem mdbar_neg_cut_conn_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ}
    {G₀ G₁ : V n → Matrix r r ℂ} {v : V n} (hρ : DifferentiableAt ℝ ρ v) (h₀ : MContDiffAt 2 G₀ v)
    (u₀ : IsUnit (G₀ v).det) (h₁ : MContDiffAt 2 G₁ v) (u₁ : IsUnit (G₁ v).det) :
    (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b))
      = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  funext a b
  have c₀ : MContDiffAt 1 (fun x => conn G₀ x (coordVec a)) v := h₀.conn u₀ (by norm_num) _
  have c₁ : MContDiffAt 1 (fun x => conn G₁ x (coordVec a)) v := h₁.conn u₁ (by norm_num) _
  have hρ' : DifferentiableAt ℝ (fun x => (ρ x : ℂ)) v := Complex.ofRealCLM.differentiableAt.comp v hρ
  have hs : mdbar (fun x => conn G₁ x (coordVec a) - conn G₀ x (coordVec a)) v (coordVec b) =
      mdbar (fun x => conn G₁ x (coordVec a)) v (coordVec b) -
        mdbar (fun x => conn G₀ x (coordVec a)) v (coordVec b) := by
    simp only [sub_eq_add_neg]
    rw [mdbar_add c₁ c₀.neg, mdbar_neg]
  rw [mdbar_neg (fun x => (ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a))),
    mdbar_smul hρ' (c₁.sub c₀), hs]
  simp only [Pi.sub_apply, Pi.smul_apply, curvAt, cutForm, curv, smul_sub, smul_neg]
  abel

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDerivCutoffConnectionDifferenceEqStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, DifferentiableAt ℝ ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b)) = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | exact GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | (intros; apply GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub <;> assumption)
end
end

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

set_option autoImplicit false

noncomputable def transConn {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ)
    (G₀ G₁ : V n → Matrix r r ℂ) (j : Fin n) (i a : Fin n) : V n → Matrix r r ℂ :=
  if i < j then fun x => -conn G₁ x (coordVec a)
  else if i = j then fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))
  else fun x => -conn G₀ x (coordVec a)

theorem weighted_bound_cut_sum (x A B w C c : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ C) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hA : A * w ≤ c) (hB : B ≤ C) : x * (A + B) * w ≤ C * (|c| + C) := by
  have h1 : (A + B) * w ≤ |c| + C := by nlinarith [le_abs_self c]
  have hC : 0 ≤ C := hx0.trans hx
  rw [mul_assoc]
  exact mul_le_mul hx h1 (by positivity) hC

theorem weighted_bound_cut_entry (x X₁ X₀ d Y₁ Y₀ : ℂ) (wa wb C c : ℝ) (hx : ‖x‖ ≤ C) (hd : ‖d‖ ≤ C)
    (hX₁ : ‖X₁‖ * (wa * wb) ≤ c) (hX₀ : ‖X₀‖ ≤ C) (hY₁ : ‖Y₁‖ * wa ≤ c) (hY₀ : ‖Y₀‖ ≤ C)
    (hwa0 : 0 ≤ wa) (hwa1 : wa ≤ 1) (hwb0 : 0 ≤ wb) (hwb1 : wb ≤ 1) :
    ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb) ≤ 2 * C * (|c| + C) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans hx
  have e1 := weighted_bound_cut_sum ‖x‖ ‖X₁‖ ‖X₀‖ (wa * wb) C c (norm_nonneg _) hx (norm_nonneg _) (norm_nonneg _)
    (by positivity) (by nlinarith) hX₁ hX₀
  have e2 := weighted_bound_cut_sum ‖d‖ ‖Y₁‖ ‖Y₀‖ wa C c (norm_nonneg _) hd (norm_nonneg _) (norm_nonneg _)
    hwa0 hwa1 hY₁ hY₀
  have n1 : ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ ≤ ‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
  have hww : 0 ≤ wa * wb := by positivity
  have e2' : ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) ≤ C * (|c| + C) := by
    have h0 : 0 ≤ ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa := by positivity
    calc ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) = (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * wb := by ring
      _ ≤ (‖d‖ * (‖Y₁‖ + ‖Y₀‖) * wa) * 1 := mul_le_mul_of_nonneg_left hwb1 h0
      _ ≤ C * (|c| + C) := by rw [mul_one]; exact e2
  calc ‖x * (X₁ - X₀) - d * (Y₁ - Y₀)‖ * (wa * wb)
      ≤ (‖x‖ * (‖X₁‖ + ‖X₀‖) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖)) * (wa * wb) := mul_le_mul_of_nonneg_right n1 hww
    _ = ‖x‖ * (‖X₁‖ + ‖X₀‖) * (wa * wb) + ‖d‖ * (‖Y₁‖ + ‖Y₀‖) * (wa * wb) := by ring
    _ ≤ C * (|c| + C) + C * (|c| + C) := add_le_add e1 e2'
    _ = 2 * C * (|c| + C) := by ring

theorem integral_mixTop_position_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → ∀ j : Fin n, IntegrableOn (fun v => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)) (offHyp S U) ∧ ∫ v in offHyp S U, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j) = 0 := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK j
  obtain ⟨C, hC0, hC⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have h3 : (2 : WithTop ℕ∞) + 1 ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hw : ∀ v ∈ U, ∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1 :=
    fun v hv a => (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv)).1 a
  have hρd : ∀ v ∈ U, ContDiffAt ℝ ∞ ρ v := fun v hv => hρ.contDiffAt (hU.mem_nhds hv)
  have hρc : ∀ v ∈ U, ContDiffAt ℝ 2 (fun x => (ρ x : ℂ)) v := fun v hv =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hρd v hv).of_le h2)
  set θ := transConn ρ G₀ G₁ j with hθ
  have hsm : ∀ i a, ∀ v ∈ offHyp S U, MContDiffAt 2 (θ i a) v := by
    intro i a v hv
    have h1 := (hG₁ v hv).1.conn (j := 2) (hG₁ v hv).2 h3 (coordVec a)
    have h0 := (hG₀ v hv.1).1.conn (j := 2) (hG₀ v hv.1).2 h3 (coordVec a)
    simp only [hθ, transConn]
    split_ifs
    · exact h1.neg
    · exact (MContDiffAt.smul (hρc v hv.1) (h1.sub h0)).neg
    · exact h0.neg
  have heq : ∀ v ∈ offHyp S U, (fun i a b => mdbar (θ i a) v (coordVec b)) =
      intersection_update_fsHerm_neg_one (curvAt G₁ v) ((ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v) (curvAt G₀ v) j := by
    intro v hv
    funext i a b
    simp only [hθ, transConn, intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · rw [mdbar_neg]; rfl
    · exact congrFun (congrFun (GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq ((hρd v hv.1).differentiableAt (by simp))
        ((hG₀ v hv.1).1.of_le h2) (hG₀ v hv.1).2 ((hG₁ v hv).1.of_le h2) (hG₁ v hv).2) a) b
    · rw [mdbar_neg]; rfl
  have hzero : ∀ a, ∀ v ∈ offHyp S U, v ∉ K → θ j a v = 0 := by
    intro a v hv hvK
    simp [hθ, transConn, hρK v hv.1 hvK]
  have hcC : 0 ≤ C * (|c| + C) := by positivity
  have hbd1 : ∀ v ∈ offHyp S U, v ∈ K → ∀ a p q,
      ‖θ j a v p q‖ * poinWt S v a ≤ |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK a p q
    obtain ⟨hρv, -, hc0, -⟩ := hC v hvK
    simp only [hθ, transConn, lt_irrefl, if_false, if_true, Matrix.neg_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have e := weighted_bound_cut_sum |ρ v| ‖conn G₁ v (coordVec a) p q‖ ‖conn G₀ v (coordVec a) p q‖ (poinWt S v a) C c
      (abs_nonneg _) hρv (norm_nonneg _) (norm_nonneg _) (hw v hv.1 a).1 (hw v hv.1 a).2
      (hconn v hv a p q) (hc0 a p q)
    have n1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)) (abs_nonneg (ρ v)))
      (hw v hv.1 a).1
    have : 0 ≤ |c| := abs_nonneg c
    nlinarith
  have hbd2 : ∀ v ∈ offHyp S U, v ∈ K → ∀ i a b p q,
      ‖mdbar (θ i a) v (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤
        |c| + C + 2 * C * (|c| + C) := by
    intro v hv hvK i a b p q
    obtain ⟨hρv, hdv, hc0, hk0⟩ := hC v hvK
    obtain ⟨hwa0, hwa1⟩ := hw v hv.1 a
    obtain ⟨hwb0, hwb1⟩ := hw v hv.1 b
    have hww : 0 ≤ poinWt S v a * poinWt S v b := by positivity
    have hww1 : poinWt S v a * poinWt S v b ≤ 1 := by nlinarith
    have hca : 0 ≤ |c| := abs_nonneg c
    rw [show mdbar (θ i a) v (coordVec b) = _ from congrFun (congrFun (congrFun (heq v hv) i) a) b]
    simp only [intersection_update_fsHerm_neg_one]
    split_ifs with h h'
    · have := hcurv v hv a b p q
      simp only [curvAt]
      nlinarith [le_abs_self c]
    · simp only [curvAt, cutForm, Pi.sub_apply, Pi.smul_apply, Matrix.sub_apply, Matrix.smul_apply,
        smul_eq_mul]
      have e := weighted_bound_cut_entry (ρ v : ℂ) (curv G₁ v (coordVec a) (coordVec b) p q) (curv G₀ v (coordVec a) (coordVec b) p q)
        (dbar (fun x => (ρ x : ℂ)) v (coordVec b)) (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
        (poinWt S v a) (poinWt S v b) C c (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hρv) (hdv b)
        (hcurv v hv a b p q) (hk0 a b p q) (hconn v hv a p q) (hc0 a p q) hwa0 hwa1 hwb0 hwb1
      nlinarith
    · simp only [curvAt]
      have := hk0 a b p q
      have := mul_le_mul_of_nonneg_left hww1 (norm_nonneg (curv G₀ v (coordVec a) (coordVec b) p q))
      nlinarith
  obtain ⟨hi, hint⟩ := GlobalTheory.T.integral_polarisedTopForm_dbarExact_eq_zero S U K θ j (|c| + C + 2 * C * (|c| + C)) hU hK hKU hsmall hsm hzero
    hbd1 hbd2
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  refine ⟨hi.congr_fun (fun v hv => congrArg mixTop (heq v hv)) hO, ?_⟩
  rw [← hint]
  exact setIntegral_congr_fun hO fun v hv => congrArg mixTop (heq v hv).symm

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPolarisedTopChernCoeffTransgressionTelescope
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_mixTop_position_sub {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K₁ K₀ : EndValuedForm11Coeffs n r) :
    ∑ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = mixTop (fun _ => K₁) - mixTop fun _ => K₀ := by
  classical
  set T : ℕ → ℂ := fun k => mixTop (fun i : Fin n => if (i : ℕ) < k then K₁ else K₀) with hT
  have hterm : ∀ j : Fin n, mixTop (intersection_update_fsHerm_neg_one K₁ (K₁ - K₀) K₀ j) = T ((j : ℕ) + 1) - T j := by
    intro j
    have hK : K₁ - K₀ = (1 : ℂ) • K₁ + (-1 : ℂ) • K₀ := by
      rw [one_smul, neg_one_smul, sub_eq_add_neg]
    rw [hK, GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ K₁ K₀ 1 (-1) j, one_mul, neg_one_mul, ← sub_eq_add_neg]
    congr 1
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j + 1 := by have := Fin.lt_def.mp h1; omega
        simp [h1, this]
      · by_cases h2 : i = j
        · subst h2; simp
        · have h3 : ¬ ((i : ℕ) < j + 1) := by
            have : j < i := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
            have := Fin.lt_def.mp this; omega
          simp [h1, h2, h3]
    · simp only [hT]
      congr 1
      funext i
      unfold intersection_update_fsHerm_neg_one
      by_cases h1 : i < j
      · have : (i : ℕ) < j := Fin.lt_def.mp h1
        simp [h1, this]
      · have : ¬ ((i : ℕ) < j) := fun h => h1 (Fin.lt_def.mpr h)
        by_cases h2 : i = j
        · simp [h1, h2, this]
        · simp [h1, h2, this]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Fin.sum_univ_eq_sum_range (fun k => T (k + 1) - T k) n, Finset.sum_range_sub]
  have e1 : (fun i : Fin n => if (i : ℕ) < n then K₁ else K₀) = fun _ => K₁ := by
    funext i; simp [i.isLt]
  have e0 : (fun i : Fin n => if (i : ℕ) < 0 then K₁ else K₀) = fun _ => K₀ := by
    funext i; simp
  show mixTop _ - mixTop _ = _
  rw [e1, e0]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormula
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mixTop_slot_smul_sub_sub {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (A B D : _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r) (s : ℂ) (j : Fin n) :
    _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (s • (A - B) - D) B j) =
      s * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (A - B) B j) +
        (-1) * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A D B j) := by
  rw [← _root_.GlobalTheory.GoodTop.mixTop_position_linear, neg_one_smul, ← sub_eq_add_neg]


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodTop.integral_cutTop_sub : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ * _root_.GlobalTheory.GoodMetric.poinWt S v a ≤ c) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ * (_root_.GlobalTheory.GoodMetric.poinWt S v a * _root_.GlobalTheory.GoodMetric.poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) = ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hS hG₀ hG₁ hconn hcurv hρ hρK
  have hstokes := _root_.GlobalTheory.GoodTop.integral_mixTop_position_eq_zero S U K G₀ G₁ ρ c hU hK hKU
    hS hG₀ hG₁ hconn hcurv hρ hρK
  have hF₁ := _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hF₀ := (_root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth U K G₀ ρ hU hK hKU hG₀ hρ
    hρK).mono_set (fun v hv => ((mem_offHyp_iff (S := S)).1 hv).1)
  have hT := _root_.GlobalTheory.GoodTop.integrableOn_corrC S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hpt : ∀ v, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v =
      ∑ j, _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ v)
        ((ρ v : ℂ) • (_root_.GlobalTheory.GoodTop.curvAt G₁ v - _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
          _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ v) (_root_.GlobalTheory.GoodTop.curvAt G₀ v) j) := by
    intro v
    simp_rw [mixTop_slot_smul_sub_sub]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      _root_.GlobalTheory.GoodTop.sum_mixTop_position_sub]
    unfold _root_.GlobalTheory.GoodTop.corrC
    ring
  have hzero : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun j _ => (hstokes j).1]
    exact Finset.sum_eq_zero fun j _ => (hstokes j).2
  have hsplit : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) =
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
    have hsub : IntegrableOn (fun v =>
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v))
        (_root_.GlobalTheory.GoodTop.offHyp S U) := hF₁.sub hF₀
    exact (integral_sub hsub hT).trans (congrArg (· - _) (integral_sub hF₁ hF₀))
  rw [← setIntegral_congr_set (_root_.GlobalTheory.GoodTop.offHyp_ae_eq S U)]
  linear_combination hzero - hsplit

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricLocalTransgressionFormulaStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMetric_local_transgression_formula : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in offHyp S U, (ρ v : ℂ) * mixTop fun _ => curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * mixTop fun _ => curvAt G₀ v) = ∫ v in offHyp S U, corrC ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.integral_cutTop_sub | exact GlobalTheory.GoodTop.integral_cutTop_sub | (intros; apply GlobalTheory.GoodTop.integral_cutTop_sub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatch
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem hasInt_patch_transgression : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → ∃ a b : ℝ, HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) a ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) b ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) (a - b) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hsupp
  obtain ⟨hUo, hUoff, hcpt⟩ := GlobalTheory.T.goodPatch_chart_image_properties E O H hP
  have h1 := GlobalTheory.T.goodMetric_cut_topChern_density_patch E O H H₀ hH hH₀ hP hρ hsupp
  have h0 := GlobalTheory.T.smoothMetric_cut_topChern_density_patch E O H H₀ hH hH₀ hP hρ hsupp
  have hc := GlobalTheory.T.transgression_term_density_good_patch E O H H₀ hH hH₀ hP hρ hsupp
  refine ⟨_, _, h1, h0, ?_⟩
  have hloc := GlobalTheory.T.goodMetric_local_transgression_formula S (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
    (fun v => ρ (e.symm v)) c hUo (hcpt _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp)
    (by
      rintro v ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha)
    (by
      rintro v ⟨z, hz, rfl⟩
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E ⊤ H₀ hH₀ hP.holo mem_ptsIn_top (hP.sub hz) (hP.frame z hz))
    (by
      intro v hv
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz))
    (by
      intro v hv a i j
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO a i j)
    (by
      intro v hv a b i j
      rw [← hUoff] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO a b i j)
    (by
      rintro v ⟨z, hz, rfl⟩
      exact (GlobalTheory.T.contDiffAt_holomorphicComplexChart_of_smoothAt hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt)
    (by
      rintro v ⟨z, hz, rfl⟩ hv
      rw [e.left_inv (hP.sub hz)]
      by_contra h
      exact hv ⟨z, subset_tsupport _ h, rfl⟩)
  convert hc using 1
  rw [← mul_sub, ← Complex.sub_re, hloc]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatchStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgression_topChernForm_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → ∃ a b : ℝ, HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) a ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) b ∧ HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) (a - b) := by
  first | exact @GlobalTheory.GoodTop.hasInt_patch_transgression | exact GlobalTheory.GoodTop.hasInt_patch_transgression | (intros; apply GlobalTheory.GoodTop.hasInt_patch_transgression <;> assumption)
end
