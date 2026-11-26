module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernNumbersEqIntegralChernFormsSmoothMetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatch

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityE
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrC_sum_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι]
    (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) →
    (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  intro n r _ _ ι _ ρ G₀ G₁ v hd h1
  have hsum : ∀ w, ∑ i, dbar (fun x => (ρ i x : ℂ)) v w = 0 := by
    intro w
    have e : (fun x => ∑ i, (ρ i x : ℂ)) = fun _ => (1 : ℂ) := by
      funext x; rw [← Complex.ofReal_sum, h1]; simp
    have hs := dbar_sum (t := Finset.univ) (A := fun i x => (ρ i x : ℂ)) (z := v)
      (fun i _ => Complex.ofRealCLM.differentiableAt.comp v (hd i))
    rw [e, dbar_const] at hs
    rw [← ContinuousLinearMap.sum_apply, ← hs]; rfl
  have hadd : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r),
      mixTop (intersection_update_fsHerm_neg_one K₁ (L + L') K₀ j) = mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
    intro K₁ K₀ j L L'; simpa using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ L L' 1 1 j
  have hzero : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n), mixTop (intersection_update_fsHerm_neg_one K₁ (0 : EndValuedForm11Coeffs n r) K₀ j) = 0 := by
    intro K₁ K₀ j; simpa using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ 0 0 0 0 j
  have hc : ∑ i, cutForm (ρ i) G₀ G₁ v = 0 := by
    funext a b
    simp only [Finset.sum_apply, cutForm, ← Finset.sum_smul, hsum, zero_smul]
    rfl
  unfold corrC
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  let F : EndValuedForm11Coeffs n r →+ ℂ :=
    { toFun := fun L => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) L (curvAt G₀ v) j)
      map_zero' := hzero _ _ _
      map_add' := fun L L' => hadd _ _ _ L L' }
  have hF : ∑ i, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm (ρ i) G₀ G₁ v) (curvAt G₀ v) j) =
      F (∑ i, cutForm (ρ i) G₀ G₁ v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; rfl
  rw [hF, hc, map_zero]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityEStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι] (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) → (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  first | exact @GlobalTheory.GoodTop.corrC_sum_eq_zero | exact GlobalTheory.GoodTop.corrC_sum_eq_zero | (intros; apply GlobalTheory.GoodTop.corrC_sum_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZero
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem sum_corrDens_eq_zero : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), ∀ {ι : Type} [Fintype ι] (ρ : ι → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) → (∀ y, ∑ i, ρ i y = 1) → ∀ (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ), y ∈ c.e.source → ∑ i, corrDens E H₀ H (ρ i) c y = 0 := by
  intro F _ σ X m E O H H₀ ι _ ρ hρ h1 c y hy
  have hc : IsHoloChart c.e := c.holo
  have key := GlobalTheory.T.sum_transgressionTopCoeffComplex_partitionOfUnity_eq_zero (fun i v => ρ i (c.e.symm v))
    (fun v => H₀ (E.nonempty (under y)).choose (c.e.symm v) ())
    (fun v => H (E.nonempty (under y)).choose (c.e.symm v) ()) (c.e y)
    (fun i => (contDiffAt_holoChart hc hy (hρ i y)).differentiableAt (by simp))
    (fun x => h1 _)
  simp only [corrDens, corrTop]
  rw [← Finset.mul_sum, ← Complex.re_sum, key]
  simp

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZeroStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_transgression_densities_partition_unity_eq_zero : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), ∀ {ι : Type} [Fintype ι] (ρ : ι → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) → (∀ y, ∑ i, ρ i y = 1) → ∀ (c : AlgChart X.str σ X.dim) (y : CxPts X.str σ), y ∈ c.e.source → ∑ i, corrDens E H₀ H (ρ i) c y = 0 := by
  first | exact @GlobalTheory.GoodTop.sum_corrDens_eq_zero | exact GlobalTheory.GoodTop.sum_corrDens_eq_zero | (intros; apply GlobalTheory.GoodTop.sum_corrDens_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralAdd
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

private theorem glue_mono {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y} (hS : MeasurableSet S) {ρ ρ' : κ → Y → ℝ≥0∞}
    (h : ∀ i y, ρ i y ≤ ρ' i y) : glueMeas e ρ S ≤ glueMeas e ρ' S := by
  have key : glueMeas e ρ ≤ glueMeas e ρ' := by
    refine iSup_mono fun i => Measure.le_iff.2 fun B hB => ?_
    rw [chartMeas_apply _ _ hB, chartMeas_apply _ _ hB]
    exact lintegral_mono fun v => h i _
  exact Measure.le_iff.1 key S hS

private theorem ofReal_balance (a b : ℝ) :
    ENNReal.ofReal (1 * (a + b)) + (ENNReal.ofReal (-1 * a) + ENNReal.ofReal (-1 * b)) =
      ENNReal.ofReal (-1 * (a + b)) + (ENNReal.ofReal (1 * a) + ENNReal.ofReal (1 * b)) := by
  have hm : ∀ v : ℝ, ENNReal.ofReal v = ENNReal.ofReal (max v 0) := fun v => by
    rcases le_total v 0 with h | h
    · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
    · rw [max_eq_left h]
  have conv : ∀ x y z : ℝ, ENNReal.ofReal x + (ENNReal.ofReal y + ENNReal.ofReal z) =
      ENNReal.ofReal (max x 0 + (max y 0 + max z 0)) := fun x y z => by
    rw [ENNReal.ofReal_add (le_max_right _ _) (add_nonneg (le_max_right _ _) (le_max_right _ _)),
      ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _), ← hm, ← hm, ← hm]
  have hs : ∀ v : ℝ, max (1 * v) 0 - max (-1 * v) 0 = v := fun v => by
    rcases le_total v 0 with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  rw [conv, conv]
  congr 1
  linarith [hs a, hs b, hs (a + b)]

theorem hasInt_add : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {s t : ℝ}, IsTopForm e d S → IsTopForm e d' S → HasInt e d S s → HasInt e d' S t → HasInt e (fun i y => d i y + d' i y) S (s + t) := by
  intro n Y κ _ _ _ _ e hd hcov S hS d d' s t hf hf' hi hi'
  have hsum : IsTopForm e (fun i y => d i y + d' i y) S :=
    ⟨fun i j y hy h1 h2 => by rw [hf.trans i j y hy h1 h2, hf'.trans i j y hy h1 h2, mul_add],
      fun i => (hf.meas i).add (hf'.meas i)⟩
  have comp : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i j y, y ∈ S → y ∈ (e i).source →
      y ∈ (e j).source → ENNReal.ofReal (c * f i y) =
        ENNReal.ofReal (‖transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (c * f j y) := by
    intro f h c i j y hy h1 h2
    rw [h.trans i j y hy h1 h2, mul_left_comm, ENNReal.ofReal_mul (by positivity)]
  have meas : ∀ {f : κ → Y → ℝ}, IsTopForm e f S → ∀ (c : ℝ) i,
      AEMeasurable (fun v => ENNReal.ofReal (c * f i ((e i).symm v)))
        (volume.restrict ((e i).target ∩ (e i).symm ⁻¹' S)) := fun h c i =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((h.meas i).const_mul c)
  have h2 : ∀ c : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * d i y) + ENNReal.ofReal (c * d' i y)) S =
      glueMeas e (fun i y => ENNReal.ofReal (c * d i y)) S +
        glueMeas e (fun i y => ENNReal.ofReal (c * d' i y)) S := fun c =>
    glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hf c) (comp hf' c) (meas hf c)
  have h3 : ∀ c c' : ℝ, glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y)) +
      (ENNReal.ofReal (c' * d i y) + ENNReal.ofReal (c' * d' i y))) S =
      glueMeas e (fun i y => ENNReal.ofReal (c * (d i y + d' i y))) S +
        (glueMeas e (fun i y => ENNReal.ofReal (c' * d i y)) S +
          glueMeas e (fun i y => ENNReal.ofReal (c' * d' i y)) S) := fun c c' => by
    rw [← h2]
    refine glueMeas_add_of_compat_on e hd hcov hS _ _ (comp hsum c) ?_ (meas hsum c)
    intro i j y hy h1 h2
    rw [comp hf c' i j y hy h1 h2, comp hf' c' i j y hy h1 h2, mul_add]
  have hfin : ∀ ε : ℤˣ,
      glueMeas e (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * (d i y + d' i y))) S ≠ ⊤ := by
    intro ε
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hi.1 ε, hi'.1 ε⟩) ?_
    rw [← h2]
    refine glue_mono e hS fun i y => ?_
    rw [mul_add]
    exact ENNReal.ofReal_add_le
  refine ⟨hfin, ?_⟩
  have hbal := h3 1 (-1)
  simp only [ofReal_balance] at hbal
  rw [h3] at hbal
  have a1 := hfin 1
  have a2 := hfin (-1)
  have b1 := hi.1 1
  have b2 := hi.1 (-1)
  have c1 := hi'.1 1
  have c2 := hi'.1 (-1)
  have e1 := hi.2
  have e2 := hi'.2
  simp only [measureReal_def, Units.val_one, Int.cast_one, Units.val_neg, Int.cast_neg] at a1 a2 b1 b2 c1 c2 e1 e2 ⊢
  have hr := congrArg ENNReal.toReal hbal
  rw [ENNReal.toReal_add a2 (ENNReal.add_ne_top.2 ⟨b1, c1⟩), ENNReal.toReal_add b1 c1,
    ENNReal.toReal_add a1 (ENNReal.add_ne_top.2 ⟨b2, c2⟩), ENNReal.toReal_add b2 c2] at hr
  linarith

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralAddStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormIntegral_add : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {s t : ℝ}, IsTopForm e d S → IsTopForm e d' S → HasInt e d S s → HasInt e d' S t → HasInt e (fun i y => d i y + d' i y) S (s + t) := by
  first | exact @GlobalTheory.GoodTop.hasInt_add | exact GlobalTheory.GoodTop.hasInt_add | (intros; apply GlobalTheory.GoodTop.hasInt_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopForms
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodTop

private theorem isTopForm_hasInt_finset_sum {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n))
    (he : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (hc : ∀ y, ∃ i, y ∈ (e i).source) {S : Set Y} (hS : MeasurableSet S) {ι : Type}
    {d : ι → κ → Y → ℝ} {t : ι → ℝ} (hd : ∀ a, IsTopForm e (d a) S) (ht : ∀ a, HasInt e (d a) S (t a))
    (s : Finset ι) :
    IsTopForm e (fun i y => ∑ a ∈ s, d a i y) S ∧ HasInt e (fun i y => ∑ a ∈ s, d a i y) S (∑ a ∈ s, t a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨⟨fun _ _ _ _ _ _ => by simp, fun _ => aemeasurable_const⟩, GlobalTheory.T.hasTopFormChartIntegral_zero e S⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    obtain ⟨hF, hI⟩ := ih
    refine ⟨⟨fun i j y hy hi hj => ?_, fun i => ((hd a).meas i).add (hF.meas i)⟩,
      GlobalTheory.T.topFormIntegral_add e he hc hS (hd a) hF (ht a) hI⟩
    rw [(hd a).trans i j y hy hi hj, hF.trans i j y hy hi hj]
    ring

theorem hasInt_sum : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)),
    (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) →
    (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι]
    {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) →
    HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  intro n Y κ _ _ _ _ e he hc S hS ι _ d t hd ht
  exact (isTopForm_hasInt_finset_sum e he hc hS hd ht Finset.univ).2

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopFormsStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_finite_sum_topForms : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] (e : κ → OpenPartialHomeomorph Y (V n)), (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → (∀ y, ∃ i, y ∈ (e i).source) → ∀ {S : Set Y}, MeasurableSet S → ∀ {ι : Type} [Fintype ι] {d : ι → κ → Y → ℝ} {t : ι → ℝ}, (∀ a, IsTopForm e (d a) S) → (∀ a, HasInt e (d a) S (t a)) → HasInt e (fun i y => ∑ a, d a i y) S (∑ a, t a) := by
  first | exact @GlobalTheory.GoodTop.hasInt_sum | exact GlobalTheory.GoodTop.hasInt_sum | (intros; apply GlobalTheory.GoodTop.hasInt_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPart
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem exists_goodPatch_of_mem : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ y ∈ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hH y hy
  classical
  obtain ⟨ch, hc⟩ := AlgChart.exists_mem_source (D := X.dim) (p := X.str) (σ := σ) y
  obtain ⟨A, hA⟩ := E.nonempty (under y)
  have hhol : IsHoloChart ch.e := ch.holo
  obtain ⟨hsm, hu⟩ := GlobalTheory.T.gramMatrix_smooth_isUnit_in_holomorphicChart E O H hH hhol hy hc hA
  set G : V X.dim → Matrix (Fin m) (Fin m) ℂ := fun v => H A (ch.e.symm v) () with hG
  have h1 : ((0 : WithTop ℕ∞) + 1) ≤ ∞ := by exact_mod_cast le_top
  have h2 : ((0 : WithTop ℕ∞) + 2) ≤ ∞ := by
    rw [zero_add]
    first
    | exact (WithTop.coe_le_coe (a := (2 : ℕ∞)) (b := ⊤)).2 le_top
    | exact ENat.LEInfty.out
    | simp
    | decide
  have hconn : ∀ (a : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => conn G (ch.e z) (coordVec a) i j) y := fun a i j =>
    ((hsm.conn hu h1 (coordVec a)) i j).continuousAt.comp (ch.e.continuousAt hc)
  have hcurv : ∀ (a b : Fin X.dim) (i j : Fin m),
      ContinuousAt (fun z => curv G (ch.e z) (coordVec a) (coordVec b) i j) y := fun a b i j =>
    ((hsm.curv hu h2 (coordVec a) (coordVec b)) i j).continuousAt.comp (ch.e.continuousAt hc)
  let C : ℝ := (∑ a : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1)) +
    ∑ a : Fin X.dim, ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m,
      (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
  have hP1 : ∀ a i j, ‖conn G (ch.e y) (coordVec a) i j‖ + 1 ≤ C := by
    intro a i j
    refine le_add_of_le_of_nonneg ?_ (by positivity)
    refine (Finset.single_le_sum (f := fun j => ‖conn G (ch.e y) (coordVec a) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ i : Fin m, ∑ j : Fin m, (‖conn G (ch.e y) (coordVec a) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  have hP2 : ∀ a b i j, ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1 ≤ C := by
    intro a b i j
    refine le_add_of_nonneg_of_le (by positivity) ?_
    refine (Finset.single_le_sum (f := fun j => ‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans ?_
    refine (Finset.single_le_sum (f := fun i => ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ i)).trans ?_
    refine (Finset.single_le_sum (f := fun b => ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ b)).trans ?_
    exact Finset.single_le_sum (f := fun a => ∑ b : Fin X.dim, ∑ i : Fin m, ∑ j : Fin m, (‖curv G (ch.e y) (coordVec a) (coordVec b) i j‖ + 1))
      (fun _ _ => by positivity) (Finset.mem_univ a)
  let T : Set (CxPts X.str σ) := {z | z ∈ ch.e.source ∧ z ∈ ptsIn X.str σ O ∧ A ∈ E.S (under z) ∧
    (∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C) ∧
    (∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C)}
  have hT : T ∈ 𝓝 y := by
    have e1 : ∀ᶠ z in 𝓝 y, ∀ a i j, ‖conn G (ch.e z) (coordVec a) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a i j
      filter_upwards [(hconn a i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP1 a i j]))
    have e2 : ∀ᶠ z in 𝓝 y, ∀ a b i j, ‖curv G (ch.e z) (coordVec a) (coordVec b) i j‖ ≤ C := by
      simp only [eventually_all]
      intro a b i j
      filter_upwards [(hcurv a b i j).norm.eventually (gt_mem_nhds (lt_add_one _))] with z hz
      exact hz.le.trans ((le_refl _).trans (by linarith [hP2 a b i j]))
    filter_upwards [ch.e.open_source.mem_nhds hc, (isOpen_ptsIn (p := X.str) (σ := σ) O).mem_nhds hy,
      GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA, e1, e2] with z h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁, h₂, h₃, h₄, h₅⟩
  refine ⟨ch.e, ∅, A, interior T, C, mem_interior_iff_mem_nhds.2 hT, ?_⟩
  have hsub : ∀ z ∈ interior T, z ∈ T := fun z hz => interior_subset hz
  refine ⟨hhol, isOpen_interior, fun z hz => (hsub z hz).1, fun z hz => (hsub z hz).2.2.1,
    fun z _ a ha => absurd ha (Finset.notMem_empty a), fun z hz => ?_, fun z hz _ a i j => ?_,
    fun z hz _ a b i j => ?_⟩
  · simp only [Finset.notMem_empty, false_imp_iff, implies_true, iff_true]
    exact (hsub z hz).2.1
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.1 a i j
  · simp only [poinWt, Finset.notMem_empty, if_false, mul_one]
    exact (hsub z hz).2.2.2.2 a b i j

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPartStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodPatch_of_complexPoint_openPart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ y ∈ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  first | exact @GlobalTheory.GoodTop.exists_goodPatch_of_mem | exact GlobalTheory.GoodTop.exists_goodPatch_of_mem | (intros; apply GlobalTheory.GoodTop.exists_goodPatch_of_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpen
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem exists_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ}
    (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens)
    (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ),
    IsGood E O H → ∀ y ∉ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  intro F _ σ X m E O H hG y hy
  obtain ⟨e, S, hholo, hys, hy0, hcomp, A, hA, c, N, hev⟩ := hG y hy
  have h1 : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O → GoodBound S c N (fun v => H A (e.symm v) ()) (e z) :=
    (eventually_nhdsWithin_iff.1 hev).mono fun z hz hzO => hz hzO ()
  have h2 : ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := GlobalTheory.T.adaptedFrame_eventually_near_complexPoint E hA
  have h3 : ∀ᶠ z in 𝓝 y, z ∈ e.source := e.open_source.mem_nhds hys
  have h4 : ∀ᶠ z in 𝓝 y, ∀ a ∈ S, ‖e z a‖ ≤ 1 / 2 := by
    refine (Filter.eventually_all_finset S).2 fun a ha => ?_
    have hc : ContinuousAt (fun z => e z a) y :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin X.dim => ℂ) a).continuous.comp
        (PiLp.continuous_ofLp 2 _)).continuousAt.comp (e.continuousAt hys)
    have h0 : e y a = 0 := hy0 a ha
    have : ∀ᶠ z in 𝓝 y, e z a ∈ Metric.ball (0 : ℂ) (1 / 2) :=
      hc.preimage_mem_nhds (by rw [h0]; exact Metric.ball_mem_nhds _ (by norm_num))
    exact this.mono fun z hz => le_of_lt (by simpa using hz)
  obtain ⟨W, hW, hWo, hyW⟩ := eventually_nhds_iff.1 (h1.and (h2.and (h3.and h4)))
  refine ⟨e, S, A, W, c, hyW, ?_⟩
  exact
  { holo := hholo
    isOpen := hWo
    sub := fun z hz => (hW z hz).2.2.1
    frame := fun z hz => (hW z hz).2.1
    small := fun z hz => (hW z hz).2.2.2
    mem := fun z hz => by
      have := hcomp z (hW z hz).2.2.1
      constructor
      · intro hzO a ha h
        exact (this.2 ⟨a, ha, h⟩) hzO
      · intro hne
        by_contra hzO
        obtain ⟨a, ha, h⟩ := this.1 hzO
        exact hne a ha h
    form := fun z hz hzO a i j => ((hW z hz).1 hzO).form a i j
    dbar := fun z hz hzO a b i j => ((hW z hz).1 hzO).dbar a b i j }

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpenStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poincareGoodPatch_outside_open : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsGood E O H → ∀ y ∉ ptsIn X.str σ O, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := by
  first | exact @GlobalTheory.GoodTop.exists_goodPatch | exact GlobalTheory.GoodTop.exists_goodPatch | (intros; apply GlobalTheory.GoodTop.exists_goodPatch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOn
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOn
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix ENNReal

namespace GlobalTheory.GoodTop

theorem hasInt_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ},
    (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  intro n Y κ _ _ _ e S hS d d' t h hd
  have key : ∀ ε : ℤˣ, glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d' i y)) S =
      glueMeas e (fun i y => ENNReal.ofReal ((ε : ℤ) * d i y)) S := by
    intro ε
    have hm := GlobalTheory.ChernScale.glueMeas_restrict_eq e
      (ρ := fun i y => ENNReal.ofReal ((ε : ℤ) * d' i y)) (ρ' := fun i y => ENNReal.ofReal ((ε : ℤ) * d i y))
      (c := 1) ENNReal.one_ne_top hS (fun i y hy hyS => by rw [one_mul, h i y hyS hy])
    have := congrArg (fun μ : Measure Y => μ S) hm
    simpa only [one_smul, Measure.restrict_apply_self] using this
  refine ⟨fun ε => by rw [key ε]; exact hd.1 ε, ?_⟩
  rw [← hd.2, measureReal_def, measureReal_def, measureReal_def, measureReal_def, key 1, key (-1)]

end GlobalTheory.GoodTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOnStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTopFormChartIntegral_congr_on : ∀ {n : ℕ} {Y κ : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (e : κ → OpenPartialHomeomorph Y (V n)) {S : Set Y}, MeasurableSet S → ∀ {d d' : κ → Y → ℝ} {t : ℝ}, (∀ i y, y ∈ S → y ∈ (e i).source → d i y = d' i y) → HasInt e d S t → HasInt e d' S t := by
  first | exact @GlobalTheory.GoodTop.hasInt_congr_on | exact GlobalTheory.GoodTop.hasInt_congr_on | (intros; apply GlobalTheory.GoodTop.hasInt_congr_on <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothPartitionOfUnityComplexPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothPartitionOfUnityComplexPoints
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}

theorem cInfAt_inv_of_ne_zero {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ} (h : CInfAt f y)
    (h0 : f y ≠ 0) : CInfAt (fun z => (f z)⁻¹) y := by
  obtain ⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩,
    (h₄.mono Set.inter_subset_left).inv fun _ hv => hv.2, ?_⟩
  · exact fun e => h0 (h₅.eq_of_nhds.trans e)
  · filter_upwards [h₅] with z e
    rw [e]

theorem cInfAt_finset_sum {ι : Type} (s : Finset ι) {f : ι → CxPts X.str σ → ℝ}
    {y : CxPts X.str σ} (h : ∀ i, CInfAt (f i) y) : CInfAt (fun z => ∑ i ∈ s, f i z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const 0 y
  | insert a s ha ih => simpa only [Finset.sum_insert ha] using (h a).add ih

theorem exists_cInf_bump (y : CxPts X.str σ) {U : Set (CxPts X.str σ)} (hU : U ∈ 𝓝 y) :
    ∃ χ : CxPts X.str σ → ℝ, (∀ z, CInfAt χ z) ∧ (∀ z, 0 ≤ χ z) ∧ 0 < χ y ∧ tsupport χ ⊆ U := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := X.dim) y
  obtain ⟨K, hKy, hKc, hKV⟩ :=
    exists_mem_nhds_isClosed_subset (inter_mem hU (c.e.open_source.mem_nhds hc))
  have hn : c.e.symm ⁻¹' K ∈ 𝓝 (c.e y) :=
    c.e.continuousAt_symm (c.e.map_source hc) (by rwa [c.e.left_inv hc])
  obtain ⟨r, hr, hrO⟩ := Metric.mem_nhds_iff.1 hn
  let b : ContDiffBump (c.e y) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hsupp : ∀ z ∈ c.e.source, b (c.e z) ≠ 0 → z ∈ K := by
    intro z hz h
    have h₁ : c.e z ∈ Metric.ball (c.e y) r := by
      have : c.e z ∈ Function.support b := h
      rwa [b.support_eq] at this
    have h₂ : c.e.symm (c.e z) ∈ K := hrO h₁
    rwa [c.e.left_inv hz] at h₂
  refine ⟨fun z => if z ∈ c.e.source then b (c.e z) else 0, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · by_cases hz : z ∈ c.e.source
    · refine cInfAt_of_chart isOpen_univ c ?_ hz trivial
      refine (b.contDiff (n := ⊤)).contDiffOn.congr fun v hv => ?_
      simp only [Function.comp_apply, if_pos (c.e.map_target hv.1), c.e.right_inv hv.1]
    · have hzK : z ∉ K := fun h => hz (hKV h).2
      refine (cInfAt_const 0 z).congr ?_
      filter_upwards [hKc.isOpen_compl.mem_nhds hzK] with w hw
      by_cases hwS : w ∈ c.e.source
      · simp only [if_pos hwS]
        by_contra h
        exact hw (hsupp w hwS h)
      · simp only [if_neg hwS]
  · dsimp only
    split_ifs
    · exact b.nonneg
    · exact le_rfl
  · simp only [if_pos hc]
    rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]
    exact one_pos
  · refine (closure_minimal (fun z hz => ?_) hKc).trans fun z hz => (hKV hz).1
    by_cases hzS : z ∈ c.e.source
    · exact hsupp z hzS (by simpa only [Function.mem_support, if_pos hzS] using hz)
    · simp only [Function.mem_support, if_neg hzS, ne_eq, not_true_eq_false] at hz

theorem exists_cInf_partition : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (W : CxPts X.str σ → Set (CxPts X.str σ)), (∀ y, W y ∈ 𝓝 y) → ∃ (s : Finset (CxPts X.str σ)) (ρ : s → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) ∧ (∀ i, tsupport (ρ i) ⊆ W i) ∧ ∀ y, ∑ i, ρ i y = 1 := by
  intro F _ σ X W hW
  haveI := CxPts.compactSpace σ X.isProjOver
  choose χ hχ h0 hpos hs using fun y => exists_cInf_bump y (hW y)
  obtain ⟨s, hcov⟩ := CompactSpace.elim_nhds_subcover (fun y => {z | 0 < χ y z})
    fun y => (hχ y y).continuousAt.eventually (lt_mem_nhds (hpos y))
  have hT (z) : ∑ i : s, χ i z ≠ 0 := by
    have hz : z ∈ ⋃ y ∈ s, {z | 0 < χ y z} := hcov ▸ Set.mem_univ z
    obtain ⟨y, hy, hz⟩ := Set.mem_iUnion₂.1 hz
    exact (Finset.sum_pos' (f := fun i : s => χ i z) (fun i _ => h0 i z)
      ⟨⟨y, hy⟩, Finset.mem_univ _, hz⟩).ne'
  refine ⟨s, fun i z => χ i z * (∑ j : s, χ j z)⁻¹, fun i y => ?_,
    fun i => (tsupport_mul_subset_left).trans (hs i), fun y => ?_⟩
  · exact (hχ i y).comp₂ (cInfAt_inv_of_ne_zero
      (cInfAt_finset_sum Finset.univ fun j : s => hχ j y) (hT y))
      (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)
  · rw [← Finset.sum_mul, mul_inv_cancel₀ (hT y)]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothPartitionOfUnityComplexPointsStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_partition_of_unity_complexPoints : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} (W : CxPts X.str σ → Set (CxPts X.str σ)), (∀ y, W y ∈ 𝓝 y) → ∃ (s : Finset (CxPts X.str σ)) (ρ : s → CxPts X.str σ → ℝ), (∀ i y, CInfAt (ρ i) y) ∧ (∀ i, tsupport (ρ i) ⊆ W i) ∧ ∀ y, ∑ i, ρ i y = 1 := by
  first | exact @GlobalTheory.GoodTop.exists_cInf_partition | exact GlobalTheory.GoodTop.exists_cInf_partition | (intros; apply GlobalTheory.GoodTop.exists_cInf_partition <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmooth
open AlgebraicGeometry MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodTop

theorem goodTopChernForm : GlobalTheory.Published.GoodTopChernForm := by
  intro F _ σ X m E O H H₀ hH hG hH₀ t ht
  rw [hasChernIntegral_iff] at ht ⊢
  haveI := X.smooth_str
  haveI : SecondCountableTopology (CxPts X.str σ) := inferInstance
  have hp : ∀ y : CxPts X.str σ, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := fun y => by
    by_cases hy : y ∈ ptsIn X.str σ O
    · exact GlobalTheory.T.exists_goodPatch_of_complexPoint_openPart E O H hH y hy
    · exact GlobalTheory.T.exists_poincareGoodPatch_outside_open E O H hG y hy
  choose e S A W c hyW hP using hp
  obtain ⟨s, ρ, hρ, hsupp, hsum⟩ := GlobalTheory.T.exists_smooth_partition_of_unity_complexPoints W fun y => (hP y).isOpen.mem_nhds (hyW y)
  choose a b ha hb hab using fun i : s => GlobalTheory.T.transgression_topChernForm_goodPatch E O H H₀ hH hH₀ (hP i) (hρ i) (hsupp i)
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hm : ∀ U : X.X.Opens, MeasurableSet (ptsIn X.str σ U) := fun U => (isOpen_ptsIn U).measurableSet
  have hc : ∀ i, Continuous (ρ i) := fun i => continuous_iff_continuousAt.2 fun y => (hρ i y).continuousAt
  have h₁ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) (∑ i, a i) := by
    refine GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm O) (fun i y _ _ => ?_)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm O) (fun i => GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E O H hH (hc i)) ha)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₂ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H₀) (ptsIn X.str σ ⊤) (∑ i, b i) := by
    refine GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm ⊤) (fun i y _ _ => ?_)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm ⊤) (fun i => GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E ⊤ H₀ hH₀ (hc i)) hb)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₃ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun _ _ => 0) (ptsIn X.str σ O) (∑ i, (a i - b i)) :=
    GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm O) (fun i y _ hy => GlobalTheory.T.sum_transgression_densities_partition_unity_eq_zero E O H H₀ ρ hρ hsum i y hy)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm O) (fun i => GlobalTheory.T.transgression_correction_isTopDegreeForm E O H H₀ hH hH₀ (hρ i)) hab)
  have e₂ : ∑ i, b i = t := h₂.2.symm.trans ht.2
  have e₃ : ∑ i, (a i - b i) = 0 := h₃.2.symm.trans (GlobalTheory.T.hasTopFormChartIntegral_zero _ _).2
  rw [Finset.sum_sub_distrib, sub_eq_zero, e₂] at e₃
  exact e₃ ▸ h₁

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmoothStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth : GlobalTheory.Published.GoodTopChernForm := by
  first | exact @GlobalTheory.GoodTop.goodTopChernForm | exact GlobalTheory.GoodTop.goodTopChernForm | (intros; apply GlobalTheory.GoodTop.goodTopChernForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocks
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem perm_submonoid_eq_top_of_adj (k : ℕ) (T : Submonoid (Equiv.Perm (Fin k)))
    (h : ∀ a b : Fin k, (b : ℕ) = a + 1 → Equiv.swap a b ∈ T) : T = ⊤ := by
  cases k with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; exact T.one_mem
  | succ n =>
    rw [eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h _ _ (by simp)

theorem alternating_of_adjacent_swap (ι : Type) [Fintype ι] (m : ι → ℕ)
    (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q,
      L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ) :
    L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  let S : Submonoid (∀ τ, Equiv.Perm (Fin (m τ))) :=
    { carrier := {w | ∀ Q, L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q}
      one_mem' := by
        intro Q
        have : (fun x : Root m => (⟨x.1, (1 : ∀ τ, Equiv.Perm (Fin (m τ))) x.1 x.2⟩ : Root m)) = id := by
          funext x; rfl
        rw [this, rename_id]
        simp
      mul_mem' := by
        intro v w hv hw Q
        have : (fun x : Root m => (⟨x.1, (v * w) x.1 x.2⟩ : Root m)) =
            (fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) ∘
              (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) := by
          funext x; rfl
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [this, ← rename_rename, hv, hw]
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, Units.val_mul, Int.cast_mul]
        ring }
  have hS : S = ⊤ := by
    have htop : (⊤ : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))) =
        Submonoid.pi Set.univ (fun τ => (⊤ : Submonoid (Equiv.Perm (Fin (m τ))))) := by
      ext x; simp [Submonoid.mem_pi]
    rw [eq_top_iff, htop, ← Submonoid.iSup_map_mulSingle, iSup_le_iff]
    intro τ
    rw [Submonoid.map_le_iff_le_comap]
    rw [perm_submonoid_eq_top_of_adj (m τ) (Submonoid.comap (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ) S) ?_]
    intro a b hab Q
    have hf : (fun x : Root m => (⟨x.1, (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) x.1 x.2⟩ : Root m)) = Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩ := by
      funext ⟨σ, c⟩
      by_cases h : σ = τ
      · subst h
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
        by_cases h1 : c = a
        · subst h1; simp
        · by_cases h2 : c = b
          · subst h2; simp [h1]
          · simp [h1, h2]
      · simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, Equiv.Perm.coe_one, id]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro e; exact h (congrArg Sigma.fst e)
        · intro e; exact h (congrArg Sigma.fst e)
    have hab' : a ≠ b := by
      intro e; subst e; omega
    have hs : (∏ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) σ)) = -1 := by
      have : ∀ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
          (Equiv.swap a b)) σ) = (Pi.mulSingle τ (Equiv.Perm.sign (Equiv.swap a b)) : ι → ℤˣ) σ := by
        intro σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Pi.mulSingle_eq_of_ne h]
      simp only [this, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
      exact Equiv.Perm.sign_swap hab'
    show L _ = _
    rw [hf, hs, hL τ a b hab Q]
    simp
  have hw : w ∈ S := by rw [hS]; trivial
  exact hw Q

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocksStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ), L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) = (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  first | exact @GlobalTheory.FlagPush.alternating_of_adjacent_swap | exact GlobalTheory.FlagPush.alternating_of_adjacent_swap | (intros; apply GlobalTheory.FlagPush.alternating_of_adjacent_swap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEq
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem linForm_eq_of_antisymm_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  intro ι _ m L hL Q Q' h
  have sq : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
    intro u
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have key : ∀ P : MvPolynomial (Root m) ℝ,
      L (antisymm P) = (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) * L P := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.GoodMetric.antisymm, map_sum, map_zsmul]
    rw [Finset.sum_congr rfl (fun w _ => by
      rw [GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks ι m L hL w P, zsmul_eq_mul, ← mul_assoc, sq, one_mul])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ∀ τ, Equiv.Perm (Fin (m τ)))).ne'
  have e := congrArg L h
  rw [key, key] at e
  exact mul_left_cancel₀ hc e

end GlobalTheory.FlagPush
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEqStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  first | exact @GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq | exact GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq | (intros; apply GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormula
noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.FlagPushProof

theorem flagPushForward : GlobalTheory.Published.FlagPushForward := by
  intro F _ _ X Y ι _ m E E' φ f gr hf hg Q R hR
  have hswap := GlobalTheory.T.flagSpace_intersectionNumber_adjacent_swap_neg F X Y ι m E E' φ f hf gr hg
  refine GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq ι m (Y.interPoly gr) hswap Q (chernRoots m R * fibrePoint m) ?_
  classical
  have rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
      (R : MvPolynomial (ι × ℕ) ℝ) :
      rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
    have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
      have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
        funext i; rfl
      rw [e, ← rename_rename, rename_esymm]
    exact AlgHom.congr_fun h R

  have antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
      (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_chernRoots, mul_smul_comm]

  have prod_Ioi_rev {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
        ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
      intro f
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      congr 1
      ext j; simp
    rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
      ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
    refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
    simp [Fin.rev_lt_rev]

  have sum_sign_prod_neg_pow {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
        ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
    let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
    have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
      rw [Matrix.det_apply']
      rfl
    have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
      ext j i
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
      congr 1
      omega
    rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
      GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde]
    simp only [neg_sub_neg]
    rw [prod_Ioi_rev]

  have antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
    have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
        ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
          ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(MvPolynomial.X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
      intro w
      unfold fibrePoint
      rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [map_pow, map_neg, rename_X]
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.sum_congr rfl fun w _ => hw w]
    rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(MvPolynomial.X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
    unfold rootDiscr
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (MvPolynomial.X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))
  rw [hR, antisymm_chernRoots_mul ι m R, antisymm_fibrePoint ι m]

end GlobalTheory.FlagPushProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormulaStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_pushForward_formula : GlobalTheory.Published.FlagPushForward := by
  first | exact @GlobalTheory.FlagPushProof.flagPushForward | exact GlobalTheory.FlagPushProof.flagPushForward | (intros; apply GlobalTheory.FlagPushProof.flagPushForward <;> assumption)
end
end

namespace GlobalTheory.GoodMetric

theorem goodChernWeil : GlobalTheory.Published.GoodChernWeil :=
  goodChernWeil_of_goodTopChernForm GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric GlobalTheory.T.fullFlagBundle_pushForward_formula

end GlobalTheory.GoodMetric
