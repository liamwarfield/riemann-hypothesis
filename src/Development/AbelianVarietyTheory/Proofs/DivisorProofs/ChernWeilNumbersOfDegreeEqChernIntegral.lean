module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllTraceOfMiddleX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumber

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairOfTwoFlaggedMetrics
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairOfTwoFlaggedMetrics
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isGramPair_of_isMetricFr : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  intro F _ σ X ι _ m k E H H' hH hH' τ
  have hA (y : CxPts X.str σ) := (E.nonempty (under y)).choose_spec
  refine ⟨fun y => ⟨(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y _ (hA y) τ).1,
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H' hH' y _ (hA y) τ).1⟩, fun y => ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E y _ (hA y)] with z hz
  have hP := (Fr.mem_iff hz).1 (hA z) τ
  have hT := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X (m τ) _ z (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)
  refine ⟨_, _, _, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ hz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m k E z _ (hA z)] with w h1 h2
  exact ⟨hH.trans w _ h1 _ h2 τ, hH'.trans w _ h1 _ h2 τ⟩

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairOfTwoFlaggedMetricsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGramConnectionPair_of_two_flagged_metrics : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H H' : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → IsMetricFr E H' → ∀ τ, IsGramPair (atlas X σ) (gramAt E H τ) (gramAt E H' τ) := by
  first | exact @GlobalTheory.ChernCalc.isGramPair_of_isMetricFr | exact GlobalTheory.ChernCalc.isGramPair_of_isMetricFr | (intros; apply GlobalTheory.ChernCalc.isGramPair_of_isMetricFr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetric
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem isForm_evalF_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ)
    (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  intro F _ σ X ι _ m k E H h R
  exact ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (atlas X σ)).2.2.2.1 _ (chernF E H) R fun x =>
    (GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ (atlas X σ) _ _ _ (GlobalTheory.T.isGramConnectionPair_of_two_flagged_metrics F σ X ι m k E H H h h x.1) x.2).1).1

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetricStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_evalRealPoly_chernForms_flaggedMetric : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ R : MvPolynomial (ι × ℕ) ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (chernF E H) R) := by
  first | exact @GlobalTheory.ChernCalc.isForm_evalF_chernF | exact GlobalTheory.ChernCalc.isForm_evalF_chernF | (intros; apply GlobalTheory.ChernCalc.isForm_evalF_chernF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricGradedWeightFrameIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmatrixMulLower
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.ChernCalc
open scoped Matrix ComplexOrder

namespace GlobalTheory.LeadingMinorPositivity

section Lin

variable {s : ℕ}

theorem submatrix_mul_lower {κ : Type} (T : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0)
    (M : Matrix (Fin s) κ ℂ) (j : ℕ) :
    (T * M).submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id =
      T.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) Subtype.val *
        M.submatrix (Subtype.val : {a : Fin s // (a : ℕ) < j} → Fin s) id := by
  ext a b
  change ∑ l, T a l * M l b = ∑ l : {a : Fin s // (a : ℕ) < j}, T a l * M l b
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin s => (l : ℕ) < j) (by simp)
    (fun l => T a l * M l b)]
  refine (Finset.sum_filter_of_ne fun l _ hl => ?_).symm
  by_contra h
  refine hl ?_
  rw [hT a l (by have := a.2; show (a.1 : ℕ) < l; omega), zero_mul]

theorem leadMinor_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (j : ℕ) :
    leadMinor (T * G * Tᴴ) j =
      ((∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < j, ‖T a a‖ ^ 2 : ℝ) : ℂ) * leadMinor G j := by
  let v : {a : Fin s // (a : ℕ) < j} → Fin s := Subtype.val
  have h1 : (G * Tᴴ).submatrix v v = G.submatrix v v * (T.submatrix v v)ᴴ := by
    have := submatrix_mul_lower T hT (G.submatrix v id)ᴴ j
    have h2 := (congrArg Matrix.conjTranspose this).trans (Matrix.conjTranspose_mul _ _)
    refine Eq.trans ?_ (h2.trans ?_)
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rfl
    · rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_conjTranspose]
      rfl
  have h3 : (T * G * Tᴴ).submatrix v v = T.submatrix v v * (G.submatrix v v * (T.submatrix v v)ᴴ) := by
    have := submatrix_mul_lower T hT ((G * Tᴴ).submatrix id v) j
    rw [← h1, Matrix.mul_assoc]
    exact this
  have h4 : (T.submatrix v v).det = ∏ a, T (v a) (v a) :=
    Matrix.det_of_isLowerTriangular _ fun a b hab => hT _ _ hab
  unfold leadMinor
  change ((T * G * Tᴴ).submatrix v v).det = _ * (G.submatrix v v).det
  rw [h3, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, h4,
    Finset.prod_subtype (p := fun l : Fin s => (l : ℕ) < j) _ (by simp), mul_left_comm, mul_comm]
  congr 1
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_prod, Finset.prod_pow]

theorem leadMinor_re_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (j : ℕ) : 0 < (leadMinor G j).re :=
  (Complex.pos_iff.1 (hG.submatrix Subtype.val_injective).det_pos).1

theorem grD_pos {G : Matrix (Fin s) (Fin s) ℂ} (hG : G.PosDef) (i : Fin s) : 0 < grD G i :=
  div_pos (leadMinor_re_pos hG _) (leadMinor_re_pos hG _)

theorem grD_conj (T G : Matrix (Fin s) (Fin s) ℂ) (hT : ∀ a b, a < b → T a b = 0) (hd : ∀ a, T a a ≠ 0) (i : Fin s) :
    grD (T * G * Tᴴ) i = ‖T i i‖ ^ 2 * grD G i := by
  have e : (Finset.univ.filter fun l : Fin s => (l : ℕ) < i + 1) =
      insert i (Finset.univ.filter fun l : Fin s => (l : ℕ) < i) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hp : (∏ a ∈ Finset.univ.filter fun l : Fin s => (l : ℕ) < i, ‖T a a‖ ^ 2 : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hd a))
  rw [grD, grD, leadMinor_conj T G hT, leadMinor_conj T G hT, Complex.re_ofReal_mul, Complex.re_ofReal_mul, e,
    Finset.prod_insert (by simp), mul_comm (‖T i i‖ ^ 2), mul_assoc, mul_div_mul_left _ _ hp, mul_div_assoc]

theorem diag_mul_lower {K : Type} [Field K] (S T : Matrix (Fin s) (Fin s) K) (hS : ∀ a b, a < b → S a b = 0)
    (hT : ∀ a b, a < b → T a b = 0) (i : Fin s) : (S * T) i i = S i i * T i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun l _ hl => ?_) (by simp)
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hT l i h, mul_zero]
  · rw [hS i l h, zero_mul]

end Lin

theorem green_frame_indep (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → GlobalTheory.CxPts X.str σ → Mat m ℂ) (hH : IsMetricFr E H)
    (B : Mat m X.Fn) (hB : B ∈ E.S (genericPoint X.X)) (y : GlobalTheory.CxPts X.str σ)
    (A : Mat m X.Fn) (hA : A ∈ E.S (under y)) (A' : Mat m X.Fn) (hA' : A' ∈ E.S (under y))
    (x : Root m) (f : X.Fn) (hu : UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f)) :
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
      -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  obtain ⟨τ, i⟩ := x
  have hT := (Fr.mem_iff hA).1 hA'
  have hS := (Fr.mem_iff (Fr.mem_genericPoint hA')).1 hB
  obtain ⟨ψ, hψ⟩ := exists_ratVal_hom y
  have hV := hT.map_of (ratVal · y) ψ hψ τ
  have hlow : ∀ a b, a < b → (A' * A⁻¹).map (ratVal · y) τ a b = 0 := fun a b h => hV.2.2.2 a b a.2 h
  have hd : ∀ a, (A' * A⁻¹).map (ratVal · y) τ a a ≠ 0 := by
    have h := hV.2.1
    rw [Matrix.det_of_isLowerTriangular _ fun a b hab => hlow a b hab] at h
    exact fun a => Finset.prod_ne_zero_iff.1 h a (Finset.mem_univ a)
  have e1 : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
    rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
  have e2 : (B * A⁻¹) τ i i / f = (B * A'⁻¹) τ i i / f * (A' * A⁻¹) τ i i := by
    rw [e1, Pi.mul_apply (B * A'⁻¹), diag_mul_lower _ _ (fun a b h => (hS τ).2.2.2 a b a.2 h)
      (fun a b h => (hT τ).2.2.2 a b a.2 h), div_mul_eq_mul_div]
  have hu0 := ratVal_ne_zero hu
  have hur : RegAt (under y) ((B * A'⁻¹) τ i i / f) := by
    by_contra h
    exact hu0 (dif_neg h)
  have ht : ratVal ((A' * A⁻¹) τ i i) y ≠ 0 := hd i
  have hg := (grD_pos (hH.posDef y A hA τ) i).ne'
  have e3 : grD (H A' y τ) i = ‖ratVal ((A' * A⁻¹) τ i i) y‖ ^ 2 * grD (H A y τ) i := by
    rw [hH.trans y A hA A' hA' τ]
    exact grD_conj _ _ hlow hd i
  have n1 := pow_ne_zero 2 (norm_ne_zero_iff.2 hu0)
  have n2 := pow_ne_zero 2 (norm_ne_zero_iff.2 ht)
  dsimp only at n1 ⊢
  rw [e2, e3, ratVal_mul hur (mem_O_ratOf.1 ((hT τ).1 i i)), norm_mul, mul_pow, Real.log_mul n1 n2,
    Real.log_mul n2 hg]
  ring

end GlobalTheory.LeadingMinorPositivity
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricGradedWeightFrameIndependent
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem grWeight_frame_indep : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ B ∈ E.S (genericPoint X.X), ∀ (y : CxPts X.str σ),
    ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ (x : Root m) (f : X.Fn), UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f) →
      -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
        -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  first
  | exact @_root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep
  | exact _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep
  | (apply _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeadingMinorPositivity.green_frame_indep ..)

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricGradedWeightFrameIndependentStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flaggedBundleMetric_graded_weight_frame_independent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ B ∈ E.S (genericPoint X.X), ∀ (y : CxPts X.str σ),
    ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ (x : Root m) (f : X.Fn), UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f) →
      -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
        -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  first | exact @GlobalTheory.ChernCalc.grWeight_frame_indep | exact GlobalTheory.ChernCalc.grWeight_frame_indep | (intros; apply GlobalTheory.ChernCalc.grWeight_frame_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormGradedLengthSubLogUnitNormSq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormGradedLengthSubLogUnitNormSq
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem leviForm_neg_log_unit_sub_log_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)) (c : AlgChart X.str σ X.dim), y ∈ c.e.source →
      leviForm (fun v => -Real.log (‖ratVal u (c.e.symm v)‖ ^ 2) - Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i c hy
  obtain ⟨W, hW, a, rfl⟩ := hu.regAt.exists_fnOf
  have hyW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 hW
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := X.str) (σ := σ) W)
  have hm := ChartGlue.mem_over c.e hy hyW
  have hg := c.holo W a
  have hf : ContDiffAt ℂ 2 (ev X.str σ W a ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn hg (ho.mem_nhds hm)).contDiffAt
  have h0 : (ev X.str σ W a ∘ c.e.symm) (c.e y) ≠ 0 := by
    have := ratVal_ne_zero hu
    rw [ratVal_fnOf hyW] at this
    simpa [Function.comp, c.e.left_inv hy] using this
  have hlog : ContDiffAt ℝ 2 (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)) (c.e y) :=
    ((hf.restrict_scalars ℝ).norm_sq ℂ).log (by simpa using h0)
  have hsm := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y A hA τ).2 c hy).self_of_nhds
  have hG := (ldPart_grD_smooth _ _ _ _ hsm.1 hsm.2).2 i
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hsm.2).2.1 i).1
  have hD : ContDiffAt ℝ 2 (fun v => Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) :=
    (hG.log hpos.ne').of_le (WithTop.coe_le_coe.2 le_top)
  rw [leviForm_congr (u' := fun v => -Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2) +
      -Real.log (grD (H A (c.e.symm v) τ) i)), leviForm_add hlog.neg hD.neg,
    leviForm_neg (fun v => Real.log (‖(ev X.str σ W a ∘ c.e.symm) v‖ ^ 2)), leviForm_log_normSq_eq_zero hf h0,
    neg_zero, zero_add]
  filter_upwards [ho.mem_nhds hm] with v hv
  simp only [Function.comp, sub_eq_add_neg]
  rw [ratVal_fnOf hv.2]

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormGradedLengthSubLogUnitNormSqStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviForm_graded_length_sub_log_unit_normSq : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)) (c : AlgChart X.str σ X.dim), y ∈ c.e.source →
      leviForm (fun v => -Real.log (‖ratVal u (c.e.symm v)‖ ^ 2) - Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H A (c.e.symm v) τ) i)) (c.e y) := by
  first | exact @GlobalTheory.ChernCalc.leviForm_neg_log_unit_sub_log_grD | exact GlobalTheory.ChernCalc.leviForm_neg_log_unit_sub_log_grD | (intros; apply GlobalTheory.ChernCalc.leviForm_neg_log_unit_sub_log_grD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtLogUnitAddGradedLength
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtLogUnitAddGradedLength
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem cInfAt_ratVal_on {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {κ : Type} [Fintype κ] {f : κ → X.Fn}
    {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a)) {G : (κ → ℂ) → ℝ} {O : Set (κ → ℂ)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ ∞ G O) (hy : (fun a => ratVal (f a) y) ∈ O) :
    CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hyU g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hyU)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  have hev (z : CxPts X.str σ) (hz : z ∈ ptsIn X.str σ W) :
      (fun a => ev X.str σ W (resG X.X (hle a) (g a)) z) = fun a => ratVal (f a) z := by
    funext a
    rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, O, hW, hO, ?_, hG, ?_⟩
  · rw [hev y hW]; exact hy
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
    rw [hev z hz]

theorem cInfAt_neg_log_normSq_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : CxPts X.str σ} {u : X.Fn}
    (hu : UnitAt (under y) u) : CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2)) y := by
  have hO : IsOpen {w : Unit → ℂ | w () ≠ 0} := isOpen_ne_fun (continuous_apply ()) continuous_const
  have hG : ContDiffOn ℝ ∞ (fun w : Unit → ℂ => -Real.log (‖w ()‖ ^ 2)) {w | w () ≠ 0} := by
    intro w hw
    have h1 : ContDiffAt ℝ ∞ (fun w : Unit → ℂ => ‖w ()‖ ^ 2) w :=
      ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) ())).contDiffAt
    have h2 : ‖w ()‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hw)
    exact (h1.log h2).neg.contDiffWithinAt
  exact cInfAt_ratVal_on (κ := Unit) (f := fun _ => u) (fun _ => hu.regAt) hO hG (ratVal_ne_zero hu)

end GlobalTheory.ChernCalc

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ChernCalc.cInfAt_logUnit_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i
  refine (GlobalTheory.ChernCalc.cInfAt_neg_log_normSq_ratVal hu).add ?_ |>.congr (Eventually.of_forall fun z => sub_eq_add_neg _ _)
  have := X.smooth_str
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y A hA τ).2 c hc)
  obtain ⟨O, hOP, hOo, hyO⟩ := eventually_nhds_iff.1 hev
  have hS : IsOpen (c.e.source ∩ c.e ⁻¹' O) := c.e.isOpen_inter_preimage hOo
  refine cInfAt_of_chart hS c ?_ hc ⟨hc, hyO⟩
  intro v hv
  have hvO : v ∈ O := by
    have := hv.2.2
    rwa [Set.mem_preimage, c.e.right_inv hv.1] at this
  obtain ⟨hsm, hpd⟩ := hOP v hvO
  have hd := (ldPart_grD_smooth _ _ _ v hsm hpd).2 i
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hpd).2.1 i).1
  exact (hd.log hpos.ne').neg.contDiffWithinAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtLogUnitAddGradedLengthStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPointsSmoothAt_log_unit_add_graded_length : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  first | exact @GlobalTheory.ChernCalc.cInfAt_logUnit_grD | exact GlobalTheory.ChernCalc.cInfAt_logUnit_grD | (intros; apply GlobalTheory.ChernCalc.cInfAt_logUnit_grD <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFullFlagFrameChangeDiagonalUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFullFlagFrameChangeDiagonalUnits
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.FlagChange

theorem diag_unitAt_and_mul : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m) (B : Mat m X.Fn),
    B ∈ E.S (genericPoint X.X) → ∀ (z : X.X) (A A' : Mat m X.Fn), A ∈ E.S z → A' ∈ E.S z → ∀ x : Root m,
      UnitAt z ((A' * A⁻¹) x.1 x.2 x.2) ∧ (B * A⁻¹) x.1 x.2 x.2 = (B * A'⁻¹) x.1 x.2 x.2 * (A' * A⁻¹) x.1 x.2 x.2 := by
  intro F _ X ι m E B hB z A A' hA hA' x
  obtain ⟨τ, i⟩ := x
  have hP : Par m ((ratOf X).O z).toSubring (A' * A⁻¹) := (Fr.mem_iff hA).1 hA'
  have hl : ∀ (C : Mat m X.Fn) (O : Subring X.Fn), Par m O C → (C τ).BlockTriangular OrderDual.toDual := by
    intro C O hC a b hab
    exact (hC τ).2.2.2 a b a.2 hab
  refine ⟨?_, ?_⟩
  · set P := A' * A⁻¹ with hPdef
    have hdet : (P τ).det = P τ i i * ∏ j ∈ Finset.univ.erase i, P τ j j := by
      rw [Matrix.det_of_lowerTriangular _ (hl P _ hP),
        Finset.mul_prod_erase Finset.univ (fun j => P τ j j) (Finset.mem_univ i)]
    have hne : (P τ).det ≠ 0 := hP.det_ne τ
    rw [hdet] at hne
    have hii : P τ i i ≠ 0 := left_ne_zero_of_mul hne
    have hR : ∏ j ∈ Finset.univ.erase i, P τ j j ≠ 0 := right_ne_zero_of_mul hne
    have hmem : ∀ a b, P τ a b ∈ (ratOf X).O z := fun a b => (hP τ).1 a b
    have hinv : (P τ i i)⁻¹ ∈ (ratOf X).O z := by
      have e : (P τ i i)⁻¹ = (P τ).det⁻¹ * ∏ j ∈ Finset.univ.erase i, P τ j j := by
        rw [hdet, _root_.mul_inv, mul_assoc, inv_mul_cancel₀ hR, mul_one]
      rw [e]
      refine ((ratOf X).O z).mul_mem (hP τ).2.2.1 (((ratOf X).O z).prod_mem fun j _ => hmem j j)
    exact (unitAt_iff hii).2 ⟨mem_O_ratOf.1 (hmem i i), mem_O_ratOf.1 hinv⟩
  · have hA'g : A' ∈ E.S (genericPoint X.X) := Fr.mem_genericPoint hA'
    have hQ : Par m ((ratOf X).O (genericPoint X.X)).toSubring (B * A'⁻¹) := (Fr.mem_iff hA'g).1 hB
    have e : B * A⁻¹ = B * A'⁻¹ * (A' * A⁻¹) := by
      rw [mul_assoc, ← mul_assoc A'⁻¹, Mat.inv_mul (Fr.det_ne hA'), one_mul]
    rw [e]
    show ((B * A'⁻¹) τ * (A' * A⁻¹) τ) i i = _
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun l _ hl' => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hl' with h | h
    · rw [(hP τ).2.2.2 l i l.2 h, mul_zero]
    · rw [(hQ τ).2.2.2 i l i.2 h, zero_mul]

end GlobalTheory.FlagChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFullFlagFrameChangeDiagonalUnitsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedFullFlag_frame_change_diagonal_units : ∀ (F : Type) [Field F] (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m) (B : Mat m X.Fn),
    B ∈ E.S (genericPoint X.X) → ∀ (z : X.X) (A A' : Mat m X.Fn), A ∈ E.S z → A' ∈ E.S z → ∀ x : Root m,
      UnitAt z ((A' * A⁻¹) x.1 x.2 x.2) ∧ (B * A⁻¹) x.1 x.2 x.2 = (B * A'⁻¹) x.1 x.2 x.2 * (A' * A⁻¹) x.1 x.2 x.2 := by
  first | exact @GlobalTheory.FlagChange.diag_unitAt_and_mul | exact GlobalTheory.FlagChange.diag_unitAt_and_mul | (intros; apply GlobalTheory.FlagChange.diag_unitAt_and_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundles
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem graded_weight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (gr : Root m → X.Dv), IsGraded E gr →
    IsMetricFr E H → ∀ x : Root m, ∃ (L : LB X.X) (r : L.ι → X.Fnˣ) (ψ : Weight X.str σ L),
      Presents (gr x) L r ∧ ψ.IsCInf ∧ c1W ψ = grF E H x := by
  intro F _ σ X ι _ m E H gr hG hH x
  obtain ⟨B, hB, hgr⟩ := hG
  have hunit : ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∀ f : X.Fnˣ, (gr x).IsEqn z f →
      UnitAt z ((B * A⁻¹) x.1 x.2 x.2 / f) := by
    intro z A hA f hf
    obtain ⟨A₀, hA₀, t, ht, he⟩ := hgr z x
    obtain ⟨hu, hd⟩ := GlobalTheory.T.adaptedFullFlag_frame_change_diagonal_units F X ι m E B hB z A₀ A hA₀ hA x
    have htf : UnitAt z ((t : X.Fn) / f) := (hf.iff_unitAt).1 he
    have hne : (A * A₀⁻¹) x.1 x.2 x.2 ≠ 0 := fun h0 => by
      obtain ⟨a, ha, h⟩ := hu
      rw [h0] at h
      exact (ha.map (algebraMap _ X.Fn)).ne_zero h
    have e : (B * A⁻¹) x.1 x.2 x.2 / f = ((t : X.Fn) / f) * ((A * A₀⁻¹) x.1 x.2 x.2)⁻¹ := by
      rw [← ht, hd]; field_simp
    rw [e]; exact htf.mul hu.inv

  let Ach : CxPts X.str σ → Mat m X.Fn := fun y => (E.nonempty (under y)).choose
  have hAch : ∀ y, Ach y ∈ E.S (under y) := fun y => (E.nonempty (under y)).choose_spec
  let val : Mat m X.Fn → CxPts X.str σ → X.Fn → ℝ := fun A y f =>
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2)
  let D := gr x
  have hP := presents_toLB D
  have heq : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      D.IsEqn (under y) (i.1.2) := fun i y hy => i.2.2 _ (mem_ptsIn.1 hy)
  have hindep : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      ∀ A ∈ E.S (under y), val (Ach y) y i.1.2 = val A y i.1.2 := fun i y hy A hA =>
    GlobalTheory.T.flaggedBundleMetric_graded_weight_frame_independent F σ X ι m E H hH B hB y (Ach y) (hAch y) A hA x _ (hunit _ A hA _ (heq i y hy))
  let ψ : Weight X.str σ (toLB D) :=
    { isLB := isLB_toLB D
      φ := fun i y => val (Ach y) y i.1.2
      trans := by
        intro i j y hi hj
        have hu1 := hunit _ _ (hAch y) _ (heq i y hi)
        have hu2 : UnitAt (under y) ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := ((heq j y hj).iff_unitAt).1 (heq i y hi)
        have hg : gv X.str σ (toLB D) i j y = ratVal ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) y := by
          have hgen : genericPoint X.X ∈ (toLB D).U i ⊓ (toLB D).U j := ⟨i.2.1, j.2.1⟩
          rw [← fnOf_toLB_g i j hgen, ratVal_fnOf (mem_ptsIn_inf.2 ⟨hi, hj⟩) hgen]
          rfl
        have hi0 := (i.1.2).ne_zero
        have hj0 := (j.1.2).ne_zero
        have e : (B * (Ach y)⁻¹) x.1 x.2 x.2 / (j.1.2 : X.Fn) =
            ((B * (Ach y)⁻¹) x.1 x.2 x.2 / i.1.2) * ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := by
          field_simp
        show val (Ach y) y j.1.2 = val (Ach y) y i.1.2 - _
        simp only [val]
        rw [e, ratVal_mul hu1.regAt hu2.regAt, log_normSq_mul (ratVal_ne_zero hu1) (ratVal_ne_zero hu2), hg]
        ring }
  refine ⟨toLB D, fun i => i.1.2, ψ, hP, ?_, ?_⟩
  · intro i y hy
    have hu := hunit _ _ (hAch y) _ (heq i y hy)
    refine (GlobalTheory.T.complexPointsSmoothAt_log_unit_add_graded_length F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2).congr ?_
    filter_upwards [frame_eventually_near F σ X ι m m E y (Ach y) (hAch y), (isOpen_ptsIn _).mem_nhds hy] with z hz hzi
    exact hindep i z hzi (Ach y) hz
  · funext p
    obtain ⟨⟨c, y⟩, hy⟩ := p
    have hy' : y ∈ c.e.source := hy
    have ha : y ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) := mem_pick ψ.isLB y
    have hu := hunit _ _ (hAch y) _ (heq _ y ha)
    have hnear : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧ Ach y ∈ E.S (under z) :=
      Filter.Eventually.and ((isOpen_ptsIn _).mem_nhds ha) (frame_eventually_near F σ X ι m m E y (Ach y) (hAch y))
    have hnear' : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧
        Ach y ∈ E.S (under (c.e.symm v)) := by
      have hc := c.e.continuousAt_symm (c.e.map_source hy')
      rw [ContinuousAt, c.e.left_inv hy'] at hc
      exact hc.eventually hnear
    have key : leviForm (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y) := by
      rw [leviForm_congr (u' := fun v => val (Ach y) (c.e.symm v) (pick ψ.isLB y).1.2)]
      · exact GlobalTheory.T.leviForm_graded_length_sub_log_unit_normSq F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2 c hy'
      · filter_upwards [hnear'] with v hv
        exact hindep _ _ hv.1 (Ach y) hv.2
    have e1 : c1W ψ ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y)) := rfl
    have e2 : grF E H x ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y)) := rfl
    rw [e1, e2]
    unfold HermFrame.ddc
    rw [key]

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundlesStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_graded_metrics_weights_on_line_bundles : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (gr : Root m → X.Dv), IsGraded E gr → IsMetricFr E H → ∀ x : Root m, ∃ (L : LB X.X) (r : L.ι → X.Fnˣ) (ψ : Weight X.str σ L), Presents (gr x) L r ∧ ψ.IsCInf ∧ c1W ψ = grF E H x := by
  first | exact @GlobalTheory.ChernCalc.graded_weight | exact GlobalTheory.ChernCalc.graded_weight | (intros; apply GlobalTheory.ChernCalc.graded_weight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsPullbackMetricFlagRefinement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsPullbackMetricFlagRefinement
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem contDiffOn_holoMap {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) : ContDiffOn ℂ ∞ p U := by
  rw [contDiffOn_piLp]
  intro i
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ U hU
    ((EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp)

theorem pull_chern_of_eventually {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} (A : HolAtlas M n)
    (A' : HolAtlas M' n') {r : Type} [Fintype r] [DecidableEq r] {f : M' → M} (hf : A.IsHolo A' f) (G : M → Matrix r r ℂ)
    (G' T : M' → Matrix r r ℂ) (p : A'.Pt) (c : A.ι) (hc : f p.pt ∈ (A.e c).source) (hG : SmoothUnitAt A G (f p.pt))
    (hT : HolUnitAt A' T p.pt) (h : ∀ᶠ z in 𝓝 p.pt, G' z = T z * G (f z) * (T z)ᴴ) (j : ℕ) :
    pull (fderiv ℂ (A.e c ∘ f ∘ p.ch.symm) p.crd) (A.chern G j ⟨(c, f p.pt), hc⟩ : Alt n) = (A'.chern G' j p : Alt n') := by
  have hp : p.pt ∈ p.ch.source := p.2
  have hinv : p.ch.symm p.crd = p.pt := p.ch.left_inv hp
  have hU : IsOpen (p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source)) :=
    p.ch.isOpen_inter_preimage_symm ((A.e c).open_source.preimage hf.1)
  have hmem : p.crd ∈ p.ch.target ∩ p.ch.symm ⁻¹' (f ⁻¹' (A.e c).source) :=
    ⟨p.ch.map_source hp, by rw [Set.mem_preimage, hinv]; exact hc⟩
  set ψ : V n' → V n := A.e c ∘ f ∘ p.ch.symm with hψ
  have hs : ContDiffAt ℂ ∞ ψ p.crd := (contDiffOn_holoMap hU (hf.2 p.1.1 c)).contDiffAt (hU.mem_nhds hmem)
  have hv : ψ p.crd = A.e c (f p.pt) := by simp only [hψ, Function.comp_apply, hinv]
  have hg : MContDiffAt ∞ (fun u => G ((A.e c).symm u)) (ψ p.crd) := hv ▸ (hG.2 c hc).self_of_nhds
  have hu : IsUnit (G ((A.e c).symm (ψ p.crd))).det := by rw [hv, (A.e c).left_inv hc]; exact hG.1
  have h1 := ((GlobalTheory.T.curvature_power_pullback_holomorphic n n' r (fun u => G ((A.e c).symm u)) ψ p.crd (hs.of_le (by norm_cast)) hg hu).2 j).2
  have hg' : MContDiffAt ∞ (fun x => G ((A.e c).symm (ψ x))) p.crd := fun a b =>
    (hg a b).comp p.crd (hs.restrict_scalars ℝ)
  have hTu : IsUnit (T (p.ch.symm p.crd)).det := by rw [hinv]; exact hT.1
  have hTd := hT.2 p.1.1 hp
  have ht : Tendsto p.ch.symm (𝓝 p.crd) (𝓝 p.pt) := by
    have := p.ch.continuousAt_symm (p.ch.map_source hp)
    rwa [ContinuousAt, p.ch.left_inv hp] at this
  have he : ∀ᶠ x in 𝓝 p.crd, G' (p.ch.symm x) =
      T (p.ch.symm x) * G ((A.e c).symm (ψ x)) * (T (p.ch.symm x))ᴴ := by
    filter_upwards [ht.eventually h, hU.mem_nhds hmem] with x hx hx'
    rw [hx]
    simp only [hψ, Function.comp_apply]
    rw [(A.e c).left_inv hx'.2]
  have h2 := (GlobalTheory.T.chernTransgression_forms_frame_invariant n' r _ _ (fun x => G' (p.ch.symm x)) (fun x => G' (p.ch.symm x)) (fun x => T (p.ch.symm x))
    (fun x => T (p.ch.symm x)) (fun x => T (p.ch.symm x)) p.crd hg' hu hg' hu hTd hTu hTd hTu hTd hTu
    (he.mono fun x hx => ⟨hx, hx⟩) j).2.1
  show pull _ (chernAt _ (A.e c (f p.pt)) j : Alt n) = (chernAt (fun v => G' (p.ch.symm v)) p.crd j : Alt n')
  rw [h2, h1, hv]

theorem pullback_chernF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ x : ι × ℕ, (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) (fld (atlas X σ) (chernF E H x)) = fld (atlas Y σ) (chernF E' (pullGram E H φ f hf) x) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH x
  funext p
  have hol := GlobalTheory.T.varietyComplexPointsMap_isHolomorphic F σ X Y f hf
  have hE := GlobalTheory.T.pulled_back_gram_matrices_independent_of_frame F σ X Y ι m E E' φ f hf hR H hH
  have hA := (E.nonempty (under (ptMap σ f hf p.pt))).choose_spec
  have hB := (E'.nonempty (under p.pt)).choose_spec
  have hP := hR.sub (under p.pt) _ hB _ (by
    have := hA
    exact (congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE p.pt).1).mp this) x.1
  refine pull_chern_of_eventually (atlas X σ) (atlas Y σ) hol (gramAt E H x.1 (ptMap σ f hf p.pt))
    (gramAt E' (pullGram E H φ f hf) x.1 p.pt)
    (fun z => (((E'.nonempty (under p.pt)).choose *
      (Mat.map (E.nonempty (under (ptMap σ f hf p.pt))).choose φ)⁻¹) x.1).map (ratVal · z)) p _ _
    (GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) _ _ hA x.1).1
    (GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ Y _ _ p.pt (fun i j => mem_O_ratOf.1 (hP.1 i j)) hP.2.1 (mem_O_ratOf.1 hP.2.2.1)) ?_ x.2
  filter_upwards [(hol.1.tendsto p.pt).eventually (GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m 0 E _ _ hA),
    GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ Y ι m m E' _ _ hB] with z h1 h2
  exact (hE z).2 _ ((congrArg (fun w => (E.nonempty (under (ptMap σ f hf p.pt))).choose ∈ E.S w) (hE z).1).mp h1) _ h2 x.1

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsPullbackMetricFlagRefinementStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernForms_pullback_metric_flag_refinement : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ x : ι × ℕ, (atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) (fld (atlas X σ) (chernF E H x)) = fld (atlas Y σ) (chernF E' (pullGram E H φ f hf) x) := by
  first | exact @GlobalTheory.ChernCalc.pullback_chernF | exact GlobalTheory.ChernCalc.pullback_chernF | (intros; apply GlobalTheory.ChernCalc.pullback_chernF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityChernPolynomialReEqChernPolyTopDensity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityChernPolynomialReEqChernPolyTopDensity
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernTopDens

variable {n : ℕ}

theorem coeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) (d : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun y => C c * X y) Q) d = c ^ (d.sum fun _ e => e) * AddMonoidAlgebra.coeff Q d := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    have : aeval (fun y => C c * X y) (monomial u a) = monomial u (c ^ (u.sum fun _ e => e) * a) := by
      rw [aeval_monomial, monomial_eq]
      simp only [mul_pow, Finsupp.prod_mul, algebraMap_eq]
      rw [Finsupp.prod, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum, C_mul, map_prod]
      simp only [map_pow]
      ring
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

section Rev

variable {r : Type} [Fintype r] [DecidableEq r]

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (M : Matrix r r A) :
    (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem charpolyRev_smul {A : Type} [CommRing A] (c : A) (M : Matrix r r A) :
    (c • M).charpolyRev = M.charpolyRev.comp (Polynomial.C c * Polynomial.X) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [Matrix.one_apply, h] <;> ring

theorem aeval_chernPoly (c : ℂ) (G : V n → Matrix r r ℂ) (v : V n) (k : ℕ) :
    aeval (fun y => C c * X y) (chernPoly G v k) = c ^ k • chernPoly G v k := by
  let ψ : MvPolynomial (Fin n × Fin n) ℂ →+* MvPolynomial (Fin n × Fin n) ℂ :=
    (aeval fun y => C c * X y : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ).toRingHom
  have e : ∀ p, aeval (fun y => C c * X y) p = ψ p := fun _ => rfl
  have hM : (-curvPoly G v).map ψ = (C c : MvPolynomial (Fin n × Fin n) ℂ) • (-curvPoly G v) := by
    refine Matrix.ext fun i j => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply, curvPoly, Matrix.of_apply, map_neg, map_sum,
      map_mul, smul_eq_mul, Finset.mul_sum, mul_neg, ← e, aeval_X, aeval_C, algebraMap_eq]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_)
    ring
  unfold chernPoly
  rw [e, ← Polynomial.coeff_map, ← charpolyRev_map, hM, charpolyRev_smul, Polynomial.comp_C_mul_X_coeff, smul_eq_C_mul,
    map_pow, mul_comm]

end Rev

theorem topCoeff_aeval_C_mul_X (c : ℂ) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun y => C c * X y) Q) = c ^ n * topCoeff Q := by
  unfold topCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hdeg : (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ).sum (fun _ e => e) = n := by
    change Finsupp.degree (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) = n
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  rw [coeff_aeval_C_mul_X, hdeg]
  ring

theorem kappa_div : kappa ^ n / (Complex.I / 2) ^ n = (((Real.pi ^ n)⁻¹ : ℝ) : ℂ) := by
  rw [← div_pow, Complex.ofReal_inv, Complex.ofReal_pow, ← inv_pow]
  congr 1
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  rw [kappa]
  field_simp

end GlobalTheory.ChernTopDens


open GlobalTheory.ChernTopDens in
theorem GlobalTheory.ChernCalc.dens_chernAt_re (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ)
    (v : V n) :
    (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re =
      chernTop R G v := by
  let Φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] Ev n := (aeval sym).comp (aeval fun y => C kappa * X y)
  have h1 : (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) =
      fun x => Φ (chernPoly (fun u => G u x.1) v x.2) := by
    funext x
    simp only [Φ, AlgHom.comp_apply, aeval_chernPoly, map_smul, chernAt]
  have h2 : aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) =
      aeval sym (aeval (fun y => C kappa * X y)
        (aeval (fun x : ι × ℕ => chernPoly (fun u => G u x.1) v x.2) R)) := by
    rw [h1, ← comp_aeval, AlgHom.comp_apply, aeval_map_algebraMap]
    rfl
  rw [h2, GlobalTheory.T.topDegreeDensityComplexForm_aeval_dzWedgeDzbar, topCoeff_aeval_C_mul_X, mul_div_right_comm, kappa_div, Complex.re_ofReal_mul]
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopDensityChernPolynomialReEqChernPolyTopDensityStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topDensity_chernPolynomial_re_eq_chernPolyTopDensity : ∀ (n : ℕ) (ι : Type) (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ) (G : V n → Mat m ℂ) (v : V n), (dens ((aeval (fun x : ι × ℕ => chernAt (fun u => G u x.1) v x.2) (R.map (algebraMap ℝ ℂ)) : Ev n) : Alt n)).re = chernTop R G v := by
  first | exact @GlobalTheory.ChernCalc.dens_chernAt_re | exact GlobalTheory.ChernCalc.dens_chernAt_re | (intros; apply GlobalTheory.ChernCalc.dens_chernAt_re <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPart
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

open GlobalTheory.ChartGlue

namespace GlobalTheory.ChernCalc

theorem chartMeas_congr_source {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] {n : ℕ}
    (e : OpenPartialHomeomorph Y (V n)) {ρ ρ' : Y → ENNReal} (h : ∀ y ∈ e.source, ρ y = ρ' y) :
    chartMeas e ρ = chartMeas e ρ' := by
  unfold chartMeas
  congr 1
  refine withDensity_congr_ae ?_
  refine (ae_restrict_iff' e.open_target.measurableSet).2 (Eventually.of_forall fun v hv => ?_)
  exact h _ (e.map_target hv)

theorem chernTopPart_eq_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  intro F _ σ X ι m E H R ε
  unfold chernTopPart HolAtlas.part glueMeas
  refine iSup_congr fun c => chartMeas_congr_source _ fun y hy => ?_
  have hx : (atlas X σ).loc (evalF (atlas X σ) (chernF E H) R) c (c.e y) =
      evalF (atlas X σ) (chernF E H) R ⟨(c, y), hy⟩ :=
    HolAtlas.loc_crd (atlas X σ) (evalF (atlas X σ) (chernF E H) R) ⟨(c, y), hy⟩
  show ENNReal.ofReal (_ * chernTop _ _ _) = ENNReal.ofReal (_ * (dens ((atlas X σ).loc _ c (c.e y))).re)
  rw [hx]
  congr 2
  exact (GlobalTheory.T.topDensity_chernPolynomial_re_eq_chernPolyTopDensity X.dim ι m R (fun v => H (E.nonempty (under y)).choose (c.e.symm v)) (c.e y)).symm

end GlobalTheory.ChernCalc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPartStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m 0) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), ∀ (R : MvPolynomial (ι × ℕ) ℝ) (ε : ℤˣ), chernTopPart E H R ε = (atlas X σ).part (evalF (atlas X σ) (chernF E H) R) ε := by
  first | exact @GlobalTheory.ChernCalc.chernTopPart_eq_part | exact GlobalTheory.ChernCalc.chernTopPart_eq_part | (intros; apply GlobalTheory.ChernCalc.chernTopPart_eq_part <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackRealPolynomialEvenFormFields
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackRealPolynomialEvenFormFields
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem algHom_aeval_ev {m m' : ℕ} {ι : Type} (φ : Alt m →ₐ[ℂ] Alt m') (u : ι → Ev m) (u' : ι → Ev m')
    (h : ∀ i, φ (u i : Alt m) = (u' i : Alt m')) (P : MvPolynomial ι ℝ) :
    φ ((aeval u (P.map (algebraMap ℝ ℂ)) : Ev m) : Alt m) = ((aeval u' (P.map (algebraMap ℝ ℂ)) : Ev m') : Alt m') := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.map_C, MvPolynomial.aeval_C]
    exact φ.commutes _
  | add p q hp hq =>
    simp only [map_add (f := _), Subalgebra.coe_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, Subalgebra.coe_mul, hp, h]

theorem pullback_evalF : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  intro M M' _ _ n n' A A' g ι w w' hw P
  funext x
  exact algHom_aeval_ev _ _ _ (fun i => congrFun (hw i) x) P

end GlobalTheory.LineForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackRealPolynomialEvenFormFieldsStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_real_polynomial_even_form_fields : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n') (g : M' → M) (ι : Type) (w : ι → A.Pt → Ev n) (w' : ι → A'.Pt → Ev n'), (∀ i, A.pullback A' g (fld A (w i)) = fld A' (w' i)) → ∀ P : MvPolynomial ι ℝ, A.pullback A' g (evalF A w P) = evalF A' w' P := by
  first | exact @GlobalTheory.LineForm.pullback_evalF | exact GlobalTheory.LineForm.pullback_evalF | (intros; apply GlobalTheory.LineForm.pullback_evalF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernWeilNumbersOfDegreeEqChernIntegral
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex :
    GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  intro h F _ σ X Y ι _ m E E' φ f gr hR hG H hH R
  have hD : GlobalTheory.Published.ChernDegree := GlobalTheory.T.degreeEqChernFormIntegral_of_complex_case h
  have hf : f ≫ X.str = Y.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hform := GlobalTheory.T.isForm_evalRealPoly_chernForms_flaggedMetric F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) R
  have hM := GlobalTheory.T.isFlaggedBundleMetric_pullGram_refinement F σ X Y ι m E E' φ f hf hR H hH
  have hu : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  choose L r ψ h1 h2 h3 using GlobalTheory.T.flag_graded_metrics_weights_on_line_bundles F σ Y ι m E' _ gr hG hM
  have e : grF E' (pullGram E H φ f hf) = fun x => c1W (ψ x) := funext fun x => (h3 x).symm
  unfold HasChernIntegral
  rw [hu]
  simp only [GlobalTheory.T.chernTopFormSignedMeasure_eq_atlas_part F σ X ι m E H R]
  refine ⟨fun ε => ?_, ?_⟩
  · have := (GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous _ _ (atlas X σ)).1 _ hform ε
    exact measure_ne_top _ _
  · refine (GlobalTheory.T.flagBundle_fibreIntegral_pullback_mul_fibreClass F σ X Y ι m E E' φ f hf hR H hH _ hform).symm.trans ?_
    rw [GlobalTheory.T.pullback_real_polynomial_even_form_fields _ _ _ _ _ _ _ _ _ _ (GlobalTheory.T.chernForms_pullback_metric_flag_refinement F σ X Y ι m E E' φ f hf hR H hH) R,
      GlobalTheory.T.integral_chernForms_eq_esymm_gradedForms_flag F σ Y ι m E' _ hM, e]
    exact GlobalTheory.T.integral_chernFormPoly_eq_intersectionNumber hD F σ Y _ gr L r ψ (fun a => ⟨h1 a, h2 a⟩) _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernWeilNumbersOfDegreeEqChernIntegralStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernWeilNumbers_of_degree_eq_chernIntegral : GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  first | exact @GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex | exact GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex | (intros; apply GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex <;> assumption)
end
