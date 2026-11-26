module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteGroupActionPreservesPrincipalFlagMultiplic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmoothFunctionsOfClosedRightDerivatives
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianActionColumnBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationRationalTranslateSubstitution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBound
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.Size.Translate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wordSum_succ {ι X : Type} [Fintype ι] (A : ι → X → X) (p : X → ℝ≥0∞) (d : ℕ) (x : X) :
    wordSum A p (d + 1) x = p x + ∑ i, wordSum A p d (A i x) := by
  classical
  unfold wordSum
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [wordAct_nil]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_equiv (Fin.snocEquiv fun _ => ι) _ _ fun q => ?_
    change _ = p (wordAct A (List.ofFn (fun i => (Fin.snoc (α := fun _ => ι) q.2 q.1 i : ι))) x)
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, wordAct_append, wordAct_cons, wordAct_nil]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem growthSob_sum_le {α : Type} (s : Finset α) (f : α → GA D V → ℂ) (hf : ∀ a, f a ∈ SmFun θ V) (d N : ℕ) :
    growthSob θ V d N (∑ a ∈ s, f a) ≤ ∑ a ∈ s, growthSob θ V d N (f a) := by
  classical
  induction s using Finset.induction_on
  · simpa using growthSob_smul (θ := θ) (φ := (0 : GA D V → ℂ)) (0 : ℂ) d N
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (growthSob_add_le (hf a) (Submodule.sum_mem _ fun b _ => hf b) d N).trans (add_le_add le_rfl ih)

theorem growthSob_RderC_le (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : ℝ≥0∞} (hB : ∀ a b, ‖Z a b‖ₑ ≤ B) (d N : ℕ) :
    growthSob θ V d N (RderC θ V τ Z φ) ≤
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) * (B * growthSob θ V (d + 1) N φ) := by
  rw [RderC_eq_sum_glDer hθ hs τ Z]
  have hmem : ∀ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ ∈ SmFun θ V := fun a =>
    (SmFun θ V).smul_mem _ ((linOnSm_RderC (θ := θ) τ (Matrix.single a.1 a.2 1)).mem φ hs)
  refine (growthSob_sum_le Finset.univ _ hmem d N).trans ?_
  calc ∑ a : Fin V.rank × Fin V.rank, growthSob θ V d N (Z a.1 a.2 • glDer θ V (τ, a) φ)
      ≤ ∑ _a : Fin V.rank × Fin V.rank, B * growthSob θ V (d + 1) N φ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [growthSob_smul]
        exact mul_le_mul' (hB a.1 a.2)
          (wordSum_letter_le (A := glDer θ V) (p := growthSize V N) d (τ, a) φ)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem growthSize_rTr_le (h : GA D V) (N : ℕ) (φ : GA D V → ℂ) :
    growthSize V N (rTr V h φ) ≤ ENNReal.ofReal (height V h) ^ N * growthSize V N φ := by
  obtain ⟨h1, -, -, hmul, -⟩ := height_laws V
  unfold growthSize
  refine iSup_le fun g => ?_
  have hgpos : 0 < height V g := lt_of_lt_of_le one_pos (h1 g)
  have hhpos : 0 < height V h := lt_of_lt_of_le one_pos (h1 h)
  have hghpos : 0 < height V (g * h) := lt_of_lt_of_le one_pos (h1 (g * h))
  have hq : 0 ≤ ‖φ (g * h)‖ / height V (g * h) ^ N := div_nonneg (norm_nonneg _) (pow_pos hghpos N).le
  have key : ‖rTr V h φ g‖ / height V g ^ N ≤ height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) := by
    change ‖φ (g * h)‖ / height V g ^ N ≤ _
    rw [div_le_iff₀ (pow_pos hgpos N)]
    have hp : height V (g * h) ^ N ≤ (height V g * height V h) ^ N := pow_le_pow_left₀ hghpos.le (hmul g h) N
    calc ‖φ (g * h)‖ = ‖φ (g * h)‖ / height V (g * h) ^ N * height V (g * h) ^ N :=
          (div_mul_cancel₀ _ (pow_pos hghpos N).ne').symm
      _ ≤ ‖φ (g * h)‖ / height V (g * h) ^ N * (height V g * height V h) ^ N := mul_le_mul_of_nonneg_left hp hq
      _ = height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) * height V g ^ N := by ring
  calc ENNReal.ofReal (‖rTr V h φ g‖ / height V g ^ N)
      ≤ ENNReal.ofReal (height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N)) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (height V h) ^ N * ENNReal.ofReal (‖φ (g * h)‖ / height V (g * h) ^ N) := by
        rw [ENNReal.ofReal_mul (pow_pos hhpos N).le, ENNReal.ofReal_pow hhpos.le]
    _ ≤ ENNReal.ofReal (height V h) ^ N * ⨆ g', ENNReal.ofReal (‖φ g'‖ / height V g' ^ N) :=
        by gcongr; exact le_iSup (fun g' => ENNReal.ofReal (‖φ g'‖ / height V g' ^ N)) (g * h)

theorem exists_adAt_le (hθ : IsInfFam θ) (V : HSp D) : ∃ C : ℝ≥0, ∀ (h : GA D V) τ a b c d,
    ‖adAt θ h τ (Matrix.single a b 1) c d‖ₑ ≤ C * ENNReal.ofReal (height V h) ^ 2 := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  refine ⟨Real.toNNReal (C ^ 2), fun h τ a b c d => ?_⟩
  have hent : ∀ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖ ≤
      C * height V h := by
    intro i j
    refine le_trans ?_ (hC h)
    calc ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖
        ≤ ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ τ', ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
      _ = _ := rfl
  have hcomp : adAt θ h τ (Matrix.single a b 1) c d =
      infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a * infMat D.sp.cm.sig V.gram (θ τ) h b d := by
    simp [adAt, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hx := hent c a
  have hy := hent b d
  have hx' : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h c a)]
  have hy' : ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ b d)]
  have hht : 0 ≤ height V h := le_trans zero_le_one ((height_laws V).1 h)
  have hreal : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤
      C ^ 2 * height V h ^ 2 := by
    calc _ ≤ (C * height V h) * (C * height V h) :=
          mul_le_mul hx' hy' (norm_nonneg _) ((norm_nonneg _).trans hx')
      _ = C ^ 2 * height V h ^ 2 := by ring
  rw [hcomp, ← ofReal_norm_eq_enorm, norm_mul]
  calc ENNReal.ofReal (‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖)
      ≤ ENNReal.ofReal (C ^ 2 * height V h ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg C), ENNReal.ofReal_pow hht]; rfl

private theorem rderC_rTr' (hθ : IsInfFam θ) (h : GA D V) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (rTr V h φ) = rTr V h (RderC θ V τ (adAt θ h τ Z) φ) := by
  obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have hZ := (GlobalTheory.SmoothAutCheck.parts_sum V τ Z).symm
  set X := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hXdef
  set Y := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hYdef
  have hsum : adAt θ h τ Z = adAt θ h τ X + Complex.I • adAt θ h τ Y := by
    conv_lhs => rw [hZ]
    simp only [adAt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum, RderC_add hθ hs, RderC_smul hθ hs,
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hX),
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hY)]
  change Rder θ V τ X (rTr V h φ) + Complex.I • Rder θ V τ Y (rTr V h φ) = _
  rw [Rder_rTr_adelic hθ h hX, Rder_rTr_adelic hθ h hY]
  rfl

theorem exists_growthSob_rTr_le (hθ : IsInfFam θ) (V : HSp D) (N d : ℕ) : ∃ C : ℝ≥0, ∀ h ∈ GinfC V, ∀ φ ∈ SmFun θ V,
    growthSob θ V d N (rTr V h φ) ≤ C * ENNReal.ofReal (height V h) ^ (N + 2 * d) * growthSob θ V d N φ := by
  obtain ⟨C₁, hC₁⟩ := exists_adAt_le hθ V
  induction d with
  | zero =>
    refine ⟨1, fun h _ φ _ => ?_⟩
    simpa [growthSob, wordSum_zero] using growthSize_rTr_le h N φ
  | succ d ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨1 + (Fintype.card (D.what₂.Tau × Fin V.rank × Fin V.rank) : ℝ≥0) * C *
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0) * C₁, fun h hh φ hs => ?_⟩
    have hT : 1 ≤ ENNReal.ofReal (height V h) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ((height_laws V).1 h)
    have hS0 : growthSize V N φ ≤ growthSob θ V (d + 1) N φ :=
      le_wordSum (A := glDer θ V) (p := growthSize V N) (l := []) (Nat.zero_le _) φ
    have hterm : ∀ a : D.what₂.Tau × Fin V.rank × Fin V.rank,
        growthSob θ V d N (glDer θ V a (rTr V h φ)) ≤
          C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) := by
      intro a
      have e : glDer θ V a (rTr V h φ) =
          rTr V h (RderC θ V a.1 (adAt θ h a.1 (Matrix.single a.2.1 a.2.2 1)) φ) :=
        rderC_rTr' hθ h hs a.1 _
      rw [e]
      refine (hC h hh _ ((linOnSm_RderC (θ := θ) a.1 _).mem φ hs)).trans ?_
      gcongr
      exact growthSob_RderC_le hθ hs a.1 (fun b c => hC₁ h a.1 a.2.1 a.2.2 b c) d N
    have hpow : ENNReal.ofReal (height V h) ^ N ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) :=
      pow_le_pow_right₀ hT (by omega)
    have e0 : growthSob θ V (d + 1) N (rTr V h φ) =
        growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ)) :=
      wordSum_succ _ _ _ _
    rw [e0]
    calc growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ))
        ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) * growthSob θ V (d + 1) N φ +
          ∑ _a : D.what₂.Tau × Fin V.rank × Fin V.rank, C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) :=
          add_le_add ((growthSize_rTr_le h N φ).trans (mul_le_mul' hpow hS0))
            (Finset.sum_le_sum fun a _ => hterm a)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring

theorem growthSob_rTr_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (d N : ℕ), ∃ (C : NNReal) (m : ℕ),
    ∀ h ∈ GinfC V, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V d N (rTr V h φ) ≤
      (C : ENNReal) * ENNReal.ofReal (GlobalTheory.Grow.height V h ^ m) * GlobalTheory.Size.growthSob θ V d N φ := by
  intro D θ hθ V d N
  obtain ⟨C, hC⟩ := exists_growthSob_rTr_le hθ V N d
  refine ⟨C, N + 2 * d, fun h hh φ hφ => ?_⟩
  rw [ENNReal.ofReal_pow (le_trans zero_le_one ((height_laws V).1 h))]
  exact hC h hh φ hφ

end GlobalTheory.Size.Translate

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModerateGrowthSobolevSizeRightTranslatePolyBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moderateGrowthSobolevSize_rightTranslate_polyBound : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (d N : ℕ), ∃ (C : NNReal) (m : ℕ), ∀ h ∈ GinfC V, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V d N (rTr V h φ) ≤ (C : ENNReal) * ENNReal.ofReal (GlobalTheory.Grow.height V h ^ m) * GlobalTheory.Size.growthSob θ V d N φ := by
  first | exact @GlobalTheory.Size.Translate.growthSob_rTr_le | exact GlobalTheory.Size.Translate.growthSob_rTr_le | (intros; apply GlobalTheory.Size.Translate.growthSob_rTr_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteLeOfGKStableDiscreteSeriesModel
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HCModIrred

open GlobalTheory.TypeSum Formalism.REAL Formalism.MainNotions.S
open scoped InnerProductSpace

section Model

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mem_of_dense (h : Std ε σ) {W : Submodule ℂ H} (hd : Dense (W : Set H))
    (hW : ∀ w ∈ W, IsKFin ε σ w) (hK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W) {v : H} (hv : IsKFin ε σ v) :
    v ∈ W := by
  obtain ⟨c1, c2, c3, c4⟩ := kCoef_kAvg n ε H σ h.1
  have havgW : ∀ e : KG ε → ℂ, Continuous e → ∀ x ∈ W, kAvg ε σ e x ∈ W := by
    intro e he x hx
    obtain ⟨S, hS, hxS, hKS⟩ := hW x hx
    haveI := hS
    haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W
    have hKSW : IsKStableOn ε σ (S ⊓ W) := fun g hg y hy =>
      Submodule.mem_inf.2 ⟨hKS g hg y (Submodule.mem_inf.1 hy).1, hK g hg y (Submodule.mem_inf.1 hy).2⟩
    exact (Submodule.mem_inf.1 (c4 e he _ inferInstance hKSW x (Submodule.mem_inf.2 ⟨hxS, hx⟩))).2
  have hrange : ∀ e : KG ε → ℂ, KFinFun ε e → Continuous e → ∀ w, kAvg ε σ e w ∈ W := by
    intro e he hc w
    obtain ⟨m, b, c, -, -, -, hbc⟩ := kAvg_finite_rank n ε H σ h e he
    obtain ⟨Q, hQ⟩ := c3 e hc
    let F : Submodule ℂ H := Submodule.span ℂ (Set.range b)
    haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
    haveI : FiniteDimensional ℂ (W ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_inf_right W F
    have hcl : IsClosed (Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H)) :=
      (Submodule.closed_of_finiteDimensional _).preimage Q.continuous
    have hsub : (W : Set H) ⊆ Q ⁻¹' ((W ⊓ F : Submodule ℂ H) : Set H) := by
      intro x hx
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [hQ]; exact havgW e hc x hx
      · rw [hQ, hbc]
        exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    have := closure_minimal hsub hcl (hd w)
    rw [← hQ]
    exact (Submodule.mem_inf.1 this).1
  obtain ⟨S, hS, hvS, hKS⟩ := hv
  haveI := hS
  haveI : FiniteDimensional ℂ (S ⊓ W : Submodule ℂ H) := Submodule.finiteDimensional_inf_left S W
  obtain ⟨w, hw, y, hy, hvwy⟩ := (S ⊓ W).exists_add_mem_mem_orthogonal v
  have hyS : y ∈ S := by
    have := S.sub_mem hvS (Submodule.mem_inf.1 hw).1
    rwa [hvwy, add_sub_cancel_left] at this
  have hy0 : y = 0 := by
    by_contra hy0
    have hk := c1 y ⟨S, hS, hyS, hKS⟩
    have hc : Continuous fun k : KG ε => star ⟪y, σ (toMK k) y⟫_ℂ := by
      obtain ⟨F, -, h1, h2, -⟩ := hk
      exact h2 _ h1
    exact c2 y hy0 (Submodule.inner_left_of_mem_orthogonal
      (Submodule.mem_inf.2 ⟨c4 _ hc S hS hKS y hyS, hrange _ hk hc y⟩) hy)
  rw [hvwy, hy0, add_zero]
  exact (Submodule.mem_inf.1 hw).2

theorem inner_exp_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {W : Submodule ℂ H} (hW : ∀ w ∈ W, IsKFin ε σ w)
    {X : Matrix (Fin n) (Fin n) ℂ} (hXg : inG ε X) (hX : ∀ w ∈ W, dRep σ X w ∈ W)
    {a : H} (ha : a ∈ W) {y : H} (hy : y ∈ Wᗮ) (t : ℝ) :
    ⟪y, σ (NormedSpace.exp (t • X)) a⟫_ℂ = 0 := by
  have hXl : X ∈ GlobalTheory.SmoothGlob.lieSet ε := hXg
  have hsplit : ∀ s t : ℝ, NormedSpace.exp (s • X) = NormedSpace.exp (t • X) * NormedSpace.exp ((s - t) • X) := by
    intro s t
    rw [← Matrix.exp_add_of_commute _ _ ((Commute.refl X).smul_left t |>.smul_right (s - t))]
    congr 1
    rw [← add_smul]; congr 1; ring
  have hderiv : ∀ v, IsKFin ε σ v → ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (σ (NormedSpace.exp (t • X)) (dRep σ X v)) t := by
    intro v hv t
    have han := (hHC.analytic hU hI hv).analytic_exp (one_mem_UJ ε) hXg 0
    simp only [one_mul] at han
    have h0 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp (s • X)) v) (dRep σ X v) 0 :=
      han.differentiableAt.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s - t) • X)) v) (dRep σ X v) t := by
      have := HasDerivAt.comp_sub_const (f := fun s : ℝ => σ (NormedSpace.exp (s • X)) v) t t (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((σ (NormedSpace.exp (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show σ (NormedSpace.exp (s • X)) v = σ (NormedSpace.exp (t • X)) (σ (NormedSpace.exp ((s - t) • X)) v)
    rw [hsplit s t, sigma_mul hU (exp_mem_UJ hXl t) (exp_mem_UJ hXl (s - t))]
  have hmem : ∀ k : ℕ, (dRep σ X)^[k] a ∈ W := by
    intro k
    induction k with
    | zero => exact ha
    | succ k ih => rw [Function.iterate_succ_apply']; exact hX _ ih
  let f : ℕ → ℝ → ℂ := fun k s => ⟪y, σ (NormedSpace.exp (s • X)) ((dRep σ X)^[k] a)⟫_ℂ
  have hf : ∀ k s, HasDerivAt (f k) (f (k + 1) s) s := by
    intro k s
    have h := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hderiv _ (hW _ (hmem k)) s)
    simp only [f, Function.iterate_succ_apply']
    exact h
  have hit : ∀ k, iteratedDeriv k (f 0) = f k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [iteratedDeriv_succ, ih]; funext s; exact (hf k s).deriv
  have hA : AnalyticOnNhd ℝ (f 0) Set.univ := by
    intro s _
    have := ((hHC.analytic hU hI (hW a ha)).clm ((innerSL ℂ y).restrictScalars ℝ)).analytic_exp (one_mem_UJ ε) hXg s
    simp only [one_mul] at this
    exact this
  have h0 : ∀ k, f k 0 = 0 := by
    intro k
    simp only [f, zero_smul, NormedSpace.exp_zero, sigma_one hU]
    exact Submodule.inner_left_of_mem_orthogonal (hmem k) hy
  have htop : analyticOrderAt (f 0) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro m
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA 0 trivial)]
    intro i _
    rw [hit, h0]
  exact hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0)
    (analyticOrderAt_eq_top.mp htop) (Set.mem_univ t)

theorem dense_of_stable (hHC : GlobalTheory.Published.HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {W : Submodule ℂ H} (hW : ∀ w ∈ W, IsKFin ε σ w)
    (hX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W) (hK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W) (h0 : W ≠ ⊥) :
    Dense (W : Set H) := by
  have hexp : ∀ X, inG ε X → ∀ x ∈ W.topologicalClosure, σ (NormedSpace.exp X) x ∈ W.topologicalClosure := by
    intro X hXg x hx
    have hW1 : ∀ a ∈ W, σ (NormedSpace.exp X) a ∈ W.topologicalClosure := by
      intro a ha
      rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
      intro y hy
      have := inner_exp_eq_zero hHC hU hI hW hXg (hX X hXg) ha hy 1
      rwa [one_smul] at this
    have hcl : IsClosed ((σ (NormedSpace.exp X)) ⁻¹' (W.topologicalClosure : Set H)) :=
      (Submodule.isClosed_topologicalClosure _).preimage (ContinuousLinearMap.continuous _)
    exact closure_minimal (fun a ha => hW1 a ha) hcl hx
  have hKc : ∀ k ∈ Kset ε, ∀ x ∈ W.topologicalClosure, σ k x ∈ W.topologicalClosure := fun k hk x hx =>
    map_mem_closure (σ k).continuous hx (hK k hk)
  have hinv : ∀ g ∈ UJset ε, ∀ x ∈ W.topologicalClosure, σ g x ∈ W.topologicalClosure := by
    intro g hg x hx
    obtain ⟨k, P, hk, hP, rfl⟩ := (Formalism.REAL.polar_decomposition_holds n ε).1 g hg
    have hPl : P ∈ GlobalTheory.SmoothGlob.lieSet ε := hP.1
    have hPe : NormedSpace.exp P ∈ UJset ε := by simpa using exp_mem_UJ hPl 1
    rw [sigma_mul hU (K_le_UJ hk) hPe]
    exact hKc k hk _ (hexp P hP.1 x hx)
  rcases hI _ (Submodule.isClosed_topologicalClosure W) hinv with h | h
  · exact absurd (le_bot_iff.1 (h ▸ W.le_topologicalClosure)) h0
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

end Model

theorem kFin_le_of_stable : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : DSModel V S) (τ : D.what₂.Tau) (W : Submodule ℂ (M.H τ)), W ≤ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ →
    (∀ X ∈ lieAt V τ, ∀ w ∈ W, dRep (M.rep τ) X w ∈ W) →
    (∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ, ∀ w ∈ W, M.rep τ k w ∈ W) → W ≠ ⊥ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ ≤ W := by
  intro hHC D V S M τ W hWk hX hK h0
  obtain ⟨hc, -, hU, hI, -⟩ := M.ds τ
  haveI := hc
  have hfr : IsUnit (M.fr τ) := M.fr_unit τ
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hfr
  have hW : ∀ w ∈ W, IsKFin (M.ε τ) (M.σ τ) w := fun w hw => hWk hw
  have hX' : ∀ X, inG (M.ε τ) X → ∀ w ∈ W, dRep (M.σ τ) X w ∈ W := by
    intro X hXg w hw
    have hXg' : Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X = 0 := hXg
    have hmem : (M.fr τ)⁻¹ * X * M.fr τ ∈ lieAt V τ := by
      show ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * gramAt D V τ + gramAt D V τ * ((M.fr τ)⁻¹ * X * M.fr τ) = 0
      rw [← M.fr_gram τ]
      have h1 : ((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ = 1 := by
        rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
      calc ((M.fr τ)⁻¹ * X * M.fr τ)ᴴ * ((M.fr τ)ᴴ * Jm (M.ε τ) * M.fr τ) +
            (M.fr τ)ᴴ * Jm (M.ε τ) * M.fr τ * ((M.fr τ)⁻¹ * X * M.fr τ)
          = (M.fr τ)ᴴ * Xᴴ * (((M.fr τ)⁻¹)ᴴ * (M.fr τ)ᴴ) * Jm (M.ε τ) * M.fr τ +
            (M.fr τ)ᴴ * Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) * X * M.fr τ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (M.fr τ)ᴴ * (Xᴴ * Jm (M.ε τ) + Jm (M.ε τ) * X) * M.fr τ := by
            rw [h1, Matrix.mul_nonsing_inv _ hd]
            simp only [Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = 0 := by rw [hXg']; simp
    have e : dRep (M.rep τ) ((M.fr τ)⁻¹ * X * M.fr τ) w = dRep (M.σ τ) X w := by
      unfold dRep
      congr 1
      funext t
      rw [DSModel.rep, GlobalTheory.SmVec.exp_conj_inv hfr X t]
      congr 2
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    rw [← e]
    exact hX _ hmem w hw
  have hK' : ∀ k ∈ Kset (M.ε τ), ∀ w ∈ W, M.σ τ k w ∈ W := by
    intro k hk w hw
    have e : M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ = k := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    have hm : (M.fr τ)⁻¹ * k * M.fr τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt M τ := by
      show M.fr τ * ((M.fr τ)⁻¹ * k * M.fr τ) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)
      rw [e]; exact hk
    have := hK _ hm w hw
    rwa [DSModel.rep, e] at this
  have hdense := dense_of_stable hHC hU hI hW hX' hK' h0
  have hstd := GlobalTheory.TypeSum.std_of_isDS hHC (M.ds τ)
  intro v hv
  exact mem_of_dense hstd hdense hW hK' hv

end GlobalTheory.HCModIrred

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlaces
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix Topology

noncomputable section
namespace GlobalTheory.SqCls

theorem finite_units_quot_sq_field {k : Type} [NontriviallyNormedField k] [CompleteSpace k] [ProperSpace k]
    (h2 : (2 : k) ≠ 0) (K : Type) [Field K] [Algebra k K] [FiniteDimensional k K] :
    Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) := by
  classical
  set S := (powMonoidHom 2 : Kˣ →* Kˣ).range with hS
  let V := Fin (Module.finrank k K) → k
  let e : K ≃ₗ[k] V := (Module.finBasis k K).equivFun
  let B : V →ₗ[k] V →ₗ[k] V :=
    ((LinearMap.mul k K).compl₁₂ (e.symm : V →ₗ[k] K) (e.symm : V →ₗ[k] K)).compr₂ (e : K →ₗ[k] V)
  have hB : ∀ a b, B a b = e (e.symm a * e.symm b) := fun a b => rfl
  have hsq := eventually_exists_sq_normed h2 B (e := e 1) (fun v => by simp [hB]) (fun v => by simp [hB])
  have key : ∀ y : Kˣ, ∀ᶠ a in 𝓝 (e y), ∀ g : Kˣ, e g = a → y⁻¹ * g ∈ S := by
    intro y
    let f : V →ₗ[k] V := B (e (y⁻¹ : Kˣ))
    have hf : Continuous f := f.continuous_of_finiteDimensional
    have hfy : f (e y) = e 1 := by simp [f, hB]
    have := (hf.tendsto (e y)).eventually (hfy ▸ hsq)
    filter_upwards [this] with a ⟨z, hz⟩ g hg
    have h1 : ((y⁻¹ : Kˣ) : K) * g = e.symm z * e.symm z := by
      apply e.injective
      rw [← hB, hz, ← hg]
      simp [f, hB]
    have hz0 : e.symm z ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1
      exact (mul_ne_zero (Units.ne_zero _) (Units.ne_zero g)) h1
    refine ⟨Units.mk0 _ hz0, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [sq, ← h1]
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one k
  set q : ℝ := ‖c‖ ^ 2 with hq
  have hq0 : 0 < q := by positivity
  have hq1 : q < 1 := by rw [hq]; nlinarith
  set C : Set V := Metric.closedBall 0 1 ∩ {b | q ≤ ‖b‖} with hC
  have hCc : IsCompact C := (isCompact_closedBall 0 1).inter_right (isClosed_le continuous_const continuous_norm)
  have hCne : ∀ b ∈ C, e.symm b ≠ 0 := by
    intro b hb h0
    have : b = 0 := by simpa using congrArg e h0
    have := hb.2
    simp_all
  let y : V → Kˣ := fun b => if h : e.symm b ≠ 0 then Units.mk0 _ h else 1
  have hy : ∀ b ∈ C, e (y b) = b := fun b hb => by
    simp only [y, dif_pos (hCne b hb), Units.val_mk0, LinearEquiv.apply_symm_apply]
  let U : V → Set V := fun b => {a | ∀ g : Kˣ, e g = a → (y b)⁻¹ * g ∈ S}
  have hU : ∀ b ∈ C, U b ∈ 𝓝 b := fun b hb => by
    have := key (y b)
    rw [hy b hb] at this
    exact this
  obtain ⟨t, htC, hcov⟩ := hCc.elim_nhds_subcover U hU
  refine Finite.of_surjective (fun b : t => (QuotientGroup.mk (y b.1) : Kˣ ⧸ S)) ?_
  intro x
  induction x using QuotientGroup.induction_on with
  | H g =>
  have ha : 0 < ‖e g‖ := norm_pos_iff.2 (fun h => Units.ne_zero g (e.injective (h.trans (map_zero e).symm)))
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow ha (one_lt_inv_iff₀.2 ⟨hq0, hq1⟩)
  let u : kˣ := Units.mk0 c (norm_pos_iff.1 hc0) ^ (n + 1)
  let w : Kˣ := Units.map (algebraMap k K : k →* K) u
  have hnorm : ‖e (w ^ 2 * g : Kˣ)‖ = q ^ (n + 1) * ‖e g‖ := by
    have : ((w ^ 2 * g : Kˣ) : K) = ((u : k) ^ 2) • (g : K) := by
      simp [w, Algebra.smul_def]
    rw [this, map_smul, norm_smul, norm_pow]
    congr 1
    simp only [u, Units.val_zpow_eq_zpow_val, Units.val_mk0, norm_zpow, hq]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  have hmem : e (w ^ 2 * g : Kˣ) ∈ C := by
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall_zero_iff, hnorm]
      have := mul_le_mul_of_nonneg_left hn2 (zpow_nonneg hq0.le (n + 1))
      rwa [inv_zpow', ← zpow_add₀ hq0.ne', add_neg_cancel, zpow_zero] at this
    · show q ≤ ‖e (w ^ 2 * g : Kˣ)‖
      rw [hnorm]
      have := mul_lt_mul_of_pos_left hn1 (zpow_pos hq0 (n + 1))
      rw [inv_zpow', ← zpow_add₀ hq0.ne', show n + 1 + -n = 1 by ring, zpow_one] at this
      exact this.le
  obtain ⟨b, hbt, hb⟩ := Set.mem_iUnion₂.1 (hcov hmem)
  refine ⟨⟨b, hbt⟩, ?_⟩
  have h3 := hb (w ^ 2 * g) rfl
  have h4 : w ^ 2 ∈ S := ⟨w, rfl⟩
  refine QuotientGroup.eq.2 ?_
  have := S.mul_mem h3 (S.inv_mem h4)
  rw [mul_comm (w ^ 2) g] at this
  convert this using 1
  group

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

theorem finite_units_quot_sq_of_reduced {k : Type} [Field k]
    (hK : ∀ (K : Type) [Field K] [Algebra k K] [FiniteDimensional k K], Finite (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range))
    (R : Type) [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsReduced R] :
    Finite (Rˣ ⧸ (powMonoidHom 2 : Rˣ →* Rˣ).range) := by
  classical
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI hmax : ∀ I : MaximalSpectrum R, I.asIdeal.IsMaximal := fun I => I.isMaximal
  letI : ∀ I : MaximalSpectrum R, Field (R ⧸ I.asIdeal) := fun I => Ideal.Quotient.field _
  haveI : ∀ I : MaximalSpectrum R, FiniteDimensional k (R ⧸ I.asIdeal) := fun I =>
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap (Ideal.Quotient.mkₐ_surjective k _)
  haveI : Finite (MaximalSpectrum R) := inferInstance
  haveI : ∀ I : MaximalSpectrum R, Finite ((R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range) :=
    fun I => hK _
  let φ : Rˣ →* ∀ I : MaximalSpectrum R, (R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range :=
    Pi.monoidHom fun I => (QuotientGroup.mk' _).comp (Units.map (Ideal.Quotient.mk I.asIdeal : R →* R ⧸ I.asIdeal))
  have hker : φ.ker ≤ (powMonoidHom 2 : Rˣ →* Rˣ).range := by
    intro u hu
    have h1 : ∀ I : MaximalSpectrum R, ∃ w : (R ⧸ I.asIdeal)ˣ, w ^ 2 = Units.map (Ideal.Quotient.mk I.asIdeal : R →* _) u :=
      fun I => by
        have h' : (QuotientGroup.mk (Units.map (Ideal.Quotient.mk I.asIdeal : R →* R ⧸ I.asIdeal) u) :
            (R ⧸ I.asIdeal)ˣ ⧸ (powMonoidHom 2 : (R ⧸ I.asIdeal)ˣ →* _).range) = 1 :=
          congrFun ((MonoidHom.mem_ker).1 hu) I
        rw [QuotientGroup.eq_one_iff] at h'
        obtain ⟨w, hw⟩ := h'
        exact ⟨w, hw⟩
    choose w hw using h1
    let e := IsArtinianRing.equivPi R
    have he : ∀ x I, e x I = Ideal.Quotient.mk I.asIdeal x := fun x I => rfl
    let z : R := e.symm fun I => (w I : R ⧸ I.asIdeal)
    let z' : R := e.symm fun I => ((w I)⁻¹ : (R ⧸ I.asIdeal)ˣ)
    have hzz : z * z' = 1 := e.injective (funext fun I => by simp [z, z', map_mul])
    refine ⟨⟨z, z', hzz, by rw [mul_comm, hzz]⟩, ?_⟩
    ext
    apply e.injective
    funext I
    have := congrArg Units.val (hw I)
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at this
    have hz : Ideal.Quotient.mk I.asIdeal z = w I := by rw [← he, e.apply_symm_apply]
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    rw [he, he, map_pow, hz, this]
  haveI : Finite (Rˣ ⧸ φ.ker) := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).toEquiv.symm
  exact Finite.of_surjective (QuotientGroup.map _ _ (MonoidHom.id _) hker) (by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => exact ⟨QuotientGroup.mk g, rfl⟩)

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

def fixSub (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k] : Subalgebra k (k ⊗[F] Fld P) where
  carrier := {a | sigR k (star' P) a = a}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, ha, hb]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_add (f := _), ha, hb]
  algebraMap_mem' t := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem finite_cls_of_fixSub (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k]
    (h : Finite ((fixSub P k)ˣ ⧸ (powMonoidHom 2 : (fixSub P k)ˣ →* (fixSub P k)ˣ).range)) : Finite (Cls P k) := by
  classical
  have hfix : ∀ x : plusUnits P k, sigR k (star' P) (x.1 : k ⊗[F] Fld P) = x.1 := fun x =>
    congrArg Units.val x.2
  let φ : (fixSub P k)ˣ →* plusUnits P k :=
    { toFun := fun u => ⟨Units.map (fixSub P k).val.toMonoidHom u, Units.ext u.1.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hφ : Function.Surjective φ := by
    intro x
    have h1 := hfix x
    have h2 := hfix x⁻¹
    refine ⟨⟨⟨x.1.1, h1⟩, ⟨(x⁻¹ : plusUnits P k).1.1, h2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, ?_⟩
    · simp
    · simp
    · ext; rfl
  let ψ : (fixSub P k)ˣ →* Cls P k := (QuotientGroup.mk' _).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hsq : (powMonoidHom 2 : (fixSub P k)ˣ →* (fixSub P k)ˣ).range ≤ ψ.ker := by
    rintro _ ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ (u ^ 2)) : plusUnits P k ⧸ (norms P k).subgroupOf (plusUnits P k)) = 1
    rw [QuotientGroup.eq_one_iff, map_pow, Subgroup.mem_subgroupOf]
    refine ⟨(φ u).1, ?_⟩
    ext
    simp only [MonoidHom.mul_apply, MonoidHom.id_apply, Units.val_mul, Units.coe_map, MonoidHom.coe_coe,
      RingHom.toMonoidHom_eq_coe, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    rw [hfix (φ u), sq]
  exact Finite.of_surjective (QuotientGroup.lift _ ψ hsq) (by
    intro q
    obtain ⟨u, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk u, rfl⟩)

end GlobalTheory.SqCls

namespace GlobalTheory.SqCls

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}

theorem finite_cls_of_normed [NumberField F] [NumberField E] (P : PPol σ r) (k : Type) [NontriviallyNormedField k]
    [CompleteSpace k] [ProperSpace k] [Algebra F k] (hred : IsReduced (k ⊗[F] Fld P)) : Finite (Cls P k) := by
  have h2 : (2 : k) ≠ 0 := by
    have := (algebraMap F k).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at this
  haveI : Module.Finite F (Fld P) := Module.Finite.of_restrictScalars_finite ℚ F (Fld P)
  haveI : IsReduced (fixSub P k) := isReduced_of_injective (fixSub P k).val Subtype.val_injective
  exact finite_cls_of_fixSub P k
    (finite_units_quot_sq_of_reduced (k := k) (by intro K _ _ _; exact finite_units_quot_sq_field h2 K) (fixSub P k))

theorem finite_cls : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∀ v : HeightOneSpectrum (𝓞 F), Finite (Cls P (Fv F v))) ∧ ∀ w : InfinitePlace F, Finite (Cls P w.Completion) := by
  intro F E _ _ _ _ _ σ _ r P
  constructor
  · intro v
    obtain ⟨ψ, -, hb, -⟩ := GlobalTheory.TraceClasses.exists_finite_decomp F (Fld P)
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    haveI := GlobalTheory.LocalData.isLocalField v
    haveI : ProperSpace (v.adicCompletion F) :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (v.adicCompletion F)
    exact finite_cls_of_normed P (v.adicCompletion F) (isReduced_of_injective (Pi.ringHom (ψ v)) (hb v).1)
  · intro w
    obtain ⟨χ, -, hb⟩ := GlobalTheory.TraceClasses.exists_infinite_decomp F (Fld P)
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
            map_ofNat]
          simp⟩ }
    haveI : ProperSpace w.Completion :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    exact finite_cls_of_normed P w.Completion (isReduced_of_injective (Pi.ringHom (χ w)) (hb w).1)

end GlobalTheory.SqCls
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlacesStatement
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), (∀ v : HeightOneSpectrum (𝓞 F), Finite (Cls P (Fv F v))) ∧ ∀ w : InfinitePlace F, Finite (Cls P w.Completion) := by
  first | exact @GlobalTheory.SqCls.finite_cls | exact GlobalTheory.SqCls.finite_cls | (intros; apply GlobalTheory.SqCls.finite_cls <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.LeftHaar

def transposeCAE (D : D7) (m n : ℕ) : Mx D m n ≃ₜ+ Mx D n m where
  toAddEquiv := Matrix.transposeAddEquiv (Fin m) (Fin n) (AE D)
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

theorem map_left_unitary (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r))
    (hν : ν.IsAddHaarMeasure) :
    ν.map (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) = ν := by
  have hJ : IsHermND D.sp.cm.sig W.gram := GlobalTheory.Mem.VolExists.isHermND D.sp.cm W
  obtain ⟨g', hg'⟩ := GlobalTheory.AdelicModulus.Row.exists_transpose (AF D.host.F) hJ h
  have hK := GlobalTheory.AdelicModulus.Row.isHermND_inv_transpose hJ
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r W.rank) := ⟨rfl⟩
  let T := transposeCAE D W.rank r
  have hT : Measurable T := T.continuous.measurable
  have hTs : Measurable T.symm := T.symm.continuous.measurable
  haveI hμ' : (ν.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map ν
  have hm := GlobalTheory.mul_unitary_map_haar D W.rank r (W.gram⁻¹)ᵀ hK.1 hK.2 g' (ν.map T) hμ'
  set A : Matrix (Fin W.rank) (Fin W.rank) (AE D) := (HA.mat (AF D.host.F) D.sp.cm.sig (W.gram⁻¹)ᵀ g').1
  have hR : Measurable (fun x : Mx D r W.rank =>
      (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hmt : mt W h = (HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1 := rfl
  have hf : (fun y : Mx D W.rank r =>
      (HMul.hMul (mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)) =
      T.symm ∘ (fun x : Mx D r W.rank => (HMul.hMul (x : Matrix (Fin r) (Fin W.rank) (AE D)) A : Mx D r W.rank)) ∘ T := by
    funext y
    simp only [Function.comp_apply, A, hg', hmt]
    show _ = ((y : Matrix (Fin W.rank) (Fin r) (AE D))ᵀ * ((HA.mat (AF D.host.F) D.sp.cm.sig W.gram h).1)ᵀ)ᵀ
    rw [← Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hf, ← Measure.map_map hTs (hR.comp hT), ← Measure.map_map hR hT, hm, Measure.map_map hTs hT]
  have : (T.symm ∘ T : Mx D W.rank r → Mx D W.rank r) = id := by
    funext y; simp
  rw [this, Measure.map_id]

theorem integral_left_unitary : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)),
    ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ,
    ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν =
      ∫ y, Φ y ∂ν := by
  intro D W r h ν hν Φ
  let u := HA.mat (AF D.host.F) D.sp.cm.sig W.gram h
  have hmt : mt W h = u.1 := rfl
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  let e : Mx D W.rank r ≃ᵐ Mx D W.rank r :=
    { toFun := fun y => (HMul.hMul u.1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      invFun := fun y => (HMul.hMul (u⁻¹).1 (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r)
      left_inv := fun y => by
        show (u⁻¹).1 * (u.1 * y) = y
        rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        show u.1 * ((u⁻¹).1 * y) = y
        rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      measurable_toFun := (continuous_const.matrix_mul continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mul continuous_id).measurable }
  have hmap := map_left_unitary D W r h ν hν
  rw [hmt] at hmap
  have he : Measure.map (⇑e) ν = ν := hmap
  have := integral_map_equiv (μ := ν) e Φ
  rw [he] at this
  rw [hmt]
  exact this.symm

end GlobalTheory.Twist.LeftHaar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLeftMulUnitaryMatrixAddHaarStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_leftMul_unitaryMatrix_addHaar : ∀ (D : D7) (W : HSp D) (r : ℕ) (h : GA D W) (ν : Measure (Mx D W.rank r)), ν.IsAddHaarMeasure → ∀ Φ : Mx D W.rank r → ℂ, ∫ y, Φ (HMul.hMul (Formalism.L2.Theta.mt W h) (y : Matrix (Fin W.rank) (Fin r) (AE D)) : Mx D W.rank r) ∂ν = ∫ y, Φ y ∂ν := by
  first | exact @GlobalTheory.Twist.LeftHaar.integral_left_unitary | exact GlobalTheory.Twist.LeftHaar.integral_left_unitary | (intros; apply GlobalTheory.Twist.LeftHaar.integral_left_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeFunctionOnHomsNormOneCovolumeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeFunctionOnHomsNormOneCovolumeOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdSpan.ReVec

variable {D : D7}

def reWEquiv (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : WO S T ≃+ WO S T where
  toFun := reW S T b
  invFun := reWi S T b
  left_inv := reWi_reW S T b
  right_inv := reW_reWi S T b
  map_add' := reW_add S T b

theorem continuous_reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reW S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

theorem continuous_reWi (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) :
    Continuous (reWi S T b) := by
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  exact continuous_id.matrix_mul continuous_const

theorem reW_mem_ratL_iff (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO S T) :
    reW S T b x ∈ ratL T S ↔ x ∈ ratL T S := by
  have key : ∀ (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (N : Matrix (Fin S.rank) (Fin S.rank) D.host.E),
      x ∈ ratL T S → HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (β := Matrix (Fin S.rank) (Fin S.rank) (AE D))
        (γ := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x (N.map (incA D)) ∈ ratL T S := by
    rintro x N ⟨γ, rfl⟩
    refine ⟨γ * N, ?_⟩
    show (γ * N).map (incA D) = _
    exact Matrix.map_mul (f := incA D)
  constructor
  · intro h
    have h2 := key _ (frP S b) h
    have : HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) (reW S T b x) ((frP S b).map (incA D)) = x :=
      reWi_reW S T b x
    rwa [this] at h2
  · exact key x _

theorem reframeFunctionOnHoms_norm_one_covolumeOne (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) :
    AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := by
  rintro ⟨⟨p0, hp0⟩, hall⟩
  have he : Continuous (reWEquiv S T b) := continuous_reW S T b
  have he' : Continuous (reWEquiv S T b).symm := continuous_reWi S T b
  have hr : ∀ x, reWEquiv S T b x ∈ ratL T S ↔ x ∈ ratL T S := reW_mem_ratL_iff S T b
  have hr' : ∀ x, (reWEquiv S T b).symm x ∈ ratL T S ↔ x ∈ ratL T S := fun x => by
    rw [← hr, AddEquiv.apply_symm_apply]
  refine ⟨⟨(p0.1.map (reWEquiv S T b).symm, (reWEquiv S T b).symm '' p0.2),
    (GlobalTheory.Unf.ParCont.isCovolOne_map hp0 (reWEquiv S T b).symm he' he hr').1⟩, ?_⟩
  have aux : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      nrm2 μ 𝓕 (fun x => f (reWEquiv S T b x)) = 1 := by
    intro μ 𝓕 hp
    obtain ⟨h1, hemb⟩ := GlobalTheory.Unf.ParCont.isCovolOne_map hp (reWEquiv S T b) he he' hr
    have h2 := hall (μ.map (reWEquiv S T b), reWEquiv S T b '' 𝓕) h1
    simp only [nrm2] at h2 ⊢
    rw [hemb.setIntegral_map, Set.preimage_image_eq _ (reWEquiv S T b).injective] at h2
    exact h2
  rintro ⟨μ', 𝓕'⟩ hp
  exact aux μ' 𝓕' hp

end GlobalTheory.AdSpan.ReVec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReframeFunctionOnHomsNormOneCovolumeOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reF_norm_one_of_norm_one_covolOne : ∀ (D : D7) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ), AllSome (fun p : Measure (WO S T) × Set (WO S T) => IsCovolOne (ratL T S) p.1 p.2) (fun p => nrm2 p.1 p.2 f = 1) → AllSome (fun p : Measure (WO (reS S b) T) × Set (WO (reS S b) T) => IsCovolOne (ratL T (reS S b)) p.1 p.2) (fun p => nrm2 p.1 p.2 (reF S T b f) = 1) := by
  first | exact @GlobalTheory.AdSpan.ReVec.reframeFunctionOnHoms_norm_one_covolumeOne | exact GlobalTheory.AdSpan.ReVec.reframeFunctionOnHoms_norm_one_covolumeOne | (intros; apply GlobalTheory.AdSpan.ReVec.reframeFunctionOnHoms_norm_one_covolumeOne <;> assumption)
end
end
