module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothConvolutionEqDerivativeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaplacianPolynomialKernelOfPolynomialLaplacian

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarGLRealPointsDensityDetInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarGLRealPointsDensityDetInv
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable section

namespace GlobalTheory.GLHaar

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem lmul_apply (y x : Lie E a) : lmul y x = toL (Matrix.of y * Matrix.of x) := rfl

theorem lmul_lmul (y x : Lie E a) : lmul (lmul y x) = (lmul y).comp (lmul x) := by
  ext z : 1
  simp only [ContinuousLinearMap.comp_apply, lmul_apply]
  simp [Matrix.mul_assoc]

theorem lmul_one : lmul (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = ContinuousLinearMap.id ℝ _ := by
  ext z : 1
  simp [lmul_apply]

def dL (x : Lie E a) : ℝ := LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)

theorem dL_mul (y x : Lie E a) : dL (lmul y x) = dL y * dL x := by
  unfold dL
  rw [lmul_lmul]
  exact LinearMap.det_comp (lmul y : Lie E a →ₗ[ℝ] Lie E a) (lmul x : Lie E a →ₗ[ℝ] Lie E a)

theorem lmul_add (x y : Lie E a) : lmul (x + y) = lmul x + lmul y := by
  ext z : 1
  exact Matrix.add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z)

theorem lmul_smul (c : ℝ) (x : Lie E a) : lmul (c • x) = c • lmul x := by
  ext z : 1
  exact Matrix.smul_mul c (Matrix.of x) (Matrix.of z)

def lmulL : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) where
  toFun := lmul
  map_add' := lmul_add
  map_smul' := lmul_smul

theorem continuous_dL : Continuous (dL (E := E) (a := a)) :=
  ContinuousLinearMap.continuous_det.comp (LinearMap.continuous_of_finiteDimensional (lmulL (E := E) (a := a)))

open scoped ENNReal NNReal

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def jG (y : glG E a) : Lie E a := toL y.1.val

theorem jG_mul (g y : glG E a) : jG (g * y) = lmul (jG g) (jG y) := rfl

theorem jG_one : jG (1 : glG E a) = toL 1 := rfl

theorem isOpenEmbedding_jG : Topology.IsOpenEmbedding (jG (E := E) (a := a)) := by
  have hO : IsOpen ((glG E a : Subgroup (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Set (Matrix (Fin a) (Fin a) (Cinf E))ˣ) := by
    change IsOpen (Set.univ : Set (Matrix (Fin a) (Fin a) (Cinf E))ˣ)
    exact isOpen_univ
  exact GlobalTheory.CuspQuot.isOpenEmbedding_val.comp hO.isOpenEmbedding_subtypeVal

theorem range_jG : Set.range (jG (E := E) (a := a)) = invSet E a := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact val_mem_invSet y.1
  · intro hx
    exact ⟨⟨hx.unit, Subgroup.mem_top _⟩, hx.unit_spec⟩

theorem lmul_jG_inv (g : glG E a) (x : Lie E a) : lmul (jG g) (lmul (jG g⁻¹) x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← lmul_lmul, ← jG_mul, mul_inv_cancel, jG_one, lmul_one]
  rfl

theorem lmul_inv_jG (g : glG E a) (x : Lie E a) : lmul (jG g⁻¹) (lmul (jG g) x) = x := by
  rw [← ContinuousLinearMap.comp_apply, ← lmul_lmul, ← jG_mul, inv_mul_cancel, jG_one, lmul_one]
  rfl

theorem dL_one : dL (toL (1 : Matrix (Fin a) (Fin a) (Cinf E))) = 1 := by
  unfold dL
  rw [lmul_one]
  exact LinearMap.det_id

theorem dL_jG_ne (g : glG E a) : dL (jG g) ≠ 0 := by
  intro h
  have e := dL_mul (jG g) (jG g⁻¹)
  rw [← jG_mul, mul_inv_cancel, jG_one, dL_one, h, zero_mul] at e
  exact one_ne_zero e

theorem dL_ne_of_mem {x : Lie E a} (hx : x ∈ invSet E a) : dL x ≠ 0 := by
  rw [← range_jG] at hx
  obtain ⟨g, rfl⟩ := hx
  exact dL_jG_ne g

def rho (x : Lie E a) : ℝ≥0∞ := ENNReal.ofReal (|dL x|⁻¹)

theorem measurable_rho : Measurable (rho (E := E) (a := a)) :=
  ENNReal.measurable_ofReal.comp (continuous_dL.abs.measurable.inv)

theorem ofReal_mul_rho (y x : Lie E a) (hy : dL y ≠ 0) :
    ENNReal.ofReal |dL y| * rho (lmul y x) = rho x := by
  unfold rho
  rw [← ENNReal.ofReal_mul (abs_nonneg _), dL_mul, abs_mul, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ (abs_ne_zero.2 hy), one_mul]

def muG [MeasurableSpace (glG E a)] (ν : MeasureTheory.Measure (Lie E a)) : MeasureTheory.Measure (glG E a) :=
  (ν.withDensity rho).comap jG

section Haar

variable [MeasurableSpace (glG E a)] [BorelSpace (glG E a)] (ν : Measure (Lie E a)) [hν : ν.IsAddHaarMeasure]

theorem mE : MeasurableEmbedding (jG (E := E) (a := a)) := isOpenEmbedding_jG.measurableEmbedding

theorem withDensity_preimage (g : glG E a) {A : Set (Lie E a)} (hA : MeasurableSet A) :
    ν.withDensity rho (lmul (jG g) ⁻¹' A) = ν.withDensity rho A := by
  set L := lmul (jG g)
  have hsurj : L '' (L ⁻¹' A) = A := Set.image_preimage_eq A (fun x => ⟨lmul (jG g⁻¹) x, lmul_jG_inv g x⟩)
  have hinj : Function.Injective L := fun x y h => by
    rw [← lmul_inv_jG g x, ← lmul_inv_jG g y]
    exact congrArg _ h
  have hS : MeasurableSet (L ⁻¹' A) := hA.preimage L.continuous.measurable
  rw [withDensity_apply _ hA, withDensity_apply _ hS]
  conv_rhs => rw [← hsurj]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul ν hS (fun x _ => L.hasFDerivAt.hasFDerivWithinAt)
    hinj.injOn]
  refine setLIntegral_congr_fun hS (fun x _ => ?_)
  exact (ofReal_mul_rho (jG g) x (dL_jG_ne g)).symm

theorem muG_leftInv : (muG ν : Measure (glG E a)).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  have hm : Measurable (g * · : glG E a → glG E a) := (continuous_const.mul continuous_id).measurable
  rw [Measure.map_apply hm hs, muG, mE.comap_apply, mE.comap_apply]
  have himg : jG '' ((g * ·) ⁻¹' s) = (lmul (jG g)) ⁻¹' (jG '' s) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g * y, hy, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      refine ⟨g⁻¹ * z, ?_, ?_⟩
      · show g * (g⁻¹ * z) ∈ s
        rwa [mul_inv_cancel_left]
      · show lmul (jG g⁻¹) (jG z) = x
        rw [hzx, lmul_inv_jG]
  rw [himg]
  exact withDensity_preimage ν g (mE.measurableSet_image.2 hs)

theorem muG_finite : IsFiniteMeasureOnCompacts (muG ν : Measure (glG E a)) := by
  refine ⟨fun K hK => ?_⟩
  rw [muG, mE.comap_apply]
  have hK' : IsCompact (jG '' K) := hK.image isOpenEmbedding_jG.continuous
  have hsub : jG '' K ⊆ invSet E a := by
    rw [← range_jG]
    exact Set.image_subset_range _ _
  rw [withDensity_apply _ hK'.measurableSet]
  have hc : ContinuousOn (fun x : Lie E a => |dL x|⁻¹) (jG '' K) :=
    continuous_dL.abs.continuousOn.inv₀ fun x hx => abs_ne_zero.2 (dL_ne_of_mem (hsub hx))
  exact (hc.integrableOn_compact hK').lintegral_lt_top

theorem muG_pos : (muG ν : Measure (glG E a)).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [muG, mE.comap_apply]
  intro h0
  rw [withDensity_apply_eq_zero' measurable_rho.aemeasurable] at h0
  have he : {x | rho x ≠ 0} ∩ jG '' U = jG '' U := by
    refine Set.inter_eq_right.2 ?_
    rintro _ ⟨y, _, rfl⟩
    exact (ENNReal.ofReal_pos.2 (inv_pos.2 (abs_pos.2 (dL_jG_ne y)))).ne'
  rw [he] at h0
  exact (isOpenEmbedding_jG.isOpenMap U hU).measure_ne_zero ν (hne.image _) h0

theorem muG_haar : (muG ν : Measure (glG E a)).IsHaarMeasure :=
  haveI := muG_leftInv ν
  haveI := muG_finite ν
  haveI := muG_pos ν
  { }

theorem integral_muG (Φ : Lie E a → ℂ) (hΦ : ∀ x ∉ invSet E a, Φ x = 0) :
    ∫ y, Φ (toL y.1.val) ∂(muG ν : Measure (glG E a)) =
      ∫ x, ((|LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
  change ∫ y, Φ (jG y) ∂(muG ν) = _
  rw [← mE.integral_map, muG, mE.map_comap, range_jG, setIntegral_eq_integral_of_forall_compl_eq_zero hΦ]
  have hf : Measurable fun x : Lie E a => (|dL x|⁻¹).toNNReal := continuous_dL.abs.measurable.inv.real_toNNReal
  change ∫ x, Φ x ∂(ν.withDensity fun x => (((|dL x|⁻¹).toNNReal : ℝ≥0) : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 (abs_nonneg _)), Complex.real_smul]
  rfl

end Haar

theorem glHaar : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ [MeasurableSpace (glG E a)] [BorelSpace (glG E a)], ∃ μ : Measure (glG E a), μ.IsHaarMeasure ∧ ∀ (Φ : Lie E a → ℂ), ContinuousOn Φ (invSet E a) → (∀ x ∉ invSet E a, Φ x = 0) → ∫ y, Φ (toL y.1.val) ∂μ = ∫ x, ((|LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
  intro E _ _ _ a ν hν _ _
  exact ⟨muG ν, muG_haar ν, fun Φ _ hΦ => integral_muG ν Φ hΦ⟩

end GlobalTheory.GLHaar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarGLRealPointsDensityDetInvStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_GL_realPoints_density_det_inv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ (ν : Measure (Lie E a)), ν.IsAddHaarMeasure → ∀ [MeasurableSpace (glG E a)] [BorelSpace (glG E a)], ∃ μ : Measure (glG E a), μ.IsHaarMeasure ∧ ∀ (Φ : Lie E a → ℂ), ContinuousOn Φ (invSet E a) → (∀ x ∉ invSet E a, Φ x = 0) → ∫ y, Φ (toL y.1.val) ∂μ = ∫ x, ((|LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
  first | exact @GlobalTheory.GLHaar.glHaar | exact GlobalTheory.GLHaar.glHaar | (intros; apply GlobalTheory.GLHaar.glHaar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionLieAlgebraPullbackDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionLieAlgebraPullbackDet
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
open scoped ContDiff Topology

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.GLExt

variable {E : Type} [Field E] [NumberField E] {a : ℕ}


variable (E a) in
def toLCLM : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap


variable (E a) in
def ofCLM : Lie E a →L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) :=
  LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).toLinearMap

def detL (x : Lie E a) : ℝ := LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)

theorem contDiff_detL : ContDiff ℝ ∞ (detL (E := E) (a := a)) := by
  let b := Module.finBasis ℝ (Lie E a)
  have e : (detL (E := E) (a := a)) = fun x => (Matrix.of fun i j => b.coord i (rmul (b j) x)).det := by
    funext x
    rw [detL, ← LinearMap.det_toMatrix b]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [e]
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (LinearMap.toContinuousLinearMap (b.coord (σ i))).contDiff.comp (ContinuousLinearMap.contDiff (rmul (b i)))

theorem detL_ne_zero {x : Lie E a} (hx : x ∈ invSet E a) : detL x ≠ 0 := by
  obtain ⟨u, hu⟩ := hx
  have h : ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) ∘ₗ
      ((lmul (toL (u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) =
        LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    change Matrix.of x * (((u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)) * Matrix.of v) =
      Matrix.of v
    rw [← hu, Units.mul_inv_cancel_left]
  intro h0
  have h1 := congrArg LinearMap.det h
  rw [LinearMap.det_comp, LinearMap.det_id] at h1
  rw [detL] at h0
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1


open Classical in
def extZ (α : glG E a → ℂ) (x : Lie E a) : ℂ :=
  if h : IsUnit (Matrix.of x) then ((|detL x|⁻¹ : ℝ) : ℂ) * α ⟨h.unit, Subgroup.mem_top _⟩ else 0

theorem extZ_val (α : glG E a → ℂ) (y : glG E a) :
    extZ α (toL y.1.val) = ((|detL (toL y.1.val)|⁻¹ : ℝ) : ℂ) * α y := by
  have h : IsUnit (Matrix.of (toL y.1.val)) := y.1.isUnit
  have e : (⟨h.unit, Subgroup.mem_top _⟩ : glG E a) = y := Subtype.ext (Units.ext h.unit_spec)
  rw [extZ, dite_eq_left h, e]

theorem continuous_toL_val : Continuous fun y : glG E a => toL y.1.val :=
  (toLCLM E a).continuous.comp (Units.continuous_val.comp continuous_subtype_val)

theorem support_extZ_subset (α : glG E a → ℂ) :
    Function.support (extZ α) ⊆ (fun y : glG E a => toL y.1.val) '' tsupport α := by
  intro x hx
  by_cases h : IsUnit (Matrix.of x)
  · refine ⟨⟨h.unit, Subgroup.mem_top _⟩, subset_tsupport _ fun h0 => hx ?_, ?_⟩
    · simp [extZ, h, h0]
    · show Matrix.of.symm (h.unit : Matrix (Fin a) (Fin a) (Cinf E)) = x
      rw [h.unit_spec]; rfl
  · exact absurd (by simp [extZ, h]) hx

theorem contDiffAt_extZ {α : glG E a → ℂ} (hα : (glH E a).IsSmoothFun α) {x₀ : Lie E a} (hx₀ : x₀ ∈ invSet E a) :
    ContDiffAt ℝ ∞ (extZ α) x₀ := by
  obtain ⟨u, hu⟩ := id hx₀
  let g : glG E a := ⟨u, Subgroup.mem_top _⟩
  let L : Lie E a → Matrix (Fin a) (Fin a) (Cinf E) :=
    fun x => ((u⁻¹ : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)) * ofCLM E a x
  have hL1 : L x₀ = 1 := by
    change _ * Matrix.of x₀ = 1
    rw [← hu, Units.inv_mul]
  have hLc : ContDiff ℝ ∞ L := contDiff_const.mul (ofCLM E a).contDiff
  have hT : (expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).target ∈ 𝓝 (L x₀) := by
    rw [hL1]
    exact (expPartialHomeomorph ℝ _).open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)
  have hU : ∀ᶠ x in 𝓝 x₀, L x ∈ (expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).target :=
    hLc.continuous.continuousAt.preimage_mem_nhds hT
  have hI : ∀ᶠ x in 𝓝 x₀, x ∈ invSet E a := isOpen_invSet.mem_nhds hx₀
  let Y : Lie E a → glL E a := fun x =>
    subspaceProj (glL E a) ((expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).symm (L x))
  have hY : ContDiffAt ℝ ∞ Y x₀ :=
    (subspaceProj (glL E a)).contDiff.contDiffAt.comp (g := ⇑(subspaceProj (glL E a))) x₀
      (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hT).comp x₀ hLc.contDiffAt)
  have hF : ContDiffAt ℝ ∞ (fun x => α (g * (glH E a).expG (Y x))) x₀ :=
    (((glH E a).isSmoothFun_iff.1 hα g).contDiffAt).comp x₀ hY
  have hD : ContDiffAt ℝ ∞ (fun x => ((|detL x|⁻¹ : ℝ) : ℂ)) x₀ :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x₀
      ((contDiff_detL.contDiffAt.abs (detL_ne_zero hx₀)).inv (abs_ne_zero.2 (detL_ne_zero hx₀)))
  refine (hD.mul hF).congr_of_eventuallyEq ?_
  filter_upwards [hU, hI] with x hx hxi
  have h2 : NormedSpace.exp ((expPartialHomeomorph ℝ (Matrix (Fin a) (Fin a) (Cinf E))).symm (L x)) = L x :=
    (expPartialHomeomorph ℝ _).right_inv hx
  have e : (⟨hxi.unit, Subgroup.mem_top _⟩ : glG E a) = g * (glH E a).expG (Y x) := by
    apply Subtype.ext; apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    rw [subspaceProj_of_mem Submodule.mem_top]
    refine (?_ : _ = (u : Matrix (Fin a) (Fin a) (Cinf E)) * L x).trans (congrArg _ h2.symm)
    change Matrix.of x = (u : Matrix (Fin a) (Fin a) (Cinf E)) * (_ * Matrix.of x)
    rw [Units.mul_inv_cancel_left]
  rw [extZ, dite_eq_left (show IsUnit (Matrix.of x) from hxi), e]

theorem exists_isTest_ext : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ α : glG E a → ℂ,
    (glH E a).IsSmoothFun α → HasCompactSupport α → ∃ β : Lie E a → ℂ, GlobalTheory.CuspQuot.IsTest (invSet E a) β ∧
      ∀ y : glG E a, β (toL y.1.val) = ((|LinearMap.det ((lmul (toL y.1.val) : Lie E a →L[ℝ] Lie E a) :
        Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * α y := by
  intro E _ _ _ a α hα hc
  have hK : IsCompact ((fun y : glG E a => toL y.1.val) '' tsupport α) := hc.image continuous_toL_val
  have hs : tsupport (extZ α) ⊆ (fun y : glG E a => toL y.1.val) '' tsupport α :=
    closure_minimal (support_extZ_subset α) hK.isClosed
  have hi : tsupport (extZ α) ⊆ invSet E a := hs.trans (by rintro _ ⟨y, _, rfl⟩; exact val_mem_invSet y.1)
  refine ⟨extZ α, ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hK.of_isClosed_subset (isClosed_tsupport _) hs, hi⟩,
    fun y => extZ_val α y⟩
  by_cases hx : x ∈ tsupport (extZ α)
  · exact contDiffAt_extZ hα (hi hx)
  · exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.1 hx)

end GlobalTheory.GLExt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionLieAlgebraPullbackDetStatement
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_test_function_lie_algebra_pullback_det : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∀ α : glG E a → ℂ, (glH E a).IsSmoothFun α → HasCompactSupport α → ∃ β : Lie E a → ℂ, GlobalTheory.CuspQuot.IsTest (invSet E a) β ∧ ∀ y : glG E a, β (toL y.1.val) = ((|LinearMap.det ((lmul (toL y.1.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)|⁻¹ : ℝ) : ℂ) * α y := by
  first | exact @GlobalTheory.GLExt.exists_isTest_ext | exact GlobalTheory.GLExt.exists_isTest_ext | (intros; apply GlobalTheory.GLExt.exists_isTest_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySoluti
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

namespace GlobalTheory.GLParametrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem continuous_lmul : Continuous fun x : Lie E a => lmul x := by
  let L : Lie E a →ₗ[ℝ] (Lie E a →L[ℝ] Lie E a) :=
    { toFun := lmul
      map_add' := fun x y => ContinuousLinearMap.ext fun z =>
        (Matrix.add_mul (Matrix.of x) (Matrix.of y) (Matrix.of z) : _)
      map_smul' := fun c x => ContinuousLinearMap.ext fun z =>
        (Matrix.smul_mul c (Matrix.of x) (Matrix.of z) : _) }
  exact L.continuous_of_finiteDimensional

theorem continuous_absDet :
    Continuous fun x : Lie E a => |LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)| :=
  continuous_abs.comp (ContinuousLinearMap.continuous_det.comp continuous_lmul)

theorem det_lmul_ne_zero (u : GL (Fin a) (Cinf E)) :
    LinearMap.det ((lmul (toL u.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) ≠ 0 := by
  have h : ((lmul (toL u.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) ∘ₗ
      ((lmul (toL (u⁻¹).val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a) = LinearMap.id :=
    LinearMap.ext fun z => u.mul_inv_cancel_left (Matrix.of z)
  intro h0
  have h1 := congrArg LinearMap.det h
  rw [LinearMap.det_comp, h0, zero_mul, LinearMap.det_id] at h1
  exact zero_ne_one h1

end


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem exists_test_reproducing : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) →
        ∫ y, α y * f y ∂ν = f (oneL E a) := by
  intro E _ _ _ a ν hν p hp
  obtain ⟨d, b, P, hP, hsol, -⟩ := GlobalTheory.T.laplacianPolynomialKernel_of_polynomial_laplacian E a p hp
  borelize ↥(GlobalTheory.HCA.glG E a)
  obtain ⟨μ, hμ, hint⟩ := GlobalTheory.T.exists_haar_GL_realPoints_density_det_inv E a ν hν
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  obtain ⟨α₀, hs, -, hc, hα₀⟩ := @GlobalTheory.T.exists_smooth_convolution_eq_derivative (Matrix (Fin a) (Fin a) (Cinf E)) _ _ _ _ (GlobalTheory.HCA.glG E a)
    (GlobalTheory.HCA.glL E a) (GlobalTheory.HCA.glH E a) d b P hP _ ⟨rfl⟩ μ hμ []
  obtain ⟨β, hβ, hβe⟩ := GlobalTheory.T.exists_test_function_lie_algebra_pullback_det E a α₀ hs hc
  refine ⟨β, hβ, fun f hf hpf => ?_⟩
  obtain ⟨hF, h0⟩ := (GlobalTheory.HCA.mem_solG (GlobalTheory.HCA.glH E a) b).1 (hsol f hf hpf)
  have key := hα₀ ⟨_, hF⟩ h0 1
  simp only [one_mul, List.foldr_nil] at key
  set D : Lie E a → ℝ := fun x => |LinearMap.det ((lmul x : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)| with hD
  have hD0 : ∀ u : GL (Fin a) (Cinf E), D (toL u.val) ≠ 0 := fun u => abs_ne_zero.2 (det_lmul_ne_zero u)
  set Φ : Lie E a → ℂ := (invSet E a).indicator fun x => (D x : ℂ) * (β x * f x) with hΦ
  have hΦc : ContinuousOn Φ (invSet E a) :=
    ((Complex.continuous_ofReal.comp continuous_absDet).continuousOn.mul
      (hβ.1.continuous.continuousOn.mul hf.continuousOn)).congr fun x hx => Set.indicator_of_mem hx _
  have hΦ0 : ∀ x ∉ invSet E a, Φ x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have H := hint Φ hΦc hΦ0
  have e1 : ∫ x, β x * f x ∂ν = ∫ x, (((D x)⁻¹ : ℝ) : ℂ) * Φ x ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ invSet E a
    · obtain ⟨u, hu⟩ := hx
      obtain rfl : x = toL u.val := hu.symm
      have h1 : ((D (toL u.val) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hD0 u)
      simp only [hΦ, Set.indicator_of_mem (val_mem_invSet u)]
      push_cast
      field_simp
    · have hb : β x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hβ.2.2 h)
      simp [hΦ0 x hx, hb]
  have e2 : ∫ y, Φ (toL y.1.val) ∂μ = ∫ y, f (toL y.1.val) * α₀ y ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have h1 : ((|LinearMap.det ((lmul (toL y.1.val) : Lie E a →L[ℝ] Lie E a) : Lie E a →ₗ[ℝ] Lie E a)| : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (hD0 y.1)
    beta_reduce
    rw [hΦ, Set.indicator_of_mem (val_mem_invSet y.1), hβe y, hD]
    dsimp only
    rw [Complex.ofReal_inv]
    field_simp
  rw [e1, ← H, e2]
  exact key
end GlobalTheory.GLParametrix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySolutiStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_testFunction_reproducing_laplacianPoly_solutions : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) →
        ∫ y, α y * f y ∂ν = f (oneL E a) := by
  first | exact @GlobalTheory.GLParametrix.exists_test_reproducing | exact GlobalTheory.GLParametrix.exists_test_reproducing | (intros; apply GlobalTheory.GLParametrix.exists_test_reproducing <;> assumption)
end
