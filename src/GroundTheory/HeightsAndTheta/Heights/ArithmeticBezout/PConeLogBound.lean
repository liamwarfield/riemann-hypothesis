module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartGram
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBrouwerFixedPoint
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField Matrix

noncomputable section

variable {n : ℕ}

theorem HermNorm.norm_pairing_le (h : HermNorm n) (u y : Fin n → ℂ) :
    ‖∑ j, u j * y j‖ ≤ h.norm u * h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  have hpair : ∑ j, u j * y j = ∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i := by
    have e1 : (∑ j, u j * y j) = u ⬝ᵥ y := rfl
    have e2 : (∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i) = (h.mat *ᵥ u) ⬝ᵥ ((h.matᵀ)⁻¹ *ᵥ y) := rfl
    rw [e1, e2, dotProduct_comm (h.mat *ᵥ u), dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
      mul_nonsing_inv _ hinv, one_mulVec, dotProduct_comm]
  rw [hpair]
  calc ‖∑ i, (h.mat *ᵥ u) i * ((h.matᵀ)⁻¹ *ᵥ y) i‖
      ≤ ∑ i, ‖(h.mat *ᵥ u) i‖ * ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp
    _ ≤ √(∑ i, ‖(h.mat *ᵥ u) i‖ ^ 2) * √(∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = h.norm u * h.dualNorm y := rfl

theorem HermNorm.dualNorm_pos (h : HermNorm n) {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < h.dualNorm y := by
  have hinv : IsUnit h.matᵀ.det := by rw [det_transpose]; exact h.isUnit_det
  unfold HermNorm.dualNorm
  apply Real.sqrt_pos.mpr
  have hBy : (h.matᵀ)⁻¹ *ᵥ y ≠ 0 := by
    intro h0
    apply hy
    have := congrArg (fun x => h.matᵀ *ᵥ x) h0
    simp only [mulVec_mulVec, mul_nonsing_inv _ hinv, one_mulVec, mulVec_zero] at this
    exact this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hBy
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, by
    have : 0 < ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ := norm_pos_iff.mpr hi
    positivity⟩

theorem fsLog_le (h : HermNorm n) {u y : Fin n → ℂ} (hy : ∑ j, u j * y j ≠ 0) :
    fsLog h u y ≤ Real.log (h.norm u) := by
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hd := h.dualNorm_pos hy0
  have hnum : 0 < ‖∑ j, u j * y j‖ := norm_pos_iff.mpr hy
  unfold fsLog
  apply Real.log_le_log (div_pos hnum hd)
  rw [div_le_iff₀ hd]
  exact h.norm_pairing_le u y

theorem measurableSet_coneBall (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ)) :
    MeasurableSet (coneBall h W) := by
  have hc : Continuous (h.pointOf) := by
    unfold HermNorm.pointOf
    fun_prop
  have hclosed : IsClosed {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} := by
    have : {y : EuclideanSpace ℂ (Fin n) | ∀ q ∈ W, eval (h.pointOf y) q = 0} =
        ⋂ q ∈ W, {y | eval (h.pointOf y) q = 0} := by
      ext y; simp
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq ((continuous_eval q).comp hc) continuous_const
  have hopen : MeasurableSet (Metric.ball (0 : EuclideanSpace ℂ (Fin n)) 1) :=
    Metric.isOpen_ball.measurableSet
  have := hopen.inter hclosed.measurableSet
  convert this using 1
  ext y
  simp [coneBall, Metric.mem_ball]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ChowHeightConst.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (H : ArchData K n) (c : K), c ≠ 0 →
    chowHt H k 0 (C c : MvPolynomial (Fin k × Fin n) K) = 0

section Ball

open Matrix

variable {n : ℕ}

def ballProd (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}

theorem continuous_hermNorm_group (h : HermNorm n) {k : ℕ} (i : Fin k) :
    Continuous fun u : Fin k × Fin n → ℂ => h.norm (fun j => u (i, j)) := by
  simp only [HermNorm.norm, Matrix.mulVec, dotProduct]
  fun_prop

theorem isOpen_ballProd (h : HermNorm n) (k : ℕ) : IsOpen (ballProd h k) := by
  have e : ballProd h k = ⋂ i, {u | h.norm (fun j => u (i, j)) < 1} := by
    ext u
    simp [ballProd]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_hermNorm_group h i) continuous_const

theorem zero_mem_ballProd (h : HermNorm n) (k : ℕ) : (0 : Fin k × Fin n → ℂ) ∈ ballProd h k := by
  intro i
  have e : (fun j : Fin n => (0 : Fin k × Fin n → ℂ) (i, j)) = 0 := rfl
  rw [e]
  simp [HermNorm.norm]

theorem norm_le_of_hermNorm_lt (h : HermNorm n) {v : Fin n → ℂ} (hv : h.norm v < 1) (j : Fin n) :
    ‖v j‖ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ := by
  have hinv : h.mat⁻¹ * h.mat = 1 := Matrix.nonsing_inv_mul _ h.isUnit_det
  have hv' : v = h.mat⁻¹ *ᵥ (h.mat *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hcoord : ∀ l, ‖(h.mat *ᵥ v) l‖ ≤ 1 := by
    intro l
    have h1 : ‖(h.mat *ᵥ v) l‖ ^ 2 ≤ ∑ m, ‖(h.mat *ᵥ v) m‖ ^ 2 :=
      Finset.single_le_sum (f := fun m => ‖(h.mat *ᵥ v) m‖ ^ 2) (fun m _ => sq_nonneg _)
        (Finset.mem_univ l)
    have h2 : √(‖(h.mat *ᵥ v) l‖ ^ 2) ≤ h.norm v := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (norm_nonneg _)] at h2
    linarith
  calc ‖v j‖ = ‖(h.mat⁻¹ *ᵥ (h.mat *ᵥ v)) j‖ := by rw [← hv']
    _ = ‖∑ l, h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := rfl
    _ ≤ ∑ l, ‖h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖h.mat⁻¹ j l‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hcoord l)
    _ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
        Finset.single_le_sum (f := fun j' => ∑ l, ‖h.mat⁻¹ j' l‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem isBounded_ballProd (h : HermNorm n) (k : ℕ) : Bornology.IsBounded (ballProd h k) := by
  have hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine (Metric.isBounded_closedBall (x := (0 : Fin k × Fin n → ℂ))
    (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun u hu => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  rintro ⟨i, j⟩
  exact norm_le_of_hermNorm_lt h (hu i) j

theorem volume_ballProd_pos (h : HermNorm n) (k : ℕ) : 0 < volume (ballProd h k) :=
  (isOpen_ballProd h k).measure_pos volume ⟨0, zero_mem_ballProd h k⟩

theorem volume_ballProd_lt_top (h : HermNorm n) (k : ℕ) : volume (ballProd h k) < ⊤ :=
  (isBounded_ballProd h k).measure_lt_top

theorem sphereMean_const (h : HermNorm n) (k : ℕ) (a : ℝ) : sphereMean h k (fun _ => a) = a :=
  setAverage_const (volume_ballProd_pos h k).ne' (volume_ballProd_lt_top h k).ne a

theorem mahler_C (h : HermNorm n) (k : ℕ) (z : ℂ) :
    mahler h k (C z : MvPolynomial (Fin k × Fin n) ℂ) = Real.log ‖z‖ := by
  unfold mahler
  simp only [eval_C]
  exact sphereMean_const h k _

end Ball

section ProductFormula

variable {K : Type*} [Field K] [NumberField K]

theorem prod_norm_embeddings (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have h : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = ∏ σ : K →+* ℂ, ‖σ x‖ := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x, norm_prod, ← Fintype.prod_equiv
      (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖) (fun φ => ‖φ x‖)
      fun _ => by simp [RingHom.equivRatAlgHom_apply]]
  rw [← h, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, Rat.cast_abs]

theorem sum_log_norm_embeddings {x : K} (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  rw [← prod_norm_embeddings, Real.log_prod]
  intro σ _
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx)

theorem finsum_log_adicAbv {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v x) =
        -Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have hpos : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      0 < NumberField.HeightOneSpectrum.adicAbv K v x := fun v =>
    (NumberField.HeightOneSpectrum.adicAbv K v).pos hx
  rw [← Real.log_finprod hpos]
  have e : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      NumberField.HeightOneSpectrum.adicAbv K v x = ∏ᶠ w : FinitePlace K, w x := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finprod_congr fun v => ?_
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  rw [e, FinitePlace.prod_eq_inv_abs_norm hx, Rat.cast_inv, Real.log_inv]

end ProductFormula

theorem chowHeightConst : ChowHeightConst.Statement := by
  intro K _ _ n k H c hc
  unfold chowHt
  have harch : ∀ σ : K →+* ℂ,
      mahler (H.normAt σ) k ((C c : MvPolynomial (Fin k × Fin n) K).map σ) = Real.log ‖σ c‖ :=
    fun σ => by rw [map_C, mahler_C]
  simp only [harch, gaussNorm_C, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero,
    finsum_log_adicAbv hc, sum_log_norm_embeddings hc, neg_add_cancel]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ReducedTensorPerfect
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

noncomputable section

universe u


set_option synthInstance.maxHeartbeats 400000 in
theorem isReduced_tensorProduct_of_forall_field {k : Type*} [Field k] (C : Type*) [CommRing C]
    [Algebra k C]
    (h : ∀ (E : Type u) [Field E] [Algebra k E] [Algebra.EssFiniteType k E], IsReduced (C ⊗[k] E))
    (A : Type u) [CommRing A] [Algebra k A] [IsReduced A] : IsReduced (C ⊗[k] A) := by
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  have : Algebra.FiniteType k B := ⟨(Subalgebra.fg_top B).mpr hB⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have : Fintype (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).fintype
  classical
  have hP : ∀ P : minimalPrimes B, P.1.IsPrime := fun P => P.2.1.1
  let φ : B →ₐ[k] ∀ P : minimalPrimes B, FractionRing (B ⧸ P.1) :=
    AlgHom.pi fun P =>
      (IsScalarTower.toAlgHom k (B ⧸ P.1) (FractionRing (B ⧸ P.1))).comp (Ideal.Quotient.mkₐ k P.1)
  have hφ : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    have hmem : b ∈ sInf (minimalPrimes B) := by
      rw [Submodule.mem_sInf]
      intro P hPm
      have h1 := congr_fun hb ⟨P, hPm⟩
      have h2 : algebraMap (B ⧸ P) (FractionRing (B ⧸ P)) (Ideal.Quotient.mk P b) = 0 := h1
      rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hmem
    have : b ∈ nilradical B := hmem
    rw [nilradical_eq_zero] at this
    exact this
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id C C) φ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (φ.toLinearMap) hφ
  have : ∀ P : minimalPrimes B, IsReduced (C ⊗[k] FractionRing (B ⧸ P.1)) := fun P => h _
  let ψ := Algebra.TensorProduct.piRight k k C (fun P : minimalPrimes B => FractionRing (B ⧸ P.1))
  exact isReduced_of_injective (ψ.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id C C) φ).toRingHom)
    ((AlgEquiv.injective ψ).comp hinj)

theorem isReduced_tensorProduct_of_isSeparable {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] [Algebra.EssFiniteType F E]
    (D : Type u) [CommRing D] [Algebra F D] [IsReduced D] : IsReduced (E ⊗[F] D) := by
  refine isReduced_tensorProduct_of_forall_field E (fun M _ _ _ => ?_) D
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  have : IsReduced (M ⊗[F] E) := Algebra.FormallyUnramified.isReduced_of_field M (M ⊗[F] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm F E M).toAlgHom (AlgEquiv.injective _)

theorem isReduced_fractionRing_mvPolynomial_tensorProduct (K : Type u) [Field K] (σ : Type u)
    (L : Type u) [Field L] [Algebra K L] :
    IsReduced (FractionRing (MvPolynomial σ K) ⊗[K] L) := by
  let R := MvPolynomial σ K
  have : IsReduced (R ⊗[K] L) :=
    isReduced_of_injective
      ((Algebra.TensorProduct.comm K R L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv)
      (RingEquiv.injective _)
  have : IsReduced (FractionRing R ⊗[R] (R ⊗[K] L)) := by
    let : Algebra (R ⊗[K] L) (FractionRing R ⊗[R] (R ⊗[K] L)) := Algebra.TensorProduct.rightAlgebra
    exact isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (R ⊗[K] L) (nonZeroDivisors R))
      (FractionRing R ⊗[R] (R ⊗[K] L)) inferInstance
  exact isReduced_of_injective
    (Algebra.TensorProduct.cancelBaseChange K R R (FractionRing R) L).symm.toAlgHom
    (AlgEquiv.injective _)


set_option synthInstance.maxHeartbeats 400000 in
theorem isReduced_tensorProduct_field_of_perfectField (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (E : Type u) [Field E] [Algebra K E]
    [Algebra.EssFiniteType K E] : IsReduced (L ⊗[K] E) := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K E
  let F := IntermediateField.adjoin K (s : Set E)
  have : Algebra.EssFiniteType F E := Algebra.EssFiniteType.of_comp K F E
  let e : FractionRing (MvPolynomial s K) ≃ₐ[K] F :=
    hs.1.aevalEquivField.trans (IntermediateField.equivOfEq (by simp [F]))
  have : IsReduced (FractionRing (MvPolynomial s K) ⊗[K] L) :=
    isReduced_fractionRing_mvPolynomial_tensorProduct K s L
  have : IsReduced (F ⊗[K] L) :=
    isReduced_of_injective (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).toAlgHom
      (AlgEquiv.injective _)
  have hD := isReduced_tensorProduct_of_isSeparable (F := F) (E := E) (F ⊗[K] L)
  exact @isReduced_of_injective _ _ _ _ _ _ _
    ((Algebra.TensorProduct.comm K L E).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange K F F E L).symm.toRingEquiv)
    (RingEquiv.injective _) hD

theorem isReduced_tensorProduct_of_perfectField (K : Type u) [Field K] [PerfectField K]
    (L : Type u) [Field L] [Algebra K L] (A : Type u) [CommRing A] [Algebra K A] [IsReduced A] :
    IsReduced (L ⊗[K] A) :=
  isReduced_tensorProduct_of_forall_field L
    (fun E _ _ _ => isReduced_tensorProduct_field_of_perfectField K L E) A

end

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open TensorProduct

noncomputable section

theorem RadicalBaseChange.proof : RadicalBaseChange.Statement := by
  intro K L _ _ _ σ ι I hI
  let : Algebra K L := σ.toAlgebra
  rw [Ideal.isRadical_iff_quotient_reduced] at hI ⊢
  have h1 : IsReduced (L ⊗[K] (MvPolynomial ι K ⧸ I)) :=
    isReduced_tensorProduct_of_perfectField K L _
  let e1 := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (MvPolynomial ι K) L I
  let e2 : L ⊗[K] MvPolynomial ι K ≃ₐ[L] MvPolynomial ι L := MvPolynomial.algebraTensorAlgEquiv K L
  have hmap : I.map (MvPolynomial.map σ) =
      (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L))).map
        (e2 : L ⊗[K] MvPolynomial ι K →+* MvPolynomial ι L) := by
    rw [← Ideal.map_coe (Algebra.TensorProduct.includeRight (R := K) (A := L)), Ideal.map_map]
    congr 1
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul, RingHom.algebraMap_toAlgebra]
    · intro i
      simp [e2, MvPolynomial.algebraTensorAlgEquiv_tmul]
  let e3 := Ideal.quotientEquivAlg (I.map (Algebra.TensorProduct.includeRight (R := K) (A := L)))
    (I.map (MvPolynomial.map σ)) e2 hmap
  exact isReduced_of_injective (e1.toRingEquiv.trans e3.toRingEquiv).symm (RingEquiv.injective _)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

theorem AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : NullMeasurableSet s μ) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ = ∫⁻ y in f '' s, g y ∂μ := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have himg : f '' t =ᵐ[μ] f '' s := by
    have hst : s = t ∪ (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [hst, image_union]
    refine (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ (fun x hx ↦ ?_)
      (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  rw [setLIntegral_congr t_eq_s.symm, ← setLIntegral_congr himg,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ht (fun x hx => (hf' x (ts hx)).mono ts)
      (hf.mono ts)]
  congr 1
  funext x
  exact mul_comm _ _

theorem AreaMultiplicityWeight.proof : AreaMultiplicityWeight.Statement := by
  intro E _ _ _ _ _ μ _ A f f' hA hf'
  classical
  set B : Set E := {x ∈ A | (f' x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hB : NullMeasurableSet B μ := by
    obtain ⟨d, hdm, hfd⟩ : AEMeasurable (fun x => (f' x).det) (μ.restrict A) :=
      ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
        (aemeasurable_fderivWithin μ hA hf')
    refine (hA.inter (hdm (measurableSet_singleton 0).compl)).nullMeasurableSet.congr ?_
    filter_upwards [(ae_restrict_iff' hA).1 hfd] with x hx
    change (x ∈ A ∩ d ⁻¹' {0}ᶜ) ↔ (x ∈ B)
    by_cases hxA : x ∈ A
    · simp [B, hxA, hx hxA]
    · simp [B, hxA]

  have hZ : μ (f '' {x ∈ A | (f' x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf' x hx.1).mono (sep_subset _ _)) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B f'
      (fun x hx => (hf' x hx.1).mono hBA) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, NullMeasurableSet (P n) μ := fun n => hB.inter (htm n).nullMeasurableSet
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x := fun n x hx =>
    (hf' x (hPA n hx)).mono (hPA n)
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (f' y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, NullMeasurableSet (f '' P n) μ := fun n =>
    nullMeasurable_image_of_fderivWithin μ (hPm n) (hderP n) (hinj n)

  have hNae : ∀ᵐ y ∂μ, ∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y =
      (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
    have hU : {x ∈ A | f x = y} = ⋃ n, {x ∈ P n | f x = y} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxA, hxy⟩
        have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
        exact ⟨n, ⟨hxB, hn⟩, hxy⟩
      · rintro ⟨n, hxP, hxy⟩
        exact ⟨hPA n hxP, hxy⟩
    rw [hU, encard_iUnion_nat_eq_tsum _ (fun m n hmn => (hPd hmn).mono (sep_subset _ _)
      (sep_subset _ _))]
    refine tsum_congr fun n => ?_
    by_cases hyn : y ∈ f '' P n
    · obtain ⟨x, hx, rfl⟩ := hyn
      have hs : {z ∈ P n | f z = f x} = {x} := by
        ext z
        simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => hinj n h.1 hx h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
      rw [hs, encard_singleton, indicator_of_mem (mem_image_of_mem f hx)]
      simp
    · have hs : {z ∈ P n | f z = y} = ∅ := by
        ext z
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hz e => hyn ⟨z, hz, e⟩
      rw [hs, encard_empty]
      simp [hyn]
  refine ⟨(AEMeasurable.tsum fun n => aemeasurable_one.indicator₀ (himg n)).congr hNae,
    fun g hg => ?_⟩
  calc ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ
      = ∫⁻ x in B, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [← lintegral_indicator hA, ← lintegral_indicator₀ hB]
        congr 1; ext x
        by_cases hx : x ∈ A
        · by_cases hd : (f' x).det = 0
          · simp [indicator, hx, hd, B]
          · simp [indicator, hx, hd, B]
        · have : x ∉ B := fun h => hx h.1
          simp [hx, this]
    _ = ∑' n, ∫⁻ x in P n, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [hBU]; exact lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _
    _ = ∑' n, ∫⁻ y in f '' P n, g y ∂μ := tsum_congr fun n =>
        AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ μ (hPm n) (hderP n) (hinj n) g
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator g y ∂μ :=
        tsum_congr fun n => (lintegral_indicator₀ (himg n) g).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator g y ∂μ :=
        (lintegral_tsum fun n => hg.aemeasurable.indicator₀ (himg n)).symm
    _ = ∫⁻ y, (∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y) * g y ∂μ := by
        congr 1; funext y
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        by_cases h : y ∈ f '' P n <;> simp [h]
    _ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hNae] with y hy
        rw [hy]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChowFormExtend

section Incidence

variable {F : Type*} [Field F] {n : ℕ}

def incidenceIdeal (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) :
    Ideal (MvPolynomial ((Fin k × Fin n) ⊕ Fin n) F) :=
  I.map (rename Sum.inr) ⊔
    Ideal.span (Set.range fun i : Fin k => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr j))

theorem mem_zeroLocus_incidenceIdeal {E : Type*} [Field E] [Algebra F E]
    (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) (z : (Fin k × Fin n) ⊕ Fin n → E) :
    z ∈ zeroLocus E (incidenceIdeal I k) ↔
      (∀ g ∈ I, aeval (z ∘ Sum.inr) g = 0) ∧ ∀ i, ∑ j, z (Sum.inl (i, j)) * z (Sum.inr j) = 0 := by
  have key : z ∈ zeroLocus E (incidenceIdeal I k) ↔ incidenceIdeal I k ≤ vanishingIdeal F {z} :=
    ⟨fun h p hp => (mem_vanishingIdeal_singleton_iff z p).2 (h p hp),
      fun h p hp => (mem_vanishingIdeal_singleton_iff z p).1 (h hp)⟩
  rw [key, incidenceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.range_subset_iff]
  refine and_congr ⟨fun h g hg => ?_, fun h g hg => ?_⟩ (forall_congr' fun i => ?_)
  · have := h hg
    rwa [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename] at this
  · rw [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename]
    exact h g hg
  · rw [SetLike.mem_coe, mem_vanishingIdeal_singleton_iff]
    simp

theorem vanishes_incidence_iff (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ)
    (g : MvPolynomial (Fin k × Fin n) F) :
    (∀ u ∈ incidence I k, aeval u g = 0) ↔
      ∀ j, X (Sum.inr j) * rename Sum.inl g ∈ (incidenceIdeal I k).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure F) (incidenceIdeal I k)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_incidenceIdeal]
  constructor
  · rintro h j z ⟨hI, hlin⟩
    rw [map_mul, aeval_X, aeval_rename]
    by_cases hx : z ∘ Sum.inr = 0
    · rw [show z (Sum.inr j) = 0 from congrFun hx j, zero_mul]
    · rw [h (z ∘ Sum.inl) ⟨z ∘ Sum.inr, hx, hI, hlin⟩, mul_zero]
  · rintro h u ⟨x, hx, hI, hlin⟩
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
    have := h j (Sum.elim u x) ⟨by simpa using hI, by simpa using hlin⟩
    rw [map_mul, aeval_X, aeval_rename] at this
    simpa [hj] using this

theorem incidenceIdeal_map {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) :
    incidenceIdeal (I.map (MvPolynomial.map σ)) k =
      (incidenceIdeal I k).map (MvPolynomial.map σ) := by
  rw [incidenceIdeal, incidenceIdeal, Ideal.map_sup, Ideal.map_span]
  congr 1
  · rw [← Ideal.map_coe (rename Sum.inr), ← Ideal.map_coe (rename Sum.inr), Ideal.map_map, Ideal.map_map]
    congr 1
    apply ringHom_ext <;> intro <;> simp
  · congr 1
    ext p
    simp

theorem radical_map_eq (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] (σ : K →+* L) {ι : Type} (J : Ideal (MvPolynomial ι K)) :
    (J.map (MvPolynomial.map σ)).radical = J.radical.map (MvPolynomial.map σ) :=
  le_antisymm
    ((h K L σ ι J.radical (Ideal.radical_isRadical J)).radical_le_iff.2
      (Ideal.map_mono Ideal.le_radical))
    (Ideal.map_radical_le _)

end Incidence

section Coord

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}

def coordPoly (φ : L →ₗ[K] K) : MvPolynomial Y L →+ MvPolynomial Y K where
  toFun p := AddMonoidAlgebra.map φ.toAddMonoidHom p
  map_zero' := by
    ext m
    simp [coeff_addMonoidAlgebraMap]
  map_add' p q := by
    ext m
    simp only [coeff_addMonoidAlgebraMap, MvPolynomial.coeff_add, map_add (f := _)]

theorem coeff_coordPoly (φ : L →ₗ[K] K) (p : MvPolynomial Y L) (m : Y →₀ ℕ) :
    AddMonoidAlgebra.coeff (coordPoly φ p) m = φ (AddMonoidAlgebra.coeff p m) :=
  rfl

theorem coordPoly_C_mul_map (φ : L →ₗ[K] K) (a : L) (q : MvPolynomial Y K) :
    coordPoly φ (C a * map (algebraMap K L) q) = C (φ a) * q := by
  ext m
  rw [coeff_coordPoly, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

variable {β : Type*} [DecidableEq β]

def coordSupport (b : Module.Basis β K L) (p : MvPolynomial Y L) : Finset β :=
  p.support.biUnion fun m => (b.repr (AddMonoidAlgebra.coeff p m)).support

theorem sum_coordPoly (b : Module.Basis β K L) (p : MvPolynomial Y L) :
    ∑ c ∈ coordSupport b p, C (b c) * map (algebraMap K L) (coordPoly (b.coord c) p) = p := by
  ext m
  rw [coeff_sum]
  simp_rw [coeff_C_mul, coeff_map, coeff_coordPoly, Module.Basis.coord_apply, mul_comm (b _),
    ← Algebra.smul_def]
  conv_rhs => rw [← b.linearCombination_repr (AddMonoidAlgebra.coeff p m)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  symm
  apply Finset.sum_subset
  · intro c hc
    have hm : m ∈ p.support := by
      rw [mem_support_iff]
      intro h0
      rw [h0, map_zero] at hc
      simp at hc
    exact Finset.mem_biUnion.2 ⟨m, hm, hc⟩
  · intro c _ hc
    rw [Finsupp.notMem_support_iff.1 hc, zero_smul]

theorem coordPoly_sum (b : Module.Basis β K L) (S : Finset β) (h : β → MvPolynomial Y K) (c : β) :
    coordPoly (b.coord c) (∑ c' ∈ S, C (b c') * map (algebraMap K L) (h c')) =
      if c ∈ S then h c else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [coordPoly_C_mul_map, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [apply_ite C, ite_mul]

theorem coordPoly_mem_of_mem_map (b : Module.Basis β K L) (T : Ideal (MvPolynomial Y K))
    {p : MvPolynomial Y L} (hp : p ∈ T.map (map (algebraMap K L))) (c : β) :
    coordPoly (b.coord c) p ∈ T := by
  have hp' : p ∈ Submodule.span (MvPolynomial Y L) ((map (algebraMap K L)) '' T) := hp
  clear hp
  revert c
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    intro c
    have e := coordPoly_C_mul_map (b.coord c) (1 : L) t
    rw [C_1, one_mul] at e
    rw [e]
    exact T.mul_mem_left _ ht
  | zero => intro c; rw [map_zero]; exact T.zero_mem
  | add x y _ _ hx hy => intro c; rw [map_add (f := _)]; exact T.add_mem (hx c) (hy c)
  | smul r x _ hx =>
    intro c
    have e : r * x = ∑ c₁ ∈ coordSupport b r, ∑ c₂ ∈ coordSupport b x,
        C (b c₁ * b c₂) * map (algebraMap K L) (coordPoly (b.coord c₁) r * coordPoly (b.coord c₂) x) := by
      conv_lhs => rw [← sum_coordPoly b r, ← sum_coordPoly b x]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      rw [C_mul, map_mul]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eq_mul, e, map_sum]
    refine T.sum_mem fun c₁ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine T.sum_mem fun c₂ _ => ?_
    rw [coordPoly_C_mul_map]
    exact T.mul_mem_left _ (T.mul_mem_left _ (hx c₂))

end Coord

theorem isChowForm_map (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] [Algebra K L] {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (hf : IsChowForm I k f) :
    IsChowForm (I.map (map (algebraMap K L))) k (map (algebraMap K L) f) := by
  obtain ⟨hf0, hf⟩ := hf
  set R := (incidenceIdeal I k).radical
  have hK := fun g => vanishes_incidence_iff I k g
  have hrad : (incidenceIdeal (I.map (map (algebraMap K L))) k).radical = R.map (map (algebraMap K L)) := by
    rw [incidenceIdeal_map, radical_map_eq h]
  have hmapX : ∀ (j : Fin n) (p : MvPolynomial (Fin k × Fin n) K),
      map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl p) =
        X (Sum.inr j) * rename Sum.inl (map (algebraMap K L) p) := by
    intro j p
    rw [map_mul, map_X, map_rename]
  refine ⟨fun h0 => hf0 (map_injective _ (algebraMap K L).injective (by rw [h0, map_zero])), fun g => ?_⟩
  rw [vanishes_incidence_iff, hrad]
  constructor
  · intro hg
    classical
    let b := Module.Basis.ofVectorSpace K L
    set S := coordSupport b g
    set hc := fun c => coordPoly (b.coord c) g
    have hsum : ∑ c ∈ S, C (b c) * map (algebraMap K L) (hc c) = g := sum_coordPoly b g
    have hdiv : ∀ c ∈ S, ∃ q, hc c = f * q := by
      intro c hcS
      refine (hf _).1 ((hK _).2 fun j => ?_)
      have e : X (Sum.inr j) * rename Sum.inl g = ∑ c' ∈ S,
          C (b c') * map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl (hc c')) := by
        conv_lhs => rw [← hsum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [map_mul, rename_C, hmapX]
        ring
      have hmem := coordPoly_mem_of_mem_map b R (e ▸ hg j) c
      rwa [coordPoly_sum, if_pos hcS] at hmem
    choose! q hq using hdiv
    refine ⟨∑ c ∈ S, C (b c) * map (algebraMap K L) (q c), ?_⟩
    conv_lhs => rw [← hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hcS => ?_
    rw [hq c hcS, map_mul]
    ring
  · rintro ⟨q, rfl⟩ j
    have hfR : X (Sum.inr j) * rename Sum.inl f ∈ R := (hK f).1 ((hf f).2 dvd_rfl) j
    have hmem := Ideal.mem_map_of_mem (map (algebraMap K L)) hfR
    rw [hmapX] at hmem
    rw [map_mul (rename Sum.inl), ← mul_assoc]
    exact Ideal.mul_mem_right _ _ hmem

theorem proof (h : RadicalBaseChange.Statement) : ChowFormExtend.Statement := by
  intro K L _ _ _ σ n k I f hf
  let _ : Algebra K L := σ.toAlgebra
  exact isChowForm_map h I f hf

end ChowFormExtend

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionAlgClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def ChowFormSectionAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I →
      IsChowFormCycle (divCycle I u) e (specFirst f u)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsProjSecDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def projVar (e : ℕ) (i : Fin (e + 1)) : FractionRing (MvPolynomial (Fin (e + 1)) ℂ) :=
  algebraMap (MvPolynomial (Fin (e + 1)) ℂ) (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (X i)

def projPar {n e : ℕ} (A : Matrix (Fin (e + 1)) (Fin n) ℂ) :
    Vertical.Par e n → FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
  | .inl (i, j) =>
      projVar e i.succ * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) -
        projVar e 0 * algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A i.succ j)
  | .inr j => algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)) (A 0 j) / projVar e 0

def ProjSecDegree.Statement : Prop :=
  ∀ (n e : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ),
    ComplexSets.projDegree J A =
      Module.finrank (FractionRing (MvPolynomial (Fin (e + 1)) ℂ))
        (Vertical.SecAlg
          (J.map (MvPolynomial.map (algebraMap ℂ (FractionRing (MvPolynomial (Fin (e + 1)) ℂ)))))
          (projPar A))

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionCycleReduced
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def SectionCycleReduced.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (J : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F),
    J.IsRadical →
    (∀ P ∈ J.minimalPrimes, ∀ Q ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ Q)) →
    (∀ P ∈ J.minimalPrimes, linForm u ∉ P) →
      fundCycle (J ⊔ Ideal.span {linForm u}) = ∑ P ∈ (fundCycle J).support, divCycle P u

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

variable {n : ℕ}

def ballH (h : HermNorm n) : Set (Fin n → ℂ) := {v | h.norm v < 1}

def nrmv (h : HermNorm n) (v : Fin n → ℂ) : Fin n → ℂ := fun j => ((h.norm v : ℝ) : ℂ)⁻¹ * v j

end

end GroundTheory.Heights₂.Heights
end
