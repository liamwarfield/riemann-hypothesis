module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapAreaOne
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMParameterQuotient
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalBranchedCovering
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalOpenMapping
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepAreaCount
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeChartGram
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMassFinite

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeTangentDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal

noncomputable section

variable {n : ℕ}

def HermNorm.pointEquiv (h : HermNorm n) : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (Matrix.toLinearEquiv' h.mat.transpose
      (Matrix.invertibleOfIsUnitDet _ (by rw [Matrix.det_transpose]; exact h.isUnit_det)))

theorem HermNorm.pointEquiv_apply (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.pointEquiv y = h.pointOf y := rfl

theorem hausdorffMeasure_pointOf_preimage_null (h : HermNorm n) {d : ℝ} (hd : 0 ≤ d)
    {S : Set (EuclideanSpace ℂ (Fin n))} (hS : μH[d] S = 0) :
    μH[d] {y | WithLp.toLp 2 (h.pointOf y) ∈ S} = 0 := by
  let E : EuclideanSpace ℂ (Fin n) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) :=
    h.pointEquiv.trans (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let F := LinearMap.toContinuousLinearMap E.symm.toLinearMap
  refine measure_mono_null (t := F '' S) (fun y hy => ⟨E y, hy, ?_⟩) ?_
  · simp [F]
  · exact le_zero_iff.1 ((F.lipschitz.hausdorffMeasure_image_le hd S).trans (by rw [hS, mul_zero]))

theorem frameDeriv_basisFun (j : Fin n) (g : MvPolynomial (Fin n) ℂ) :
    frameDeriv (EuclideanSpace.basisFun (Fin n) ℂ) j g = pderiv j g := by
  simp [frameDeriv, EuclideanSpace.basisFun_apply, PiLp.single_apply, apply_ite C, ite_mul]

theorem finrank_coneTangent_of_jacobian (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s : MvPolynomial (Fin n) ℂ)
    (hf : ∀ k, f k ∈ J) (hs : ∀ p ∈ J, s * p ∈ Ideal.span (Set.range f))
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ coneSet h J) (hsy : eval (h.pointOf y) s ≠ 0)
    (hD : eval (h.pointOf y) (frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f) ≠ 0) :
    finrank ℂ (coneTangent h J y) = I₀.card := by
  set x := h.pointOf y with hx
  let a : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun k j => eval x (pderiv j (f k))

  have hT : coneTangent h J y = (LinearMap.ker a.mulVecLin).comap h.pointEquiv.toLinearMap := by
    ext v
    simp only [coneTangent, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq, Submodule.mem_comap, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, HermNorm.pointEquiv_apply]
    constructor
    · intro hv
      funext k
      simpa [Matrix.mulVec, dotProduct, a] using hv (f k) (hf k)
    · intro hv q hq
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 (hs q hq)
      have hq0 : eval x q = 0 := hy q hq
      have hf0 : ∀ k, eval x (f k) = 0 := fun k => hy _ (hf k)
      have hder : ∀ j, eval x s * eval x (pderiv j q) = ∑ k, eval x (c k) * a k j := by
        intro j
        have := congrArg (fun P => eval x (pderiv j P)) hc
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, pderiv_mul, map_add (f := _), map_mul, hq0, hf0, mul_zero, zero_add] at this
        simpa [a, mul_comm] using this.symm
      have hk : ∀ k, ∑ j, a k j * h.pointOf v j = 0 := fun k => by
        simpa [Matrix.mulVec, dotProduct] using congrFun hv k
      have : eval x s * ∑ j, eval x (pderiv j q) * h.pointOf v j = 0 := by
        rw [Finset.mul_sum]
        simp_rw [← mul_assoc, hder, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp_rw [mul_assoc, ← Finset.mul_sum, hk, mul_zero, Finset.sum_const_zero]
      exact (mul_eq_zero.1 this).resolve_left hsy

  let M : Matrix {j // j ∉ I₀} {j // j ∉ I₀} ℂ := Matrix.of fun k j => a k j
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    convert hD using 1
    rw [frameJacobianDet, RingHom.map_det]
    congr 1
    ext k j
    simp [M, a, frameDeriv_basisFun]
  have hsurj : Function.Surjective a.mulVecLin := by
    intro t
    obtain ⟨v, hv⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM t
    refine ⟨fun j => if hj : j ∉ I₀ then v ⟨j, hj⟩ else 0, ?_⟩
    rw [← hv]
    funext k
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Matrix.of_apply]
    rw [← Finset.sum_subset (Finset.subset_univ I₀ᶜ) (fun j _ hj => by
      simp only [Finset.mem_compl, not_not] at hj; simp [hj]),
      Finset.sum_subtype I₀ᶜ (p := fun j => j ∉ I₀) (fun j => Finset.mem_compl)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [j.2]
  have hrank := LinearMap.finrank_range_add_finrank_ker a.mulVecLin
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fintype_fun_eq_card, Module.finrank_fin_fun,
    Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin] at hrank
  rw [hT, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  have hle : I₀.card ≤ n := by simpa using Finset.card_le_univ I₀
  omega

theorem ConeTangentDim.proof (hDim : ConeKrullDimLe.Statement) (hNull : NullSmaller.Statement)
    (hJac : FrameJacobianGeneric.Statement) : ConeTangentDim.Statement := by
  intro n m h J hJ hm hmn hfin
  have := hJ.isPrime
  rw [ae_restrict_iff' (isClosed_coneSet h J).measurableSet, ae_iff]
  rcases (hDim n m h J hJ hm hmn hfin).lt_or_eq with hlt | heq
  · refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m J hlt))
    exact fun q hq => (Classical.not_imp.1 hy).1 q hq
  · obtain ⟨I₀, f, s, hcard, hf, hsJ, hDJ, hspan⟩ :=
      hJac n m J hJ.isPrime heq (EuclideanSpace.basisFun (Fin n) ℂ)
    set D := frameJacobianDet (EuclideanSpace.basisFun (Fin n) ℂ) I₀ f
    have hsD : s * D ∉ J := fun h' => (hJ.isPrime.mem_or_mem h').elim hsJ hDJ
    have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {s * D})) < m := by
      rw [← ringKrullDim_eq_of_ringEquiv
          (R := (MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.map (Ideal.Quotient.mk J) (Ideal.span {s * D}))
          (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {s * D})),
        Ideal.map_span, Set.image_singleton]
      have hnz : Ideal.Quotient.mk J (s * D) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
        mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
      have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
      rw [heq] at h1
      by_contra hge
      have h2 : ((m : ℕ) : WithBot ℕ∞) + 1 ≤
          ringKrullDim ((MvPolynomial (Fin n) ℂ ⧸ J) ⧸ Ideal.span {Ideal.Quotient.mk J (s * D)}) + 1 := by
        gcongr; exact not_lt.1 hge
      have h3 := h2.trans h1
      exact absurd h3 (by exact_mod_cast (by omega : ¬ m + 1 ≤ m))
    refine measure_mono_null (fun y hy => ?_)
      (hausdorffMeasure_pointOf_preimage_null h (by positivity) (hNull n m _ hdim))
    obtain ⟨hyC, hyT⟩ := Classical.not_imp.1 hy
    have hsD0 : eval (h.pointOf y) (s * D) = 0 := by
      by_contra hne
      rw [map_mul] at hne
      exact hyT (hcard ▸ finrank_coneTangent_of_jacobian h J I₀ f s hf hspan y hyC
        (left_ne_zero_of_mul hne) (right_ne_zero_of_mul hne))
    intro q hq
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hq
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    change eval (h.pointOf y) (a + c * (s * D)) = 0
    rw [map_add (f := _), map_mul, hsD0, mul_zero, add_zero]
    exact hyC a ha

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeGraphCover
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal NNReal

noncomputable section

theorem coneSet_hausdorff_null_of_dim_lt {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J) = 0 := by
  set g : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.transpose h.mat)⁻¹)
  have hu : IsUnit (Matrix.transpose h.mat).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hsub : coneSet h J ⊆ g '' zeroSetEuc J := by
    intro y hy
    refine ⟨WithLp.toLp 2 (h.pointOf y), hy, ?_⟩
    ext i
    simp [g, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
  calc Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (g '' zeroSetEuc J)
      ≤ (‖g‖₊ : ℝ≥0∞) ^ ((2 * d : ℕ) : ℝ) * Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J) :=
        g.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [NullSmaller.proof n d J hd, mul_zero]

theorem ConeGraphCover.proof (hDim : ConeFiniteFibreDim.Statement) (hTan : ConeTangentDim.Statement)
    (hLoc : ConeSmoothLocalGraph.Statement) : ConeGraphCover.Statement := by
  intro n m h J hJ hm hmn hfib
  have e0 : Fin n ≃ Fin m ⊕ Fin (n - m) :=
    (finCongr (Nat.add_sub_cancel' hmn).symm).trans finSumFinEquiv.symm
  rcases (hDim n m h J hJ hm hmn hfib).lt_or_eq with hlt | heq
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    exact measure_mono_null Set.sdiff_subset (coneSet_hausdorff_null_of_dim_lt h J m hlt)

  set S := {y | y ∈ coneSet h J ∧ finrank ℂ (coneTangent h J y) = m} with hSdef
  have hbad : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ S) = 0 := by
    have hae := hTan n m h J hJ hm hmn hfib
    rw [ae_iff] at hae
    refine measure_mono_null ?_ (nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans hae.le))
    intro y hy
    exact ⟨fun h' => hy.2 ⟨hy.1, h'⟩, hy.1⟩

  have hloc := fun y (hy : y ∈ S) => hLoc n m h J hJ.isPrime heq y hy.1 hy.2
  have : Nonempty (Fin n ≃ Fin m ⊕ Fin (n - m)) := ⟨e0⟩
  choose! E Om Ph U hUo hyU hCU hΩ hΦ hG hT using hloc

  obtain ⟨T, hTS, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable S U hUo
  have hScov : S ⊆ ⋃ y ∈ T, graphPt (E y) (Ph y) '' Om y := by
    intro y hy
    have hy' : y ∈ ⋃ z ∈ S, U z := Set.mem_biUnion hy (hyU y hy)
    rw [← hTU] at hy'
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy'
    exact Set.mem_biUnion hz (hCU z (hTS hz) ⟨hy.1, hyz⟩)
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => ?_⟩
    have hy' := hScov hyS
    simp [hT0] at hy'
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    have hfS : ∀ i, f i ∈ S := fun i => hTS (by rw [hf]; exact Set.mem_range_self i)
    refine ⟨fun i => E (f i), fun i => Om (f i), fun i => Ph (f i),
      fun i => ⟨hΩ _ (hfS i), hΦ _ (hfS i), hG _ (hfS i), hT _ (hfS i)⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => hy.2 ?_⟩
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (hScov hyS)
    rw [hf] at hz
    obtain ⟨i, rfl⟩ := hz
    exact Set.mem_iUnion.2 ⟨i, hyz⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTangentGaussInvariant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped Matrix

open scoped ENNReal

noncomputable section

def unitMat {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis U.toLinearMap

theorem unitMat_mem {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    unitMat U ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  U.toMatrix_mem_unitaryGroup _ _

theorem unitary_apply_eq_sum {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (v : EuclideanSpace ℂ (Fin n)) (k : Fin n) : U v k = ∑ j, unitMat U k j * v j := by
  have h := LinearMap.toMatrix_mulVec_repr (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis U.toLinearMap v
  have h2 := congrFun h k
  simpa [unitMat, Matrix.mulVec, dotProduct] using h2.symm

theorem unitMat_mul_symm {n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    unitMat U * unitMat U.symm = 1 := by
  rw [unitMat, unitMat, ← LinearMap.toMatrix_mul]
  have : U.toLinearMap * U.symm.toLinearMap = 1 := LinearMap.ext fun x => by simp
  rw [this, LinearMap.toMatrix_one]

theorem sum_norm_sq_vecMul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (r : Fin n → ℂ) :
    ∑ j, ‖(r ᵥ* A) j‖ ^ 2 = ∑ j, ‖r j‖ ^ 2 := by
  have key : ∀ s : Fin n → ℂ, ((∑ j, ‖s j‖ ^ 2 : ℝ) : ℂ) = s ⬝ᵥ star s := by
    intro s
    simp [dotProduct, Complex.mul_conj']
  apply Complex.ofReal_injective
  rw [key (r ᵥ* A), key r, Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 hA, Matrix.vecMul_one]

theorem measurePreserving_vecMul {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    MeasurePreserving (fun r : Fin n → ℂ => r ᵥ* A) volume volume := by
  set f : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) := (Matrix.toLin' Aᵀ).restrictScalars ℝ with hf
  have hfun : (fun r : Fin n → ℂ => r ᵥ* A) = f := by
    funext r
    simp [hf, Matrix.toLin'_apply, Matrix.mulVec_transpose]
  have hdet : LinearMap.det f = 1 := by
    have hd : ‖A.det‖ = 1 := by
      have h1 : A.det ∈ unitary ℂ := Matrix.det_of_mem_unitary hA
      exact CStarRing.norm_of_mem_unitary h1
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose,
      Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, hd]
    norm_num
  have hmeas : Measurable (fun r : Fin n → ℂ => r ᵥ* A) := by
    apply Continuous.measurable
    fun_prop
  refine ⟨hmeas, ?_⟩
  rw [hfun, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; norm_num), hdet]
  simp

def matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) : Fin m → Fin n → ℂ :=
  fun i => π i ᵥ* unitMat U

theorem measurePreserving_matSub {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    MeasurePreserving (matSub (m := m) U) volume volume :=
  volume_preserving_pi fun _ => measurePreserving_vecMul (unitMat_mem U)

theorem matSub_symm_matSub {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) (π : Fin m → Fin n → ℂ) :
    matSub U.symm (matSub U π) = π := by
  funext i
  simp [matSub, Matrix.vecMul_vecMul, unitMat_mul_symm]

def matSubEquiv {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n)) :
    (Fin m → Fin n → ℂ) ≃ᵐ (Fin m → Fin n → ℂ) where
  toFun := matSub U
  invFun := matSub U.symm
  left_inv := matSub_symm_matSub U
  right_inv π := by simpa using matSub_symm_matSub U.symm π
  measurable_toFun := (measurePreserving_matSub U).measurable
  measurable_invFun := (measurePreserving_matSub U.symm).measurable

theorem linProj_matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) (v : EuclideanSpace ℂ (Fin n)) :
    linProj (matSub U π) v = linProj π (U v) := by
  simp only [linProj, matSub, unitary_apply_eq_sum, Matrix.vecMul, dotProduct]
  congr 1
  funext i
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem matGauss_matSub {m n : ℕ} (U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n))
    (π : Fin m → Fin n → ℂ) : matGauss (matSub U π) = matGauss π := by
  simp only [matGauss, matSub, sum_norm_sq_vecMul (unitMat_mem U)]

theorem firstCoordVec_eq_basisFun {n : ℕ} (hn : 0 < n) :
    firstCoordVec n = EuclideanSpace.basisFun (Fin n) ℂ ⟨0, hn⟩ := by
  ext j
  simp [firstCoordVec, EuclideanSpace.basisFun_apply, Fin.ext_iff]

theorem exists_unitary_leadCoordPlane {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (T : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (hT : finrank ℂ T = m)
    (y : EuclideanSpace ℂ (Fin n)) (hy : y ∈ T) :
    ∃ U : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin n),
      (∀ v ∈ leadCoordPlane n m, U v ∈ T) ∧ (∀ t ∈ T, ∃ v ∈ leadCoordPlane n m, U v = t) ∧
        U ((‖y‖ : ℂ) • firstCoordVec n) = y := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  obtain ⟨u, huT, hu1, hyu⟩ : ∃ u ∈ T, ‖u‖ = 1 ∧ (‖y‖ : ℂ) • u = y := by
    by_cases hy0 : y = 0
    · have hTne : T ≠ ⊥ := by
        intro h
        rw [h, finrank_bot] at hT
        omega
      obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hTne
      exact ⟨(‖t‖⁻¹ : ℂ) • t, T.smul_mem _ htT, norm_smul_inv_norm ht0, by simp [hy0]⟩
    · refine ⟨(‖y‖⁻¹ : ℂ) • y, T.smul_mem _ hy, norm_smul_inv_norm hy0, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast norm_ne_zero_iff.2 hy0), one_smul]
  obtain ⟨bT, hbT⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ) (E := T)
    (ι := Fin m) (v := fun _ => (⟨u, huT⟩ : T)) (s := {⟨0, hm⟩}) (by simp [hT]) (by
      refine ⟨fun i => by simpa using hu1, fun i j hij => ?_⟩
      exact absurd (Subtype.ext ((Set.mem_singleton_iff.1 i.2).trans
        (Set.mem_singleton_iff.1 j.2).symm)) hij)
  have hbT0 : (bT ⟨0, hm⟩ : EuclideanSpace ℂ (Fin n)) = u := by
    rw [hbT _ (Set.mem_singleton _)]
  set v : Fin n → EuclideanSpace ℂ (Fin n) :=
    fun j => if h : (j : ℕ) < m then (bT ⟨j, h⟩ : EuclideanSpace ℂ (Fin n)) else 0 with hv
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := EuclideanSpace ℂ (Fin n)) (ι := Fin n) (v := v) (s := {j | (j : ℕ) < m}) (by simp) (by
      rw [orthonormal_iff_ite]
      rintro ⟨i, hi⟩ ⟨j, hj⟩
      have hi' : (i : ℕ) < m := hi
      have hj' : (j : ℕ) < m := hj
      simp only [Set.domRestrict, hv, dif_pos hi', dif_pos hj']
      rw [← Submodule.coe_inner, orthonormal_iff_ite.1 bT.orthonormal]
      simp [Fin.ext_iff])
  have hBv : ∀ j : Fin n, ∀ h : (j : ℕ) < m, B j = (bT ⟨j, h⟩ : EuclideanSpace ℂ (Fin n)) := by
    intro j h
    rw [hB j h]
    simp [hv, h]
  set e := EuclideanSpace.basisFun (Fin n) ℂ with he
  have hU : ∀ w, e.equiv B (Equiv.refl _) w = ∑ j, w j • B j := by
    intro w
    conv_lhs => rw [← e.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, OrthonormalBasis.equiv_apply_basis, Equiv.refl_apply]
    rfl
  refine ⟨e.equiv B (Equiv.refl _), ?_, ?_, ?_⟩
  · intro w hw
    have hw' : ∀ j : Fin n, m ≤ (j : ℕ) → w j = 0 := hw
    rw [hU]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h : (j : ℕ) < m
    · rw [hBv j h]
      exact T.smul_mem _ (bT _).2
    · rw [hw' j (by omega), zero_smul]
      exact T.zero_mem
  · intro t ht
    have hBk : ∀ k : Fin m, B (Fin.castLE hmn k) = (bT k : EuclideanSpace ℂ (Fin n)) :=
      fun k => hBv _ (by simp)
    refine ⟨∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • e (Fin.castLE hmn k), ?_, ?_⟩
    · refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
      show ∀ j : Fin n, m ≤ (j : ℕ) → (e (Fin.castLE hmn k)) j = 0
      intro j hj
      have hne : j ≠ Fin.castLE hmn k := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [he, EuclideanSpace.basisFun_apply, hne]
    · calc e.equiv B (Equiv.refl _) (∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • e (Fin.castLE hmn k))
            = ∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • (bT k : EuclideanSpace ℂ (Fin n)) := by
              set_option synthInstance.maxHeartbeats 100000 in
                simp [map_sum, map_smul, OrthonormalBasis.equiv_apply_basis, hBk]
        _ = ((∑ k : Fin m, (bT.repr ⟨t, ht⟩ k) • bT k : T) : EuclideanSpace ℂ (Fin n)) := by
              simp
        _ = t := by rw [bT.sum_repr]
  · rw [firstCoordVec_eq_basisFun hn, map_smul, OrthonormalBasis.equiv_apply_basis,
      Equiv.refl_apply, hBv _ hm]
    rw [show (⟨((⟨0, hn⟩ : Fin n) : ℕ), hm⟩ : Fin m) = ⟨0, hm⟩ from rfl, hbT0, hyu]

theorem TangentGaussInvariant.proof : TangentGaussInvariant.Statement := by
  intro n m hm hmn T hT y hy
  obtain ⟨U, hLT, hTL, hUy⟩ := exists_unitary_leadCoordPlane hm hmn T hT y hy
  set L := leadCoordPlane n m with hL
  let W : L →ₗᵢ[ℂ] T :=
    { toFun := fun x => ⟨U x, hLT x x.2⟩
      map_add' := fun x x' => by ext1; simp
      map_smul' := fun c x => by ext1; simp
      norm_map' := fun x => by simp }
  have hWx : ∀ x : L, (W x : EuclideanSpace ℂ (Fin n)) = U x := fun _ => rfl
  have hWsurj : Function.Surjective W := by
    intro t
    obtain ⟨w, hw, hwt⟩ := hTL t t.2
    exact ⟨⟨w, hw⟩, Subtype.ext hwt⟩
  have hfin : finrank ℂ L = finrank ℂ T :=
    (LinearEquiv.ofBijective W.toLinearMap ⟨W.injective, hWsurj⟩).finrank_eq
  have hJ : ∀ π : Fin m → Fin n → ℂ, tangentJac (matSub U π) L = tangentJac π T := by
    intro π
    have hcomp : (linProjₗ (matSub U π)).comp L.subtype =
        ((linProjₗ π).comp T.subtype).comp W.toLinearMap := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearIsometry.coe_toLinearMap,
        hWx]
      exact linProj_matSub U π x
    unfold tangentJac
    have h2 := LinearMap.normDet_comp_of_finrank_eq (𝕜 := ℂ) (U := L) (V := T)
      (W := EuclideanSpace ℂ (Fin m)) W.toLinearMap ((linProjₗ π).comp T.subtype) (by exact hfin)
    rw [hcomp, h2, LinearIsometry.normDet_eq_one, mul_one]
  have hemb : MeasurableEmbedding (matSub (m := m) U) := (matSubEquiv U).measurableEmbedding
  have key := (measurePreserving_matSub (m := m) U).lintegral_comp_emb hemb
    (fun π => matGauss π *
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
        (linProj π (((‖y‖ : ℝ) : ℂ) • firstCoordVec n)) *
      ENNReal.ofReal (tangentJac π (leadCoordPlane n m)))
  unfold tangentGaussProfile
  refine Eq.trans ?_ key
  refine lintegral_congr fun π => ?_
  simp only [matGauss_matSub, linProj_matSub, hUy, ← hL, hJ]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSpecFirstHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem specFirstVar_isWeightedHomogeneous {k n : ℕ} (u : Fin n → ℂ) (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    have h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0 := by
      funext i
      simp [groupWeight, Fin.succ_ne_zero i]
    rw [h0]
    simpa [specFirstVar] using isWeightedHomogeneous_C (groupWeight k n) (u j)
  | succ i' =>
    have h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j) := by
      funext i
      simp [groupWeight, Pi.single_apply]
    rw [h1]
    simpa [specFirstVar] using isWeightedHomogeneous_X ℂ (groupWeight k n) (i', j)

theorem SpecFirstHomog.proof : SpecFirstHomog.Statement := by
  intro n k δ f u hf
  unfold IsMultiHomog specFirst
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous u ij).pow _

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PProjPrimeHasPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem ProjPrimeHasPoint.proof : ProjPrimeHasPoint.Statement := by
  intro F _ n W hW
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.isRelevant
  by_contra hcon
  push Not at hcon
  apply hj
  have hmem : (X j : MvPolynomial (Fin n) F) ∈
      vanishingIdeal F (zeroLocus (AlgebraicClosure F) W) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      simp
    · obtain ⟨q, hq, hne⟩ := hcon x hx0
      exact absurd (hx q hq) hne
  rwa [IsPrime.vanishingIdeal_zeroLocus] at hmem

end GroundTheory.Heights₂.Heights
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ChowFormBaseChange.full : ChowFormBaseChange.Statement :=
  (ChowFormBaseChange.proof
    RadicalBaseChange.proof
    (ChowFormExtend.proof RadicalBaseChange.proof)
    (ChowFormReduced.proof_of_prime_separate
      IncIdealPrime.full
      (IncIdealSeparate.proof
        IncidenceZeroLocus.proof
        (FormsThroughPoint.proof
          IncidenceZeroLocus.proof
          ThroughPointIncIdeal.proof
          (ChartZeroTrdeg.proof AffineChartTrdeg.full)
          (ThroughTwoPointsTrdeg.proof TrdegAdjoinLe.proof)
          TrdegBaseAlgebraic.proof)
        (IncIdealNeBotDim.proof IncIdealDim.full))))

theorem BaseChangeAvoid.full : BaseChangeAvoid.Statement :=
  BaseChangeAvoid.proof

theorem ProjPrimeHasPoint.full : ProjPrimeHasPoint.Statement :=
  ProjPrimeHasPoint.proof

theorem ChowFormSectionVertical.full : ChowFormSectionVertical.Statement :=
  Vertical.ChowFormSectionVertical.full

theorem ConeMassOfFibre.full : ConeMassOfFibre.Statement :=
  (ConeMassOfFibre.of_open
    ConeFiniteFibreDim.proof
    (ConeGraphCover.proof
      ConeFiniteFibreDim.proof
      (ConeTangentDim.proof
        (ConeKrullDimLe.proof ConeFiniteFibreDim.proof)
        NullSmaller.full
        (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
      (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof HolomorphicImplicitGraph.proof))
    (ConeJacMeasurable.proof TangentJacCompress.proof KernelProjMeasurable.proof)
    (ConeTangentDim.proof
      (ConeKrullDimLe.proof ConeFiniteFibreDim.proof)
      NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
    (GraphAreaFibre.proof
      (GraphAreaIntegral.proof GraphAreaHolomorphic.full)
      TangentJacComp.proof
      AreaMultiplicityWeight.proof)
    TangentGaussInvariant.proof)

theorem ConeIntegralMass.full : ConeIntegralMass.Statement :=
  (ConeIntegralMass.proof ConeFibreDegree.full ConeMassOfFibre.full)

theorem ConeBallFinite.full : ConeBallFinite.Statement :=
  (ConeBallFinite.proof ConeIntegralMass.full)

theorem ConeFsLogIntegrable.full : ConeFsLogIntegrable.Statement :=
  (ConeFsLogIntegrable.proof ConeBallFinite.full ConeSlabBound.full)

end GroundTheory.Heights₂.Heights
