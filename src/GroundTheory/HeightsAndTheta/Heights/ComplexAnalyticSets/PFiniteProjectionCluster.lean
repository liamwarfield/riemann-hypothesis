module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameGraphGeneric

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjectionCluster
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Topology

noncomputable section

namespace FiniteProjectionCluster

variable {n d : ℕ}

theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by
    ext x; simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem exists_monic (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (j : Fin n) :
    ∃ P : Polynomial (MvPolynomial (Fin d) ℂ), P.Monic ∧
      ∀ x ∈ zeroSet J, (P.map (eval (A.mulVec x))).IsRoot (x j) := by
  obtain ⟨P, hPm, hP⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J (X j))
  refine ⟨P, hPm, fun x hx => ?_⟩
  have hf : (projHom J A).toRingHom = (Ideal.Quotient.mk J).comp (pullback A).toRingHom := rfl
  rw [hf, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hP
  have h0 := hx _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) :=
    RingHom.ext (FibreBound.eval_pullback A x)
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0

theorem exists_bound (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (c : Fin d → ℂ) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ zeroSet J, dist (A.mulVec x) c ≤ R → ‖x‖ ≤ C := by
  choose P hPm hP using exists_monic J A hA
  let g : (Fin d → ℂ) → ℝ := fun y =>
    ∑ j, (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval y ((P j).coeff i)‖)
  have hg : Continuous g :=
    continuous_finsetSum _ fun j _ => continuous_const.add
      (continuous_finsetSum _ fun i _ => (MvPolynomial.continuous_eval _).norm)
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x hx hd => ?_⟩
  have hy : A.mulVec x ∈ Metric.closedBall c R := hd
  have hgC : g (A.mulVec x) ≤ C := (Real.le_norm_self _).trans (hC _ hy)
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hC _ hy))).2 fun j => ?_
  have hj := IndefiniteRowSideFullHecke.ComplexSets.norm_lt_of_isRoot_map_eval (hPm j) (A.mulVec x) (hP j x hx)
  have hle : (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval (A.mulVec x) ((P j).coeff i)‖) ≤
      g (A.mulVec x) :=
    Finset.single_le_sum (f := fun j => 1 + ∑ i ∈ Finset.range (P j).natDegree,
      ‖eval (A.mulVec x) ((P j).coeff i)‖)
      (fun k _ => add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (Finset.mem_univ j)
  linarith

theorem fibre_finite (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (y : Fin d → ℂ) :
    {x | x ∈ zeroSet J ∧ A.mulVec x = y}.Finite := by
  choose P hPm hP using exists_monic J A hA
  refine (Set.Finite.pi (t := fun j => {a | ((P j).map (eval y)).IsRoot a})
    fun j => Polynomial.finite_setOfPred_isRoot ((hPm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxA⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  intro j
  rw [← hxA]
  exact hP j x hx

end FiniteProjectionCluster


open FiniteProjectionCluster in
theorem FiniteProjectionCluster.proof : FiniteProjectionCluster.Statement := by
  intro n d J A w U hA hw hU
  have hcont : Continuous fun x : Fin n → ℂ => A.mulVec x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  obtain ⟨C, hC⟩ := exists_bound J A hA (A.mulVec w) 1
  have hF := fibre_finite J A hA (A.mulVec w)
  obtain ⟨ε0, hε0, hballU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, ⟨hε, hεlt⟩, hεF⟩ :=
    ((Set.Ioo_infinite hε0).sdiff (hF.image fun x => dist x w)).nonempty
  set K := zeroSet J ∩ {x | dist (A.mulVec x) (A.mulVec w) ≤ 1} ∩ Metric.sphere w ε with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact ((isClosed_zeroSet J).inter (isClosed_le (hcont.dist continuous_const)
        continuous_const)).inter Metric.isClosed_sphere
    · exact (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx =>
        mem_closedBall_zero_iff.2 (hC x hx.1.1 hx.1.2)
  have hT : IsCompact (A.mulVec '' K) := hKc.image hcont
  have hnot : A.mulVec w ∉ A.mulVec '' K := by
    rintro ⟨x, ⟨⟨hx, _⟩, hxs⟩, hxA⟩
    exact hεF ⟨x, ⟨hx, hxA⟩, hxs⟩
  obtain ⟨r0, hr0, hr0T⟩ := Metric.isOpen_iff.1 hT.isClosed.isOpen_compl _ hnot
  refine ⟨min r0 1, Metric.ball w ε, (Metric.closedBall w ε)ᶜ, lt_min hr0 one_pos, Metric.isOpen_ball,
    Metric.isClosed_closedBall.isOpen_compl, Metric.mem_ball_self hε,
    (Metric.ball_subset_ball hεlt.le).trans hballU,
    Set.disjoint_left.2 fun x hx hx' => hx' (Metric.ball_subset_closedBall hx), ?_, ?_⟩
  · rintro x ⟨hx, hxr⟩
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hxr
    by_cases h : dist x w < ε
    · exact Or.inl h
    · refine Or.inr fun hcb => ?_
      have heq : dist x w = ε := le_antisymm hcb (not_lt.1 h)
      have hxK : x ∈ K := ⟨⟨hx, hxr'.le.trans (min_le_right _ _)⟩, heq⟩
      exact hr0T (Metric.mem_ball.2 (hxr'.trans_le (min_le_left _ _))) ⟨x, hxK, rfl⟩
  · refine (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx => ?_
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hx.2
    exact mem_closedBall_zero_iff.2 (hC x hx.1 (hxr'.le.trans (min_le_right _ _)))

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

theorem AreaGraph.proof (h : AreaGraphBound.Statement) : AreaGraph.Statement := by
  intro k m U F hU hF A hAU hA

  change μH[(k : ℝ)] (realGraphPt F '' A) =
    ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])
  set S := μH[(k : ℝ)] (realGraphPt F '' A)
  set I := ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)])

  have hplus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.add continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hminus : ∀ j : ℕ,
      Tendsto (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) (𝓝[>] 0) (𝓝 1) := by
    intro j
    have hcont : Continuous (fun δ : ℝ≥0 => ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ j) :=
      (ENNReal.continuous_pow j).comp (ENNReal.continuous_coe.comp (continuous_const.sub continuous_id))
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds

  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), 0 < δ ∧ δ < 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ≥0) < 1 from one_pos)] with δ hδ
    exact hδ
  have hb : ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0),
      S ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) * I ∧
        ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * I ≤ ((1 + δ : ℝ≥0) : ℝ≥0∞) * S := by
    filter_upwards [hev] with δ hδ
    exact h k m U F hU hF A hAU hA δ hδ.1 hδ.2
  apply le_antisymm
  · have hlim := ENNReal.Tendsto.mul_const (hplus (k + 1)) (b := I) (Or.inl one_ne_zero)
    rw [one_mul] at hlim
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hb.mono fun δ hδ => hδ.1)
  · have hlim₁ := ENNReal.Tendsto.mul_const (hminus k) (b := I) (Or.inl one_ne_zero)
    have hlim₂ := ENNReal.Tendsto.mul_const (by simpa using hplus 1) (b := S) (Or.inl one_ne_zero)
    rw [one_mul] at hlim₁ hlim₂
    exact le_of_tendsto_of_tendsto hlim₁ hlim₂ (hb.mono fun δ hδ => hδ.2)

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFrameJacobianSum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Finset Module

noncomputable section

namespace FrameJacobianSumAlt

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem real_inner_eq_re (x y : EuclideanSpace ℂ ι) : inner ℝ x y = (inner ℂ x y).re := by
  simp [PiLp.inner_apply, Complex.re_sum, Complex.inner]

theorem adjoint_restrictScalars (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.adjoint (S.restrictScalars ℝ) = (LinearMap.adjoint S).restrictScalars ℝ := by
  symm
  rw [LinearMap.eq_adjoint_iff]
  intro x y
  rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, real_inner_eq_re,
    real_inner_eq_re, LinearMap.adjoint_inner_left]

theorem areaJacobian_restrictScalars (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    areaJacobian (S.restrictScalars ℝ) = ‖LinearMap.det (LinearMap.adjoint S ∘ₗ S)‖ := by
  rw [areaJacobian, adjoint_restrictScalars, ← LinearMap.restrictScalars_comp,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.norm_def]

theorem det_adjoint_comp (S : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ ι) :
    LinearMap.det (LinearMap.adjoint S ∘ₗ S) =
      (Matrix.of fun i j : Fin d => inner ℂ (S (EuclideanSpace.basisFun (Fin d) ℂ i))
        (S (EuclideanSpace.basisFun (Fin d) ℂ j))).det := by
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℂ).toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    LinearMap.adjoint_inner_right, Matrix.of_apply]

end FrameJacobianSumAlt


open FrameJacobianSumAlt in
theorem FrameJacobianSum.proof : FrameJacobianSum.Statement := by
  intro d n T b
  classical
  set e := EuclideanSpace.basisFun (Fin d) ℂ
  set N : Matrix (Fin n) (Fin d) ℂ := Matrix.of fun k j => inner ℂ (b k) (T (e j)) with hN
  have hI : ∀ (I : Finset (Fin n)) (h : I.card = d),
      areaJacobian ((frameProjLin b I ∘ₗ T).restrictScalars ℝ) = ‖(rowsOf N ⟨I, h⟩).det‖ ^ 2 := by
    intro I h
    rw [areaJacobian_restrictScalars, det_adjoint_comp]
    have hG : (Matrix.of fun i j : Fin d => inner ℂ ((frameProjLin b I ∘ₗ T) (e i))
        ((frameProjLin b I ∘ₗ T) (e j))) = (rowsOf N ⟨I, h⟩)ᴴ * rowsOf N ⟨I, h⟩ := by
      ext i j
      rw [Matrix.of_apply, PiLp.inner_apply, Matrix.mul_apply, ← (I.orderIsoOfFin h).toEquiv.sum_comp]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp [rowsOf, hN, frameProjLin, conjTranspose_apply, e, RCLike.inner_apply, mul_comm]
    rw [hG, det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul', norm_pow,
      Complex.norm_real, norm_norm]
  have hT : LinearMap.det (LinearMap.adjoint T ∘ₗ T) =
      ∑ I : {I : Finset (Fin n) // I.card = d}, ((‖(rowsOf N I).det‖ ^ 2 : ℝ) : ℂ) := by
    rw [det_adjoint_comp]
    have hG : (Matrix.of fun i j : Fin d => inner ℂ (T (e i)) (T (e j))) = Nᴴ * N := by
      ext i j
      rw [Matrix.of_apply, ← b.sum_inner_mul_inner, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [hN, conjTranspose_apply]
    rw [hG, CauchyBinet.proof]
    refine Finset.sum_congr rfl fun I _ => ?_
    have hc : colsOf Nᴴ I = (rowsOf N I)ᴴ := by
      ext i j
      simp [colsOf, rowsOf, conjTranspose_apply]
    rw [hc, det_conjTranspose, Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  rw [areaJacobian_restrictScalars, hT, ← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity),
    Finset.sum_subtype (univ.powersetCard d) (p := fun I : Finset (Fin n) => I.card = d)
      (fun I => by simp [mem_powersetCard])]
  exact Finset.sum_congr rfl fun I _ => (hI I.1 I.2).symm

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBranchContainsNormalPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology

theorem HolomorphicOnSubset.continuousWithinAt {σ : Type*} [Fintype σ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : (σ → ℂ) → E} {S : Set (σ → ℂ)}
    (hf : HolomorphicOnSubset f S) {z : σ → ℂ} (hz : z ∈ S) : ContinuousWithinAt f S z := by
  obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hf z hz
  have hc : ContinuousWithinAt F S z :=
    (hF.differentiableAt (hUo.mem_nhds hzU)).continuousAt.continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (hFeq ⟨hz, hzU⟩)
  filter_upwards [inter_mem_nhdsWithin S (hUo.mem_nhds hzU)] with y hy
  exact hFeq hy

theorem BranchContainsNormalPoint.proof (hirr : NormalLocallyIrreducible.Statement)
    (hinv : BranchInverseHolomorphic.Statement) (hext : NormalRiemannExtension.Statement)
    (hmax : NormalMaximumPrinciple.Statement) : BranchContainsNormalPoint.Statement := by
  intro σ _ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  obtain ⟨B', hB'o, hwB', hB'B, -, hdense⟩ := hirr σ I h w hI hIc hh hw B hB
  set P := (zeroSetIn I ∩ B') \ {z | eval z h = 0} with hP
  have hPfill : P ⊆ φ '' Metric.ball 0 r := fun z hz => hfill ⟨⟨hz.1.1, hB'B hz.1.2⟩, hz.2⟩
  have hPsub : P ⊆ zeroSetIn I ∩ B' := fun y hy => hy.1
  have hwcl : w ∈ closure P := hdense ⟨hw, hwB'⟩
  obtain ⟨ψ, hψ, hψφ⟩ := hinv σ I h w k r φ B hI hIc hh hw hφd hφi hφZ hB hfill
  have hPψ : ∀ z ∈ P, ψ z ∈ Metric.ball (0 : Fin k → ℂ) r ∧ φ (ψ z) = z := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hPfill hz
    rw [hψφ t ht]
    exact ⟨ht, rfl⟩
  have hPlt : ∀ z ∈ P, ∀ j, ‖ψ z j‖ < r := fun z hz j =>
    (norm_le_pi_norm (ψ z) j).trans_lt (mem_ball_zero_iff.mp (hPψ z hz).1)

  have hcoord : ∀ j : Fin k, ∃ g : (σ → ℂ) → ℂ, HolomorphicOnSubset g (zeroSetIn I ∩ B') ∧
      Set.EqOn g (fun z => ψ z j) P := by
    intro j
    refine hext σ I h B' (fun z => ψ z j) hI hIc hh hB'o ?_ ?_
    · intro z hz
      obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hψ z (hPfill hz)
      exact ⟨U, hUo, hzU, fun y => F y j, differentiableOn_pi.mp hF j,
        fun y hy => congrFun (hFeq ⟨hPfill hy.1, hy.2⟩) j⟩
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := r)).subset ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hPlt z hz j).le
  choose g hg hgeq using hcoord

  have hgle : ∀ j, ∀ z ∈ zeroSetIn I ∩ B', ‖g j z‖ ≤ r := by
    intro j z hz
    have hcl := (((hg j).continuousWithinAt hz).mono hPsub).mem_closure_image (hdense hz)
    have hsub : g j '' P ⊆ Metric.closedBall 0 r := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right, hgeq j hy]
      exact (hPlt y hy j).le
    have := closure_minimal hsub Metric.isClosed_closedBall hcl
    rwa [Metric.mem_closedBall, dist_zero_right] at this

  have hglt : ∀ j, ‖g j w‖ < r := by
    intro j
    by_contra hlt
    have heq : ‖g j w‖ = r := le_antisymm (hgle j w ⟨hw, hwB'⟩) (not_lt.mp hlt)
    have hev := hmax σ I w B' (g j) hI hIc hw (hB'o.mem_nhds hwB') (hg j)
      (fun z hz => (hgle j z hz).trans heq.ge)
    obtain ⟨z, hz, hzP⟩ := mem_closure_iff_nhds.mp hwcl _ hev
    have h1 : ‖g j z‖ < r := (congrArg norm (hgeq j hzP)).trans_lt (hPlt z hzP j)
    rw [hz hzP.1.1, heq] at h1
    exact lt_irrefl r h1
  have hr : 0 < r := by
    obtain ⟨z, -, hzP⟩ := mem_closure_iff_nhds.mp hwcl _ Filter.univ_mem
    exact (norm_nonneg _).trans_lt (mem_ball_zero_iff.mp (hPψ z hzP).1)
  set t₀ : Fin k → ℂ := fun j => g j w with ht₀
  have ht₀Δ : t₀ ∈ Metric.ball (0 : Fin k → ℂ) r := mem_ball_zero_iff.mpr ((pi_norm_lt_iff hr).mpr hglt)
  refine ⟨t₀, ht₀Δ, ?_⟩

  have : (𝓝[P] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hwcl
  have hG : Tendsto (fun z => fun j => g j z) (𝓝[P] w) (𝓝 t₀) :=
    tendsto_pi_nhds.mpr fun j => (((hg j).continuousWithinAt ⟨hw, hwB'⟩).mono hPsub).tendsto
  have hφc : ContinuousAt φ t₀ := (hφd.differentiableAt (Metric.isOpen_ball.mem_nhds ht₀Δ)).continuousAt
  have h1 : Tendsto (fun z => φ (fun j => g j z)) (𝓝[P] w) (𝓝 (φ t₀)) := hφc.tendsto.comp hG
  have h2 : Tendsto (fun z => φ (fun j => g j z)) (𝓝[P] w) (𝓝 w) := by
    refine (tendsto_id.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hgz : (fun j => g j z) = ψ z := funext fun j => hgeq j hz
    rw [hgz, (hPψ z hz).2]
    rfl
  exact tendsto_nhds_unique h1 h2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal NNReal

theorem realGraphPt_injective {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)) :
    Function.Injective (realGraphPt F) := by
  intro x y hxy
  ext i
  simpa [realGraphPt] using congrArg (fun z : EuclideanSpace ℝ (Fin k ⊕ Fin m) => z (Sum.inl i)) hxy

theorem realGraphPt_continuousOn {k m : ℕ} {F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin k))} (hF : ContinuousOn F s) : ContinuousOn (realGraphPt F) s := by
  unfold realGraphPt
  refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun i => ?_)
  rcases i with i | i
  · exact (PiLp.continuous_apply 2 _ i).continuousOn
  · exact (PiLp.continuous_apply 2 _ i).comp_continuousOn hF

theorem AreaGraphBound.proof (h₁ : AreaGraphPiece.Statement) (h₂ : AreaGraphPartition.Statement)
    (h₃ : GraphJacContinuous.Statement) : AreaGraphBound.Statement := by
  intro k m U F hU hF A hAU hA δ hδ0 hδ1
  set J : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) → ℝ≥0∞ := fun B =>
    ENNReal.ofReal (graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) with hJ
  set c : ℝ≥0∞ := ((1 + δ : ℝ≥0) : ℝ≥0∞) with hc

  choose r₃ hr₃0 hr₃ using fun B => h₃ k m B δ (by exact_mod_cast hδ0)
  obtain ⟨t, An, hdisj, htm, -, hcov, happrox, hder⟩ :=
    h₂ k m U F hU hF (fun B => min δ (r₃ B).toNNReal)
      (fun B => (lt_min hδ0 (Real.toNNReal_pos.2 (hr₃0 B))).ne')
  set p : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => A ∩ t n with hp
  have hpm : ∀ n, MeasurableSet (p n) := fun n => hA.inter (htm n)
  have hpd : Pairwise (Function.onFun Disjoint p) := fun i j hij =>
    (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hAp : A = ⋃ n, p n := by
    rw [← Set.inter_iUnion]
    exact (Set.inter_eq_left.2 (hAU.trans hcov)).symm

  have hcmp : ∀ n, ∀ x ∈ p n, J (fderiv ℝ F x) ≤ c * J (An n) ∧ J (An n) ≤ c * J (fderiv ℝ F x) := by
    intro n x hx
    have hle : ‖fderiv ℝ F x - An n‖ ≤ r₃ (An n) := by
      have := (hder n x hx.2).trans (min_le_right _ _)
      have h' : ((‖fderiv ℝ F x - An n‖₊ : ℝ≥0) : ℝ) ≤ ((r₃ (An n)).toNNReal : ℝ) := by exact_mod_cast this
      simpa [Real.coe_toNNReal _ (hr₃0 (An n)).le] using h'
    obtain ⟨h1, h2⟩ := hr₃ (An n) (fderiv ℝ F x) hle
    have e : ∀ y : ℝ, ENNReal.ofReal ((1 + δ) * y) = c * ENNReal.ofReal y := fun y => by
      rw [ENNReal.ofReal_mul (by positivity), hc]; congr 1
      rw [← ENNReal.ofReal_coe_nnreal]; push_cast; rfl
    exact ⟨(ENNReal.ofReal_le_ofReal h1).trans (e _).le, (ENNReal.ofReal_le_ofReal h2).trans (e _).le⟩

  have hpiece : ∀ n, μH[(k : ℝ)] (realGraphPt F '' p n) ≤ c ^ (k + 1) * ∫⁻ x in p n, J (fderiv ℝ F x)
      ∂(μH[(k : ℝ)]) ∧ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤
        c * μH[(k : ℝ)] (realGraphPt F '' p n) := by
    intro n
    obtain ⟨u, l⟩ := h₁ k m F (An n) δ (p n) hδ1
      (((happrox n).mono_set Set.inter_subset_right).mono_num (min_le_left _ _))
    have i₁ : J (An n) * μH[(k : ℝ)] (p n) ≤ c * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) := by
      rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact setLIntegral_mono' (hpm n) fun x hx => (hcmp n x hx).2
    have i₂ : ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤ c * (J (An n) * μH[(k : ℝ)] (p n)) := by
      rw [← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
      exact setLIntegral_mono' (hpm n) fun x hx => (hcmp n x hx).1
    constructor
    · calc _ ≤ c ^ k * (J (An n) * μH[(k : ℝ)] (p n)) := by rw [← mul_assoc]; exact u
        _ ≤ c ^ k * (c * ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)])) := by gcongr
        _ = _ := by rw [pow_succ, mul_assoc]
    · calc _ ≤ ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * (c * (J (An n) * μH[(k : ℝ)] (p n))) := by gcongr
        _ = c * (((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * J (An n) * μH[(k : ℝ)] (p n)) := by ring
        _ ≤ _ := by gcongr

  have hG : ∀ n, MeasurableSet (realGraphPt F '' p n) := fun n =>
    (hpm n).image_of_continuousOn_injOn
      (realGraphPt_continuousOn (hF.continuousOn.mono (Set.inter_subset_left.trans hAU)))
      (realGraphPt_injective F).injOn
  have hGd : Pairwise (Function.onFun Disjoint fun n => realGraphPt F '' p n) := fun i j hij =>
    (Set.disjoint_image_iff (realGraphPt_injective F)).2 (hpd hij)
  have hS : μH[(k : ℝ)] (realGraphPt F '' A) = ∑' n, μH[(k : ℝ)] (realGraphPt F '' p n) := by
    rw [hAp, Set.image_iUnion, measure_iUnion hGd hG]
  have hI : ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) =
      ∑' n, ∫⁻ x in p n, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) := by
    rw [hAp, lintegral_iUnion hpm hpd]
  change μH[(k : ℝ)] (realGraphPt F '' A) ≤ c ^ (k + 1) * ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ∧
    ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k * ∫⁻ x in A, J (fderiv ℝ F x) ∂(μH[(k : ℝ)]) ≤
      c * μH[(k : ℝ)] (realGraphPt F '' A)
  rw [hS, hI, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact ⟨ENNReal.tsum_le_tsum fun n => (hpiece n).1, ENNReal.tsum_le_tsum fun n => (hpiece n).2⟩

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularOffHypersurface
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem exists_ringKrullDim_quotient_eq_nat {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) :
    ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
  have : J.IsPrime := hJ
  have hge : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) :=
    ringKrullDim_nonneg_of_nontrivial
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (n : WithBot ℕ∞) := by
    refine (ringKrullDim_quotient_le J).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      Fintype.card_fin, zero_add]
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hge hle
  induction x using WithBot.recBotCoe with
  | bot => exact absurd hge (by simp)
  | coe m =>
    induction m using ENat.recTopCoe with
    | top => exact absurd hle (by norm_cast)
    | coe d => exact ⟨d, rfl⟩

theorem analyticOnNhd_of_differentiableOn_fin {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by
  intro y hy
  refine AnalyticAt.pi fun s => ?_
  have hs : DifferentiableOn ℂ (fun x => G x s) U :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) s).differentiable.comp_differentiableOn hG
  refine analyticOnNhd_of_continuousOn_of_separately hU hs.continuousOn (fun z hz i => ?_) y hy
  have h1 : DifferentiableAt ℂ (fun x => G x s) (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hs.differentiableAt (hU.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update (𝕜 := ℂ) z (z i)).differentiableAt

theorem RegularOffHypersurface.proof (hG : FrameGraphGeneric.Statement) : RegularOffHypersurface.Statement := by
  intro σ _ I hI
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := I.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (q : MvPolynomial (Fin n) ℂ), eval x (φ q) = eval (x ∘ e.symm) q := fun x q => by
    simp [φ, eval_rename]
  obtain ⟨d, hd⟩ := exists_ringKrullDim_quotient_eq_nat J hJ
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, q, hcard, hqJ, hreg⟩ := hG n d J hJ hd b

  let T : (σ → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    ((EuclideanSpace.equiv (Fin n) ℂ).symm : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).comp
      (ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm i))
  let S : EuclideanSpace ℂ (Fin n) →L[ℂ] (σ → ℂ) :=
    (ContinuousLinearMap.pi fun s : σ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) (e s)).comp
      ((EuclideanSpace.equiv (Fin n) ℂ : EuclideanSpace ℂ (Fin n) →L[ℂ] (Fin n → ℂ)))
  have hT : ∀ x i, T x i = x (e.symm i) := fun x i => rfl
  have hS : ∀ w s, S w s = w (e s) := fun w s => rfl
  have hST : ∀ x, S (T x) = x := fun x => funext fun s => by simp [hS, hT]
  have hTS : ∀ w, T (S w) = w := fun w => by ext i; simp [hS, hT]
  have hZ : ∀ x : σ → ℂ, x ∈ zeroSetIn I ↔ T x ∈ zeroSetEuc J := by
    intro x
    have hx : (fun i => T x i) = x ∘ e.symm := rfl
    simp only [zeroSetIn, zeroSetEuc, Set.mem_ofPred_eq, hx]
    constructor
    · intro h p hp
      rw [← hφ]
      exact h _ (Ideal.mem_comap.mp hp)
    · intro h p hp
      have := h (φ.symm p) (by simpa [J, Ideal.mem_comap] using hp)
      rwa [← hφ, AlgEquiv.apply_symm_apply] at this
  refine ⟨φ q, fun h => hqJ (Ideal.mem_comap.mpr h), ?_⟩
  intro z hz hzh
  obtain ⟨Ω, V, g, hΩ, hV, hzV, hg, hproj, hgraph⟩ :=
    hreg (T z) ((hZ z).mp hz) (by rwa [hφ] at hzh)
  let eI : I₀ ≃ Fin d := I₀.equivFinOfCardEq hcard
  let Ψ : (Fin d → ℂ) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i : I₀ => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) (eI i)
  let A : (σ → ℂ) →L[ℂ] (Fin d → ℂ) :=
    ContinuousLinearMap.pi fun k : Fin d =>
      ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) (e.symm (eI.symm k))
  have hΨ : ∀ y i, Ψ y i = y (eI i) := fun y i => rfl
  have hA : ∀ x k, A x k = x (e.symm (eI.symm k)) := fun x k => rfl
  have hO : IsOpen (Ψ ⁻¹' Ω) := hΩ.preimage Ψ.continuous
  refine ⟨hz, d, A, Ψ ⁻¹' Ω, T ⁻¹' V, fun y => S (g (Ψ y)), hO, hV.preimage T.continuous, hzV, ?_, ?_, ?_⟩
  · exact analyticOnNhd_of_differentiableOn_fin hO (S.differentiable.comp_differentiableOn
      (hg.comp Ψ.differentiable.differentiableOn fun y hy => hy))
  · intro y hy
    ext k
    have h1 := congrFun (hproj (Ψ y) hy) (eI.symm k)
    simp only [frameProj, b, EuclideanSpace.basisFun_inner] at h1
    show A (S (g (Ψ y))) k = y k
    rw [hA, hS, Equiv.apply_symm_apply, h1, hΨ, Equiv.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨hxZ, hxV⟩
      have hmem : T x ∈ zeroSetEuc J ∩ V := ⟨(hZ x).mp hxZ, hxV⟩
      rw [hgraph] at hmem
      obtain ⟨u, hu, hgu⟩ := hmem
      have hΨu : Ψ (fun k => u (eI.symm k)) = u := funext fun i => by simp [hΨ]
      refine ⟨fun k => u (eI.symm k), ?_, ?_⟩
      · show Ψ _ ∈ Ω
        rwa [hΨu]
      · simp only [hΨu, hgu, hST]
    · rintro ⟨y, hy, rfl⟩
      have hmem : g (Ψ y) ∈ zeroSetEuc J ∩ V := hgraph ▸ Set.mem_image_of_mem g hy
      refine ⟨(hZ _).mpr ?_, ?_⟩
      · rw [hTS]; exact hmem.1
      · show T (S (g (Ψ y))) ∈ V
        rw [hTS]; exact hmem.2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphAreaHolomorphic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

namespace GraphAreaHolomorphic

theorem norm_sq_sumElim {𝕜 : Type*} [RCLike 𝕜] {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (e : ν ≃ ι ⊕ κ) (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖(WithLp.toLp 2 (fun j => Sum.elim (fun i => a i) (fun i => b i) (e j)) : EuclideanSpace 𝕜 ν)‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_equiv e _ (fun s => ‖Sum.elim (fun i => a i) (fun i => b i) s‖ ^ 2) (fun j => rfl),
    Fintype.sum_sum_type]
  all_goals rfl

theorem norm_sq_sumElim' {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : EuclideanSpace 𝕜 ι) (b : EuclideanSpace 𝕜 κ) :
    ‖(WithLp.toLp 2 (Sum.elim (fun i => a i) (fun i => b i)) : EuclideanSpace 𝕜 (ι ⊕ κ))‖ ^ 2 =
      ‖a‖ ^ 2 + ‖b‖ ^ 2 :=
  norm_sq_sumElim (Equiv.refl _) a b

theorem adjoint_comp_self_of_norm {E H K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
    (T : E →ₗ[ℝ] K) (L : E →ₗ[ℝ] H) (h : ∀ v, ‖T v‖ ^ 2 = ‖v‖ ^ 2 + ‖L v‖ ^ 2) :
    LinearMap.adjoint T ∘ₗ T = 1 + LinearMap.adjoint L ∘ₗ L := by
  refine LinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
  simp only [LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply, inner_add_left,
    LinearMap.adjoint_inner_left]
  simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two, ← map_add (f := _)]
  have h1 := h (v + w)
  have h2 := h v
  have h3 := h w
  simp only [sq] at h1 h2 h3
  linarith

theorem det_one_add_comp {E E' H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (φ : E ≃ₗᵢ[ℝ] E') (L : E' →ₗ[ℝ] H) :
    LinearMap.det (1 + LinearMap.adjoint (L ∘ₗ φ.toLinearMap) ∘ₗ (L ∘ₗ φ.toLinearMap)) =
      LinearMap.det (1 + LinearMap.adjoint L ∘ₗ L) := by
  rw [← LinearMap.det_conj (1 + LinearMap.adjoint L ∘ₗ L) φ.symm.toLinearEquiv]
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]

theorem differentiableAt_graphPt_real {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    (hF : DifferentiableAt ℝ F x) : DifferentiableAt ℝ (graphPt e F) x := by
  rw [differentiableAt_piLp]
  intro j
  show DifferentiableAt ℝ (fun y => Sum.elim (fun i => y i) (fun i => F y i) (e j)) x
  rcases e j with i | i
  · exact (differentiableAt_piLp 2).1 differentiableAt_id i
  · exact (differentiableAt_piLp 2).1 hF i

theorem hasFDerivAt_graphPt_apply {d m n : ℕ} (e : Fin n ≃ Fin d ⊕ Fin m)
    {F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)} {x : EuclideanSpace ℂ (Fin d)}
    {L : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin m)} (hF : HasFDerivAt F L x)
    {T : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n)} (hG : HasFDerivAt (graphPt e F) T x)
    (v : EuclideanSpace ℂ (Fin d)) :
    T v = WithLp.toLp 2 (fun j => Sum.elim (fun i => v i) (fun i => L v i) (e j)) := by
  ext j
  obtain ⟨s, rfl⟩ := e.symm.surjective j
  have hj := (hasFDerivWithinAt_piLp 2).1 (hasFDerivWithinAt_univ.2 hG) (e.symm s)
  rw [hasFDerivWithinAt_univ] at hj
  rcases s with i | i
  · have h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inl i)))
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℂ) i) x := by
      simpa [graphPt] using PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x i
    simpa using congrArg (fun M => M v) (hj.unique h')
  · have hfun : (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i))) =
        (fun f : EuclideanSpace ℂ (Fin m) => f i) ∘ F := by
      funext y
      simp [graphPt]
    have h' : HasFDerivAt (fun y : EuclideanSpace ℂ (Fin d) => graphPt e F y (e.symm (Sum.inr i)))
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℂ) i).comp L) x := by
      rw [hfun]
      exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (F x) i).comp x hF
    simpa using congrArg (fun M => M v) (hj.unique h')

theorem exists_graph_isometry {d m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : Fin n ≃ Fin d ⊕ Fin m) (φ : EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (φm : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    ∃ ψ : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℝ (ι ⊕ κ), Isometry ψ ∧
      ∀ (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)) x,
        ψ (graphPt e F x) = WithLp.toLp 2 (Sum.elim (fun i => φ x i) (fun i => φm (F x) i)) := by
  let πd : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin d) :=
    { toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inl k))
      map_add' := fun z w => by ext; simp
      map_smul' := fun c z => by ext; simp }
  let πm : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    { toFun := fun z => WithLp.toLp 2 fun k => z (e.symm (Sum.inr k))
      map_add' := fun z w => by ext; simp
      map_smul' := fun c z => by ext; simp }
  have hz : ∀ z : EuclideanSpace ℂ (Fin n),
      z = WithLp.toLp 2 (fun j => Sum.elim (fun i => πd z i) (fun i => πm z i) (e j)) := by
    intro z
    ext j
    obtain ⟨s, rfl⟩ := e.symm.surjective j
    rcases s with i | i <;> simp [πd, πm]
  refine ⟨fun z => WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)), ?_, ?_⟩
  · refine Isometry.of_dist_eq fun z w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : (WithLp.toLp 2 (Sum.elim (fun i => φ (πd z) i) (fun i => φm (πm z) i)) :
        EuclideanSpace ℝ (ι ⊕ κ)) - WithLp.toLp 2 (Sum.elim (fun i => φ (πd w) i) (fun i => φm (πm w) i)) =
        WithLp.toLp 2 (Sum.elim (fun i => φ (πd (z - w)) i) (fun i => φm (πm (z - w)) i)) := by
      ext s
      rcases s with i | i <;> simp [map_sub]
    rw [hsub]
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    have hn := norm_sq_sumElim e (πd (z - w)) (πm (z - w))
    rw [← hz (z - w)] at hn
    rw [norm_sq_sumElim', φ.norm_map, φm.norm_map, hn]
  · intro F x
    have h1 : πd (graphPt e F x) = x := by ext k; simp [πd, graphPt]
    have h2 : πm (graphPt e F x) = F x := by ext k; simp [πm, graphPt]
    simp only [h1, h2]

end GraphAreaHolomorphic

open GraphAreaHolomorphic in
theorem GraphAreaHolomorphic.proof (h : AreaGraph.Statement) : GraphAreaHolomorphic.Statement := by
  intro d m n e Ω F hΩ hF A hAΩ hA

  have hFcC : ContDiffOn ℂ 1 F Ω := by
    refine contDiffOn_piLp' 2 fun j x hx => ContDiffAt.contDiffWithinAt ?_
    have hU : IsOpen ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω) :=
      hΩ.preimage (PiLp.continuous_toLp 2 _)
    have hg : DifferentiableOn ℂ (fun w : Fin d → ℂ => F (WithLp.toLp 2 w) j)
        ((WithLp.toLp 2 : (Fin d → ℂ) → EuclideanSpace ℂ (Fin d)) ⁻¹' Ω) := fun w hw =>
      (((differentiableAt_piLp 2).1 (hF.differentiableAt (hΩ.mem_nhds hw)) j).comp w
        (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 w).differentiableAt).differentiableWithinAt
    exact ((ReciprocityTheory.AnForm.Osgood.osgood d _ _ hU hg (WithLp.ofLp x) hx).contDiffAt).comp x
      PiLp.contDiff_ofLp.contDiffAt
  have hFc : ContDiffOn ℝ 1 F Ω := hFcC.restrict_scalars ℝ
  have hd : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hm : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨φ⟩ : Nonempty (EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * d))) :=
    ⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hd)).repr⟩
  obtain ⟨φm⟩ : Nonempty (EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) :=
    ⟨((stdOrthonormalBasis ℝ _).reindex (finCongr hm)).repr⟩
  obtain ⟨ψ, hψ, hψG⟩ := exists_graph_isometry e φ φm
  obtain ⟨F', hF'⟩ : ∃ F' : EuclideanSpace ℝ (Fin (2 * d)) → EuclideanSpace ℝ (Fin (2 * m)),
      F' = fun y => φm (F (φ.symm y)) := ⟨_, rfl⟩
  have hU : IsOpen (φ '' Ω) := φ.toHomeomorph.isOpenMap Ω hΩ
  have hA' : MeasurableSet (φ '' A) := φ.toHomeomorph.measurableEmbedding.measurableSet_image.2 hA
  have hF'c : ContDiffOn ℝ 1 F' (φ '' Ω) := by
    rw [hF']
    exact φm.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hFc.comp φ.symm.toContinuousLinearEquiv.contDiff.contDiffOn
        (by rintro _ ⟨y, hy, rfl⟩; simpa using hy))
  have hmp : MeasurePreserving φ μH[((2 * d : ℕ) : ℝ)] μH[((2 * d : ℕ) : ℝ)] :=
    φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _
  have himg : (fun x => ψ (graphPt e F x)) '' A = realGraphPt F' '' (φ '' A) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [hψG, hF']
    simp [realGraphPt]
  rw [← hψ.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)) (graphPt e F '' A), Set.image_image,
    himg, h (2 * d) (2 * m) (φ '' Ω) F' hU hF'c (φ '' A) (Set.image_mono hAΩ) hA',
    ← hmp.setLIntegral_comp_emb φ.toHomeomorph.measurableEmbedding]
  refine setLIntegral_congr_fun hA fun x hx => ?_
  have hFx : HasFDerivAt F (fderiv ℝ F x) x :=
    ((hF.differentiableAt (hΩ.mem_nhds (hAΩ hx))).restrictScalars ℝ).hasFDerivAt
  have hG : HasFDerivAt (graphPt e F) (fderiv ℝ (graphPt e F) x) x :=
    (differentiableAt_graphPt_real e hFx.differentiableAt).hasFDerivAt
  set K : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
    (φm.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin m) →L[ℝ] _).comp
      ((fderiv ℝ F x).comp (φ.symm.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin (2 * d)) →L[ℝ] _))
    with hK
  have hF'x : HasFDerivAt F' K (φ x) := by
    rw [hF']
    exact φm.toContinuousLinearEquiv.hasFDerivAt.comp _
      ((by simpa using hFx : HasFDerivAt F (fderiv ℝ F x) (φ.symm (φ x))).comp _
        φ.symm.toContinuousLinearEquiv.hasFDerivAt)
  simp only [hF'x.fderiv, areaJacobian]
  congr 2
  rw [adjoint_comp_self_of_norm _
    ((K : EuclideanSpace ℝ (Fin (2 * d)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * m))) ∘ₗ φ.toLinearMap),
    det_one_add_comp]
  intro v
  simp only [ContinuousLinearMap.coe_coe]
  rw [hasFDerivAt_graphPt_apply e hFx hG v, norm_sq_sumElim]
  simp [hK]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCompletionNormalDescent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def CompletionNormalDescent.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (J : Ideal R), IsNoetherianRing R → J ≤ (⊥ : Ideal R).jacobson →
    IsDomain (AdicCompletion J R) → IsIntegrallyClosed (AdicCompletion J R) →
      IsDomain R ∧ IsIntegrallyClosed R

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyGermPointPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def PolyGermPointPow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (q : MvPolynomial σ ℂ),
    polyGerm w q ∈ holGermPointIdeal w ^ k → q ∈ RingHom.ker (MvPolynomial.eval w) ^ k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAffineCompletionNormal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def AffineCompletionNormal.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (m : Ideal (MvPolynomial σ ℂ ⧸ I)),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → m.IsMaximal →
      IsDomain (AdicCompletion m (MvPolynomial σ ℂ ⧸ I)) ∧
        IsIntegrallyClosed (AdicCompletion m (MvPolynomial σ ℂ ⧸ I))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermPointIdealSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def HolGermPointIdealSpan.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ),
    holGermPointIdeal w = Ideal.span (Set.range fun i : σ => polyGerm w (X i - C (w i)))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermCompletionEquiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def GermCompletionEquiv.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    ∃ e : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) ≃+*
        AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I),
      ∀ q : MvPolynomial σ ℂ,
        e (AdicCompletion.of (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))
            (Ideal.Quotient.mk (I.map (polyGerm w)) (polyGerm w q))) =
          AdicCompletion.of (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) (Ideal.Quotient.mk I q)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
