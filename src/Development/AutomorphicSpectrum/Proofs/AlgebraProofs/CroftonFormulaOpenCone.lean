module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementA

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionBallIndicator
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionBallIndicator
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

noncomputable section

theorem coneTangentAverage_inter (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : IsProjPrime J) (hm : 0 < m) (hmn : m ≤ n)
    (hfib : ∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤)
    (A : Set (EuclideanSpace ℂ (Fin n))) (hA : MeasurableSet A) :
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ y in coneSet h J ∩ A,
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      ∫⁻ y in coneSet h J ∩ A, tangentGaussProfile n m ‖y‖
        ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
  have hMass : ConeLocalMass.Statement := ConeLocalMass.of_open ConeFiniteFibreDim.proof
  have hMeas : ConeJacMeasurable.Statement :=
    ConeJacMeasurable.proof TangentJacCompress.proof KernelProjMeasurable.proof
  have hDim : ConeTangentDim.Statement :=
    ConeTangentDim.proof (ConeKrullDimLe.proof ConeFiniteFibreDim.proof) NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)
  have hInv : TangentGaussInvariant.Statement := TangentGaussInvariant.proof
  have hres : (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J ∩ A) =
      ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
        Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)).restrict A := by
    rw [Measure.restrict_restrict hA, Set.inter_comm]
  rw [hres]
  have hS : SFinite ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
      Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) :=
    sFinite_restrict_of_ball _ _ (hMass n m h J hJ hm hmn hfib)
  have hG : Measurable fun π : Fin m → Fin n → ℂ => matGauss π := by
    unfold matGauss
    exact (by fun_prop : Continuous fun π : Fin m → Fin n → ℂ =>
      Real.exp (-∑ i, ∑ j, ‖π i j‖ ^ 2)).measurable.ennreal_ofReal
  have hP : Continuous fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) =>
      linProj p.1 p.2 := by
    unfold linProj
    fun_prop
  have hF : AEMeasurable
      (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
        matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        ((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) :=
    (hG.comp measurable_fst).aemeasurable.mul
      (((measurable_one.indicator Metric.isOpen_ball.measurableSet).comp
        hP.measurable).aemeasurable.mul (hMeas n m h J hJ hm hmn hfib).ennreal_ofReal)
  have hFA : AEMeasurable
      (Function.uncurry fun (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) =>
        matGauss π * ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y)))
      ((volume : Measure (Fin m → Fin n → ℂ)).prod
        (((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)).restrict A)) := by
    have hpr := Measure.prod_restrict (μ := (volume : Measure (Fin m → Fin n → ℂ)))
      (ν := (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) :
        Measure (EuclideanSpace ℂ (Fin n))).restrict (coneSet h J)) Set.univ A
    rw [Measure.restrict_univ] at hpr
    rw [hpr]
    exact hF.restrict
  rw [show (fun π : Fin m → Fin n → ℂ => matGauss π *
      ∫⁻ y in A, (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
        ENNReal.ofReal (coneJac h J π y)
          ∂((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J))) =
      fun π => ∫⁻ y in A, matGauss π *
        ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
          ENNReal.ofReal (coneJac h J π y))
          ∂((Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)).restrict (coneSet h J)) from
    funext fun π => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm,
    lintegral_lintegral_swap hFA]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hDim n m h J hJ hm hmn hfib,
    ae_restrict_mem (isClosed_coneSet h J).measurableSet] with y hy hyC
  simp only [← mul_assoc]
  exact hInv n m hm hmn _ hy y (mem_coneTangent_self h hJ hyC)

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionBallIndicatorStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_projection_ball_indicator : ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
  (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet A →
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
        ∫⁻ y in coneSet h J ∩ A,
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      ∫⁻ y in coneSet h J ∩ A, tangentGaussProfile n m ‖y‖ ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneTangentAverage_inter <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionConeCoarea
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionConeCoarea
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem coneArea_inter : ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
  (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ (π : Fin m → Fin n → ℂ) (A : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet A →
  ∀ g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞, Measurable g →
    volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ w : EuclideanSpace ℂ (Fin m), cntOver (coneSet h J ∩ A) π w * g w := by
  intro n m h J hJ hm hmn hfin π A hA g hg
  have hCover : ConeGraphCover.Statement := ConeGraphCover.proof ConeFiniteFibreDim.proof
    (ConeTangentDim.proof (ConeKrullDimLe.proof ConeFiniteFibreDim.proof) NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
    (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof HolomorphicImplicitGraph.proof)
  have hArea : GraphAreaFibre.Statement :=
    GraphAreaFibre.proof (GraphAreaIntegral.proof GraphAreaHolomorphic.full) TangentJacComp.proof
      AreaMultiplicityWeight.proof
  obtain ⟨e, Ω, Φ, hpc, hnull⟩ := hCover n m h J hJ hm hmn hfin
  let S : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => graphPt (e i) (Φ i) '' Ω i
  let D₀ := disjointed S
  let D : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => D₀ i ∩ A
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (hpc i).1.measurableSet.image_of_continuousOn_injOn
      (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn
  have hD₀m : ∀ i, MeasurableSet (D₀ i) := MeasurableSet.disjointed hSm
  have hDm : ∀ i, MeasurableSet (D i) := fun i => (hD₀m i).inter hA
  have hD₀S : ∀ i, D₀ i ⊆ S i := disjointed_subset S
  have hDS : ∀ i, D i ⊆ S i := fun i => Set.inter_subset_left.trans (hD₀S i)
  have hDd : Pairwise (Function.onFun Disjoint D) := fun i j hij =>
    (disjoint_disjointed S hij).mono Set.inter_subset_left Set.inter_subset_left
  have hU₀ : ⋃ i, D₀ i = ⋃ i, S i := iUnion_disjointed
  have hUC₀ : ⋃ i, S i ⊆ coneSet h J := Set.iUnion_subset fun i => (hpc i).2.2.1
  have hUC : ⋃ i, D i ⊆ coneSet h J ∩ A := Set.iUnion_subset fun i y hy =>
    ⟨hUC₀ (hU₀ ▸ Set.mem_iUnion.2 ⟨i, hy.1⟩), hy.2⟩
  have hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) ((coneSet h J ∩ A) \ ⋃ i, D i) = 0 := by
    refine measure_mono_null ?_ hnull
    rintro y ⟨⟨hyC, hyA⟩, hyD⟩
    refine ⟨hyC, fun hyS => hyD ?_⟩
    rw [← hU₀] at hyS
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyS
    exact Set.mem_iUnion.2 ⟨i, hi, hyA⟩
  have hCae : (coneSet h J ∩ A : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i :=
    ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩
  have hpiece := fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i)
    (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π
  have hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      cntOver (coneSet h J ∩ A) π w * g w =
        ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw
    rw [ENNReal.tsum_mul_right, cntOver, ptsOver, ← encard_iUnion_disjoint_nat]
    · congr 3
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hy, rfl⟩
        by_contra hne
        exact hw ⟨y, ⟨hy, fun hyD => hne (by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyD
          exact ⟨i, hi, rfl⟩)⟩, rfl⟩
      · rintro ⟨i, hi, hw'⟩
        exact ⟨hUC (Set.mem_iUnion.2 ⟨i, hi⟩), hw'⟩
    · intro i j hij
      exact (hDd hij).mono (fun y hy => hy.1) (fun y hy => hy.1)
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
          ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
      = ∑' i, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in D i, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
        rw [Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]
    _ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w :=
        tsum_congr fun i => (hpiece i).2 g hg
    _ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, cntOver (coneSet h J ∩ A) π w * g w := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w)
          fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionConeCoareaStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_projection_cone_coarea : ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
  (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ (π : Fin m → Fin n → ℂ) (A : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet A →
  ∀ g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞, Measurable g →
    volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ w : EuclideanSpace ℂ (Fin m), cntOver (coneSet h J ∩ A) π w * g w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneArea_inter | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneArea_inter | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.coneArea_inter <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzChowMahlerFibreavg
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

theorem PositivityTheory.Xgn.t_xgz_chow_mahler_fibreavg : ∀ n m : ℕ, 0 < m → m ≤ n → ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
  ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet A → (∀ y ∈ A, ∀ t : ℝ, 0 < t → t • y ∈ A) →
    (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} < ⊤ →
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1), cntOver (coneSet h J ∩ A) π w =
      K * (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} := by
  intro n m hm hmn
  obtain ⟨hkm, -, -, hM0, hMtop⟩ := TangentGaussMoment.full n m hm hmn
  set μ := Measure.hausdorffMeasure (X := EuclideanSpace ℂ (Fin n)) ((2 * m : ℕ) : ℝ) with hμ
  set k := tangentGaussProfile n m with hk
  set M := ∫⁻ r in Set.Ioi (0 : ℝ), k r * ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) with hM
  have hd : ((2 * m : ℕ) : ℝ) = (Module.finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  obtain ⟨H, hHdef⟩ : ∃ H, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
      (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = H := ⟨_, rfl⟩
  obtain ⟨V, hVdef⟩ : ∃ V, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) = V := ⟨_, rfl⟩
  have hH0 : H ≠ 0 := by
    rw [← hHdef, hd]
    exact (Metric.measure_ball_pos _ _ one_pos).ne'
  have hHtop : H ≠ ⊤ := by
    rw [← hHdef, hd]
    exact measure_ball_lt_top.ne
  have hV0 : V ≠ 0 := hVdef ▸ (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ⊤ := hVdef ▸ measure_ball_lt_top.ne
  have hc0 : H⁻¹ * V ≠ 0 := mul_ne_zero (ENNReal.inv_ne_zero.2 hHtop) hV0
  have hctop : H⁻¹ * V ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hH0) hVtop
  refine ⟨H⁻¹ * V * M, ENNReal.mul_pos hc0 hM0.ne', ENNReal.mul_lt_top hctop.lt_top hMtop, ?_⟩
  intro h J hJ hfib A hA hAs hfin
  have hin : ∀ π : Fin m → Fin n → ℂ,
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, cntOver (coneSet h J ∩ A) π w =
        H⁻¹ * V * ∫⁻ y in coneSet h J ∩ A,
          (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 (linProj π y) *
            ENNReal.ofReal (coneJac h J π y) ∂μ := by
    intro π
    have harea := GlobalTheory.T.gaussian_projection_cone_coarea n m h J hJ hm hmn hfib π A hA
      ((Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1)
      (measurable_one.indicator Metric.isOpen_ball.measurableSet)
    have hind : ∫⁻ w, cntOver (coneSet h J ∩ A) π w *
        (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1 w =
        ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, cntOver (coneSet h J ∩ A) π w := by
      rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
      congr 1
      funext w
      by_cases hw : w ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1
      · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, Pi.one_apply, mul_one]
      · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem hw, mul_zero]
    rw [hind, hVdef, hHdef] at harea
    rw [mul_assoc, harea, ← mul_assoc, ENNReal.inv_mul_cancel hH0 hHtop, one_mul]
  have hlhs : ∫⁻ π : Fin m → Fin n → ℂ, matGauss π *
      ∫⁻ w in Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1, cntOver (coneSet h J ∩ A) π w =
      H⁻¹ * V * ∫⁻ y in coneSet h J ∩ A, k ‖y‖ ∂μ := by
    rw [← GlobalTheory.T.gaussian_projection_ball_indicator n m h J hJ hm hmn hfib A hA, ← lintegral_const_mul' _ _ hctop]
    refine lintegral_congr fun π => ?_
    rw [hin π]
    ring
  rw [hlhs, ConeRadialIntegral.full n m hm (coneSet h J ∩ A)
    (fun y hy t ht => ⟨real_smul_mem_coneSet h hJ hy.1 t, hAs y hy.2 t ht⟩) hfin k hkm]
  ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HausdorffConeBallMeasure
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HausdorffConeBallMeasure
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure : ∀ n m : ℕ, 0 < m → m ≤ n → ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
  ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet A → (∀ y ∈ A, ∀ t : ℝ, 0 < t → t • y ∈ A) →
    (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} < ⊤ →
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1), cntOver (coneSet h J ∩ A) π w =
      K * (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} := by
  first | exact @PositivityTheory.Xgn.t_xgz_chow_mahler_fibreavg | exact PositivityTheory.Xgn.t_xgz_chow_mahler_fibreavg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HausdorffConeBallMeasureStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hausdorff_cone_ball_measure : ∀ n m : ℕ, 0 < m → m ≤ n → ∃ K : ℝ≥0∞, 0 < K ∧ K < ⊤ ∧
  ∀ (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet A → (∀ y ∈ A, ∀ t : ℝ, 0 < t → t • y ∈ A) →
    (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} < ⊤ →
    ∫⁻ π : Fin m → Fin n → ℂ, matGauss π * ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1), cntOver (coneSet h J ∩ A) π w =
      K * (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h J ∩ A} := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure | exact GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure | (intros; apply GlobalTheory.CompanionTheory.Relay.hausdorff_cone_ball_measure <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaOpenCone
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem setCrofton : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), IsOpen A → IsScaleStable A →
    planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ *
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by
  intro n e δ h W f hW hf hδ A hA hAs
  have hle : e + 1 ≤ n := chowGroups_le hW hf hδ
  have hδpos : 1 ≤ δ := ChowDegreePos.proof n (e + 1) δ W f (Nat.succ_pos e) hW hf hδ
  have hfib := ConeFibreDegree.full n e δ h W f hW hf hδ
  have hfin : ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)),
      fibreCount h W π w ≠ ⊤ := by
    filter_upwards [hfib] with π hπ
    filter_upwards [hπ] with w hw
    rw [hw]
    exact ENat.natCast_ne_top δ
  obtain ⟨K, hK0, hKtop, hK⟩ := GlobalTheory.T.hausdorff_cone_ball_measure n (e + 1) (Nat.succ_pos e) hle
  have hball : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) < ⊤ :=
    ConeBallFinite.full n e h W f hW hf
  have hmass : ∀ B : Set (EuclideanSpace ℂ (Fin n)),
      Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} < ⊤ := fun B =>
    lt_of_le_of_lt (measure_mono (show _ ⊆ coneBall h W from fun y hy => And.intro hy.1 hy.2.1)) hball

  have key : ∀ B : Set (EuclideanSpace ℂ (Fin n)), IsOpen B → IsScaleStable B →
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
          cntOver (coneSet h W ∩ B) π (firstCoordVec (e + 1)) =
      K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ B} := by
    intro B hB hBs
    have h1 := hK h W hW hfin B hB.measurableSet
      (fun y hy t ht => by
        have := hBs y hy (t : ℂ) (by exact_mod_cast ht.ne')
        simpa using this) (hmass B)
    have h2 := GlobalTheory.T.ball_average_fibre_count n e (coneSet h W ∩ B)
      ((isScaleStable_coneSet h hW).inter hBs) (isSigmaCompact_cone_inter h W hB) id measurable_id
    simp only [id] at h2
    rw [← h2, h1]
  have hΓ : gaussM (e + 1) n Set.univ = ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π := by
    rw [gaussM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcnt : ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
      cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ * (δ : ℝ≥0∞) := by
    rw [hΓ, ← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top δ)]
    refine lintegral_congr_ae ?_
    filter_upwards [GlobalTheory.T.ae_fibre_points_card_eq_degree n e δ h W f hW hf hδ] with π hπ
    have : cntOver (coneSet h W ∩ Set.univ) π (firstCoordVec (e + 1)) = (δ : ℝ≥0∞) := by
      rw [Set.inter_univ, cntOver]
      have : (ptsOver (coneSet h W) π (firstCoordVec (e + 1))).encard = δ := hπ
      rw [this]
      simp
    rw [this]
  have hcb : {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ Set.univ} = coneBall h W := by
    ext y
    simp [coneBall, coneSet]
  have hmf : Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W) =
      (δ : ℝ≥0∞) * planeMass n e :=
    ConeMassOfFibre.full n (e + 1) δ h W hW hfib
  have hV0 : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hVtop : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  have hδtop : (δ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top δ

  have hVΓ : volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * gaussM (e + 1) n Set.univ =
      K * planeMass n e := by
    have h0 := key Set.univ isOpen_univ (fun _ _ _ _ => Set.mem_univ _)
    rw [hcnt, hcb, hmf] at h0
    refine (ENNReal.mul_left_inj hδ0 hδtop).1 ?_
    rw [mul_assoc, h0]
    ring
  have hA1 := key A hA hAs
  refine (ENNReal.mul_right_inj hV0 hVtop).1 ?_
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * (planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)))
      = planeMass n e * (volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1))) := by ring
    _ = planeMass n e * (K * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A}) := by rw [hA1]
    _ = (K * planeMass n e) * (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ))
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by ring
    _ = _ := by rw [← hVΓ]; ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CroftonFormulaOpenConeStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crofton_formula_open_cone : ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
  (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ), IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
  ∀ A : Set (EuclideanSpace ℂ (Fin n)), IsOpen A → IsScaleStable A →
    planeMass n e * ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        cntOver (coneSet h W ∩ A) π (firstCoordVec (e + 1)) =
      gaussM (e + 1) n Set.univ *
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ coneSet h W ∩ A} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.setCrofton <;> assumption)
end
