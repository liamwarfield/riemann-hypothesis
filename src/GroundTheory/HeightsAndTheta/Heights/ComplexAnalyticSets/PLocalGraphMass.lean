module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.OsgoodSeparate
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PInjectiveHolomorphicJacobianNeZero
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreRFlatAscent
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalGraphMass
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Function

open scoped ENNReal

noncomputable section

namespace LocalGraphMass

variable {n : ℕ}

theorem norm_le_of_frameProj (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) (x : EuclideanSpace ℂ I)
    (hx : WithLp.ofLp x = frameProj b I z) : ‖x‖ ≤ ‖z‖ := by
  have h1 : ‖x‖ ^ 2 = ∑ i ∈ I, ‖inner ℂ (b i) z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_coe_sort I]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun hx i
    simp only [frameProj] at this
    simp [this]
  have h2 := b.orthonormal.sum_inner_products_le (s := I) (x := z)
  nlinarith [norm_nonneg x, norm_nonneg z]

theorem frameProj_basisFun_repr (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) :
    frameProj (EuclideanSpace.basisFun (Fin n) ℂ) I (b.repr z) = frameProj b I z := by
  funext i
  simp only [frameProj]
  rw [EuclideanSpace.basisFun_inner, b.repr_apply_apply]

theorem frameFibreCount_image_repr (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (A : Set (EuclideanSpace ℂ (Fin n))) (x : I → ℂ) :
    frameFibreCount (EuclideanSpace.basisFun (Fin n) ℂ) I (b.repr '' A) x =
      frameFibreCount b I A x := by
  have h : {y ∈ b.repr '' A | frameProj (EuclideanSpace.basisFun (Fin n) ℂ) I y = x} =
      b.repr '' {z ∈ A | frameProj b I z = x} := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      exact ⟨z, ⟨hz, by rwa [frameProj_basisFun_repr] at hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, by rw [frameProj_basisFun_repr]; exact hzx⟩
  simp only [frameFibreCount]
  rw [h, b.repr.injective.injOn.encard_image]

theorem image_repr_eq_graph (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I₀ : Finset (Fin n)) {d : ℕ} (hd : I₀.card = d) (Ω : Set (I₀ → ℂ))
    (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω' : Set (EuclideanSpace ℂ (Fin d)))
      (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
      IsOpen Ω' ∧ DifferentiableOn ℂ F Ω' ∧ b.repr '' (g '' Ω) = graphPt e F '' Ω' := by
  classical
  let σ : I₀ ≃ Fin d := Fintype.equivFinOfCardEq (by simp [hd])
  let m := Fintype.card {j : Fin n // j ∉ I₀}
  let τ : {j : Fin n // j ∉ I₀} ≃ Fin m := Fintype.equivFin _
  let e : Fin n ≃ Fin d ⊕ Fin m := (Equiv.sumCompl (· ∈ I₀)).symm.trans (Equiv.sumCongr σ τ)
  let P : EuclideanSpace ℂ (Fin d) →L[ℂ] (I₀ → ℂ) :=
    ContinuousLinearMap.pi fun i => EuclideanSpace.proj (σ i)
  let Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℂ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k => innerSL ℂ (b (τ.symm k)))
  have hP : ∀ x i, P x i = x (σ i) := fun x i => rfl
  have hQ : ∀ z k, Q z k = inner ℂ (b (τ.symm k)) z := fun z k => rfl
  have hPsurj : Function.Surjective P := fun w =>
    ⟨(EuclideanSpace.equiv (Fin d) ℂ).symm (fun i => w (σ.symm i)), by funext i; simp [hP]⟩
  refine ⟨m, e, P ⁻¹' Ω, Q ∘ g ∘ P, hΩ.preimage P.continuous, ?_, ?_⟩
  · exact Q.differentiable.comp_differentiableOn
      (hg.comp P.differentiable.differentiableOn fun x hx => hx)
  · have key : ∀ x ∈ P ⁻¹' Ω, graphPt e (Q ∘ g ∘ P) x = b.repr (g (P x)) := by
      intro x hx
      have hfx := hfix (P x) hx
      ext j
      by_cases hj : j ∈ I₀
      · have he : e j = Sum.inl (σ ⟨j, hj⟩) := by
          simp [e, Equiv.sumCompl_symm_apply_of_pos hj]
        have := congrFun hfx ⟨j, hj⟩
        simp only [frameProj, hP] at this
        simp [graphPt, he, b.repr_apply_apply, this]
      · have he : e j = Sum.inr (τ ⟨j, hj⟩) := by
          simp [e, Equiv.sumCompl_symm_apply_of_neg hj]
        simp [graphPt, he, b.repr_apply_apply, hQ]
    rw [Set.image_congr key, ← Set.image_image (fun w => b.repr (g w)) P,
      Set.image_preimage_eq Ω hPsurj, Set.image_image]

theorem mass_piece (hPF : ProjectionFormula.Statement)
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n)) {d : ℕ}
    (hd : I₀.card = d) (Ω : Set (I₀ → ℂ)) (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n))
    (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω) (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w)
    (M : Set (EuclideanSpace ℂ (Fin n))) (hM : MeasurableSet M) :
    μH[((2 * d : ℕ) : ℝ)] (g '' Ω ∩ M) =
      ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
        frameFibreCount b I (g '' Ω ∩ M) (WithLp.ofLp x) ∂(μH[((2 * d : ℕ) : ℝ)]) := by
  obtain ⟨m, e, Ω', F, hΩ', hF, himg⟩ := image_repr_eq_graph b I₀ hd Ω g hΩ hg hfix
  have hT : b.repr '' (g '' Ω ∩ M) = graphPt e F '' Ω' ∩ b.repr '' M := by
    rw [Set.image_inter b.repr.injective, himg]
  have hM' : MeasurableSet (b.repr '' M) :=
    b.repr.toHomeomorph.measurableEmbedding.measurableSet_image.2 hM
  have h := hPF d m n e Ω' F hΩ' hF (EuclideanSpace.basisFun (Fin n) ℂ) _ hM'
  rw [← hT, b.repr.isometry.hausdorffMeasure_image (Or.inr b.repr.surjective)] at h
  rw [h]
  simp_rw [frameFibreCount_image_repr]

theorem tsum_frameFibreCount_le (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) {A : Set (EuclideanSpace ℂ (Fin n))} (As : ℕ → Set (EuclideanSpace ℂ (Fin n)))
    (hsub : ∀ k, As k ⊆ A) (hdisj : Pairwise (Disjoint on As)) (x : I → ℂ) :
    ∑' k, frameFibreCount b I (As k) x ≤ frameFibreCount b I A x := by
  have hfin : ∀ s : Finset ℕ,
      ∑ k ∈ s, frameFibreCount b I (As k) x = frameFibreCount b I (⋃ k ∈ s, As k) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [frameFibreCount]
    | insert k s hk ih =>
      rw [Finset.sum_insert hk, ih, Finset.set_biUnion_insert]
      simp only [frameFibreCount]
      rw [← ENat.toENNReal_add, ← Set.encard_union_eq]
      · congr 2
        ext z
        simp only [Set.mem_union, Set.mem_ofPred_eq]
        tauto
      · refine Set.disjoint_of_subset (Set.sep_subset _ _) (Set.sep_subset _ _) ?_
        refine Set.disjoint_iUnion₂_right.2 fun j hj => hdisj ?_
        rintro rfl
        exact hk hj
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [hfin s]
  simp only [frameFibreCount]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨?_, hz.2⟩)
  exact Set.iUnion₂_subset (fun k _ => hsub k) hz.1

theorem tsum_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ≥0∞) :
    ∑' k, ∫⁻ x, f k x ∂μ ≤ ∫⁻ x, ∑' k, f k x ∂μ := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ k ∈ s, ∫⁻ x, f k x ∂μ ≤ ∫⁻ x, ∑ k ∈ s, f k x ∂μ := by
        induction s using Finset.induction_on with
        | empty => simp
        | insert k s hk ih =>
          rw [Finset.sum_insert hk]
          simp_rw [Finset.sum_insert hk]
          exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
    _ ≤ ∫⁻ x, ∑' k, f k x ∂μ := lintegral_mono fun x => ENNReal.sum_le_tsum s

theorem frameFibreCount_ball_le (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (S : Set (EuclideanSpace ℂ (Fin n))) (R : ℝ) (x : EuclideanSpace ℂ I) :
    frameFibreCount b I (S ∩ Metric.ball 0 R) (WithLp.ofLp x) ≤
      (Metric.ball (0 : EuclideanSpace ℂ I) R).indicator
        (fun _ => ⨆ y : I → ℂ, frameFibreCount b I S y) x := by
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℂ I) R
  · rw [Set.indicator_of_mem hx]
    refine le_trans ?_ (le_iSup (fun y => frameFibreCount b I S y) (WithLp.ofLp x))
    simp only [frameFibreCount]
    exact ENat.toENNReal_le.2 (Set.encard_le_encard fun z hz => ⟨hz.1.1, hz.2⟩)
  · rw [Set.indicator_of_notMem hx]
    have h : {z ∈ S ∩ Metric.ball 0 R | frameProj b I z = WithLp.ofLp x} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun z hz => hx ?_
      rw [mem_ball_zero_iff]
      exact (norm_le_of_frameProj b I z x hz.2.symm).trans_lt (mem_ball_zero_iff.1 hz.1.2)
    simp only [frameFibreCount]
    rw [h]
    simp

end LocalGraphMass


open LocalGraphMass in
theorem LocalGraphMass.proof (hPF : ProjectionFormula.Statement) : LocalGraphMass.Statement := by
  intro n d b I₀ S hd hS R
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hS' : ∀ z : S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ (z : EuclideanSpace ℂ (Fin n)) ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω :=
    fun z => hS z z.2
  choose Ω V g hΩ hV hzV hg hfix hSV using hS'
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hV
  have hmemT : ∀ z ∈ S, ∃ i ∈ T, z ∈ V i := by
    intro z hz
    have : z ∈ ⋃ i ∈ T, V i := hTU ▸ Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV _⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 this
    exact ⟨i, hi, hzi⟩
  have hTne : T.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    obtain ⟨i, hi, -⟩ := hmemT z hz
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
  let W : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun k => V (f k)
  have hcover : S ⊆ ⋃ k, disjointed W k := by
    intro z hz
    rw [iUnion_disjointed]
    obtain ⟨i, hi, hzi⟩ := hmemT z hz
    rw [hf] at hi
    obtain ⟨k, rfl⟩ := hi
    exact Set.mem_iUnion.2 ⟨k, hzi⟩
  have hDmeas : ∀ k, MeasurableSet (disjointed W k) :=
    MeasurableSet.disjointed fun k => (hV _).measurableSet
  have hpiece : ∀ k, S ∩ Metric.ball 0 R ∩ disjointed W k =
      g (f k) '' Ω (f k) ∩ (Metric.ball 0 R ∩ disjointed W k) := by
    intro k
    rw [← hSV (f k)]
    ext z
    constructor
    · rintro ⟨⟨hzS, hzB⟩, hzD⟩
      exact ⟨⟨hzS, disjointed_subset W k hzD⟩, hzB, hzD⟩
    · rintro ⟨⟨hzS, -⟩, hzB, hzD⟩
      exact ⟨⟨hzS, hzB⟩, hzD⟩
  have hdisj : Pairwise (Disjoint on fun k => S ∩ Metric.ball 0 R ∩ disjointed W k) :=
    fun i j hij => (disjoint_disjointed W hij).mono Set.inter_subset_right Set.inter_subset_right
  calc μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R)
      ≤ μH[((2 * d : ℕ) : ℝ)] (⋃ k, S ∩ Metric.ball 0 R ∩ disjointed W k) := by
        refine measure_mono fun z hz => ?_
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 (hcover hz.1)
        exact Set.mem_iUnion.2 ⟨k, hz, hk⟩
    _ ≤ ∑' k, μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball 0 R ∩ disjointed W k) := measure_iUnion_le _
    _ = ∑' k, ∑ I ∈ Finset.univ.powersetCard d, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
            ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        congr 1
        funext k
        rw [hpiece k]
        exact mass_piece hPF b I₀ hd _ _ (hΩ _) (hg _) (hfix _) _
          (Metric.isOpen_ball.measurableSet.inter (hDmeas k))
    _ = ∑ I ∈ Finset.univ.powersetCard d, ∑' k, ∫⁻ x : EuclideanSpace ℂ I,
          frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
            ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ I ∈ Finset.univ.powersetCard d,
          (⨆ x : I → ℂ, frameFibreCount b I S x) *
            μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ I) R) := by
        refine Finset.sum_le_sum fun I _ => ?_
        calc _ ≤ ∫⁻ x : EuclideanSpace ℂ I, ∑' k,
              frameFibreCount b I (S ∩ Metric.ball 0 R ∩ disjointed W k) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) := tsum_lintegral_le _ _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, frameFibreCount b I (S ∩ Metric.ball 0 R) (WithLp.ofLp x)
                ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x =>
                tsum_frameFibreCount_le b I _ (fun k => Set.inter_subset_left) hdisj _
          _ ≤ ∫⁻ x : EuclideanSpace ℂ I, (Metric.ball (0 : EuclideanSpace ℂ I) R).indicator
                (fun _ => ⨆ y : I → ℂ, frameFibreCount b I S y) x ∂(μH[((2 * d : ℕ) : ℝ)]) :=
              lintegral_mono fun x => frameFibreCount_ball_le b I S R x
          _ = _ := lintegral_indicator_const Metric.isOpen_ball.measurableSet _

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarSlabMeasure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem VarSlabMeasure.proof (hV : VarietySlabMeasure.Statement) : VarSlabMeasure.Statement := by
  intro n d J u R hJ hd hu
  obtain ⟨C, α, -, hα, hb⟩ := hV n d J u hJ hd.le hu R
  refine ⟨C, α, hα, fun ε hε hε1 => ?_⟩
  have hset : zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖∑ j, u j * z j‖ ≤ ε} =
      {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [hset]
  exact hb ε hε hε1

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormalFibresRegularPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem FormalFibresRegularPolynomial.proof (hJ : JacobianPrimeDerivations.Statement)
    (hE : DerivationAdicCompletion.Statement) (hC : AdicCompletionRegular.Statement)
    (hI : DerivationCotangentIndependent.Statement) (hQ : RegularQuotientIndependent.Statement) :
    FormalFibresRegularPolynomial.Statement := by
  intro k _ n M hM P _
  let B := MvPolynomial (Fin n) k
  let Bh := AdicCompletion M B
  let L := Localization.AtPrime P
  obtain ⟨h, f, D, s, hfp, hs, hsp, hdet⟩ := hJ k n (P.comap (algebraMap B Bh)) (Ideal.comap_isPrime _ _)
  choose D' hD' using fun j => hE B M (D j)
  have : IsRegularLocalRing Bh := hC B inferInstance M inferInstance
  have : IsRegularLocalRing L := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.localization_atPrime P
  have hdet' : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))).det ∉ P := by
    have hm : (Matrix.of fun i j => D' j (algebraMap B Bh (f i))) =
        (algebraMap B Bh).mapMatrix (Matrix.of fun i j => D j (f i)) := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact hD' j (f i)
    rw [hm, ← RingHom.map_det]
    exact hdet
  have hmem : ∀ i, algebraMap Bh L (algebraMap B Bh (f i)) ∈ maximalIdeal L := fun i =>
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L P _).mpr (hfp i)
  have hreg := hQ L h _ hmem (hI Bh P h D' (fun i => algebraMap B Bh (f i)) hfp hdet')
  have heq : Ideal.span (Set.range fun i => algebraMap Bh L (algebraMap B Bh (f i))) =
      Ideal.map (algebraMap Bh L) (Ideal.map (algebraMap B Bh) (P.comap (algebraMap B Bh))) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (hfp i))
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap Bh L (algebraMap B Bh s)) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff L P _).mpr hs
      have hsx := Ideal.mem_map_of_mem ((algebraMap Bh L).comp (algebraMap B Bh)) (hsp x hx)
      rw [Ideal.map_span, ← Set.range_comp, map_mul] at hsx
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hsx
  exact IsRegularLocalRing.of_ringEquiv (Ideal.quotEquivOfEq heq)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteModuloEliminate
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem FiniteModuloEliminate.proof (hG : FiniteModuloGeneralEquation.Statement)
    (hW : WeierstrassDivisionAtPoint.Statement) : FiniteModuloEliminate.Statement := by
  intro σ τ _ _ _ x k f L c hf hfin hpow
  obtain ⟨d, F, hF, hFan, hhF, hFev, hord⟩ := hG σ τ x k f L c hf hfin hpow
  obtain ⟨n, e, he, hgen⟩ := hfin

  set t : (σ → ℂ) → ℂ := fun z => L z c - L x c with ht_def
  have ht : AnalyticAt ℂ t x :=
    (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : τ => ℂ) c).comp L).analyticAt x).sub analyticAt_const
  let ix : Fin (n * d) → Fin n × Fin d := fun p => finProdFinEquiv.symm p
  refine ⟨n * d, fun p z => t z ^ ((ix p).2 : ℕ) * e (ix p).1 z, fun p => (ht.pow _).mul (he _), ?_⟩
  intro g hg
  obtain ⟨b, h, hb, hh, hev⟩ := hgen g hg
  choose q a hq ha hdiv using fun m => hW τ (L x) c d F (b m) hFan (hb m) hord
  have hLt : Tendsto L (𝓝 x) (𝓝 (L x)) := L.continuous.tendsto x
  refine ⟨fun p y => a (ix p).1 (ix p).2 y, fun i z => h i z + ∑ m, q m (L z) * e m z * hF i z,
    fun p => by simpa using ha (ix p).1 (ix p).2, fun i => ?_, ?_⟩
  · refine (hh i).add (Finset.univ.analyticAt_fun_sum fun m _ => ?_)
    have hqL : AnalyticAt ℂ (fun z => q m (L z)) x := (hq m).comp (L.analyticAt x)
    exact (hqL.mul (he m)).mul (hhF i)
  · have hdivL : ∀ᶠ z in 𝓝 x, ∀ m, b m (L z) = q m (L z) * F (L z) +
        ∑ j : Fin d, a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) :=
      eventually_all.2 fun m => hLt.eventually (hdiv m)
    filter_upwards [hev, hdivL, hFev] with z hz hzd hzF
    rw [hz]
    simp only [hzd, hzF, ContinuousLinearMap.comp_apply]
    have hre : ∀ φ : Fin n × Fin d → ℂ, ∑ p : Fin (n * d), φ (ix p) = ∑ m, ∑ j, φ (m, j) := fun φ => by
      rw [← Fintype.sum_prod_type']
      exact finProdFinEquiv.symm.sum_comp φ
    rw [hre (fun mj => a mj.1 mj.2 (zeroCoordinate c (L z)) * (t z ^ (mj.2 : ℕ) * e mj.1 z))]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ht_def]
    have h1 : ∑ m, (q m (L z) * ∑ i, hF i z * f i z) * e m z =
        ∑ i, ∑ m, q m (L z) * e m z * hF i z * f i z := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring
    have h2 : ∀ m (j : Fin d), a m j (zeroCoordinate c (L z)) * (L z c - L x c) ^ (j : ℕ) * e m z =
        a m j (zeroCoordinate c (L z)) * ((L z c - L x c) ^ (j : ℕ) * e m z) := fun m j => by ring
    simp only [h2]
    rw [h1]
    ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNonIsolatedFibreCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter

theorem NonIsolatedFibreCurve.analyticOnNhd_of_differentiableOn {k : ℕ} {O : Set (Fin k → ℂ)}
    {g : (Fin k → ℂ) → ℂ} (hO : IsOpen O) (hg : DifferentiableOn ℂ g O) : AnalyticOnNhd ℂ g O := by
  refine analyticOnNhd_of_continuousOn_of_separately hO hg.continuousOn fun z hz i => ?_
  have h1 : DifferentiableAt ℂ g (Function.update z i (z i)) := by
    rw [Function.update_eq_self]
    exact hg.differentiableAt (hO.mem_nhds hz)
  exact h1.comp (z i) (hasFDerivAt_update z (z i)).differentiableAt

theorem NonIsolatedFibreCurve.proof (hComp : AnalyticGermComponents.Statement)
    (hCurve : IrreducibleGermCurve.Statement) : NonIsolatedFibreCurve.Statement := by
  intro k m U f p hU hf hp hacc
  set Z : Set (Fin k → ℂ) := {v | v ∈ U ∧ f v = f p} with hZ
  have hZan : IsAnalyticNear Z p := by
    refine ⟨U, m, fun i v => f v i - f p i, hU, hp, fun i => ?_, ?_⟩
    · exact analyticOnNhd_of_differentiableOn hU ((differentiableOn_pi.1 hf i).sub_const _)
    · ext v
      simp only [hZ, Set.mem_inter_iff, Set.mem_ofPred_eq, sub_eq_zero, funext_iff]
      tauto
  obtain ⟨n, Y, hY, W, hW, hZW⟩ := hComp (Fin k) Z p hZan ⟨hp, rfl⟩

  have hfreq : ∃ᶠ y in 𝓝 p, y ≠ p ∧ y ∈ ⋃ i, Y i := by
    have h := accPt_iff_frequently.1 hacc
    refine (h.and_eventually hW).mono fun y ⟨⟨hne, hyZ⟩, hyW⟩ => ⟨hne, ?_⟩
    have : y ∈ Z ∩ W := ⟨hyZ, hyW⟩
    rw [hZW] at this
    exact this.1
  obtain ⟨i, hi⟩ : ∃ i, AccPt p (𝓟 (Y i)) := by
    by_contra hno
    push Not at hno
    have hev : ∀ᶠ y in 𝓝 p, ∀ i, ¬ (y ≠ p ∧ y ∈ Y i) := by
      refine eventually_all.2 fun i => ?_
      have := hno i
      rw [accPt_iff_frequently, Filter.not_frequently] at this
      exact this
    obtain ⟨y, ⟨hne, hyU⟩, hy⟩ := (hfreq.and_eventually hev).exists
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hyU
    exact hy j ⟨hne, hj⟩
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγm⟩ := hCurve (Fin k) (Y i) p (hY i).1 (hY i).2 hi

  have hcont : ContinuousAt γ 0 := (hγd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousAt
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rwa [hγ0])
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hpre
  have hsub : ball (0 : ℂ) (min r ε) ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r ε, lt_min hr hε, γ, hγd.mono hsub, hγi.mono hsub, hγ0, fun τ hτ => ?_⟩
  have hτW : γ τ ∈ W := hεW (ball_subset_ball (min_le_right _ _) hτ)
  have : γ τ ∈ (⋃ j, Y j) ∩ W := ⟨Set.mem_iUnion.2 ⟨i, hγm (hsub hτ)⟩, hτW⟩
  rw [← hZW] at this
  exact this.1

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleFiniteGermProjectionOpenAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric Filter Set

theorem IrreducibleFiniteGermProjectionOpenAt.proof
    (hpts : IrreducibleGermPointsOffDiscriminant.Statement) :
    IrreducibleFiniteGermProjectionOpenAt.Statement := by
  intro σ _ X x d A hX hirr hiso hinj V hV
  obtain ⟨δ, hδa, hδne, hδpts⟩ := hpts σ X x d A hX hirr hiso hinj
  obtain ⟨N, k, f, hNo, hxN, hf, hXN⟩ := hX
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hV (hNo.mem_nhds hxN))
  set r' := r / 2 with hr'
  have hr'0 : 0 < r' := by positivity
  have hcb : closedBall x r' ⊆ V ∩ N := (closedBall_subset_ball (by linarith)).trans hrV

  set K : Set (σ → ℂ) := closedBall x r' ∩ ⋂ i, (closedBall x r' ∩ f i ⁻¹' {0}) with hK
  have hKc : IsCompact K := by
    refine (isCompact_closedBall x r').of_isClosed_subset ?_ inter_subset_left
    refine isClosed_closedBall.inter (isClosed_iInter fun i => ?_)
    exact ((hf i).continuousOn.mono (hcb.trans inter_subset_right)).preimage_isClosed_of_isClosed
      isClosed_closedBall isClosed_singleton
  have hKV : A '' K ⊆ A '' (X ∩ V) := by
    refine image_mono fun z hz => ?_
    have hzN : z ∈ N := (hcb hz.1).2
    have hzX : z ∈ X ∩ N := by
      rw [hXN]
      exact ⟨hzN, fun i => by simpa using ((mem_iInter.mp hz.2) i).2⟩
    exact ⟨hzX.1, (hcb hz.1).1⟩
  have hball : ∀ z ∈ X ∩ ball x r', z ∈ K := by
    intro z hz
    have hzcb : z ∈ closedBall x r' := ball_subset_closedBall hz.2
    have hzN : z ∈ X ∩ N := ⟨hz.1, (hcb hzcb).2⟩
    rw [hXN] at hzN
    exact ⟨hzcb, mem_iInter.mpr fun i => ⟨hzcb, by simpa using hzN.2 i⟩⟩

  obtain ⟨ε₁, hε₁, hε₁a⟩ := hδa.exists_ball_analyticOnNhd
  obtain ⟨ε₂, hε₂, hε₂p⟩ := Metric.eventually_nhds_iff.mp (hδpts (ball x r') (ball_mem_nhds x hr'0))
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hDa : AnalyticOnNhd ℂ δ (ball (A x) ε) := hε₁a.mono (ball_subset_ball (min_le_left _ _))
  have hsub : {y | y ∈ ball (A x) ε ∧ δ y ≠ 0} ⊆ A '' K := by
    rintro y ⟨hy, hδy⟩
    have hy2 : dist y (A x) < ε₂ := lt_of_lt_of_le (mem_ball.mp hy) (min_le_right _ _)
    obtain ⟨x', hx', rfl⟩ := hε₂p hy2 hδy
    exact ⟨x', hball x' hx', rfl⟩
  have hD : ball (A x) ε ⊆ A '' K := by
    intro y hy
    refine (hKc.image A.continuous).isClosed.closure_subset_iff.mpr hsub (mem_closure_iff_frequently.mpr ?_)
    intro hev
    have hev' : δ =ᶠ[𝓝 y] 0 := by
      filter_upwards [hev, isOpen_ball.mem_nhds hy] with z hz hzD
      by_contra hz0
      exact hz ⟨hzD, hz0⟩
    have hzero := hDa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (A x) ε).isPreconnected hy hev'
    apply hδne
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with z hz using hzero hz
  exact Filter.mem_of_superset (ball_mem_nhds (A x) hε) (hD.trans hKV)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PDerivationAdicCompletion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open AdicCompletion

variable {R : Type} [CommRing R] (I : Ideal R) (D : Derivation ℤ R R)

theorem derivation_mem_pow_of_mem_pow_succ {n : ℕ} {r : R} (hr : r ∈ I ^ (n + 1)) : D r ∈ I ^ n :=
  by apply _root_.UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ <;> assumption

theorem pow_smul_top_eq (n : ℕ) : (I ^ n • ⊤ : Ideal R) = I ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

noncomputable def derivQuot (n : ℕ) :
    R ⧸ (I ^ (n + 1) • ⊤ : Ideal R) →+ R ⧸ (I ^ n • ⊤ : Ideal R) :=
  QuotientAddGroup.lift (I ^ (n + 1) • ⊤ : Ideal R).toAddSubgroup
    ((Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R)).toAddMonoidHom.comp (D : R →ₗ[ℤ] R).toAddMonoidHom)
    (fun r hr => by
      change r ∈ (I ^ (n + 1) • ⊤ : Ideal R) at hr
      rw [AddMonoidHom.mem_ker]
      change Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_smul_top_eq]
      rw [pow_smul_top_eq] at hr
      exact derivation_mem_pow_of_mem_pow_succ I D hr)

theorem derivQuot_mk (n : ℕ) (r : R) :
    derivQuot I D n (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D r) := rfl

theorem exists_rep_succ (x : AdicCompletion I R) (n : ℕ) :
    ∃ a : R, x.val (n + 1) = Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) a ∧
      x.val n = Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) a := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
  refine ⟨a, ha.symm, ?_⟩
  rw [← x.property (Nat.le_succ n), ← ha]
  rfl

noncomputable def derivCompletionAdd : AdicCompletion I R →+ AdicCompletion I R where
  toFun x := ⟨fun n => derivQuot I D n (x.val (n + 1)), fun {m n} hmn => by
    change transitionMap I R hmn (derivQuot I D n (x.val (n + 1))) = derivQuot I D m (x.val (m + 1))
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x.val (n + 1))
    have hm : x.val (m + 1) = Ideal.Quotient.mk (I ^ (m + 1) • ⊤ : Ideal R) a := by
      rw [← x.property (Nat.succ_le_succ hmn), ← ha]
      rfl
    rw [hm, ← ha, derivQuot_mk, derivQuot_mk]
    rfl⟩
  map_zero' := AdicCompletion.ext fun n => map_zero (derivQuot I D n)
  map_add' x y := AdicCompletion.ext fun n => map_add (derivQuot I D n) _ _

noncomputable def derivCompletion : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R) :=
  Derivation.mk' (derivCompletionAdd I D).toIntLinearMap (fun a b => by
    refine AdicCompletion.ext fun n => ?_
    obtain ⟨p, hp1, hp0⟩ := exists_rep_succ I a n
    obtain ⟨q, hq1, hq0⟩ := exists_rep_succ I b n
    change derivQuot I D n ((a * b).val (n + 1)) =
      a.val n * derivQuot I D n (b.val (n + 1)) + b.val n * derivQuot I D n (a.val (n + 1))
    rw [val_mul, hp1, hq1, hp0, hq0, ← map_mul, derivQuot_mk, derivQuot_mk, derivQuot_mk, D.leibniz,
      smul_eq_mul (α := R), smul_eq_mul (α := R), map_add, map_mul, map_mul])

theorem DerivationAdicCompletion.proof : DerivationAdicCompletion.Statement := by
  intro R _ I D
  refine ⟨derivCompletion I D, fun r => AdicCompletion.ext fun n => ?_⟩
  rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularQuotientIndependent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing Ideal

theorem RegularQuotientIndependent.proof : RegularQuotientIndependent.Statement := by
  intro S _ _ h
  induction h generalizing S with
  | zero =>
    intro x _ _
    have hr : Set.range x = ∅ := Set.range_eq_empty x
    rw [hr, Ideal.span_empty]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot S).symm
  | succ h ih =>
    intro x hxm hind
    have hx02 : x 0 ∉ maximalIdeal S ^ 2 := by
      intro hc
      have h1 := hind (Pi.single 0 1) (by simpa [Pi.single_apply] using hc) 0
      simp at h1
    have hne : span {x 0} ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top
      ((span_singleton_le_iff_mem _).mpr (hxm 0))
    have : Nontrivial (S ⧸ span {x 0}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x 0}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    have := (GroundTheory.Arith.SchemeCoh.isRegularLocalRing_quotient (hxm 0) hx02).1
    set f := Ideal.Quotient.mk (span {x 0}) with hf
    have hmax : (maximalIdeal S).map f = maximalIdeal (S ⧸ span {x 0}) :=
      map_maximalIdeal_of_surjective f Ideal.Quotient.mk_surjective
    let y : Fin h → S ⧸ span {x 0} := fun i ↦ f (x i.succ)
    have hy : ∀ i, y i ∈ maximalIdeal (S ⧸ span {x 0}) := fun i ↦
      hmax ▸ Ideal.mem_map_of_mem f (hxm i.succ)
    have hyind : ∀ b : Fin h → S ⧸ span {x 0}, ∑ i, b i * y i ∈ maximalIdeal (S ⧸ span {x 0}) ^ 2 →
        ∀ i, b i ∈ maximalIdeal (S ⧸ span {x 0}) := by
      intro b hb i
      choose a ha using fun i ↦ Ideal.Quotient.mk_surjective (I := span {x 0}) (b i)
      have hsum : ∑ i, b i * y i = f (∑ i, a i * x i.succ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by simp only [map_mul, ← ha i, hf, y]
      rw [hsum, ← hmax, ← Ideal.map_pow, hf, Ideal.mem_quotient_iff_mem_sup] at hb
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
      have h2 := hind (Fin.cons (-c) a) (by
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have : -c * x 0 + ∑ i, a i * x i.succ = z := by rw [← hzw]; ring
        rw [this]; exact hz) i.succ
      simp only [Fin.cons_succ] at h2
      rw [← ha i, ← hmax]
      exact Ideal.mem_map_of_mem _ h2
    have hreg := ih (S ⧸ span {x 0}) y hy hyind
    set J : Ideal S := span (Set.range (fun i : Fin h ↦ x i.succ)) with hJ
    have hspan : span (Set.range y) = J.map f := by
      rw [hJ, Ideal.map_span, ← Set.range_comp]
      rfl
    have hsup : span {x 0} ⊔ J = span (Set.range x) := by
      rw [hJ, ← Ideal.span_union]
      congr 1
      ext s
      simp [Fin.exists_fin_succ, eq_comm]
    exact IsRegularLocalRing.of_ringEquiv (((Ideal.quotEquivOfEq hspan).trans
      (DoubleQuot.quotQuotEquivQuotSup (span {x 0}) J)).trans (Ideal.quotEquivOfEq hsup))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPolyDerivationsDetectSquare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

open IsLocalRing KaehlerDifferential TensorProduct

theorem PolyDerivationsDetectSquare.of_perfectField
    (h₁ : PerfectFieldExtensionFormallySmooth.Statement) (h₂ : PolyKaehlerFree.Statement)
    (F k : Type) [Field F] [Field k] [Algebra F k] [PerfectField F] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] (g : MvPolynomial (Fin n) k) (hg : g ∈ p)
    (hD : ∀ D : Derivation ℤ (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k), D g ∈ p) :
    algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  classical

  have : Algebra.FormallySmooth F k := h₁ F k
  have : Algebra.FormallySmooth F p.ResidueField := h₁ F p.ResidueField
  have : Algebra.FormallySmooth F (MvPolynomial (Fin n) k) :=
    Algebra.FormallySmooth.comp F k (MvPolynomial (Fin n) k)
  have hsurj : Function.Surjective (algebraMap (Localization.AtPrime p) p.ResidueField) :=
    IsLocalRing.residue_surjective
  obtain ⟨ret, hret⟩ := (Algebra.FormallySmooth.iff_split_injection (R := F)
    (P := Localization.AtPrime p) hsurj).mp inferInstance
  have hinj : Function.Injective (kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField) :=
    Function.LeftInverse.injective (g := ret) fun x => LinearMap.congr_fun hret x
  have hgI : algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g ∈
      RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) := by
    rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hg

  have : Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F] := h₂ F k n
  let b := Module.Free.chooseBasis (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄F]
  have hc : ∀ α, b.repr (D F (MvPolynomial (Fin n) k) g) α ∈ p := fun α =>
    hD (((b.coord α).compDer (D F (MvPolynomial (Fin n) k))).restrictScalars ℤ)

  have hzero : kerCotangentToTensor F (Localization.AtPrime p) p.ResidueField
      (Ideal.toCotangent _ ⟨_, hgI⟩) = 0 := by
    change (1 : p.ResidueField) ⊗ₜ[Localization.AtPrime p]
      D F (Localization.AtPrime p) (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime p) g) = 0
    rw [← map_D F F (MvPolynomial (Fin n) k) (Localization.AtPrime p),
      ← b.linearCombination_repr (D F (MvPolynomial (Fin n) k) g), Finsupp.linearCombination_apply,
      map_finsuppSum, Finsupp.sum, tmul_sum]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [LinearMap.map_smul, ← algebraMap_smul (Localization.AtPrime p), tmul_smul,
      ← algebraMap_smul p.ResidueField, ← IsScalarTower.algebraMap_apply,
      Ideal.algebraMap_residueField_eq_zero.mpr (hc α), zero_smul]
  have h0 := hinj (hzero.trans (map_zero _).symm)
  have hker : RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) =
      maximalIdeal (Localization.AtPrime p) := IsLocalRing.ker_residue
  rw [Ideal.toCotangent_eq_zero] at h0
  rw [← hker]
  exact h0

theorem PolyDerivationsDetectSquare.proof (h₁ : PerfectFieldExtensionFormallySmooth.Statement)
    (h₂ : PolyKaehlerFree.Statement) : PolyDerivationsDetectSquare.Statement := by
  intro k _ n p _ g hg hD
  obtain ⟨q, hq⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k q with hqp | rfl
  · have : Fact q.Prime := ⟨hqp⟩
    let _ : Algebra (ZMod q) k := ZMod.algebra k q
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ (ZMod q) k n p g hg hD
  · have : CharZero k := CharP.charP_to_charZero k
    exact PolyDerivationsDetectSquare.of_perfectField h₁ h₂ ℚ k n p g hg hD

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCotangentBasisInPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

theorem CotangentBasisInPrime.proof : CotangentBasisInPrime.Statement := by
  intro T _ _ P _

  let g : P → maximalIdeal (Localization.AtPrime P) := fun x =>
    ⟨algebraMap T _ x, (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P (x : T)).2 x.2⟩
  let v : P → CotangentSpace (Localization.AtPrime P) := fun x => (maximalIdeal _).toCotangent (g x)
  have hspan : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range v) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨y, rfl⟩ := (maximalIdeal (Localization.AtPrime P)).toCotangent_surjective z
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective P.primeCompl (y : Localization.AtPrime P)
    simp only at hxs
    have hx : x ∈ P :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (Localization.AtPrime P) P x s).1 (hxs ▸ y.2)
    have hy : y = IsLocalization.mk' (Localization.AtPrime P) (1 : T) s • g ⟨x, hx⟩ := by
      ext
      simp only [g, Submodule.coe_smul, smul_eq_mul, ← hxs]
      rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
    rw [hy, map_smul, ← algebraMap_smul (ResidueField (Localization.AtPrime P))]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩)
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' (ResidueField (Localization.AtPrime P)) v
  have : Finite κ := hli.finite_of_isNoetherian
  let e := Finite.equivFin κ
  let w := (v ∘ a) ∘ e.symm
  have hliw : LinearIndependent (ResidueField (Localization.AtPrime P)) w :=
    hli.comp e.symm e.symm.injective
  have hspw : Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) = ⊤ := by
    rw [show Set.range w = Set.range (v ∘ a) from e.symm.surjective.range_comp _, hsp, hspan]
  let G : Fin (Nat.card κ) → maximalIdeal (Localization.AtPrime P) := fun i => g (a (e.symm i))
  have hsum : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      (maximalIdeal _).toCotangent (∑ i, c i • G i) = ∑ i, residue _ (c i) • w i := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, ← ResidueField.algebraMap_eq, algebraMap_smul]
    rfl
  have hcoe : ∀ c : Fin (Nat.card κ) → Localization.AtPrime P,
      ((∑ i, c i • G i : maximalIdeal (Localization.AtPrime P)) : Localization.AtPrime P) =
        ∑ i, c i * algebraMap T _ (a (e.symm i) : T) := by
    intro c
    simp [G, g]
  refine ⟨Nat.card κ, fun i => (a (e.symm i) : T), fun i => (a (e.symm i)).2, ?_, ?_⟩
  · intro y hy
    have hz : (maximalIdeal _).toCotangent ⟨y, hy⟩ ∈
        Submodule.span (ResidueField (Localization.AtPrime P)) (Set.range w) := by
      rw [hspw]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
    choose c' hc' using fun i => residue_surjective (R := Localization.AtPrime P) (c i)
    have hdiff : (maximalIdeal _).toCotangent (⟨y, hy⟩ - ∑ i, c' i • G i) = 0 := by
      rw [map_sub, hsum, ← hc]
      simp [hc']
    rw [Ideal.toCotangent_eq_zero, Submodule.coe_sub, hcoe] at hdiff
    rw [show y = (y - ∑ i, c' i * algebraMap T _ (a (e.symm i) : T)) +
        ∑ i, c' i * algebraMap T _ (a (e.symm i) : T) by ring]
    refine add_mem (Ideal.mem_sup_right hdiff) (Ideal.mem_sup_left (Ideal.sum_mem _ fun i _ => ?_))
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro c hc i
    have h0 : (maximalIdeal _).toCotangent (∑ i, c i • G i) = 0 := by
      rw [Ideal.toCotangent_eq_zero, hcoe]; exact hc
    rw [hsum] at h0
    exact (residue_eq_zero_iff _).1 (Fintype.linearIndependent_iff.1 hliw _ h0 i)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
