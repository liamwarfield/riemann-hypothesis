module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DifferentiableOnSheet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.MinimalPrimeDimensions.MemMinimalPrimesOfMemSupport
set_option autoImplicit false

noncomputable section

open MvPolynomial MeasureTheory GroundTheory.Heights₂.Heights

namespace ChowFormHeightComparison₂.CF.C

variable {n : ℕ}

theorem eq_zero_of_pointOf_eq_zero (h : HermNorm n) {y : EuclideanSpace ℂ (Fin n)}
    (hy : h.pointOf y = 0) : y = 0 := by
  have hu : IsUnit (Matrix.transpose h.mat) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
  have h0 : (fun i => y i) = 0 :=
    Matrix.mulVec_injective_iff_isUnit.mpr hu (by rw [Matrix.mulVec_zero]; exact hy)
  ext i
  simpa using congrFun h0 i

theorem coneBall_subset (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsRadical) :
    coneBall h J ⊆ {0} ∪ ⋃ W ∈ (fundCycle J).support, coneBall h W := by
  classical
  rintro y ⟨hy1, hyJ⟩
  have : (RingHom.ker (eval (h.pointOf y))).IsPrime := RingHom.ker_isPrime _
  obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le
    (fun q hq => (RingHom.mem_ker).2 (hyJ q hq) : J ≤ RingHom.ker (eval (h.pointOf y)))
  by_cases hrel : IsRelevant W
  · right
    have hmem : W ∈ (fundCycle J).support := by
      rw [Finsupp.mem_support_iff]
      unfold fundCycle
      rw [Finsupp.onFinset_apply, if_pos ⟨hWmin, hrel⟩, localMult_eq_one_of_isRadical hJ hWmin]
      exact one_ne_zero
    exact Set.mem_biUnion hmem ⟨hy1, fun q hq => (RingHom.mem_ker).1 (hWle hq)⟩
  · left
    refine eq_zero_of_pointOf_eq_zero h (funext fun j => ?_)
    have hX : X j ∈ W := by
      by_contra hj
      exact hrel ⟨j, hj⟩
    simpa using (RingHom.mem_ker).1 (hWle hX)

theorem hausdorffMeasure_zero (e : ℕ) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) ({0} : Set (EuclideanSpace ℂ (Fin n))) = 0 := by
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  refine hausdorffMeasure_of_dimH_lt ?_
  rw [dimH_singleton, ENNReal.coe_natCast]
  exact_mod_cast (by omega : 0 < 2 * (e + 1))

theorem setIntegral_finset_biUnion_ae {ι X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    (t : Finset ι) {s : ι → Set X} (hs : ∀ i ∈ t, MeasurableSet (s i))
    (hd : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → μ (s i ∩ s j) = 0) (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hs' : ∀ i ∈ t, MeasurableSet (s i) := fun i hi => hs i (Finset.mem_insert_of_mem hi)
    have hf' : ∀ i ∈ t, IntegrableOn f (s i) μ := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hdis : AEDisjoint μ (s a) (⋃ i ∈ t, s i) := by
      change μ (s a ∩ ⋃ i ∈ t, s i) = 0
      rw [Set.inter_iUnion₂]
      refine (measure_biUnion_null_iff t.countable_toSet).2 fun i hi => ?_
      exact hd a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
        (fun hai => ha (hai ▸ hi))
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha,
      setIntegral_union₀ hdis (Finset.measurableSet_biUnion t hs').nullMeasurableSet
        (hf a (Finset.mem_insert_self a t)) (integrableOn_finset_iUnion.2 hf'),
      ih hs' (fun i hi j hj => hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)) hf']

theorem mem_minimalPrimes_of_mem_support {J W : Ideal (MvPolynomial (Fin n) ℂ)}
    (hW : W ∈ (fundCycle J).support) : W ∈ J.minimalPrimes := by
  have h := Finsupp.support_onFinset_subset hW
  rwa [Set.Finite.mem_toFinset] at h

theorem cone_side {K : Type} [Field K] [NumberField K] {e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : IsProjPrime I) {f : MvPolynomial (Fin (e + 1) × Fin n) K} (hf : IsChowForm I (e + 1) f) (σ : K →+* ℂ)
    (h : HermNorm n) {u : Fin n → K} (hu : linForm u ∉ I) :
    e + 1 ≤ n ∧
    IntegrableOn (fun y => fsLog h (fun k => σ (u k)) (h.pointOf y)) (coneBall h (I.map (MvPolynomial.map σ)))
      (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) ∧
    cycleIntegral h (fundCycle (I.map (MvPolynomial.map σ))) e (fsLog h fun k => σ (u k)) =
      coneIntegral h (I.map (MvPolynomial.map σ)) e (fsLog h fun k => σ (u k)) ∧
    ∀ q : MvPolynomial (Fin n) K, q ∉ I → Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      (coneBall h (I.map (MvPolynomial.map σ)) ∩ {y | eval (h.pointOf y) (MvPolynomial.map σ q) = 0}) = 0 := by
  classical
  have hp := hI.isPrime
  have hDim : ConeDimOfChowForm.Statement := ConeDimOfChowForm.proof IncIdealDim.full IncIdealPrime.full
  have hrad : (I.map (MvPolynomial.map σ)).IsRadical := RadicalBaseChange.proof K ℂ σ _ I hp.isRadical
  obtain ⟨hproj, c, -, g, hg, -⟩ := ChowFormBaseChange.full K n (e + 1) I f σ hI hf
  have hav := BaseChangeAvoid.full K n I u σ hI hu
  set J := I.map (MvPolynomial.map σ) with hJ
  set S := (fundCycle J).support with hS
  set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n)) with hμ
  have hdimW : ∀ W ∈ S, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
    fun W hW => (hDim ℂ n (e + 1) W (g W) (hproj W hW) (hg W hW)).le
  have hJW : ∀ W ∈ S, J ≤ W := fun W hW => (mem_minimalPrimes_of_mem_support hW).1.2
  have hae : coneBall h J =ᵐ[μ] ⋃ W ∈ S, coneBall h W := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) (hausdorffMeasure_zero e), ?_⟩
    · rcases coneBall_subset h hrad hy.1 with h0 | h1
      · exact h0
      · exact absurd h1 hy.2
    · have hsub : (⋃ W ∈ S, coneBall h W) ⊆ coneBall h J :=
        Set.iUnion₂_subset fun W hW y (hy : y ∈ coneBall h W) =>
          (⟨hy.1, fun q hq => hy.2 q (hJW W hW hq)⟩ : y ∈ coneBall h J)
      rw [Set.sdiff_eq_empty.2 hsub, measure_empty]
  have hint : ∀ W ∈ S, IntegrableOn (fun y => fsLog h (fun k => σ (u k)) (h.pointOf y)) (coneBall h W) μ :=
    fun W hW => ConeFsLogIntegrable.full n e h W (g W) _ (hproj W hW) (hg W hW) (hav W hW)
  have key := setIntegral_finset_biUnion_ae (μ := μ) (f := fun y => fsLog h (fun k => σ (u k)) (h.pointOf y)) S
    (fun W _ => measurableSet_coneBall h W)
    (fun W hW W' hW' hne => ConeMeetNull.proof ZeroLocusDimH.proof n e h W W' (hproj W hW).isPrime
      (hproj W' hW').isPrime hne (hdimW W hW) (hdimW W' hW')) hint
  refine ⟨?_, ?_, ?_, fun q hq => ?_⟩
  · have h1 := (hDim K n (e + 1) I f hI hf).ge.trans (ringKrullDim_quotient_le I)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h1
    simp only [ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h1
    exact_mod_cast h1
  · exact (integrableOn_finset_iUnion.2 hint).congr_set_ae hae
  · unfold cycleIntegral
    rw [Finset.sum_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hrad hW, Nat.cast_one, one_mul]]
    unfold coneIntegral
    rw [← Finset.sum_div]
    congr 1
    change ∑ W ∈ S, ∫ y in coneBall h W, fsLog h (fun k => σ (u k)) (h.pointOf y) ∂μ =
      ∫ y in coneBall h J, fsLog h (fun k => σ (u k)) (h.pointOf y) ∂μ
    rw [setIntegral_congr_set hae, key]
  · have hsub : coneBall h J ∩ {y | eval (h.pointOf y) (MvPolynomial.map σ q) = 0} ⊆
        {0} ∪ ⋃ W ∈ S, coneBall h W ∩ coneBall h (Ideal.span {MvPolynomial.map σ q}) := by
      rintro y ⟨hy, hyq⟩
      rcases coneBall_subset h hrad hy with h0 | h1
      · exact Or.inl h0
      · obtain ⟨W, hW, hyW⟩ := Set.mem_iUnion₂.1 h1
        refine Or.inr (Set.mem_iUnion₂.2 ⟨W, hW, hyW, hy.1, fun r hr => ?_⟩)
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        rw [map_mul, show eval (h.pointOf y) (MvPolynomial.map σ q) = 0 from hyq, mul_zero]
    refine measure_mono_null hsub (measure_union_null (hausdorffMeasure_zero e)
      ((measure_biUnion_null_iff S.countable_toSet).2 fun W hW => ?_))
    have := (hproj W hW).isPrime
    refine ConeMeetNull.null_of_mem_not_mem ZeroLocusDimH.proof h W _ (hdimW W hW) _
      (Ideal.mem_span_singleton_self _) fun hqW => hq ?_
    rw [← BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I (mem_minimalPrimes_of_mem_support hW)]
    exact hqW

end ChowFormHeightComparison₂.CF.C
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open MeasureTheory Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GroundTheory.Heights₂.Heights (HermNorm coneBall fsLog coneIntegral coordBall_mass IsProjPrime)
open scoped ENNReal

namespace ChowFormHeightComparison₂.CF.C

theorem integral_of_lintegral {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    {b : ℝ≥0∞} (hb : b ≠ 0) (hb' : b ≠ ⊤) {f : X → ℝ} {g : Y → ℝ} (hg : Measurable g) (hf : Integrable f μ)
    (h : ∀ G : ℝ → ℝ≥0∞, Measurable G → ∫⁻ x, G (f x) ∂μ = b * ∫⁻ y, G (g y) ∂ν) :
    Integrable g ν ∧ ∫ y, g y ∂ν = (∫ x, f x ∂μ) / b.toReal := by
  have hG1 : Measurable fun t : ℝ => ‖t‖ₑ := measurable_enorm
  have hgi : Integrable g ν := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    have hfin : ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤ := hf.2
    rw [h _ hG1] at hfin
    exact ENNReal.lt_top_of_mul_ne_top_right hfin.ne hb
  refine ⟨hgi, ?_⟩
  have hp := h _ ENNReal.measurable_ofReal
  have hn := h (fun t => ENNReal.ofReal (-t)) (ENNReal.measurable_ofReal.comp measurable_neg)
  have hb0 : b.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hb, hb'⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi, hp, hn,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ← mul_sub]
  field_simp

theorem map_notMem {K : Type} [Field K] [NumberField K] {m : ℕ} {P : Ideal (MvPolynomial (Fin m) (𝓞 K))}
    (hP : P.IsPrime) (hI : P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) ≠ ⊤) {q : MvPolynomial (Fin m) (𝓞 K)}
    (hq : q ∉ P) : MvPolynomial.map (algebraMap (𝓞 K) K) q ∉ P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) (𝓞 K)) (MvPolynomial (Fin m) K) :=
    MvPolynomial.algebraMvPolynomial
  haveI hloc := MvPolynomial.isLocalization (σ := Fin m) (nonZeroDivisors (𝓞 K)) K
  have hdisj : Disjoint (((nonZeroDivisors (𝓞 K)).map (C (σ := Fin m)) : Submonoid (MvPolynomial (Fin m) (𝓞 K))) :
      Set (MvPolynomial (Fin m) (𝓞 K))) (P : Set (MvPolynomial (Fin m) (𝓞 K))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haP
    apply hI
    have hmem : MvPolynomial.map (algebraMap (𝓞 K) K) (C a) ∈ P.map (MvPolynomial.map (algebraMap (𝓞 K) K)) :=
      Ideal.mem_map_of_mem _ haP
    rw [map_C] at hmem
    have ha0 : algebraMap (𝓞 K) K a ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero ha
    exact Ideal.eq_top_of_isUnit_mem _ hmem ((Ne.isUnit ha0).map C)
  intro hmem
  apply hq
  have hc := IsLocalization.under_map_of_isPrime_disjoint (M := (nonZeroDivisors (𝓞 K)).map (C (σ := Fin m)))
    (S := MvPolynomial (Fin m) K) hP hdisj
  rw [← hc, Ideal.mem_comap]
  exact hmem

theorem volume_univ_zero : (volume : Measure (V 0)) univ = 1 := by
  rw [← (stdOrthonormalBasis ℝ (V 0)).volume_parallelepiped]
  congr 1
  refine (Set.eq_univ_of_forall fun x => ?_).symm
  have hx : x = 0 := by
    ext i
    exact i.elim0
  rw [hx]
  exact (mem_parallelepiped_iff _ _).2 ⟨0, Set.left_mem_Icc.2 zero_le_one, by simp⟩

theorem integral_zero {R : Type} [CommRing R] {Z : Scheme.{0}} {B : LB Z} {p : Z ⟶ Sp R} {σ : R →+* ℂ}
    [SecondCountableTopology (CxPts p σ)] [CompactSpace (CxPts p σ)] {φ : Weight p σ B} (hφ : φ.IsCInf)
    (hc : ∀ y : CxPts p σ, ∃ c : AlgChart p σ 0, y ∈ c.e.source) (G : CxPts p σ → ℝ) :
    ∑ᶠ y, G y = ∫ y, G y ∂φ.chernPart 0 1 := by
  classical
  have hV : ∀ a b : V 0, a = b := fun a b => by
    ext i
    exact i.elim0
  have hsrc : ∀ (c : AlgChart p σ 0) (y : CxPts p σ), y ∈ c.e.source → c.e.source = {y} := by
    intro c y hy
    ext z
    constructor
    · intro hz
      exact c.e.injOn hz hy (hV _ _)
    · rintro rfl
      exact hy
  haveI : DiscreteTopology (CxPts p σ) := by
    rw [discreteTopology_iff_isOpen_singleton]
    intro y
    obtain ⟨c, hcy⟩ := hc y
    rw [← hsrc c y hcy]
    exact c.e.open_source
  haveI : Finite (CxPts p σ) := finite_of_compact_of_discrete
  letI := Fintype.ofFinite (CxPts p σ)
  have hμ : φ.chernPart 0 1 = Measure.count := by
    rw [Measure.ext_iff_singleton]
    intro y
    obtain ⟨c, hcy⟩ := hc y
    have himg : (c.e '' {y}) = Set.univ := Set.eq_univ_of_forall fun v => ⟨y, rfl, hV _ _⟩
    rw [Measure.count_singleton,
      Weight.chernPart_apply hφ 1 c (measurableSet_singleton y) (Set.singleton_subset_iff.2 hcy), himg]
    simp [GlobalTheory.AlgChart.chernDens_zero, volume_univ_zero]
  rw [hμ, finsum_eq_sum_of_fintype, integral_fintype Integrable.of_finite]
  simp [Measure.real, Measure.count_singleton]

end ChowFormHeightComparison₂.CF.C

namespace ChowFormHeightComparison₂.CF

open C

theorem stArch (h1 : StPts) (h2 : StCharts) : StArch := by
  unfold StArch
  intro K _ _ Z _ p B m s e hE hAV hChow hproj σ φ h hφ hFS u hu
  obtain ⟨f, hf⟩ := hChow
  haveI : CompactSpace (CxPts p (σ.comp (algebraMap (𝓞 K) K))) := hAV.compactSpace _
  haveI : SecondCountableTopology (CxPts p (σ.comp (algebraMap (𝓞 K) K))) :=
    GlobalTheory.CxPts.secondCountableTopology_of_isProjOver _ hAV.isProjOver
  obtain ⟨hem, hint, hcyc, hnull⟩ := C.cone_side hproj hf σ h hu
  obtain ⟨n, q, hqh, hqP, hqc⟩ := h2 K Z p B m s e hE hAV
  have hPprime : (ptIdeal p s (genericPoint Z)).IsPrime :=
    ((h1 (𝓞 K) Z p B m s hE).1 (genericPoint Z)).isPrime
  have hq' : MvPolynomial.map (algebraMap (𝓞 K) K) q ∉ genIdeal p s :=
    C.map_notMem hPprime hproj.isPrime.ne_top hqP
  have hJzero : ∀ x : Fin m → ℂ,
      (∀ r ∈ Ideal.map (MvPolynomial.map σ) (genIdeal p s), MvPolynomial.eval x r = 0) ↔
        ∀ r ∈ ptIdeal p s (genericPoint Z), eval₂ (σ.comp (algebraMap (𝓞 K) K)) x r = 0 := by
    intro x
    constructor
    · intro hx r hr
      have hx' := hx _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))
      rw [MvPolynomial.map_map, MvPolynomial.eval_map] at hx'
      exact hx'
    · intro hx r hr
      have hle : Ideal.map (MvPolynomial.map σ) (genIdeal p s) ≤ RingHom.ker (MvPolynomial.eval x) := by
        rw [Ideal.map_le_iff_le_comap, genIdeal, Ideal.map_le_iff_le_comap]
        intro r' hr'
        rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, MvPolynomial.map_map, MvPolynomial.eval_map]
        exact hx r' hr'
      exact hle hr
  have hμ0 : μH[↑(2 * (e + 1))] ({0} ∪ coneBall h (Ideal.map (MvPolynomial.map σ) (genIdeal p s)) ∩
      {y : EuclideanSpace ℂ (Fin m) | eval₂ (σ.comp (algebraMap (𝓞 K) K)) (h.pointOf y) q = 0}) = 0 := by
    refine measure_union_null (C.hausdorffMeasure_zero e) ?_
    refine measure_mono_null ?_ (hnull _ hq')
    rintro y ⟨hy1, hy2⟩
    refine ⟨hy1, ?_⟩
    simp only [Set.mem_setOf_eq] at hy2 ⊢
    rw [MvPolynomial.map_map, MvPolynomial.eval_map]
    exact hy2
  have hℓs : ∀ t : ℂ, t ≠ 0 → ∀ x : EuclideanSpace ℂ (Fin m),
      fsLog h (fun k => σ (u k)) (h.pointOf (t • x)) = fsLog h (fun k => σ (u k)) (h.pointOf x) := by
    intro t ht x
    rw [HermNorm.pointOf_smul']
    have hsum : ∑ j : Fin m, σ (u j) * (t • h.pointOf x) j = t * ∑ j : Fin m, σ (u j) * h.pointOf x j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [fsLog]
    rw [hsum, HermNorm.dualNorm_smul, norm_mul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 ht)]
  have hpc : Continuous fun y : EuclideanSpace ℂ (Fin m) => h.pointOf y := by
    unfold HermNorm.pointOf
    fun_prop
  have hℓm : Measurable fun y : EuclideanSpace ℂ (Fin m) => fsLog h (fun k => σ (u k)) (h.pointOf y) := by
    simp only [GroundTheory.Heights₂.Heights.ConeFsLog.fsLog_pointOf]
    have hc : Continuous fun y : EuclideanSpace ℂ (Fin m) => ∑ j : Fin m, σ (u j) * h.pointOf y j :=
      continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hpc)
    exact Real.measurable_log.comp (hc.norm.measurable.div measurable_norm)
  have hgm : Measurable fun y : CxPts p (σ.comp (algebraMap (𝓞 K) K)) =>
      fsLog h (fun k => σ (u k)) (coords p (σ.comp (algebraMap (𝓞 K) K)) hE.isLB s y) := by
    have := C.measurable_coords (h := h) (s := s) (p := p) (σ := σ.comp (algebraMap (𝓞 K) K)) hE.isLB hℓm hℓs
    simpa only [C.pointOf_euc] using this
  have hkey : ∀ G : ℝ → ℝ≥0∞, Measurable G →
      ∫⁻ y in coneBall h (Ideal.map (MvPolynomial.map σ) (genIdeal p s)),
          G (fsLog h (fun k => σ (u k)) (h.pointOf y)) ∂μH[↑(2 * (e + 1))] =
        μH[↑(2 * (e + 1))] {y : EuclideanSpace ℂ (Fin m) | ‖y‖ < 1 ∧ ∀ j : Fin m, e + 1 ≤ ↑j → y.ofLp j = 0} *
          ∫⁻ y, G (fsLog h (fun k => σ (u k)) (coords p (σ.comp (algebraMap (𝓞 K) K)) hE.isLB s y))
            ∂φ.chernPart e 1 := by
    intro G hG
    have hc := C.lintegral_cone hE hφ hFS hJzero hqh (hqc _) hμ0
      (F := fun y => G (fsLog h (fun k => σ (u k)) (h.pointOf y))) (hG.comp hℓm) (fun t ht x => by
        simp only [hℓs t ht])
    rw [hc]
    simp only [C.pointOf_euc]
  obtain ⟨-, hgint⟩ := C.integral_of_lintegral (coordBall_mass hem).1.ne' (coordBall_mass hem).2.ne hgm hint hkey
  constructor
  · unfold Weight.chernInt
    rw [C.chernPart_neg hE hφ hFS, Measure.restrict_zero, integral_zero_measure, sub_zero,
      setIntegral_eq_integral_of_forall_compl_eq_zero, hgint, hcyc]
    · rfl
    · intro y hy
      simp only [Set.mem_setOf_eq, not_not] at hy
      rw [fsLog, hy, norm_zero, zero_div, Real.log_zero]
  · intro he0
    subst he0
    have hch : ∀ y : CxPts p (σ.comp (algebraMap (𝓞 K) K)), ∃ c : AlgChart p (σ.comp (algebraMap (𝓞 K) K)) 0,
        y ∈ c.e.source := by
      intro y
      refine hqc _ y ?_
      exact C.eval₂_loc_ne_zero (GlobalTheory.TwistTop.under_eq_genericPoint hAV y) (GlobalTheory.CxPts.mem_pick hE.isLB y) hqh hqP
    rw [C.integral_zero hφ hch, hgint, hcyc]
    rfl

end ChowFormHeightComparison₂.CF
