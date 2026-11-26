module

public import Development.AutomorphicArithmetic.AdelicQuotients.CentralizerCommutativeOfSeparableCharpoly
public import Development.AutomorphicArithmetic.AdelicQuotients.CentralSectionBaseChange
public import Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideBaseFieldOfAbsoluteConvergence

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.InfinitePartFiniteOfAdelicBound
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem mapGL_id' {R : Type} [CommRing R] (n : ℕ) (x : Matrix.GeneralLinearGroup (Fin n) R) :
    PositivityTheory.Rg.Tf.Geo.mapGL n (RingHom.id R) x = x := by
  ext i j
  simp

theorem UpperTheory.infinitePart_finite_of_adelicBound :
    P2 → Triv → BoundE → InfF := by
  intro hP hT hB F _ _ n hn γ
  have hz : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    have h1 : τ = 1 := by
      ext x
      exact τ.commutes x
    rw [h1]
    exact one_mem _
  obtain ⟨hg, hi, -⟩ := hT F
  have hi' : GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := F) = RingHom.id _ := hi
  have hB' := hB F F 1 hz n hn γ
  have hP' := (hP F F 1 hz n hn).2 γ γ
  rw [hg] at hB' hP'
  rw [hi'] at hP'
  simp only [mapGL_id'] at hB' hP'
  refine ⟨hB', fun hs D hD => ?_⟩
  have hN : PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (RingHom.id _)) (Module.finrank F F) γ = γ := by
    simp [PositivityTheory.Rg.Tf.Loc.twNorm]
    rfl
  obtain ⟨C, hC, h⟩ := hP' hs hN D hD
  exact ⟨C, hC, h⟩
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.EulerProductSupportFinite
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

theorem UpperTheory.euler_product_support_finite :
    EulerSupp := by
  intro V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K T _ _ _ _ _ _ _ _
    Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hR hRT j ji jv hq hp hK S Fi Fv hFi hFii hFv hS
  classical
  have hKA : ∀ v x, x ∈ K v → ∃ t, ∃ y ∈ K v, x = jv v t * y :=
    fun v x hx => ⟨1, x, hx, by simp⟩
  have hfin : ∀ g, (Function.mulSupport fun v => Fv v (p v g)).Finite := by
    intro g
    refine ((Filter.eventually_cofinite.1 (hR.ae g)).union S.finite_toSet).subset ?_
    intro v hv
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, Finset.mem_coe, not_or, not_not] at hc
    exact hv ((hS v hc.2 _).1 (hKA v _ hc.1))
  obtain ⟨W, hW⟩ : ∃ W : Set G, W = {g | ∀ v ∉ S, ∃ t, ∃ y ∈ K v, p v g = jv v t * y} := ⟨_, rfl⟩
  have hmem : ∀ g, g ∈ W ↔ ∀ v ∉ S, ∃ t, ∃ y ∈ K v, p v g = jv v t * y := by
    intro g; rw [hW]; rfl
  have hoff : ∀ g, g ∉ W → ∏ᶠ v, Fv v (p v g) = 0 := by
    intro g hg
    rw [hmem] at hg
    push_neg at hg
    obtain ⟨v, hv, hx⟩ := hg
    refine finprod_eq_zero _ v ((hS v hv _).2 ?_) (hfin g)
    rintro ⟨t, y, hy, e⟩
    exact hx t y hy e
  have hon : ∀ g ∈ W, ∏ᶠ v, Fv v (p v g) = ∏ v ∈ S, Fv v (p v g) := by
    intro g hg
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hv
    by_contra hc
    exact hv ((hS v hc _).1 ((hmem g).1 hg v hc))
  have hWopen : IsOpen W := by
    rw [isOpen_iff_forall_mem_open]
    intro g hg
    refine ⟨(fun x => g⁻¹ * x) ⁻¹' (US p K S : Set G), ?_,
      (continuous_const.mul continuous_id).isOpen_preimage _ (hR.opnU S), ?_⟩
    · intro x hx
      refine (hmem x).2 fun v hv => ?_
      obtain ⟨t, y, hy, e⟩ := (hmem g).1 hg v hv
      have hx' : p v (g⁻¹ * x) ∈ K v := hx v hv
      refine ⟨t, y * p v (g⁻¹ * x), mul_mem hy hx', ?_⟩
      rw [← mul_assoc, ← e, ← map_mul, mul_inv_cancel_left]
    · simp only [Set.mem_preimage, inv_mul_cancel]
      exact one_mem (US p K S)
  have hqm : Measurable q := hR.cq.measurable
  have hpm : ∀ v, Measurable (p v) := fun v => (hR.cp v).measurable
  have hmeas : Measurable fun g => Fi (q g) * ∏ v ∈ S, Fv v (p v g) :=
    (hFi.comp hqm).mul (Finset.measurable_prod _ fun v _ => (hFv v).1.comp (hpm v))
  have hEq : (fun g => Fi (q g) * ∏ᶠ v, Fv v (p v g)) =
      W.indicator (fun g => Fi (q g) * ∏ v ∈ S, Fv v (p v g)) := by
    funext g
    by_cases hg : g ∈ W
    · rw [Set.indicator_of_mem hg, hon g hg]
    · rw [Set.indicator_of_notMem hg, hoff g hg, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq]
    exact hmeas.indicator hWopen.measurableSet
  · intro g h
    have hgW : g ∈ W := by
      by_contra hc
      exact h (by rw [hoff g hc, mul_zero])
    have hch : ∀ v, ∃ t : Tv v, (p v g ∈ K v → t = 1) ∧ (v ∉ S → (jv v t)⁻¹ * p v g ∈ K v) := by
      intro v
      by_cases hk : p v g ∈ K v
      · exact ⟨1, fun _ => rfl, fun _ => by simpa using hk⟩
      · by_cases hv : v ∈ S
        · exact ⟨1, fun h => absurd h hk, fun h => absurd hv h⟩
        · obtain ⟨t, y, hy, e⟩ := (hmem g).1 hgW v hv
          exact ⟨t, fun h => absurd h hk, fun _ => by rw [e]; simpa using hy⟩
    choose tv ht1 ht2 using hch
    obtain ⟨t, -, ht⟩ := hRT.surj 1 tv
      ((hR.ae g).mono fun v hv => by rw [ht1 v hv]; exact one_mem _)
    refine Set.mem_mul.2 ⟨j t, ⟨t, rfl⟩, (j t)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    refine SetLike.mem_coe.2 (mem_US.2 fun v hv => ?_)
    rw [map_mul, map_inv, hp, ht]
    exact ht2 v hv
  · intro u hu
    have huW : u ∈ W := (hmem u).2 fun v hv => hKA v _ (hu v hv)
    rw [hon u huW, Finset.prod_coe_sort S (fun v => Fv v (p v u))]
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.ExistsHaarMeasureAdelicGL
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology Filter

theorem UpperTheory.exists_haarMeasure_adelicGL :
    HaarEx := by
  unfold HaarEx
  intro V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hR μ μi m hμ hμi hm S
  classical
  haveI : ∀ v, (m v).IsHaarMeasure := hm
  have cf : Continuous (prS q p S) := by
    have h : ⇑(prS q p S) = fun g => (q g, fun v : S => p v g) := rfl
    rw [h]
    exact hR.cq.prodMk (continuous_pi fun v => hR.cp v)
  have mf : Measurable (prS q p S) := cf.measurable
  have hs : ∀ h : Gi × ∀ v : S, Gv v, ∃ u ∈ US p K S, prS q p S u = h := by
    rintro ⟨gi, gv⟩
    obtain ⟨g, h1, h2⟩ := hR.surj gi (fun v => if hv : v ∈ S then gv ⟨v, hv⟩ else 1) (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      rw [dif_neg hv']
      exact one_mem _)
    refine ⟨g, ?_, ?_⟩
    · intro v hv
      rw [h2, dif_neg hv]
      exact one_mem _
    · rw [prS_apply, h1]
      congr 1
      funext v
      rw [h2, dif_pos v.2]
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (μ.restrict (US p K S : Set G)).map (prS q p S) := ⟨_, rfl⟩
  haveI inv : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    obtain ⟨u, hu, rfl⟩ := hs h
    ext A hA
    have hA' : MeasurableSet ((fun x => prS q p S u * x) ⁻¹' A) := measurable_const_mul _ hA
    rw [Measure.map_apply (measurable_const_mul _) hA, hν, Measure.map_apply mf hA',
      Measure.map_apply mf hA, Measure.restrict_apply (mf hA'), Measure.restrict_apply (mf hA)]
    have hset : prS q p S ⁻¹' ((fun x => prS q p S u * x) ⁻¹' A) ∩ (US p K S : Set G) =
        (fun x => u * x) ⁻¹' (prS q p S ⁻¹' A ∩ (US p K S : Set G)) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, SetLike.mem_coe,
        Subgroup.mul_mem_cancel_left _ hu]
    rw [hset, measure_preimage_mul]
  haveI fin : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun D hD => ?_⟩
    rw [hν, Measure.map_apply mf hD.measurableSet, Measure.restrict_apply (mf hD.measurableSet)]
    let C : ∀ v, Set (Gv v) := fun v =>
      if hv : v ∈ S then (fun h : Gi × ∀ v : S, Gv v => h.2 ⟨v, hv⟩) '' D else K v
    have hC : ∀ v, IsCompact (C v) := by
      intro v
      by_cases hv : v ∈ S
      · simp only [C, dif_pos hv]
        exact hD.image (by fun_prop)
      · simp only [C, dif_neg hv]
        exact hR.cpt v
    have hW := hR.prop (Prod.fst '' D) C (hD.image continuous_fst) hC (by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      have hv' : v ∉ S := by simpa using hv
      simp only [C, dif_neg hv']
      exact subset_rfl)
    refine lt_of_le_of_lt (measure_mono ?_) hW.measure_lt_top
    rintro g ⟨h1, h2⟩
    refine ⟨⟨_, h1, rfl⟩, fun v => ?_⟩
    by_cases hv : v ∈ S
    · simp only [C, dif_pos hv]
      exact ⟨_, h1, rfl⟩
    · simp only [C, dif_neg hv]
      exact h2 v hv
  have e := Measure.isMulLeftInvariant_eq_smul ν (μi.prod (Measure.pi fun v : S => m v))
  refine ⟨Measure.haarScalarFactor ν (μi.prod (Measure.pi fun v : S => m v)), ?_, ?_⟩
  · intro h0
    rw [h0, zero_smul] at e
    have h1 : ν Set.univ = 0 := by rw [e]; rfl
    rw [hν, Measure.map_apply mf MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ] at h1
    exact (hR.opnU S).measure_ne_zero μ ⟨1, one_mem _⟩ h1
  · unfold Eul
    rw [← hν]
    exact e
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.QuotientHaarMeasurePushforward
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotOpen
noncomputable section

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace UpperTheory.ConvolutionTheory.G

section

variable {G T : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [T2Space T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]

private lemma uni_comap (μ : Measure G) (hμ : Uni μ) (U : Subgroup G) (hU : IsOpen (U : Set G)) :
    Uni (μ.comap fun u : U => (u : G)) := by
  obtain ⟨h1, h2⟩ := hμ
  haveI := h1
  haveI := h2
  have hUm : MeasurableSet (U : Set G) := hU.measurableSet
  have emb : MeasurableEmbedding (fun u : U => (u : G)) := MeasurableEmbedding.subtype_coe hUm
  have hH : (μ.comap U.subtype).IsHaarMeasure :=
    Measure.IsHaarMeasure.comap (mH := inferInstance) μ hU.isOpenEmbedding_subtypeVal
  refine ⟨hH, ⟨?_⟩⟩
  ext s hs
  rw [Measure.inv_apply, emb.comap_apply, emb.comap_apply]
  have e : (fun u : U => (u : G)) '' s⁻¹ = ((fun u : U => (u : G)) '' s)⁻¹ := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u⁻¹, hu, by simp⟩
    · intro hx
      obtain ⟨u, hu, hux⟩ := hx
      refine ⟨u⁻¹, by simpa using hu, ?_⟩
      have hux' : (u : G) = x⁻¹ := hux
      simp [hux']
  rw [e, Measure.measure_inv]

private def ext0 (U : Subgroup G) (r : U → ℝ≥0∞) : G → ℝ≥0∞ :=
  Function.extend (fun u : U => (u : G)) r 0

private lemma ext0_coe (U : Subgroup G) (r : U → ℝ≥0∞) (u : U) : ext0 U r (u : G) = r u :=
  Subtype.val_injective.extend_apply _ _ _

private lemma extendByZero_not_mem (U : Subgroup G) (r : U → ℝ≥0∞) {g : G} (hg : g ∉ U) : ext0 U r g = 0 := by
  unfold ext0
  rw [Function.extend_apply']
  · rfl
  · rintro ⟨u, rfl⟩
    exact hg u.2

private lemma nrm_on_coset (j : T →* G) (ν : Measure T) (U : Subgroup G)
    (hV : MeasurableSet ((U.comap j : Subgroup T) : Set T)) (i : U.comap j →* U)
    (hi : ∀ t, (i t : G) = j t) (r : U → ℝ≥0∞)
    (h₀ : ∀ x, ∫⁻ t, r (i t * x) ∂(ν.comap fun t : U.comap j => (t : T)) = 1) (u : U) :
    ∫⁻ t, ext0 U r (j t * u) ∂ν = 1 := by
  have e : (fun t => ext0 U r (j t * u)) =
      ((U.comap j : Subgroup T) : Set T).indicator (fun t => ext0 U r (j t * u)) := by
    funext t
    by_cases ht : t ∈ U.comap j
    · rw [Set.indicator_of_mem (by exact ht)]
    · rw [Set.indicator_of_notMem (by exact ht)]
      apply extendByZero_not_mem
      intro hmem
      apply ht
      have h2 : j t = (j t * u) * (u : G)⁻¹ := by group
      rw [Subgroup.mem_comap, h2]
      exact U.mul_mem hmem (U.inv_mem u.2)
  have h := lintegral_subtype_comap hV (μ := ν) (fun t => ext0 U r (j t * u))
  rw [e, lintegral_indicator hV, ← h, ← h₀ u]
  refine lintegral_congr fun t => ?_
  have h3 : j (t : T) * (u : G) = ((i t * u : U) : G) := by simp [hi]
  rw [h3, ext0_coe]

open Classical in
private lemma isNrm_glue (j : T →* G) (ν : Measure T) (hν : Uni ν) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hV : MeasurableSet ((U.comap j : Subgroup T) : Set T))
    (i : U.comap j →* U) (hi : ∀ t, (i t : G) = j t) (r : U → ℝ≥0∞)
    (h₀ : IsNrm i (ν.comap fun t : U.comap j => (t : T)) r) (r' : G → ℝ≥0∞) (h' : IsNrm j ν r') :
    IsNrm j ν ((Set.range j * (U : Set G)).piecewise (ext0 U r) r') := by
  haveI := hν.2
  haveI := hν.1
  haveI : ν.IsMulRightInvariant := by
    have h2 : (ν.inv).IsMulRightInvariant := inferInstance
    rwa [Measure.IsInvInvariant.inv_eq_self] at h2
  have hS : IsOpen (Set.range j * (U : Set G)) := hU.mul_left
  have hm : Measurable (ext0 U r) :=
    (MeasurableEmbedding.subtype_coe hU.measurableSet).measurable_extend h₀.1 measurable_const
  refine ⟨hm.piecewise hS.measurableSet h'.1, fun x => ?_⟩
  by_cases hx : x ∈ Set.range j * (U : Set G)
  · obtain ⟨_, ⟨s, rfl⟩, u, hu, rfl⟩ := hx
    have e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * (j s * u)) =
        ext0 U r (j (t * s) * u) := by
      intro t
      rw [Set.piecewise_eq_of_mem, map_mul, mul_assoc]
      exact ⟨j (t * s), ⟨_, rfl⟩, u, hu, by simp [mul_assoc]⟩
    refine Eq.trans (lintegral_congr e) ((lintegral_mul_right_eq_self (μ := ν)
      (fun t => ext0 U r (j t * u)) s).trans ?_)
    exact nrm_on_coset j ν U hV i hi r h₀.2 ⟨u, hu⟩
  · have e : ∀ t, (Set.range j * (U : Set G)).piecewise (ext0 U r) r' (j t * x) = r' (j t * x) := by
      intro t
      apply Set.piecewise_eq_of_notMem
      intro hm2
      apply hx
      obtain ⟨_, ⟨s, rfl⟩, u, hu, hxe⟩ := hm2
      refine ⟨j (t⁻¹ * s), ⟨_, rfl⟩, u, hu, ?_⟩
      have hxe' : j s * u = j t * x := hxe
      change j (t⁻¹ * s) * u = x
      rw [map_mul, map_inv, mul_assoc, hxe', inv_mul_cancel_left]
    exact (lintegral_congr e).trans (h'.2 x)

end

end UpperTheory.ConvolutionTheory.G

open MeasureTheory Topology UpperTheory.ConvolutionTheory.G in
theorem UpperTheory.ConvolutionTheory.G.quotOpen_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotOpen := by
  classical
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ μ j ν h U hU i hi
  obtain ⟨hμ, hj, hν⟩ := id h
  have hV : IsOpen ((U.comap j : Subgroup T) : Set T) := hU.preimage hj.continuous
  have hUm : MeasurableSet (U : Set G) := hU.measurableSet
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : SecondCountableTopology (U.comap j) :=
    TopologicalSpace.Subtype.secondCountableTopology ((U.comap j : Subgroup T) : Set T)
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (U.comap j) := hV.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hUc : IsClosedEmbedding (fun u : U => (u : G)) :=
    (Subgroup.isClosed_of_isOpen U hU).isClosedEmbedding_subtypeVal
  have hVc : IsClosedEmbedding (fun t : U.comap j => (t : T)) :=
    (Subgroup.isClosed_of_isOpen _ hV).isClosedEmbedding_subtypeVal
  have hic : IsClosedEmbedding i := by
    have h1 : IsClosedEmbedding ((fun u : U => (u : G)) ∘ i) := by
      have h2 : ((fun u : U => (u : G)) ∘ i) = j ∘ (fun t : U.comap j => (t : T)) := by
        funext t
        exact hi t
      rw [h2]
      exact hj.comp hVc
    exact (IsClosedEmbedding.of_comp_iff hUc).1 h1
  have hs : Pair (μ.comap fun u : U => (u : G)) i (ν.comap fun t : U.comap j => (t : T)) :=
    ⟨uni_comap μ hμ U hU, hic, uni_comap ν hν _ hV⟩
  refine ⟨hs, fun F hFm hFi hFs => ?_⟩
  obtain ⟨r₀, -, hr₀, -⟩ := hN U (U.comap j) _ i _ hs
  obtain ⟨r', -, hr', -⟩ := hN G T μ j ν h
  have hg := isNrm_glue j ν hν U hU hV.measurableSet i hi _ hr₀ _ hr'
  obtain ⟨hQ1, -, hQ3⟩ := hE G T μ j ν h F hFm hFi _ hg
  have hFm' : Measurable (fun u : U => F u) := hFm.comp measurable_subtype_coe
  have hFi' : ∀ (t : U.comap j) (g : U), F ((i t * g : U) : G) = F g := by
    intro t g
    simp [hi, hFi]
  obtain ⟨hq1, -, hq3⟩ := hE U (U.comap j) _ i _ hs (fun u => F u) hFm' hFi' _ hr₀
  have key : (fun x => F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) =
      (U : Set G).indicator (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) := by
    funext x
    by_cases hxU : x ∈ (U : Set G)
    · rw [Set.indicator_of_mem hxU, Set.piecewise_eq_of_mem]
      exact ⟨1, ⟨1, map_one j⟩, x, hxU, one_mul x⟩
    · rw [Set.indicator_of_notMem hxU]
      by_cases hxS : x ∈ Set.range j * (U : Set G)
      · rw [Set.piecewise_eq_of_mem _ _ _ hxS, extendByZero_not_mem U _ hxU]
        simp
      · have : F x = 0 := by
          by_contra h0
          exact hxS (hFs x h0)
        simp [this]
  have cmp : (fun x => F x * (((ext0 U fun u => (r₀ u : ENNReal)) x).toReal : ℂ)) ∘
      (fun u : U => (u : G)) = fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ) := by
    funext u
    simp only [Function.comp]
    rw [show ext0 U (fun u => (r₀ u : ENNReal)) (u : G) = _ from ext0_coe U _ u]
  have i1 : Integrable (fun x => F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ)) μ ↔
      Integrable (fun u : U => F u * (((r₀ u : ENNReal)).toReal : ℂ))
        (μ.comap fun u : U => (u : G)) := by
    rw [key, integrable_indicator_iff hUm, integrableOn_iff_comap_subtypeVal hUm]
    exact Iff.of_eq (congrArg (fun f => Integrable f (μ.comap fun u : U => (u : G))) cmp)
  have i2 : ∫ x, F x * ((((Set.range j * (U : Set G)).piecewise
        (ext0 U fun u => (r₀ u : ENNReal)) fun g => (r' g : ENNReal)) x).toReal : ℂ) ∂μ =
      ∫ u : U, F u * (((r₀ u : ENNReal)).toReal : ℂ) ∂(μ.comap fun u : U => (u : G)) := by
    rw [key, integral_indicator hUm, ← integral_subtype_comap hUm]
    exact congrArg (fun f => ∫ u : U, f u ∂(μ.comap fun u : U => (u : G))) cmp
  exact ⟨hQ1.trans (i1.trans hq1.symm), hQ3.trans (i2.trans hq3.symm)⟩
end
end

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal

theorem UpperTheory.quotient_haar_measure_pushforward :
    QPush := by
  intro G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν μ' j' ν' hP hP' U hU π πT hπ hπT hc hμ hν F F' hF hFi hF' hF'i hs hFF
  have hjc : Continuous j := hP.2.1.continuous
  have hUT : IsOpen ((U.comap j : Subgroup T) : Set T) := hU.preimage hjc
  haveI : LocallyCompactSpace U := hU.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (U.comap j) := hUT.isOpenEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology (U : Set G)
  haveI : SecondCountableTopology (U.comap j) :=
    TopologicalSpace.Subtype.secondCountableTopology ((U.comap j : Subgroup T) : Set T)
  haveI : BorelSpace U := Subtype.borelSpace (fun x => x ∈ (U : Set G))
  haveI : BorelSpace (U.comap j) := Subtype.borelSpace (fun x => x ∈ ((U.comap j : Subgroup T) : Set T))
  let i : U.comap j →* U := (j.comp (U.comap j).subtype).codRestrict U (fun t => t.2)
  have hi : ∀ t : U.comap j, (i t : G) = j t := fun _ => rfl
  obtain ⟨hPU, hO⟩ := quotOpen_of normEx quotEq G T μ j ν hP U hU i hi
  obtain ⟨ρ', hρc, hρ, -⟩ := normEx H T' μ' j' ν' hP'
  have embG : MeasurableEmbedding (fun u : U => (u : G)) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have embT : MeasurableEmbedding (fun t : U.comap j => (t : T)) :=
    MeasurableEmbedding.subtype_coe hUT.measurableSet
  have mapG : (μ.comap fun u : U => (u : G)).map (fun u : U => (u : G)) = μ.restrict (U : Set G) := by
    rw [embG.map_comap]; congr 1; exact Subtype.range_coe
  have mapT : (ν.comap fun t : U.comap j => (t : T)).map (fun t : U.comap j => (t : T)) =
      ν.restrict (j ⁻¹' (U : Set G)) := by
    rw [embT.map_comap]; congr 1; exact Subtype.range_coe
  have hρm : Measurable fun h : H => ((ρ' h : NNReal) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp hρc.measurable
  have hn : IsNrm i (ν.comap fun t : U.comap j => (t : T)) (fun u : U => ((ρ' (π u) : NNReal) : ℝ≥0∞)) := by
    refine ⟨hρm.comp (hπ.measurable.comp measurable_subtype_coe), fun x => ?_⟩
    have hg : Measurable fun s : T' => ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) :=
      hρm.comp ((hP'.2.1.continuous.measurable).mul_const _)
    calc ∫⁻ t, ((ρ' (π ((i t * x : U) : G)) : NNReal) : ℝ≥0∞) ∂(ν.comap fun t : U.comap j => (t : T))
        = ∫⁻ t, (fun s : T => ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞)) ((fun t : U.comap j => (t : T)) t)
            ∂(ν.comap fun t : U.comap j => (t : T)) := by
          refine lintegral_congr fun t => ?_
          simp only [Subgroup.coe_mul, map_mul, hi, hc]
      _ = ∫⁻ s, ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞)
            ∂((ν.comap fun t : U.comap j => (t : T)).map (fun t : U.comap j => (t : T))) :=
          (embT.lintegral_map (fun s : T => ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞))).symm
      _ = ∫⁻ s, ((ρ' (j' (πT s) * π x) : NNReal) : ℝ≥0∞) ∂(ν.restrict (j ⁻¹' (U : Set G))) := by
          rw [mapT]
      _ = ∫⁻ s, ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) ∂((ν.restrict (j ⁻¹' (U : Set G))).map πT) :=
          (lintegral_map hg hπT.measurable).symm
      _ = ∫⁻ s, ((ρ' (j' s * π x) : NNReal) : ℝ≥0∞) ∂ν' := by rw [hν]
      _ = 1 := hρ.2 (π x)
  have hFU : Measurable fun u : U => F u := hF.comp measurable_subtype_coe
  have hFUi : ∀ (t : U.comap j) (g : U), F ((i t * g : U) : G) = F g := by
    intro t g
    rw [Subgroup.coe_mul, hi, hFi]
  have hgm : Measurable fun h : H => F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) :=
    hF'.mul (Complex.measurable_ofReal.comp hρm.ennreal_toReal)
  have e1 := (hO F hF hFi hs).2
  have e2 := (quotEq (↥U) (↥(U.comap j)) (μ.comap fun u : U => (u : G)) i
    (ν.comap fun t : U.comap j => (t : T)) hPU (fun u : U => F u) hFU hFUi _ hn).2.2
  have e3 := (quotEq H T' μ' j' ν' hP' F' hF' hF'i _ hρ).2.2
  rw [e1, e2, e3]
  calc ∫ u : U, F u * ((((ρ' (π u) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂(μ.comap fun u : U => (u : G))
      = ∫ u : U, (fun x : G => F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ))
            ((fun u : U => (u : G)) u) ∂(μ.comap fun u : U => (u : G)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hFF u u.2]
    _ = ∫ x, F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ)
          ∂((μ.comap fun u : U => (u : G)).map (fun u : U => (u : G))) :=
        (embG.integral_map (fun x : G => F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ))).symm
    _ = ∫ x, F' (π x) * ((((ρ' (π x) : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂(μ.restrict (U : Set G)) := by
        rw [mapG]
    _ = ∫ h, F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂((μ.restrict (U : Set G)).map π) :=
        (integral_map hπ.aemeasurable hgm.aestronglyMeasurable).symm
    _ = ∫ h, F' h * ((((ρ' h : NNReal) : ℝ≥0∞).toReal : ℝ) : ℂ) ∂μ' := by rw [hμ]
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.LocalUnimodularOfExistsHaarMeasure
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory
open scoped ENNReal Pointwise

private theorem inv_map_sub {G P : Type} [Group G] [Group P] [MeasurableSpace G] [MeasurableSpace P]
    [MeasurableInv G] [MeasurableInv P] (μ : Measure G) [μ.IsInvInvariant] (U : Subgroup G)
    (f : G →* P) (hf : Measurable f) (hU : MeasurableSet (U : Set G)) (E : Set P) (hE : MeasurableSet E) :
    ((μ.restrict (U : Set G)).map f) E⁻¹ = ((μ.restrict (U : Set G)).map f) E := by
  rw [Measure.map_apply hf hE.inv, Measure.map_apply hf hE, Measure.restrict_apply (hf hE.inv),
    Measure.restrict_apply (hf hE)]
  have h : f ⁻¹' E⁻¹ ∩ (U : Set G) = (f ⁻¹' E ∩ (U : Set G))⁻¹ := by
    ext x
    simp [Set.mem_inv, map_inv, Subgroup.inv_mem_iff]
  rw [h, Measure.measure_inv]

private theorem inv_all {P : Type} [Group P] [MeasurableSpace P] [MeasurableInv P] (ν : Measure P)
    (h : ∀ E, MeasurableSet E → ν E⁻¹ = ν E) (E : Set P) : ν E⁻¹ = ν E := by
  have hi : ν.inv = ν := Measure.ext fun E hE => by rw [Measure.inv_apply]; exact h E hE
  rw [← Measure.inv_apply, hi]

theorem UpperTheory.local_unimodular_of_exists_haar_measure :
    HaarEx → UniLoc := by
  intro hH V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K hRP μ μi m hμ hμi hm
  haveI := hμ.1
  haveI := hμ.2
  haveI := hμi
  haveI := fun v => hm v
  have key : ∀ (S : Finset V) (A : Set Gi) (B : ∀ v : S, Set (Gv v)),
      μi A⁻¹ * ∏ v : S, m v (B v)⁻¹ = μi A * ∏ v : S, m v (B v) := by
    intro S A B
    obtain ⟨a, ha, hE⟩ := hH V G Gi Gv q p K hRP μ μi m hμ.1 hμi hm S
    have hE' : (μ.restrict (US p K S : Set G)).map (prS q p S) = a • μi.prod (Measure.pi fun v : S => m v) := hE
    have hf : Measurable (prS q p S) := by
      have h1 : Measurable q := hRP.cq.measurable
      have h2 : Measurable fun g : G => fun v : S => p v g :=
        Measurable.of_eval fun v => (hRP.cp v).measurable
      exact h1.prodMk h2
    have hU : MeasurableSet (US p K S : Set G) := (hRP.opnU S).measurableSet
    have h1 := inv_all ((μ.restrict (US p K S : Set G)).map (prS q p S))
      (inv_map_sub μ (US p K S) (prS q p S) hf hU) (A ×ˢ Set.pi Set.univ B)
    have hset : (A ×ˢ Set.pi Set.univ B)⁻¹ = A⁻¹ ×ˢ Set.pi Set.univ (fun v => (B v)⁻¹) := by
      ext ⟨x, y⟩
      simp [Set.mem_prod, Set.mem_pi, Set.mem_inv]
    rw [hE', hset, Measure.smul_apply, Measure.smul_apply, Measure.prod_prod, Measure.prod_prod,
      Measure.pi_pi, Measure.pi_pi, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul] at h1
    exact (ENNReal.mul_right_inj (by exact_mod_cast ha) ENNReal.coe_ne_top).1 h1
  have hinv : ∀ A : Set Gi, μi A⁻¹ = μi A := by
    intro A
    have h := key ∅ A (fun _ => Set.univ)
    simpa using h
  refine ⟨⟨hμi, ⟨Measure.ext fun A _ => by rw [Measure.inv_apply]; exact hinv A⟩⟩, fun v => ⟨hm v, ⟨Measure.ext fun B _ => ?_⟩⟩⟩
  rw [Measure.inv_apply]
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : Gi)
  have hpos : μi C ≠ 0 := (Measure.measure_pos_of_mem_nhds μi hC1).ne'
  have htop : μi C ≠ ⊤ := hC.measure_lt_top.ne
  let v0 : ({v} : Finset V) := ⟨v, Finset.mem_singleton_self v⟩
  have h := key {v} C (Function.update (fun _ => Set.univ) v0 B)
  rw [hinv C, Fintype.prod_subsingleton _ v0, Fintype.prod_subsingleton _ v0] at h
  simp only [Function.update_self] at h
  exact (ENNReal.mul_right_inj hpos htop).1 h
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.GeometricSideAbsolutelyConvergentOfEulerFubini
open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory

theorem UpperTheory.geometric_side_absolutely_convergent_of_euler_fubini :
    Euler → Fub → SideAbs := by
  intro hE hF V G _ _ _ _ _ _ _ _ Gi _ _ _ _ _ _ _ _ Gv _ _ _ _ _ _ _ _ q p K
    T _ _ _ _ _ _ _ _ Ti _ _ _ _ _ _ _ _ Tv _ _ _ _ _ _ _ _ qT pT KT hRP hRPT j ji jv
    hqj hpj hK μ μi m ν νi nv hP hPi hPv S a b ha hb hEa hEb θ θi θv hqθ hpθ cθi cθv
    δ z cz hpz hinv hC hB φi φ cφi sφi cφ hS
  classical
  have invI : ∀ t, (ji t)⁻¹ * q δ * θi (ji t) = q δ := by
    intro t
    obtain ⟨τ, h1, -⟩ := hRPT.surj t (fun _ => 1) (Filter.Eventually.of_forall fun v => one_mem _)
    have h := congrArg q (hinv τ)
    rw [map_mul, map_mul, map_inv, hqθ, hqj, h1] at h
    exact h
  have invV : ∀ v t, (jv v t)⁻¹ * p v δ * θv v (jv v t) = p v δ := by
    intro v t
    have hev : ∀ᶠ w in Filter.cofinite, Function.update (fun w => (1 : Tv w)) v t w ∈ KT w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
      exact one_mem _
    obtain ⟨τ, -, h1⟩ := hRPT.surj 1 _ hev
    have h2 : pT v τ = t := by rw [h1 v, Function.update_self]
    have h := congrArg (p v) (hinv τ)
    rw [map_mul, map_mul, map_inv, hpθ, hpj, h2] at h
    exact h
  have twI : ∀ t g, (ji t * g)⁻¹ * q δ * θi (ji t * g) = g⁻¹ * q δ * θi g := by
    intro t g
    rw [map_mul, mul_inv_rev]
    calc g⁻¹ * (ji t)⁻¹ * q δ * (θi (ji t) * θi g)
        = g⁻¹ * ((ji t)⁻¹ * q δ * θi (ji t)) * θi g := by simp only [mul_assoc]
      _ = g⁻¹ * q δ * θi g := by rw [invI]
  have twV : ∀ v t g, (jv v t * g)⁻¹ * p v δ * θv v (jv v t * g) = g⁻¹ * p v δ * θv v g := by
    intro v t g
    rw [map_mul, mul_inv_rev]
    calc g⁻¹ * (jv v t)⁻¹ * p v δ * (θv v (jv v t) * θv v g)
        = g⁻¹ * ((jv v t)⁻¹ * p v δ * θv v (jv v t)) * θv v g := by simp only [mul_assoc]
      _ = g⁻¹ * p v δ * θv v g := by rw [invV]
  let Fi : Gi → ℂ := fun x => ∫ s, φi (q (z s) * (x⁻¹ * q δ * θi x))
  let Fv : ∀ v, Gv v → ℂ := fun v x => φ v (x⁻¹ * p v δ * θv v x)
  have hf := hF Gi Ti μi ji νi hPi θi (q δ) (fun s => q (z s)) cθi (hRP.cq.comp cz) invI hC hB
    φi cφi sφi
  have hfm : Measurable Fi := hf.1
  have hf2 : qI μi ji νi Fi = ∫ s, qI μi ji νi fun x => φi (q (z s) * (x⁻¹ * q δ * θi x)) := hf.2
  have hFiI : ∀ t g, Fi (ji t * g) = Fi g := by
    intro t g
    show (∫ s, φi (q (z s) * ((ji t * g)⁻¹ * q δ * θi (ji t * g)))) = ∫ s, φi (q (z s) * (g⁻¹ * q δ * θi g))
    simp only [twI]
  have hFv : ∀ v, Measurable (Fv v) ∧ ∀ t g, Fv v (jv v t * g) = Fv v g := by
    intro v
    refine ⟨((cφ v).comp ((continuous_inv.mul continuous_const).mul (cθv v))).measurable, ?_⟩
    intro t g
    show φ v ((jv v t * g)⁻¹ * p v δ * θv v (jv v t * g)) = φ v (g⁻¹ * p v δ * θv v g)
    rw [twV]
  have hFS : ∀ v ∉ S, ∀ x, ((∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 1) ∧
      ((¬ ∃ t, ∃ y ∈ K v, x = jv v t * y) → Fv v x = 0) := by
    intro v hv x
    obtain ⟨h1, h2⟩ := hS v hv
    constructor
    · intro h
      show φ v (x⁻¹ * p v δ * θv v x) = 1
      rw [h1]
      exact Set.indicator_of_mem ((h2 x).2 h) _
    · intro h
      show φ v (x⁻¹ * p v δ * θv v x) = 0
      rw [h1]
      exact Set.indicator_of_notMem (fun hm => h ((h2 x).1 hm)) _
  have he := hE V G Gi Gv q p K T Ti Tv qT pT KT hRP hRPT j ji jv hqj hpj hK μ μi m ν νi nv
    hP hPi hPv S a b ha hb hEa hEb Fi Fv hfm hFiI hFv hFS
  have key : (fun x => ∫ s, φi (q (z s * (x⁻¹ * δ * θ x))) *
      ∏ᶠ v, φ v (p v (z s * (x⁻¹ * δ * θ x)))) = fun x => Fi (q x) * ∏ᶠ v, Fv v (p v x) := by
    funext x
    have h1 : ∀ s, q (z s * (x⁻¹ * δ * θ x)) = q (z s) * ((q x)⁻¹ * q δ * θi (q x)) := by
      intro s
      rw [map_mul, map_mul, map_mul, map_inv, hqθ]
    have h2 : ∀ s v, p v (z s * (x⁻¹ * δ * θ x)) = (p v x)⁻¹ * p v δ * θv v (p v x) := by
      intro s v
      rw [map_mul, hpz, one_mul, map_mul, map_mul, map_inv, hpθ]
    simp only [h1, h2]
    exact integral_mul_const _ _
  rw [key]
  exact ⟨he.1, he.2.trans (congrArg (fun w => ((a : ℝ) : ℂ) / ((b : ℝ) : ℂ) * w *
    ∏ v ∈ S, qI (m v) (jv v) (nv v) (Fv v)) hf2)⟩
end

section -- merged from Development.AutomorphicArithmetic.AdelicQuotients.QuotientMeasureSplit
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.QuotMap
open MeasureTheory Topology
open scoped ENNReal

theorem UpperTheory.ConvolutionTheory.G.quotMap_of :
    UpperTheory.ConvolutionTheory.G.NormEx → UpperTheory.ConvolutionTheory.G.QuotEq → UpperTheory.ConvolutionTheory.G.QuotMap := by
  intro hN hE G _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ G' _ _ _ _ _ _ _ _ T' _ _ _ _ _ _ _ _
    μ j ν hP μ' j' ν' hP' e y hμ hν F hF hinv
  obtain ⟨ρ0, -, hρ, -⟩ := hN G' T' μ' j' ν' hP'
  set ρ : G' → ℝ≥0∞ := fun g => (ρ0 g : ℝ≥0∞) with hρdef
  have hjc : Continuous j := hP.2.1.continuous
  have hj'c : Continuous j' := hP'.2.1.continuous
  have hec : Continuous e := e.continuous_toFun
  have hejc : Continuous (fun t => e (j t)) := hec.comp hjc
  haveI := hP.2.2.1
  haveI := hP'.1.1
  haveI := hP'.1.2
  have hrange : ∀ t, e (j t) ∈ Set.range j' := by
    have hcl : IsClosed (Set.range j') := hP'.2.1.isClosed_range
    have ho : IsOpen (Set.range j')ᶜ := hcl.isOpen_compl
    have h0 : (ν.map (fun t => e (j t))) (Set.range j')ᶜ = 0 := by
      rw [hν, Measure.map_apply hj'c.measurable ho.measurableSet]
      have : j' ⁻¹' (Set.range j')ᶜ = ∅ := by
        ext t; simp
      rw [this, measure_empty]
    rw [Measure.map_apply hejc.measurable ho.measurableSet] at h0
    have he := (ho.preimage hejc).eq_empty_of_measure_zero h0
    intro t
    by_contra hc
    have : t ∈ (fun t => e (j t)) ⁻¹' (Set.range j')ᶜ := hc
    rw [he] at this
    exact this
  have hφ : Measurable (fun g : G => e g * y) := (hec.mul continuous_const).measurable
  have hF1 : Measurable (fun g => F (e g * y)) := hF.comp hφ
  have hinv1 : ∀ t g, (fun g => F (e g * y)) (j t * g) = (fun g => F (e g * y)) g := by
    intro t g
    obtain ⟨t', ht'⟩ := hrange t
    simp only [map_mul, ← ht', mul_assoc, hinv]
  have hρ1 : UpperTheory.ConvolutionTheory.G.IsNrm j ν (fun g => ρ (e g * y)) := by
    refine ⟨hρ.1.comp hφ, fun x => ?_⟩
    have hm : Measurable (fun z : G' => ρ (z * (e x * y))) := hρ.1.comp (measurable_mul_const _)
    have h1 := lintegral_map (μ := ν) hm hejc.measurable
    have h2 := lintegral_map (μ := ν') hm hj'c.measurable
    rw [hν, h2, hρ.2] at h1
    simp only [map_mul, mul_assoc]
    exact h1.symm
  haveI : μ'.IsMulRightInvariant := by
    have h : μ'.inv.IsMulRightInvariant := inferInstance
    rwa [Measure.inv_eq_self] at h
  have hmp : MeasurePreserving (fun g : G => e g * y) μ μ' :=
    (measurePreserving_mul_right μ' y).comp ⟨hec.measurable, hμ⟩
  have hemb : MeasurableEmbedding (fun g : G => e g * y) :=
    (e.toHomeomorph.trans (Homeomorph.mulRight y)).measurableEmbedding
  obtain ⟨a1, -, a3⟩ := hE G T μ j ν hP _ hF1 hinv1 _ hρ1
  obtain ⟨b1, -, b3⟩ := hE G' T' μ' j' ν' hP' F hF hinv ρ hρ
  refine ⟨?_, ?_⟩
  · rw [a1, b1]
    exact hmp.integrable_comp_emb hemb (g := fun x => F x * ((ρ x).toReal : ℂ))
  · rw [a3, b3]
    exact hmp.integral_comp hemb (fun x => F x * ((ρ x).toReal : ℂ))
end

open UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory Topology
open scoped ENNReal

private theorem uni_map {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [MeasurableSpace A] [BorelSpace A] [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [MeasurableSpace B] [BorelSpace B] {m : Measure A} (h : Uni m) (e : A ≃ₜ* B) :
    Uni (m.map e) := by
  obtain ⟨h1, h2⟩ := h
  have he : Measurable e := (map_continuous e).measurable
  refine ⟨e.isHaarMeasure_map m, ⟨?_⟩⟩
  rw [Measure.inv_def, Measure.map_map measurable_inv he]
  have hc : (Inv.inv ∘ e : A → B) = e ∘ Inv.inv := by
    funext x
    simp
  rw [hc, ← Measure.map_map he measurable_inv, Measure.map_inv_eq_self]

private theorem qI_one_id {R : Type} [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
    [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R] [MeasurableSpace R]
    [BorelSpace R] {l : Measure R} (hP : Pair l (MonoidHom.id R) l) :
    qI l (MonoidHom.id R) l (fun _ => 1) = 1 := by
  obtain ⟨ρ, -, hρ, -⟩ := normEx R R l (MonoidHom.id R) l hP
  obtain ⟨-, -, h3⟩ := quotEq R R l (MonoidHom.id R) l hP (fun _ => 1) measurable_const
    (fun _ _ => rfl) _ hρ
  rw [h3]
  have h := hρ.2 1
  simp only [MonoidHom.id_apply, mul_one] at h
  simp only [one_mul]
  have h4 : ∫ x, (((ρ x : ℝ≥0∞).toReal : ℝ) : ℂ) ∂l = ((∫ x, (ρ x : ℝ≥0∞).toReal ∂l : ℝ) : ℂ) :=
    integral_ofReal
  rw [h4, integral_toReal hρ.1.aemeasurable (ae_of_all _ fun x => ENNReal.coe_lt_top), h]
  simp

theorem UpperTheory.quotient_measure_split :
    SplitQ := by
  intro G₁ _ _ _ _ _ _ _ _ T₁ _ _ _ _ _ _ _ _ R _ _ _ _ _ _ _ _ G _ _ _ _ _ _ _ _
    T _ _ _ _ _ _ _ _ μ j₁ ν l hP hl e eT j hj
  have hPl : Pair l (MonoidHom.id R) l := ⟨hl, IsClosedEmbedding.id, hl⟩
  obtain ⟨hPP, hQ⟩ := quotProd_of normEx quotEq G₁ T₁ R R μ j₁ ν hP l (MonoidHom.id R) l hPl
  have hje : ∀ x : T₁ × R, j (eT x) = e (j₁.prodMap (MonoidHom.id R) x) := fun x => hj x
  have hcomp : (j : T → G) = e ∘ (j₁.prodMap (MonoidHom.id R)) ∘ eT.symm := by
    funext t
    have := hje (eT.symm t)
    simpa using this
  have hcl : IsClosedEmbedding j := by
    rw [hcomp]
    exact e.toHomeomorph.isClosedEmbedding.comp
      (hPP.2.1.comp eT.symm.toHomeomorph.isClosedEmbedding)
  have hPair : Pair ((μ.prod l).map e) j ((ν.prod l).map eT) :=
    ⟨uni_map hPP.1 e, hcl, uni_map hPP.2.2 eT⟩
  refine ⟨hPair, fun F hF hFi => ?_⟩
  have he : Measurable e := (map_continuous e).measurable
  have heT : Measurable eT := (map_continuous eT).measurable
  have hjm : Measurable j := hcl.continuous.measurable
  have hjp : Measurable (j₁.prodMap (MonoidHom.id R)) := hPP.2.1.continuous.measurable
  have hf : Measurable (fun x => F (e (x, (1 : R)))) :=
    hF.comp (he.comp (measurable_id.prodMk measurable_const))
  have hfi : ∀ t g, F (e (j₁ t * g, (1 : R))) = F (e (g, (1 : R))) := by
    intro t g
    have h : e (j₁ t * g, (1 : R)) = j (eT (t, 1)) * e (g, 1) := by
      rw [hj, ← map_mul]
      simp
    rw [h, hFi]
  have h1 := (hQ (fun x => F (e (x, (1 : R)))) (fun _ => 1) hf hfi measurable_const
    (fun _ _ => rfl)).2
  rw [qI_one_id hPl, mul_one] at h1
  rw [← h1]
  have hmap : (ν.prod l).map (fun t => e (j₁.prodMap (MonoidHom.id R) t)) =
      ((ν.prod l).map eT).map j := by
    rw [Measure.map_map hjm heT]
    congr 1
    funext t
    exact (hje t).symm
  have h2 := (quotMap_of normEx quotEq (G₁ × R) (T₁ × R) G T (μ.prod l)
    (j₁.prodMap (MonoidHom.id R)) (ν.prod l) hPP ((μ.prod l).map e) j ((ν.prod l).map eT) hPair
    e 1 rfl hmap F hF hFi).2
  rw [← h2]
  congr 1
  funext g
  have h3 : e g = j (eT (1, g.2)) * e (g.1, 1) := by
    rw [hj, ← map_mul]
    simp
  simp only [mul_one]
  rw [h3, hFi]
end

open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem match_qI {n : ℕ} {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R]
    [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)] {ι : R →+* S} {s : S →+* S} {l : ℕ}
    {μS : Measure (GL (Fin n) S)} {μR : Measure (GL (Fin n) R)} {c : ℂ} {φ : GL (Fin n) S → ℂ} {f : GL (Fin n) R → ℂ}
    (h : Match ι s l μS μR c φ f) (γ : GL (Fin n) R) (hγ : γ.val.charpoly.Separable) (H : Subgroup (GL (Fin n) R))
    (hH : H = Subgroup.centralizer {γ}) (ν : Measure H) (hν : ν.IsHaarMeasure) :
    (∀ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ →
      qI μS ((mapGL n ι).comp H.subtype) ν (fun x => φ (x⁻¹ * δ * mapGL n s x)) =
        c * qI μR H.subtype ν (fun x => f (x⁻¹ * γ * x))) ∧
    ((¬ ∃ δ : GL (Fin n) S, twNorm (mapGL n s) l δ = mapGL n ι γ) → qI μR H.subtype ν (fun x => f (x⁻¹ * γ * x)) = 0) := by
  subst hH
  exact h γ hγ ν hν

private theorem cent_mul {G : Type} [Group G] (z g : G) (hz : ∀ x, z * x = x * z) :
    Subgroup.centralizer {g} = Subgroup.centralizer {z * g} := by
  ext t
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change (t * g = g * t) ↔ (t * (z * g) = (z * g) * t)
  rw [← mul_assoc, ← hz t, mul_assoc, mul_assoc, mul_right_inj]

private theorem lc_cent {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] (g : G) :
    LocallyCompactSpace (Subgroup.centralizer {g}) := by
  have : IsClosed (Subgroup.centralizer {g} : Set G) := Set.isClosed_centralizer _
  exact this.locallyCompactSpace

private theorem main (hGl : Glob) (hC : HaarConst) (hX : HaarEx) (hRF : RPF) (hRE : RPE) (hRC : RPCen) (hSF : SideF) (hSE : SideE)
    (hK : K1) (hKF : SelmerRankBoundLaurent) (hH : H1) (hZ : ZNorm) (hN : LocNorm) (hS : SepLoc) (hL : CentLoc) : G4 := by
  classical
  intro F E _ _ _ _ _ _ σ hσ n hn hp _ _ _ _ _ _ _ _ μE μF μiE μiF mE mF hμE hμF hiE hiF hmE hmF
  obtain ⟨μE', μF', uE, uF, hG⟩ := hGl F E σ hσ n hn μE μF hμE hμF
  obtain ⟨aE, haE, hEE⟩ := hC _ _ _ _ _ _ _ (hRE F E n) μE' μiE mE uE.1 hiE hmE
  obtain ⟨aF, haF, hEF⟩ := hC _ _ _ _ _ _ _ (hRF F n) μF' μiF mF uF.1 hiF hmF
  refine ⟨aE / aF, div_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haE)) (NNReal.coe_pos.2 (pos_iff_ne_zero.2 haF)), ?_⟩
  intro S φi fi φ f ci c hφi hφi' hfi hfi' hφ hoff hMi hM γ γ₁ hγ₁ hirr ν hν
  have hsep : IsRegSemisimple γ := hirr.separable
  obtain ⟨ν', hν', hGF, hGE⟩ := hG γ γ₁ hγ₁ hsep ν hν
  obtain ⟨hs1, hs2, hs3⟩ := hS F n γ hsep
  haveI : LocallyCompactSpace (TA γ) := lc_cent _
  haveI : LocallyCompactSpace (TI γ) := lc_cent _
  haveI : ∀ v, LocallyCompactSpace (TF γ v) := fun v => lc_cent _
  haveI : SecondCountableTopology (TA γ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ∀ v, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology _
  have hT := fun S' => hX _ _ _ _ _ _ _ (hRC _ _ _ _ _ _ _ (hRF F n) (AdelicGLn.diagonal F n γ)) ν' Measure.haar
    (fun _ => Measure.haar) hν' inferInstance (fun _ => inferInstance) S'
  have hcF := (hKF F n hn γ hsep)
  rw [eventually_cofinite] at hcF
  have hFside := fun (S' : Finset (Pl F)) (h1 : S ⊆ S') (h2 : hcF.toFinset ⊆ S') (b : NNReal) (hb : b ≠ 0)
      (hE : EulT γ ν' Measure.haar (fun _ => Measure.haar) b S') =>
    hSF F n hn μF' μiF mF uF hiF (fun v => (hmF v).1) γ hsep ν' Measure.haar (fun _ => Measure.haar) hν' inferInstance
      (fun _ => inferInstance) S' aF b haF hb hE (hEF S') fi f hfi hfi' (fun v => (hφ v).2.2.1)
      (fun v hv => ⟨(hoff v fun h => hv (h1 h)).2.1, by
        by_contra h
        exact hv (h2 (hcF.mem_toFinset.2 h))⟩)
  have hMi' := fun s : ℝ => match_qI hMi _ (hs2 s) (TI γ) (cent_mul _ _ (hL F n _).2.1) Measure.haar inferInstance
  have hM' := fun v => match_qI (hM v) _ (hs3 v) (TF γ v) rfl Measure.haar inferInstance
  constructor
  · intro δ hδ
    have hcE := hK F E σ hσ n hn δ γ hsep hδ
    rw [eventually_cofinite] at hcE
    obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset ∪ hcE.toFinset)
    have h1 : S ⊆ S ∪ hcF.toFinset ∪ hcE.toFinset := Finset.subset_union_left.trans Finset.subset_union_left
    obtain ⟨m1, e1⟩ := hFside _ h1 (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE
    obtain ⟨m2, e2⟩ := hSE F E σ hσ n hn μE' μiE mE uE hiE (fun v => (hmE v).1) γ hsep δ hδ ν' Measure.haar (fun _ => Measure.haar)
      hν' inferInstance (fun _ => inferInstance) _ aE b haE hb hE (hEE _) φi φ hφi hφi' (fun v => (hφ v).1)
      (fun v hv => ⟨(hoff v fun h => hv (h1 h)).1, by
        by_contra h
        exact hv (Finset.subset_union_right (hcE.mem_toFinset.2 h))⟩)
    obtain ⟨n1, n2⟩ := hN F E σ hσ n hn δ γ hδ
    rw [hGF _ m1, hGE δ hδ _ m2, e1, e2]
    have i1 := fun s : ℝ => (hMi' s).1 (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) (by
      rw [hZ F E σ hσ n hn, n1, ← map_mul])
    have i2 := fun v => (hM' v).1 _ (n2 v)
    simp only [i1, i2]
    rw [integral_const_mul, Finset.prod_mul_distrib, ← Finset.prod_subset h1 fun v _ hv => (hoff v hv).2.2]
    have : ((aF : ℝ) : ℂ) ≠ 0 := by exact_mod_cast haF
    push_cast
    field_simp
  · intro hno
    by_cases hi : ∃ δ, twNorm (mapGL n (galInf σ)) (Module.finrank F E) δ =
        mapGL n (infMap F E) (pI F n (AdelicGLn.diagonal F n γ))
    · have : ¬ ∀ v : Pl F, ∃ δ, twNorm (mapGL n (galFin σ v)) (Module.finrank F E) δ =
          mapGL n (incFin E v) (finAt v (AdelicGLn.diagonal F n γ)) := fun h => hno (hH F E σ hσ n hn hp γ hirr hi h)
      obtain ⟨v, hv⟩ := not_forall.1 this
      obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset ∪ {v})
      obtain ⟨m1, e1⟩ := hFside _ (Finset.subset_union_left.trans Finset.subset_union_left)
        (Finset.subset_union_right.trans Finset.subset_union_left) b hb hE
      rw [hGF _ m1, e1, Finset.prod_eq_zero (i := v) (by simp) ((hM' v).2 hv), mul_zero]
    · obtain ⟨b, hb, hE⟩ := hT (S ∪ hcF.toFinset)
      obtain ⟨m1, e1⟩ := hFside _ Finset.subset_union_left Finset.subset_union_right b hb hE
      have i1 := fun s : ℝ => (hMi' s).2 (by
        rintro ⟨δ, hδ⟩
        refine hi ⟨(pI E n (zA E n s))⁻¹ * δ, ?_⟩
        have h := hZ F E σ hσ n hn s ((pI E n (zA E n s))⁻¹ * δ)
        rw [mul_inv_cancel_left, hδ, map_mul] at h
        exact (mul_left_cancel h).symm)
      rw [hGF _ m1, e1]
      simp only [i1, integral_zero, mul_zero, zero_mul]

theorem UpperTheory.ConvolutionTheory.G.stable_twisted_trace_formula_comparison :
    Q1 → Q2 → Q3 → N3 → N5 → P1 → P2 → K1 → H1 → G4 := by
  intro _ _ _ n3 n5 _ p2 k1 h1
  have qpush : QPush := UpperTheory.quotient_haar_measure_pushforward
  have splitEq : SplitEquiv := UpperTheory.adelicGL_split_equiv
  have splitQ : SplitQ := UpperTheory.quotient_measure_split
  have uniOf : UniOf := UpperTheory.haar_unimodular_criterion
  have haarEx : HaarEx := UpperTheory.exists_haarMeasure_adelicGL
  have haarConst : HaarConst := UpperTheory.haar_const_of_haar_exists haarEx
  have uniLoc : UniLoc := UpperTheory.local_unimodular_of_exists_haar_measure haarEx
  have rpCen : RPCen := UpperTheory.restrictedProduct_centralizer_adelicGL
  have euler : Euler := UpperTheory.eulerProduct_of_quotient_pushforward_support qpush UpperTheory.euler_product_support_finite
  have sideAbs : SideAbs := UpperTheory.geometric_side_absolutely_convergent_of_euler_fubini euler UpperTheory.orbital_integral_fubini
  have qsub : QSub := UpperTheory.haar_quotient_subgroup
  have rpf : RPF := UpperTheory.restrictedProduct_finite_adelicGL
  have rpe : RPE := UpperTheory.restrictedProduct_extension_of_base_regroup rpf
  have compat : Compat := UpperTheory.adele_galois_action_baseChange_compat
  have galCont : GalCont := UpperTheory.adele_galois_action_continuous compat rpe
  have locEmb : LocEmb := UpperTheory.adele_baseChange_local_isClosedEmbedding
  have unitIff : UnitIff := UpperTheory.adicCompletion_integers_baseChange_iff
  have centLoc : CentLoc := UpperTheory.centralSection_local_scalar
  have centBC : CentBC := UpperTheory.centralSection_baseChange
  have zNorm : ZNorm := UpperTheory.twistedNorm_central_of_baseChange_compat compat centLoc centBC
  have locNorm : LocNorm := UpperTheory.twistedNorm_local_of_compat compat
  have sepLoc : SepLoc := UpperTheory.separableLocal_of_separableScalar UpperTheory.charpoly_separable_unit_smul centLoc
  have tComm : TComm := UpperTheory.torusCommutative_of_centralizerCommutative UpperTheory.centralizer_commutative_of_separable_charpoly
  have triv : Triv := UpperTheory.baseChange_trivial_extension
  have boundE : BoundE := UpperTheory.adelicBound_of_centralizer_localization n5 compat centLoc rpe
  have infF : InfF := UpperTheory.infinitePart_finite_of_adelicBound p2 triv boundE
  have k1F : SelmerRankBoundLaurent := UpperTheory.maximalCompactNorm_of_unit_criterion k1 triv unitIff compat
  have spl : Spl := UpperTheory.splitCentralizer_of_splitEquiv splitEq n5 centBC
  have glob : Glob := UpperTheory.globalOrbitalComparison_of_split qsub splitQ uniOf tComm spl n3 n5 centBC
  have sideF : SideF := UpperTheory.orbitalSideBaseField_of_absoluteConvergence sideAbs rpf rpCen uniLoc uniOf tComm sepLoc centLoc infF
  have sideE : SideE := UpperTheory.orbitalSideExtension_of_absoluteConvergence sideAbs rpf rpe rpCen uniLoc uniOf tComm sepLoc centLoc compat galCont locEmb unitIff locNorm boundE n3 n5 p2
  exact main glob haarConst haarEx rpf rpe rpCen sideF sideE k1 k1F h1 zNorm locNorm sepLoc centLoc
