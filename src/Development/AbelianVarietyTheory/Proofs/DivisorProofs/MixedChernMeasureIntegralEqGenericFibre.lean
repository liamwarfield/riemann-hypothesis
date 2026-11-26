module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralGeneratorRigidificationAllLevels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVariety
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteIffFiniteKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOverRingHomIsHomeomorphBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOverRingHomIsHomeomorphBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX isPushout_sections)

theorem isHomeomorph_bcPt (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0})
    (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ) :
    IsHomeomorph (bcPt hp.w τ) := by
  let E : CxPts q τ ≃ CxPts p (τ.comp ρ) := Equiv.ofBijective (bcPt hp.w τ) (CxPts.bijective_bcMap hp τ)
  have hm : ∀ z, (bcPt hp.w τ z).1 = z.1 ≫ j := fun _ => rfl
  have hE : ∀ y, bcPt hp.w τ (E.symm y) = y := E.apply_symm_apply
  have hc : Continuous E.symm := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    obtain ⟨U, hyU⟩ := CxPts.exists_mem_ptsIn (iSup_affineOpens_eq_top X) y
    have hU : IsAffineOpen U.1 := U.2
    have hW : IsAffineOpen (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := by
      rw [show j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤ = j ⁻¹ᵁ U.1 from inf_top_eq _]
      exact GlobalTheory.TopForm.isAffineOpen_preimage_of_isPullback hp hU
    have hin : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, E.symm w ∈ ptsIn q τ (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := fun w hw =>
      mem_ptsIn_inf.2 ⟨(mem_ptsIn_preimage hm).2 (by rw [hE]; exact hw), mem_ptsIn_top⟩
    have hnb : ptsIn p (τ.comp ρ) U.1 ∈ 𝓝 y := (isOpen_ptsIn _).mem_nhds hyU
    have hev : ∀ᶠ w in 𝓝 y, E.symm w ∈ ptsIn q τ (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) := eventually_of_mem hnb hin
    letI := ρ.toAlgebra
    have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout (isPushout_sections p q j hp U.1 hU)
    refine tendsto_subtype_rng.2 ((Points.tendsto_iff_of_generators hW (hin y hyU) hgen).2 ⟨hev, ?_⟩)
    rintro f (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · have e : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, ev p (τ.comp ρ) U.1 a w =
          valR (E.symm w).1 _ ((j.appLE U.1 (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) inf_le_left).hom a) := fun w hw => by
        have := CxPts.ev_appLE_of_comp hm inf_le_left a (hin w hw)
        rw [hE] at this
        exact this.symm
      have h := ((continuousOn_ev a).continuousAt hnb).tendsto
      rw [e y hyU] at h
      exact h.congr' (eventually_of_mem hnb e)
    · have e : ∀ w ∈ ptsIn p (τ.comp ρ) U.1, τ b =
          valR (E.symm w).1 _ (algX q (j ⁻¹ᵁ U.1 ⊓ q ⁻¹ᵁ ⊤) b) := fun w hw => (ev_algX (hin w hw) b).symm
      have h : Tendsto (fun _ : CxPts p (τ.comp ρ) => τ b) (𝓝 y) (𝓝 (τ b)) := tendsto_const_nhds
      have h' := h.congr' (eventually_of_mem hnb e)
      rw [e y hyU] at h'
      exact h'
  exact (Homeomorph.mk E (continuous_bcPt hp.w τ) hc).isHomeomorph

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOverRingHomIsHomeomorphBaseChangeStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ), IsHomeomorph (bcPt hp.w τ) := by
  first | exact @GlobalTheory.Mix.isHomeomorph_bcPt | exact GlobalTheory.Mix.isHomeomorph_bcPt | (intros; apply GlobalTheory.Mix.isHomeomorph_bcPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartDensBc
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.Mix

theorem exists_chart_dens_bc : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ) (D : ℕ) (c : AlgChart p (τ.comp ρ) D) (z : CxPts q τ), bcPt hp.w τ z ∈ c.e.source → ∃ c' : AlgChart q τ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, bcPt hp.w τ w ∈ c.e.source ∧ c'.e w = c.e (bcPt hp.w τ w) ∧ ∀ L : Fin D → MLine p (τ.comp ρ), dens (fun i => (L i).bc hp.w τ) c' w = dens L c (bcPt hp.w τ w) := by
  intro k K _ _ ρ X G p q j hp τ D c z hz
  have hm : ∀ w, (bcPt hp.w τ w).1 = w.1 ≫ j := fun _ => rfl
  obtain ⟨c₀, hz₀, h, hx⟩ := c.exists_baseChange hp hm hz
  let c' := c₀.restr (bcPt hp.w τ ⁻¹' c.e.source) (c.e.open_source.preimage (continuous_bcPt hp.w τ))
  have H : ∀ w ∈ c'.e.source, bcPt hp.w τ w ∈ c.e.source ∧ c'.e w = c.e (bcPt hp.w τ w) := by
    intro w hw
    rw [AlgChart.restr_source] at hw
    refine ⟨hw.2, ?_⟩
    change c₀.e w = _
    ext a
    rw [c.apply_eq _ hw.2, c₀.apply_eq _ hw.1, hx, ev_appLE_of_comp hm h _ (c₀.source_subset hw.1)]
  refine ⟨c', by rw [AlgChart.restr_source]; exact ⟨hz₀, hz⟩, fun w hw => ⟨(H w hw).1, (H w hw).2, fun L => ?_⟩⟩
  have hw' := (H w hw).1
  have key (N : MLine p (τ.comp ρ)) :
      c'.hess (N.bc hp.w τ).φ (pick (N.bc hp.w τ).φ.isLB w) w =
        c.hess N.φ (pick N.φ.isLB (bcPt hp.w τ w)) (bcPt hp.w τ w) := by
    have hj := mem_of_mem_linComb (m := fun _ => bcPt hp.w τ w) (fun _ => rfl)
      (mem_pick (N.bc hp.w τ).φ.isLB w) PUnit.unit
    rw [c.hess_eq N.cInf hw' hj (mem_pick _ _), AlgChart.hess,
      AlgChart.hess, ← (H w hw).2, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr]
    filter_upwards [c'.e.open_target.mem_nhds (c'.e.map_source hw)] with v hv
    obtain ⟨h₁, h₂⟩ := H _ (c'.e.map_target hv)
    rw [c'.e.right_inv hv] at h₂
    have e₁ : c.e.symm v = bcPt hp.w τ (c'.e.symm v) := (congrArg c.e.symm h₂).trans (c.e.left_inv h₁)
    rw [e₁]
    simp [MLine.bc, Weight.linComb]
  simp only [dens, key]

end GlobalTheory.Mix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibre
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

open GlobalTheory.ChartGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixGen

theorem ofReal_dens_trans {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) (ε : ℤˣ) (c c' : AlgChart p σ D) (y : CxPts p σ) (hy : y ∈ c.e.source)
    (hy' : y ∈ c'.e.source) :
    ENNReal.ofReal ((ε : ℤ) * dens L c y) =
      ENNReal.ofReal (‖transDet c.e c'.e y‖ ^ 2) * ENNReal.ofReal ((ε : ℤ) * dens L c' y) := by
  rw [GlobalTheory.T.mixedChernFormDensity_change_of_chart k X p σ D L c c' y hy hy', ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem map_part {k K : Type} [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] {X G : Scheme.{0}}
    [IsIntegral X] {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X}
    (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) {D : ℕ} (hX : IsArithVar p D)
    (L : Fin D → MLine p (τ.comp (algebraMap k K))) (ε : ℤˣ) :
    Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε := by
  have hm : IsHomeomorph (bcPt hp.w τ) := GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange k K (algebraMap k K) X G p q j hp τ
  obtain ⟨_, hT2, hSC⟩ := (IsArithVar.finite_emb_and_topology hX).2 (τ.comp (algebraMap k K))
  let h := hm.homeomorph (bcPt hp.w τ)
  haveI : T2Space (CxPts q τ) := h.isEmbedding.t2Space
  haveI : SecondCountableTopology (CxPts q τ) := h.isEmbedding.secondCountableTopology
  obtain ⟨hGi, _, _, _, hgen, _⟩ := GlobalTheory.Mix.genericFibre_facts k K X G p q j hp D hX
  obtain ⟨U, hU, hηU, t, ht⟩ := GenericCoords.exists_affine_etale_coords hX
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgZ : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hηU
  have hTc : IsClosed {y : CxPts p (τ.comp (algebraMap k K)) |
      y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
    have e : {y : CxPts p (τ.comp (algebraMap k K)) | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} =
        (ptsIn p (τ.comp (algebraMap k K)) U)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [e]
    exact (isOpen_ptsIn _).isClosed_compl
  have hZG : IsClosed (j ⁻¹' (U : Set X)ᶜ) := hZ.preimage j.continuous
  have hgZG : genericPoint G ∉ j ⁻¹' (U : Set X)ᶜ := by
    simp only [Set.mem_preimage]
    rw [hgen]
    exact hgZ
  have key := GlueCoverNull.map_glueMeas_of_cover D (CxPts p (τ.comp (algebraMap k K))) (CxPts q τ)
    (AlgChart p (τ.comp (algebraMap k K)) D) (AlgChart q τ D) (fun c => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y)) (fun c => c.e)
    (fun c y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).bc hp.w τ) c y))
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ofReal_dens_trans L ε c c' y hy hy')
    (fun c c' => c.holo_trans c') (fun c c' y hy hy' => ofReal_dens_trans _ ε c c' y hy hy')
    (bcPt hp.w τ) hm.continuous _ hTc (fun c => ChernNull.chart_null hX hZ hgZ _ c)
    (fun c => ChernNull.chart_null_field K G q τ D _ hZG hgZG c) 1
    (fun x _ => by
      obtain ⟨w0, hw0⟩ := hm.surjective x
      exact Set.encard_eq_one.2 ⟨w0, Set.ext fun w =>
        ⟨fun hw => hm.injective (hw.trans hw0.symm), fun hw => hw ▸ hw0⟩⟩)
    (fun z hz => by
      have hmem : bcPt hp.w τ z ∈ ptsIn p (τ.comp (algebraMap k K)) U := by
        simpa [mem_ptsIn] using hz
      obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hU t ht hmem
      obtain ⟨c', hz', hc'⟩ := GlobalTheory.Mix.exists_chart_dens_bc k K (algebraMap k K) X G p q j hp τ D c z hc
      exact ⟨c, c', hz', hc, fun w hw _ => ⟨(hc' w hw).2.1, by simp only [(hc' w hw).2.2 L]⟩⟩)
  rw [Nat.cast_one, one_smul] at key
  exact key

theorem part_int_generic : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → MLine p (τ.comp (algebraMap k K))), (∀ ε : ℤˣ, Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε) ∧ ∀ f : CxPts p (τ.comp (algebraMap k K)) → ℝ, (Intg (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) = Mix.int L f := by
  intro k K _ _ _ _ X G _ p q j hp τ D hX L
  have hmap := map_part hp τ hX L
  have hm : IsHomeomorph (bcPt hp.w τ) := GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange k K (algebraMap k K) X G p q j hp τ
  have he : MeasurableEmbedding (bcPt hp.w τ) := (hm.homeomorph (bcPt hp.w τ)).measurableEmbedding
  refine ⟨hmap, fun f => ⟨?_, ?_⟩⟩
  · simp only [Intg]
    rw [← hmap 1, ← hmap (-1), he.integrable_map_iff, he.integrable_map_iff]
    rfl
  · simp only [Mix.int]
    rw [← hmap 1, ← hmap (-1), he.integral_map, he.integral_map]

end GlobalTheory.MixGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibreStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (τ : K →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → MLine p (τ.comp (algebraMap k K))), (∀ ε : ℤˣ, Measure.map (bcPt hp.w τ) (part (fun i => (L i).bc hp.w τ) ε) = part L ε) ∧ ∀ f : CxPts p (τ.comp (algebraMap k K)) → ℝ, (Intg (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).bc hp.w τ) (fun y => f (bcPt hp.w τ y)) = Mix.int L f := by
  first | exact @GlobalTheory.MixGen.part_int_generic | exact GlobalTheory.MixGen.part_int_generic | (intros; apply GlobalTheory.MixGen.part_int_generic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupSchemeOfGeometricallyIntegralImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupSchemeOfGeometricallyIntegralImage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_lift_of_surjective_of_isReduced {K : Type} [Field K] {T T' Z Y : Over (Sp K)}
    (i : Z ⟶ Y) [IsClosedImmersion i.left] [IsReduced T.left] (q : T' ⟶ T) (g : T ⟶ Y) (r : T' ⟶ Z)
    (hq : Surjective q.left) (h : q ≫ g = r ≫ i) : ∃ e : T ⟶ Z, e ≫ i = g := by
  obtain ⟨e, he⟩ := GlobalTheory.lift_of_reduced_of_support i.left g.left (fun t => by
    obtain ⟨t', rfl⟩ := hq.surj t
    apply i.left.range_subset_ker_support
    refine ⟨r.left t', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, ← h, Over.comp_left, Scheme.Hom.comp_apply])
  exact ⟨Over.homMk e (by rw [← Over.w i, ← Category.assoc, he, Over.w g]), Over.OverMorphism.ext he⟩

theorem exists_grpObj_of_image :
    ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X), p ≫ i = f.hom → Surjective p.left → IsClosedImmersion i.left → GeometricallyIntegral Z.hom → ∃ _ : GrpObj Z, IsMonHom p ∧ IsMonHom i := by
  intro K _ A B f Z p i hf hp hi hZ
  have hmono : Mono i := Over.mono_of_mono_left i
  haveI : IsIntegral Z.left := GeometricallyIntegral.isIntegral_of_subsingleton Z.hom
  haveI := B.smooth
  haveI : Smooth B.X.hom := SmoothOfRelativeDimension.smooth B.dim _
  haveI : LocallyOfFiniteType Z.hom := by rw [← Over.w i]; infer_instance
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  haveI : IsReduced (Z ⊗ Z).left := (inferInstance : IsReduced (pullback Z.hom Z.hom))
  haveI : MorphismProperty.IsStableUnderComposition @Surjective :=
    ⟨fun f g hf hg => by haveI := hf; haveI := hg; infer_instance⟩
  have hpp : Surjective (p ⊗ₘ p).left :=
    MorphismProperty.pullbackMap (P := @Surjective) hp hp (Over.w p).symm (Over.w p).symm
  have hinv : ι[A.X] ≫ f.hom = f.hom ≫ ι[B.X] := by
    calc ι[A.X] ≫ f.hom = (𝟙 A.X)⁻¹ ≫ f.hom := by rw [Hom.inv_def, Category.id_comp]
      _ = (𝟙 A.X ≫ f.hom)⁻¹ := GrpObj.inv_comp _ _
      _ = f.hom ≫ ι[B.X] := by rw [Category.id_comp, Hom.inv_def]
  obtain ⟨m, hm⟩ := exists_lift_of_surjective_of_isReduced i (p ⊗ₘ p) ((i ⊗ₘ i) ≫ μ[B.X]) (μ[A.X] ≫ p) hpp (by
    rw [← Category.assoc, tensorHom_comp_tensorHom, hf, ← IsMonHom.mul_hom, Category.assoc, hf])
  obtain ⟨v, hv⟩ := exists_lift_of_surjective_of_isReduced i p (i ≫ ι[B.X]) (ι[A.X] ≫ p) hp (by
    rw [← Category.assoc, hf, Category.assoc, hf, hinv])
  have h1 : (η[A.X] ≫ p) ≫ i = η[B.X] := by rw [Category.assoc, hf, IsMonHom.one_hom]
  have h1a : η[A.X] ≫ p ≫ i = η[B.X] := by rw [← Category.assoc, h1]
  letI M : MonObj Z :=
    { one := η[A.X] ≫ p
      mul := m
      one_mul := by
        rw [← cancel_mono i, Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, h1,
          Category.id_comp, tensorHom_def', Category.assoc, MonObj.one_mul, leftUnitor_naturality]
      mul_one := by
        rw [← cancel_mono i, Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, h1,
          Category.id_comp, MonoidalCategory.tensorHom_def, Category.assoc, MonObj.mul_one, rightUnitor_naturality]
      mul_assoc := by
        rw [← cancel_mono i]
        calc (m ▷ Z ≫ m) ≫ i = ((i ⊗ₘ i) ⊗ₘ i) ≫ μ[B.X] ▷ B.X ≫ μ[B.X] := by
              simp only [Category.assoc, hm, ← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
                Category.comp_id]
          _ = ((i ⊗ₘ i) ⊗ₘ i) ≫ (α_ _ _ _).hom ≫ B.X ◁ μ[B.X] ≫ μ[B.X] := by rw [MonObj.mul_assoc]
          _ = (α_ Z Z Z).hom ≫ (i ⊗ₘ (i ⊗ₘ i)) ≫ B.X ◁ μ[B.X] ≫ μ[B.X] := by
              rw [associator_naturality_assoc]
          _ = ((α_ Z Z Z).hom ≫ Z ◁ m ≫ m) ≫ i := by
              simp only [Category.assoc, hm, ← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
                Category.comp_id] }
  letI G : GrpObj Z :=
    { inv := v
      left_inv := by
        rw [← cancel_mono i, Category.assoc]
        change lift v (𝟙 Z) ≫ m ≫ i = (toUnit Z ≫ η[A.X] ≫ p) ≫ i
        rw [hm, lift_map_assoc, hv, Category.id_comp,
          show lift (i ≫ ι[B.X]) i = i ≫ lift ι[B.X] (𝟙 B.X) by rw [comp_lift, Category.comp_id],
          Category.assoc, GrpObj.left_inv, ← Category.assoc, comp_toUnit]
        simp only [Category.assoc, h1a]
      right_inv := by
        rw [← cancel_mono i, Category.assoc]
        change lift (𝟙 Z) v ≫ m ≫ i = (toUnit Z ≫ η[A.X] ≫ p) ≫ i
        rw [hm, lift_map_assoc, hv, Category.id_comp,
          show lift i (i ≫ ι[B.X]) = i ≫ lift (𝟙 B.X) ι[B.X] by rw [comp_lift, Category.comp_id],
          Category.assoc, GrpObj.right_inv, ← Category.assoc, comp_toUnit]
        simp only [Category.assoc, h1a] }
  refine ⟨G, ⟨rfl, ?_⟩, ⟨h1, hm⟩⟩
  change μ[A.X] ≫ p = (p ⊗ₘ p) ≫ m
  rw [← cancel_mono i, Category.assoc, Category.assoc, hm, hf, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hf]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubgroupSchemeOfGeometricallyIntegralImageStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subgroupScheme_of_geometricallyIntegral_image : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X), p ≫ i = f.hom → Surjective p.left → IsClosedImmersion i.left → GeometricallyIntegral Z.hom → ∃ _ : GrpObj Z, IsMonHom p ∧ IsMonHom i := by
  first | (exact @GlobalTheory.AV.AbVar.exists_grpObj_of_image) | (exact GlobalTheory.AV.AbVar.exists_grpObj_of_image) | (intros; apply GlobalTheory.AV.AbVar.exists_grpObj_of_image  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricallyIntegralImageOfHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricallyIntegralImageOfHom
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem geometricallyReduced_of_schDominant_comp {K : Type} [Field K] {X Y : Scheme.{0}} (p : X ⟶ Y)
    (f : Y ⟶ Spec (.of K)) [IsSchemeTheoreticallyDominant p] [QuasiCompact p]
    [h : GeometricallyReduced (p ≫ f)] : GeometricallyReduced f := by
  refine ⟨fun L _ y W a b hW => ?_⟩
  have hy : Flat y := by
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.Flat.of_isField (Field.toIsField K) _)
  have : Flat a := MorphismProperty.of_isPullback hW.flip hy
  have : IsReduced (pullback p a) :=
    h.geometrically_isReduced y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd p a)

theorem geometricallyIrreducible_of_surjective_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (f : Y ⟶ Z) [Surjective p]
    [h : GeometricallyIrreducible (p ≫ f)] : GeometricallyIrreducible f := by
  refine ⟨fun L _ y W a b hW => ?_⟩
  have : IrreducibleSpace ↥(Limits.pullback p a) :=
    h.geometrically_irreducibleSpace y _ _ ((IsPullback.of_hasPullback p a).paste_vert hW)
  exact Function.Surjective.irreducibleSpace (pullback.snd p a).continuous (pullback.snd p a).surjective

theorem exists_image_geometricallyIntegral :
    ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X),
      p ≫ i = f.hom ∧ Surjective p.left ∧ IsClosedImmersion i.left ∧ GeometricallyIntegral Z.hom := by
  intro K _ A B f
  have hA := A.ab
  have hB := B.ab
  have : Smooth A.X.hom := hA.smooth
  have : IsProper A.X.hom := hA.proper
  have : GeometricallyConnected A.X.hom := hA.geomConnected
  have : IsProper B.X.hom := hB.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : IsProper f.hom.left := IsProper.of_comp f.hom.left B.X.hom
  have : IsSchemeTheoreticallyDominant f.hom.left.toImage := GlobalTheory.isSchemeTheoreticallyDominant_toImage _
  have hsurj : Surjective f.hom.left.toImage := ⟨by
    have h2 : IsClosed (Set.range f.hom.left.toImage) := f.hom.left.toImage.isClosedMap.isClosed_range
    rw [← Set.range_eq_univ, ← h2.closure_eq]
    exact f.hom.left.toImage.denseRange.closure_range⟩
  have hwi : f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom) = A.X.hom := by
    rw [Scheme.Hom.toImage_imageι_assoc, hw]
  have : GeometricallyIntegral A.X.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have : GeometricallyIntegral (f.hom.left.toImage ≫ (f.hom.left.imageι ≫ B.X.hom)) := by
    rw [hwi]; infer_instance
  have := geometricallyReduced_of_schDominant_comp f.hom.left.toImage (f.hom.left.imageι ≫ B.X.hom)
  have := geometricallyIrreducible_of_surjective_comp f.hom.left.toImage (f.hom.left.imageι ≫ B.X.hom)
  refine ⟨Over.mk (f.hom.left.imageι ≫ B.X.hom), Over.homMk f.hom.left.toImage hwi,
    Over.homMk f.hom.left.imageι rfl, ?_, hsurj, ?_, ?_⟩
  · ext1
    simp
  · exact inferInstanceAs (IsClosedImmersion f.hom.left.imageι)
  · show GeometricallyIntegral (f.hom.left.imageι ≫ B.X.hom)
    exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricallyIntegralImageOfHomStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_geometricallyIntegral_image_of_hom : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (Z : Over (Sp K)) (p : A.X ⟶ Z) (i : Z ⟶ B.X), p ≫ i = f.hom ∧ Surjective p.left ∧ IsClosedImmersion i.left ∧ GeometricallyIntegral Z.hom := by
  first | (exact @GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral) | (exact GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral) | (intros; apply GlobalTheory.AV.AbVar.exists_image_geometricallyIntegral  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjSmoothOfGeometricallyReduced
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem grpObj_smooth_of_geometricallyReduced : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G], LocallyOfFiniteType G.hom → GeometricallyReduced G.hom → Smooth G.hom := by
  intro K _ G _ h1 h2
  letI : GrpObj (Over.mk G.hom) := ‹GrpObj G›
  exact smooth_of_grpObj (f := G.hom)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvariety
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_factor_abelianSubvariety : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B),
    ∃ (C : AbVar K) (p : A ⟶ C) (i : C ⟶ B), Surjective p.hom.left ∧ IsClosedImmersion i.hom.left ∧ p ≫ i = f := by
  intro K _ A B f
  obtain ⟨Z, p, i, hpi, hp, hi, hg⟩ := GlobalTheory.T.exists_geometricallyIntegral_image_of_hom K A B f
  obtain ⟨hG, hpm, him⟩ := GlobalTheory.T.exists_subgroupScheme_of_geometricallyIntegral_image K A B f Z p i hpi hp hi hg
  letI := hG
  have hmono : Mono i := by
    have : Mono i.left := inferInstance
    exact Over.mono_of_mono_left i
  have hcomm : IsCommMonObj Z := ⟨by
    apply (cancel_mono i).1
    rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc,
      IsCommMonObj.mul_comm]⟩
  have hw : i.left ≫ B.X.hom = Z.hom := Over.w i
  have hB := B.ab
  have : Smooth B.X.hom := hB.smooth
  have : IsProper B.X.hom := hB.proper
  have hlft : LocallyOfFiniteType Z.hom := by rw [← hw]; infer_instance
  have hpr : IsProper Z.hom := by rw [← hw]; infer_instance
  have hsm : Smooth Z.hom := GlobalTheory.grpObj_smooth_of_geometricallyReduced K Z hlft inferInstance
  have hgc : GeometricallyConnected Z.hom := ⟨fun L _ y W fst snd h => by
    have : IsIntegral W := hg.geometrically_isIntegral y fst snd h
    infer_instance⟩
  have hab : IsAbelianScheme Z := ⟨hcomm, hsm, hpr, hgc⟩
  obtain ⟨g, hd⟩ := GlobalTheory.T.abelianScheme_field_smoothOfRelativeDimension_exists K Z hab
  let C : AbVar K := { X := Z, ab := hab, dim := g, smooth := hd }
  refine ⟨C, Hom.mk (B := C) p, Hom.mk (A := C) i, hp, hi, ?_⟩
  exact Subtype.ext hpi

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorisationThroughAbelianSubvarietyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factorisation_through_abelianSubvariety : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), ∃ (C : AbVar K) (p : A ⟶ C) (i : C ⟶ B), Surjective p.hom.left ∧ IsClosedImmersion i.hom.left ∧ p ≫ i = f := by
  first | exact @GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety | exact GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety | (intros; apply GlobalTheory.AV.AbVar.exists_factor_abelianSubvariety <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDualNumberPointInverseConstantTangent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDualNumberPointInverseConstantTangent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanAdd

theorem tanVal_const_point {S : Type} [CommRing S] {A : Over (Sp S)} (c : epsR S ⟶ A) (p : Sp S ⟶ A.left)
    (hc : c.left = spMap (algebraMap S (DualNumber S)) ≫ p) (f : Form (A.hom ≫ 𝟙 _)) :
    tanVal c f = 0 := by
  have e : GlobalTheory.GrpTangent.epsScale (0 : S) ≫ c = c := by
    refine Over.OverMorphism.ext ?_
    have h := Over.w (GlobalTheory.GrpTangent.epsScale (0 : S))
    rw [Over.comp_left, hc, ← Category.assoc]
    exact congrArg (· ≫ p) h
  rw [← e, tanVal_epsScale, zero_mul]

theorem isTangent_iff_reduction_eq_one {S : Type} [CommRing S] {A : Over (Sp S)} [GrpObj A] (z : epsR S ⟶ A) :
    IsTangent z ↔ spOver (TrivSqZeroExt.fstHom S S S) ≫ z = 1 := by
  have h1 : (1 : Over.mk (spMap (algebraMap S S)) ⟶ A).left = η[A].left := by
    rw [Hom.one_def, Over.comp_left]
    have : (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap S S)))).left = 𝟙 (Sp S) := by
      have h := Over.w (CartesianMonoidalCategory.toUnit (Over.mk (spMap (algebraMap S S))))
      refine (Category.comp_id _).symm.trans (h.trans ?_)
      exact Spec.map_id _
    rw [this]
    exact Category.id_comp _
  constructor
  · intro h
    exact Over.OverMorphism.ext (h.trans h1.symm)
  · intro h
    exact (congrArg Over.Hom.left h).trans h1

theorem translate_const (hC : CrystallineSmoothLift) (hH : AbelianHodgeDeRham) (S : Type) [CommRing S]
    (A : Over (Sp S)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (c : epsR S ⟶ A) (p : Sp S ⟶ A.left)
    (hc : c.left = spMap (algebraMap S (DualNumber S)) ≫ p) (y : epsR S ⟶ A) :
    (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left =
      spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧
      ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  refine ⟨?_, fun f ↦ ?_⟩
  · rw [isTangent_iff_reduction_eq_one, MonObj.comp_mul, GrpObj.comp_inv, mul_inv_eq_one]
    exact ⟨fun h ↦ Over.OverMorphism.ext h, fun h ↦ congrArg Over.Hom.left h⟩
  · have h := tanVal_mul_all hC hH S A g hA hg f (y * c⁻¹) c
    rw [inv_mul_cancel_right, tanVal_const_point c p hc f, add_zero] at h
    exact h

end GlobalTheory.TanAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateDualNumberPointInverseConstantTangentStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_dual_number_point_inverse_constant_tangent : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (S : Type) [CommRing S] (A : Over (Sp S)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (c : epsR S ⟶ A) (p : Sp S ⟶ A.left), c.left = spMap (algebraMap S (DualNumber S)) ≫ p → ∀ y : epsR S ⟶ A, (spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ y.left = spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ c.left ↔ IsTangent (y * c⁻¹)) ∧ ∀ f, tanVal y f = tanVal (y * c⁻¹) f := by
  first | exact @GlobalTheory.TanAdd.translate_const | exact GlobalTheory.TanAdd.translate_const | (intros; apply GlobalTheory.TanAdd.translate_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrBoxOfIsSumDeg
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

variable {R : Type} [CommRing R] [IsDomain R] {D D₁ D₂ : DegPre R} (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A)
  [IsMonHom p₁] [IsMonHom p₂] (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left))

theorem isBoxGen_cub (hw : w.IsGen) :
    IsBoxGen w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D.P.isAb _) (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2)
  have he : e.left ≫ (snd D.P.A (D.P.A ⊗ D.P.A)).left ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (ε := thε)
    (fun a => (CubeMap.ofHom p₁).psum_comm a.down) (fun a => (CubeMap.ofHom p₂).psum_comm a.down)
    D.cub.isGen D₁.cub.isGen D₂.cub.isGen _ e.left he sj fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have C : IsCub (cubV D.cub s I) := isCub_cubV D.cub hI
  have C₁ : IsCub (cubV D₁.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₁) := isCub_cubV D₁.cub hI₁
  have C₂ : IsCub (cubV D₂.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I₂) := isCub_cubV D₂.cub hI₂
  have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1 1 (om w s I₁ I₂ I)
  rw [_root_.mul_one, _root_.mul_one] at p
  have o₁ : e.left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₁.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₁ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have o₂ : e.left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D₂.P.A) (lift 1 1)).left := by
    refine (groupObj_lift3_comp_tensorCube_monHom p₂ 1 1 1).trans ?_
    rw [MonObj.one_comp]
  have v₁ := (congrArg (fun m => val D₁.cub.t m s I₁) o₁).trans (C₁.face 1 1)
  have v₂ := (congrArg (fun m => val D₂.cub.t m s I₂) o₂).trans (C₂.face 1 1)
  exact (congrArg₂ (· * ·) p (C.face 1 1)).trans (Eq.trans (by simp) (congrArg₂ (· * ·) v₁ v₂).symm)

theorem isBoxGen_sym (hw : w.IsGen) : IsBoxGen w p₁.left p₂.left D.sym D₁.sym D₂.sym := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (inv_comp p₁) (inv_comp p₂)
    D.sym_gen D₁.sym_gen D₂.sym_gen D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2
    fun s I₁ I₂ I hI₁ hI₂ hI => ?_
  have q := prod_sym (eSec D.P.A) (om w s I₁ I₂ I)
  have o : eSec D.P.A ≫ (ι[D.P.A]).left = eSec D.P.A :=
    congrArg (fun m => m.left) (GrpObj.one_inv : η[D.P.A] ≫ ι[D.P.A] = η[D.P.A])
  rw [o, mul_inv_cancel] at q
  rw [eSec_comp, eSec_comp, val_sym_zero D₁ hI₁, val_sym_zero D₂ hI₂]
  exact congrArg₂ (· * ·) q (val_sym_zero D hI)

theorem exists_strBox_of_isSumDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∃ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), StrBox p₁ p₂ w D.rig D₁.rig D₂.rig D.cub.t D₁.cub.t D₂.cub.t D.sym D₁.sym D₂.sym ∧ ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ h
  have := h.hom₁
  have := h.hom₂
  obtain ⟨w, hw, hr, hψ⟩ := h.w
  exact ⟨w, ⟨hw, isBoxGen_of_mapsAt w _ _ hr, isBoxGen_cub p₁ p₂ w hw, isBoxGen_sym p₁ p₂ w hw⟩,
    fun x => isBoxGen_of_mapsAt w _ _ (hψ x)⟩

end GlobalTheory.ProdUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFormsFunctionalAbelianBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFormsFunctionalAbelianBaseChange
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.BaseChangeForm

theorem existsUnique_of_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {G G' : Type} {F F' : Type 1} [AddCommGroup G] [Module R G] [AddCommGroup G'] [Module R' G']
    [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R' F']
    (c : F →ₗ[R] G) (hc : Function.Surjective c) (c' : F' →ₗ[R'] G')
    (p : F →ₛₗ[algebraMap R R'] F') (e : R' ⊗[R] G ≃ₗ[R'] G') (hp : ∀ f, c' (p f) = e (1 ⊗ₜ c f))
    (l : G →ₗ[R] R') :
    ∃! ψ : F' →ₗ[R'] R', (∀ f, c' f = 0 → ψ f = 0) ∧ ∀ f, ψ (p f) = l (c f) := by
  have key : ∀ x : R' ⊗[R] G, ∃ f' : F', c' f' = e x ∧
      ∀ ψ : F' →ₗ[R'] R', (∀ f, ψ (p f) = l (c f)) → ψ f' = LinearMap.liftBaseChange R' l x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, fun ψ _ ↦ by simp⟩
    | tmul b y =>
      obtain ⟨f, rfl⟩ := hc y
      refine ⟨b • p f, ?_, fun ψ hψ ↦ ?_⟩
      · rw [map_smul, hp, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      · rw [map_smul, hψ, LinearMap.liftBaseChange_tmul]
    | add x y hx hy =>
      obtain ⟨a, ha, ha'⟩ := hx
      obtain ⟨b, hb, hb'⟩ := hy
      exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb],
        fun ψ hψ ↦ by rw [map_add (f := _), map_add (f := _), ha' ψ hψ, hb' ψ hψ]⟩
  refine ⟨LinearMap.liftBaseChange R' l ∘ₗ e.symm.toLinearMap ∘ₗ c', ⟨fun f hf ↦ ?_, fun f ↦ ?_⟩,
    fun ψ hψ ↦ LinearMap.ext fun f ↦ ?_⟩
  · simp [hf]
  · simp [hp]
  · obtain ⟨f', h1, h2⟩ := key (e.symm (c' f))
    have h3 : ψ (f - f') = 0 := hψ.1 _ (by rw [map_sub, h1, LinearEquiv.apply_symm_apply, sub_self])
    rw [map_sub, sub_eq_zero] at h3
    rw [h3, h2 ψ hψ.2]
    rfl


set_option maxHeartbeats 1600000 in
theorem existsUnique_functional : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := by
  intro hC hH R _ A _ g hab hdim R' _ _ A' φ hφ m l
  obtain ⟨e, he⟩ : ∃ e : R' ⊗[R] GlobForm (A.hom ≫ 𝟙 (Sp R)) ≃ₗ[R'] GlobForm (A'.hom ≫ 𝟙 (Sp R')),
      ∀ c, IsPullForm m.w c (e (1 ⊗ₜ c)) :=
    ((hH R A g hab hdim).2.2.2.2.2 R' A'.left A'.hom φ hφ).2.1
  have hp : ∀ f, GlobalTheory.LieDual.glob _ (m.pullForm f) = e (1 ⊗ₜ GlobalTheory.LieDual.glob _ f) := fun f ↦
    (GlobalTheory.T.affinePairRestriction_injective_firstCohomology φ (A'.hom ≫ 𝟙 (Sp R'))).2.1 ((GlobalTheory.LieDual.isPullForm_glob m f).symm.trans (he _))
  obtain ⟨ψ, hψ, hu⟩ := existsUnique_of_baseChange (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)))
    (GlobalTheory.LieDual.glob_surjective hC hH A g hab hdim) (GlobalTheory.LieDual.glob (A'.hom ≫ 𝟙 (Sp R')))
    m.pullForm e hp l
  exact ⟨ψ, ⟨fun f hf ↦ hψ.1 f (congrArg Subtype.val hf), hψ.2⟩,
    fun χ hχ ↦ hu χ ⟨fun f hf ↦ hχ.1 f (Subtype.ext hf), hχ.2⟩⟩

end GlobalTheory.BaseChangeForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFormsFunctionalAbelianBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
open MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_forms_functional_abelian_base_change : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] (A' : Over (Sp R')) (φ : A'.left ⟶ A.left), IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) → ∀ (m : IsMor (dp0 R) (A.hom ≫ 𝟙 (Sp R)) (dp0 R') (A'.hom ≫ 𝟙 (Sp R')) (algebraMap R R') φ) (l : GlobForm (A.hom ≫ 𝟙 (Sp R)) →ₗ[R] R'), ∃! ψ : Form (A'.hom ≫ 𝟙 (Sp R')) →ₗ[R'] R', (∀ f, cmpForm (A'.hom ≫ 𝟙 (Sp R')) f = 0 → ψ f = 0) ∧ ∀ f, ψ (m.pullForm f) = l (GlobalTheory.LieDual.glob (A.hom ≫ 𝟙 (Sp R)) f) := by
  first | exact @GlobalTheory.BaseChangeForm.existsUnique_functional | exact GlobalTheory.BaseChangeForm.existsUnique_functional | (intros; apply GlobalTheory.BaseChangeForm.existsUnique_functional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TMulOfBox
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.SumDeg

theorem tMul_of_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), IsBoxGen (φ := thφ D.P.A (x3 D.P.A)) (φ₁ := thφ D₁.P.A (x3 D₁.P.A)) (φ₂ := thφ D₂.P.A (x3 D₂.P.A)) (ε := thε) w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.cub.t D₁.cub.t D₂.cub.t → ∀ (T T₁ T₂ : Over (Sp R)) (P : T ⟶ D.P.A) (P₁ : T₁ ⟶ D₁.P.A) (P₂ : T₂ ⟶ D₂.P.A) (ρ₁ : T ⟶ T₁) (ρ₂ : T ⟶ T₂), P ≫ p₁ = ρ₁ ≫ P₁ → P ≫ p₂ = ρ₂ ≫ P₂ → ∀ (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : ∀ χ : D₁.X, LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ χ) Oinvε)) (t₂ : ∀ χ : D₂.X, LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ χ) Oinvε)), (∀ x, IsBoxGen w ρ₁.left ρ₂.left (t x) (t₁ (q₁ x)) (t₂ (q₂ x))) → TMul D₁ P₁ t₁ → TMul D₂ P₂ t₂ → TMul D P t := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hc T T₁ T₂ P P₁ P₂ ρ₁ ρ₂ e₁ e₂ t t₁ t₂ hb h₁ h₂ χ χ'
  haveI := hS.hom₁
  haveI := hS.hom₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have B : ∀ x, (om w y J₁ J₂ J (P * cP D T x).left)⁻¹ * om w y J₁ J₂ J (cP D T x).left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹ * val (t x) (𝟙 T.left) y J =
      val (t₁ (q₁ x)) ρ₁.left y J₁ * val (t₂ (q₂ x)) ρ₂.left y J₂ := fun x => by
    have := hb x T.left (𝟙 T.left) y J₁ J₂ J hJ₁ hJ₂ hJ
    simp only [Category.id_comp] at this
    rwa [GlobalTheory.TorusCoordPull.prod_O D P x (om w y J₁ J₂ J)] at this
  have K₁ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left =
      ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₁, cPoint_pr hS.c_pr₁, e₁, ← comp_cP D₁ ρ₁ (q₁ χ), ← comp_cP D₁ ρ₁ (q₁ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have K₂ : (lift (cP D T χ) (lift (cP D T χ') P)).left ≫ (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left =
      ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left := by
    rw [groupObj_lift3_comp_tensorCube_monHom, cPoint_pr hS.c_pr₂, cPoint_pr hS.c_pr₂, e₂, ← comp_cP D₂ ρ₂ (q₂ χ), ← comp_cP D₂ ρ₂ (q₂ χ'),
      ← comp_lift, ← comp_lift, Over.comp_left]
  have C0 := hc T.left (lift (cP D T χ) (lift (cP D T χ') P)).left y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [K₁, K₂] at C0
  have pc := prod_cub (cP D T χ) (cP D T χ') P (om w y J₁ J₂ J)
  have C : (om w y J₁ J₂ J (cP D T χ * cP D T χ' * P).left * (om w y J₁ J₂ J (cP D T χ * cP D T χ').left)⁻¹ *
      (om w y J₁ J₂ J (cP D T χ * P).left)⁻¹ * (om w y J₁ J₂ J (cP D T χ' * P).left)⁻¹ *
      om w y J₁ J₂ J (cP D T χ).left * om w y J₁ J₂ J (cP D T χ').left * om w y J₁ J₂ J P.left *
      (om w y J₁ J₂ J (1 : T ⟶ D.P.A).left)⁻¹) * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ := by
    rw [← pc]; exact C0
  have M₁ : val (t₁ (q₁ χ + q₁ χ')) ρ₁.left y J₁ *
      val D₁.cub.t (ρ₁.left ≫ (lift (cP D₁ T₁ (q₁ χ)) (lift (cP D₁ T₁ (q₁ χ')) P₁)).left) y J₁ =
      val (t₁ (q₁ χ)) ρ₁.left y J₁ * val (t₁ (q₁ χ')) ρ₁.left y J₁ := by
    have := (val_mul hJ₁ _ _ _).symm.trans ((val_corr hJ₁ (h₁ (q₁ χ) (q₁ χ')) ρ₁.left).trans (val_mul hJ₁ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₁ _ _ _).symm
  have M₂ : val (t₂ (q₂ χ + q₂ χ')) ρ₂.left y J₂ *
      val D₂.cub.t (ρ₂.left ≫ (lift (cP D₂ T₂ (q₂ χ)) (lift (cP D₂ T₂ (q₂ χ')) P₂)).left) y J₂ =
      val (t₂ (q₂ χ)) ρ₂.left y J₂ * val (t₂ (q₂ χ')) ρ₂.left y J₂ := by
    have := (val_mul hJ₂ _ _ _).symm.trans ((val_corr hJ₂ (h₂ (q₂ χ) (q₂ χ')) ρ₂.left).trans (val_mul hJ₂ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_pull hJ₂ _ _ _).symm
  have B0 := B (χ + χ')
  have Ba := B χ
  have Bb := B χ'
  rw [map_add (f := _), map_add (f := _), cPoint_add,
    show P * (cP D T χ * cP D T χ') = cP D T χ * cP D T χ' * P from mul_comm _ _] at B0
  rw [show P * cP D T χ = cP D T χ * P from mul_comm _ _] at Ba
  rw [show P * cP D T χ' = cP D T χ' * P from mul_comm _ _] at Bb
  refine ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ((val_pull hJ _ _ _).trans
    (congrArg (fun r => val D.cub.t r y J) (Category.id_comp _))))).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  show val (t (χ + χ')) (𝟙 T.left) y J * val D.cub.t (lift (cP D T χ) (lift (cP D T χ') P)).left y J =
    val (t χ) (𝟙 T.left) y J * val (t χ') (𝟙 T.left) y J
  apply Additive.ofMul.injective
  have a0 := congrArg Additive.ofMul B0
  have a1 := congrArg Additive.ofMul Ba
  have a2 := congrArg Additive.ofMul Bb
  have a3 := congrArg Additive.ofMul C
  have a4 := congrArg Additive.ofMul M₁
  have a5 := congrArg Additive.ofMul M₂
  simp only [ofMul_mul, ofMul_inv] at a0 a1 a2 a3 a4 a5 ⊢
  linear_combination (norm := abel) a0 + a3 - a1 - a2 + a4 + a5

end GlobalTheory.ProdUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmCharHom
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnifWeight

open ReciprocityTheory.ChartRestriction.G.DVR

section Char

variable {S : Scheme.{0}} {X X₁ X₂ : Type} [AddCommGroup X] [AddCommGroup X₁] [AddCommGroup X₂]

theorem gm_char_hom {j : X₁ → X} {τ : splitTorus S X ⟶ splitTorus S X₁} (hτ : TorusHomOf j τ) {T : Over S}
    (r : T ⟶ splitTorus S X) (y : T.left) (x : X₁) :
    gm (r ≫ τ).left y ⊤ (charUnit S X₁ x) = gm r.left y ⊤ (charUnit S X (j x)) := by
  rw [← hτ x]
  exact ((gm_res r.left y (V := ⊤) _ trivial _).trans (gm_pull r.left τ.left y ⊤ trivial _)).symm

theorem gm_char_add {T : Over S} (r : T ⟶ splitTorus S X) (y : T.left) (a b : X) :
    gm r.left y ⊤ (charUnit S X (a + b)) = gm r.left y ⊤ (charUnit S X a) * gm r.left y ⊤ (charUnit S X b) := by
  rw [PowTorusCoord.gm_char, PowTorusCoord.gm_char, PowTorusCoord.gm_char, ofAdd_add, map_mul, map_mul]

end Char

theorem val_weight {R : Type} [CommRing R] [IsDomain R] {D₁ : DegPre R} {S : Scheme.{0}} {s : S ⟶ Sp R}
    {X : Type} [AddCommGroup X] {G G₁ : Over S} [GrpObj G] [GrpObj G₁] (σ : G ⟶ G₁) [IsMonHom σ]
    {P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A} {x : D₁.X} (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ x) Oinvε))
    (κ : splitTorus S X ⟶ G) (κ₁ : splitTorus S D₁.X ⟶ G₁) (τ : splitTorus S X ⟶ splitTorus S D₁.X)
    (hκ : κ ≫ σ = τ ≫ κ₁)
    (hw : LB.Gen.Corr D₁.P.L _ _ _ _
      (LB.pullGen D₁.P.L _ _ t₁ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]).left)
      (LB.mulGen D₁.P.L _ _ _ _ (charGen D₁.X G₁ D₁.P.L x)
        (LB.pullGen D₁.P.L _ _ t₁ (snd (splitTorus S D₁.X) G₁).left)))
    (y : (splitTorus S X ⊗ G).left) {J} (hJ : Good D₁.P.L y J) :
    val (Y := G₁.left) t₁ ((lift (fst (splitTorus S X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ σ).left y J =
      gm (fst (splitTorus S X) G ≫ τ).left y ⊤ (charUnit _ D₁.X x) *
        val (Y := G₁.left) t₁ (snd (splitTorus S X) G ≫ σ).left y J := by
  let N : splitTorus S X ⊗ G ⟶ splitTorus S D₁.X ⊗ G₁ := τ ⊗ₘ σ
  have n₁ : N ≫ fst _ _ = fst _ _ ≫ τ := tensorHom_fst _ _
  have n₂ : N ≫ snd _ _ = snd _ _ ≫ σ := tensorHom_snd _ _
  have n₃ : N ≫ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]) =
      (lift (fst (splitTorus S X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ σ := by
    rw [← Hom.mul_def, ← Hom.mul_def, MonObj.comp_mul, MonObj.mul_comp, ← Category.assoc, n₁, n₂, Category.assoc,
      Category.assoc, hκ]
  rw [← n₁, ← n₂, ← n₃]
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ hw N.left).trans ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (TorusCoordPull.val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))))

theorem weight_box₂ : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (S : Scheme.{0}) (s : S ⟶ Sp R) (G G₁ G₂ : Over S) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (σ₁ : G ⟶ G₁) (σ₂ : G ⟶ G₂) (P : (Over.map s).obj G ⟶ D.P.A) (P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A) (P₂ : (Over.map s).obj G₂ ⟶ D₂.P.A) (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ (q₁ χ)) Oinvε)) (t₂ : LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ (q₂ χ)) Oinvε)), IsMonHom σ₁ → IsMonHom σ₂ → IsBoxGen (Y := G.left) (Y₁ := G₁.left) (Y₂ := G₂.left) w σ₁.left σ₂.left t t₁ t₂ → ∀ (κ : splitTorus S D.X ⟶ G) (κ₁ : splitTorus S D₁.X ⟶ G₁) (κ₂ : splitTorus S D₂.X ⟶ G₂) (j₁ : D₁.X → D.X) (j₂ : D₂.X → D.X) (τ₁ : splitTorus S D.X ⟶ splitTorus S D₁.X) (τ₂ : splitTorus S D.X ⟶ splitTorus S D₂.X), j₁ (q₁ χ) + j₂ (q₂ χ) = χ → TorusHomOf j₁ τ₁ → TorusHomOf j₂ τ₂ → κ ≫ σ₁ = τ₁ ≫ κ₁ → κ ≫ σ₂ = τ₂ ≫ κ₂ → (Over.map s).map (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]) ≫ P = (Over.map s).map (snd (splitTorus S D.X) G) ≫ P → LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ t₁ (lift (fst (splitTorus S D₁.X) G₁ ≫ κ₁) (snd _ _) ≫ μ[G₁]).left) (LB.mulGen D₁.P.L _ _ _ _ (charGen D₁.X G₁ D₁.P.L (q₁ χ)) (LB.pullGen D₁.P.L _ _ t₁ (snd (splitTorus S D₁.X) G₁).left)) → LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ t₂ (lift (fst (splitTorus S D₂.X) G₂ ≫ κ₂) (snd _ _) ≫ μ[G₂]).left) (LB.mulGen D₂.P.L _ _ _ _ (charGen D₂.X G₂ D₂.P.L (q₂ χ)) (LB.pullGen D₂.P.L _ _ t₂ (snd (splitTorus S D₂.X) G₂).left)) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left) (LB.mulGen D.P.L _ _ _ _ (charGen D.X G D.P.L χ) (LB.pullGen D.P.L _ _ t (snd (splitTorus S D.X) G).left)) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ w S s G G₁ G₂ _ _ _ σ₁ σ₂ P P₁ P₂ χ t t₁ t₂ hσ₁ hσ₂ H κ κ₁ κ₂ j₁ j₂ τ₁ τ₂ hχ
    hτ₁ hτ₂ hκ₁ hκ₂ aO hw₁ hw₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have v₁ := val_weight σ₁ t₁ κ κ₁ τ₁ hκ₁ hw₁ y hJ₁
  have v₂ := val_weight σ₂ t₂ κ κ₂ τ₂ hκ₂ hw₂ y hJ₂
  rw [gm_char_hom hτ₁] at v₁
  rw [gm_char_hom hτ₂] at v₂
  have c := gm_char_add (fst (splitTorus S D.X) G) y (j₁ (q₁ χ)) (j₂ (q₂ χ))
  rw [hχ] at c
  have b₁ := H _ (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left y J₁ J₂ J hJ₁ hJ₂ hJ
  have b₂ := H _ (snd (splitTorus S D.X) G).left y J₁ J₂ J hJ₁ hJ₂ hJ
  have e : ∀ a, (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left ≫ D.Oφ P χ a =
      (snd (splitTorus S D.X) G).left ≫ D.Oφ P χ a := fun a =>
    (WeightPf.Oφ_comp ((Over.map s).map (lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G])) P χ a).trans
      ((congrArg (fun m => D.Oφ m χ a) aO).trans
        (WeightPf.Oφ_comp ((Over.map s).map (snd (splitTorus S D.X) G)) P χ a).symm)
  have o : (∏ a, om w y J₁ J₂ J ((lift (fst (splitTorus S D.X) G ≫ κ) (snd _ _) ≫ μ[G]).left ≫ D.Oφ P χ a) ^ Oinvε a) =
      ∏ a, om w y J₁ J₂ J ((snd (splitTorus S D.X) G).left ≫ D.Oφ P χ a) ^ Oinvε a :=
    Finset.prod_congr rfl fun a _ => congrArg (fun m => om w y J₁ J₂ J m ^ Oinvε a) (e a)
  have v₄ := (congrArg₂ (· * ·) o rfl).symm.trans (b₁.trans ((congrArg₂ (· * ·) v₁ v₂).trans
    ((_root_.mul_mul_mul_comm _ _ _ _).trans ((congrArg₂ (· * ·) c.symm b₂.symm).trans (mul_left_comm _ _ _)))))
  have v₅ := mul_left_cancel v₄
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) (TorusCoordPull.val_charGen _ _ _ _ _ _ _) (val_pull hJ _ _ _))).symm)
  rw [Category.id_comp, Category.id_comp, Category.id_comp]
  exact v₅

end GlobalTheory.ProdUnifWeight
end
end
