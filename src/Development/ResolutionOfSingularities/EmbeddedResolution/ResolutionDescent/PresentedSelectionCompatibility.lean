module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.LastCoordinateSlices
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedSelection

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SmoothLocalChart
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure SmoothLocalChart {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
    {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y pY) (H : EmbeddingDatum k V pV) (u : V ⟶ Y) (y : ↥V) where
  func : Γ(H.ambient, ⊤)
  mem_domain : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  isAffine_ambient : AlgebraicGeometry.IsAffine ambient
  smooth_ambientStruct : AlgebraicGeometry.Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : AlgebraicGeometry.LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : AlgebraicGeometry.QuasiCompact ambientStruct
  toAmbient : ambient ⟶ G.ambient
  smooth_toAmbient : AlgebraicGeometry.Smooth toAmbient
  comp_eq : toAmbient ≫ G.ambientStruct = ambientStruct
  imm : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ⟶ ambient
  isClosedImmersion_imm : AlgebraicGeometry.IsClosedImmersion imm
  isPullback :
    CategoryTheory.IsPullback imm ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u) toAmbient
      G.emb

namespace SmoothLocalChart

variable {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
  {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
  {G : EmbeddingDatum k Y pY} {H : EmbeddingDatum k V pV} {u : V ⟶ Y} {y : ↥V}

abbrev chartDomain (C : SmoothLocalChart G H u y) : V.Opens :=
  H.emb ⁻¹ᵁ H.ambient.basicOpen C.func

instance instSmoothToAmbient (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.Smooth C.toAmbient := C.smooth_toAmbient

theorem isAffineOpen_chartDomain [AlgebraicGeometry.IsAffine V]
    (C : SmoothLocalChart G H u y) :
    AlgebraicGeometry.IsAffineOpen C.chartDomain := by
  show AlgebraicGeometry.IsAffineOpen (H.emb ⁻¹ᵁ H.ambient.basicOpen C.func)
  have h : (H.emb ⁻¹ᵁ H.ambient.basicOpen C.func) = V.basicOpen (H.emb.app ⊤ C.func) :=
    Scheme.preimage_basicOpen H.emb C.func
  rw [h]
  exact (isAffineOpen_top V).basicOpen _

theorem isPullback_morphismRestrict_basicOpen (C : SmoothLocalChart G H u y) :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict H.emb (H.ambient.basicOpen C.func))
      C.chartDomain.ι (H.ambient.basicOpen C.func).ι H.emb :=
  AlgebraicGeometry.isPullback_morphismRestrict H.emb (H.ambient.basicOpen C.func)

end SmoothLocalChart

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EtaleCoverClosedEmbedding
section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PresentedLocalChart
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure PresentedLocalChart {k : Type u} [Field k] [CharZero k] {Y V : Scheme.{u}}
    {pY : Y ⟶ Spec (CommRingCat.of k)} {pV : V ⟶ Spec (CommRingCat.of k)}
    {G : EmbeddingDatum k Y pY} (P : ClosedEmbeddingIntoAffineSpace G) (H : EmbeddingDatum k V pV)
    (u : V ⟶ Y) (r : ℕ) (y : ↥V) extends SmoothLocalChart G H u y where
  threshold : ℕ
  presentation : ∀ N : ℕ, threshold ≤ N →
    ∃ σ : ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N + 1))),
      AlgebraicGeometry.IsClosedImmersion σ ∧
      σ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1))) = ambientStruct ∧
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))) σ
        (P.codimBound + (N - r) + 1)
  le_threshold : r ≤ threshold

theorem nonempty_presentedLocalChart (hS : SmoothPullbackHasLocalAmbientEmbedding.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G) (H : EmbeddingDatum k V pV)
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) (y : ↥V) :
    Nonempty (PresentedLocalChart P H u r y) := by
  classical
  obtain ⟨V₀, hyV₀, hV₀aff, A', pA', hA'aff, hA'sm, hA'ft, hA'qc, gg, hgsm, hgp, jj, hjci,
      hjpb, N₀, hrN₀, hpres⟩ :=
    hS k Y V G.ambient pY pV G.ambientStruct G.emb G.comp_eq P.dim P.codimBound P.toAffine
      P.toAffine_comp P.locallyConstCodim r u hu y
  have := hA'aff
  have := hA'sm
  have := hA'ft
  have := hA'qc
  have := hgsm
  have := hjci
  obtain ⟨σ₀, hσ₀ci, hσ₀comp, hσ₀codim⟩ := hpres N₀ le_rfl
  have := hσ₀ci
  have hembCI : AlgebraicGeometry.IsClosedImmersion H.emb := H.isClosedImmersion_emb
  have hind := H.emb.isClosedEmbedding.toIsEmbedding.toIsInducing
  obtain ⟨Ω, hΩ, hΩeq⟩ := hind.isOpen_iff.mp V₀.isOpen
  have hyΩ : H.emb.base y ∈ Ω := by
    have h0 : y ∈ ⇑H.emb.base ⁻¹' Ω := by rw [hΩeq]; exact hyV₀
    exact h0
  obtain ⟨Ubase, hUmem, hyU, hUΩ⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (isBasis_basicOpen H.ambient)
      (U := (⟨Ω, hΩ⟩ : H.ambient.Opens)) (x := H.emb.base y) hyΩ
  obtain ⟨func, rfl⟩ := hUmem
  have hymem : y ∈ (H.emb ⁻¹ᵁ H.ambient.basicOpen func) := hyU
  have hsub : (H.emb ⁻¹ᵁ H.ambient.basicOpen func) ≤ V₀ := by
    intro x hx
    have hx1 : H.emb.base x ∈ H.ambient.basicOpen func := hx
    have hx2 : x ∈ ⇑H.emb.base ⁻¹' Ω := hUΩ hx1
    rw [hΩeq] at hx2
    exact hx2
  obtain ⟨L, hL⟩ : ∃ L : Γ(affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀))), ⊤),
      (ConcreteCategory.hom (Scheme.Hom.appTop (jj ≫ σ₀))) L
        = (ConcreteCategory.hom (Scheme.Hom.appTop (V₀.ι ≫ H.emb))) func :=
    ⟨_, appTop_globalSectionLift k (P.dim + N₀) (jj ≫ σ₀) _⟩
  obtain ⟨Fsec, hopen⟩ : ∃ Fsec : Γ(A', ⊤),
      jj ⁻¹ᵁ (A'.basicOpen Fsec) = V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func) := by
    refine ⟨(ConcreteCategory.hom (Scheme.Hom.appTop σ₀)) L, ?_⟩
    have eA : A'.basicOpen ((ConcreteCategory.hom (Scheme.Hom.appTop σ₀)) L)
        = σ₀ ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L) :=
      (Scheme.preimage_basicOpen σ₀ L).symm
    have e1 : jj ⁻¹ᵁ
          (σ₀ ⁻¹ᵁ ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L))
        = (jj ≫ σ₀) ⁻¹ᵁ
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L) := rfl
    have eB : (jj ≫ σ₀) ⁻¹ᵁ
          ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N₀)))).basicOpen L)
        = (↑V₀ : Scheme.{u}).basicOpen
            ((ConcreteCategory.hom (Scheme.Hom.appTop (jj ≫ σ₀))) L) :=
      Scheme.preimage_basicOpen _ _
    have e2 : V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)
        = (V₀.ι ≫ H.emb) ⁻¹ᵁ (H.ambient.basicOpen func) := rfl
    have eC : (V₀.ι ≫ H.emb) ⁻¹ᵁ (H.ambient.basicOpen func)
        = (↑V₀ : Scheme.{u}).basicOpen
            ((ConcreteCategory.hom (Scheme.Hom.appTop (V₀.ι ≫ H.emb))) func) :=
      Scheme.preimage_basicOpen _ _
    rw [eA, e1, eB, hL, e2, eC]
  obtain ⟨θ, hθ⟩ : ∃ θ : (H.emb ⁻¹ᵁ H.ambient.basicOpen func).toScheme ≅
      (jj ⁻¹ᵁ A'.basicOpen Fsec).toScheme,
      θ.hom ≫ ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι)
        = (H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι := by
    have hrange : Set.range ⇑(H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι.base
        = Set.range ⇑((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι).base := by
      have hcomp : Set.range ⇑((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ V₀.ι).base
          = ⇑V₀.ι.base '' Set.range ⇑(jj ⁻¹ᵁ A'.basicOpen Fsec).ι.base := by
        simp [Set.range_comp]
      rw [hcomp, hopen, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      have h4 : (↑(V₀.ι ⁻¹ᵁ (H.emb ⁻¹ᵁ H.ambient.basicOpen func)) : Set ↥V₀.toScheme)
          = ⇑V₀.ι.base ⁻¹' (↑(H.emb ⁻¹ᵁ H.ambient.basicOpen func) : Set ↥V) := rfl
      rw [h4, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
      exact (Set.inter_eq_self_of_subset_left (fun x hx => hsub hx)).symm
    exact ⟨AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq _ _ hrange,
      AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange⟩
  have hθ' : (θ.hom ≫ (jj ⁻¹ᵁ A'.basicOpen Fsec).ι) ≫ V₀.ι
      = (H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι := by
    rw [Category.assoc]; exact hθ
  have hpb1 : CategoryTheory.IsPullback
      (AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec))
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) ((A'.basicOpen Fsec).ι ≫ gg) G.emb :=
    (AlgebraicGeometry.isPullback_morphismRestrict jj (A'.basicOpen Fsec)).paste_vert hjpb
  have hcomm : CategoryTheory.CommSq θ.hom
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) (𝟙 Y) := by
    constructor
    rw [Category.comp_id, ← Category.assoc, ← Category.assoc, hθ']
  have hiso : CategoryTheory.IsPullback θ.hom
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((jj ⁻¹ᵁ A'.basicOpen Fsec).ι ≫ (V₀.ι ≫ u)) (𝟙 Y) :=
    CategoryTheory.IsPullback.of_horiz_isIso hcomm
  have hpb : CategoryTheory.IsPullback
      (θ.hom ≫ AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec))
      ((H.emb ⁻¹ᵁ H.ambient.basicOpen func).ι ≫ u)
      ((A'.basicOpen Fsec).ι ≫ gg) G.emb := by
    have h5 := hiso.paste_horiz hpb1
    rwa [Category.id_comp] at h5
  have hambaff : AlgebraicGeometry.IsAffine (A'.basicOpen Fsec).toScheme :=
    (AlgebraicGeometry.isAffineOpen_top A').basicOpen Fsec
  refine ⟨{
    func := func
    mem_domain := hymem
    ambient := (A'.basicOpen Fsec).toScheme
    ambientStruct := (A'.basicOpen Fsec).ι ≫ pA'
    isAffine_ambient := hambaff
    smooth_ambientStruct := by infer_instance
    locallyOfFiniteType_ambientStruct := by infer_instance
    quasiCompact_ambientStruct := by infer_instance
    toAmbient := (A'.basicOpen Fsec).ι ≫ gg
    smooth_toAmbient := by infer_instance
    comp_eq := by rw [Category.assoc, hgp]
    imm := θ.hom ≫ AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec)
    isClosedImmersion_imm := by
      have : AlgebraicGeometry.IsClosedImmersion
          (AlgebraicGeometry.morphismRestrict jj (A'.basicOpen Fsec)) := by infer_instance
      infer_instance
    isPullback := hpb
    threshold := N₀
    le_threshold := hrN₀
    presentation := by
      intro N hN
      obtain ⟨σ, hσci, hσcomp, hσcodim⟩ := hpres N hN
      have := hσci
      refine ⟨basicOpenEmbedding k (P.dim + N) σ Fsec ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} (P.dim + N) 1)
            (Spec (CommRingCat.of k))).hom, by infer_instance, ?_, ?_⟩
      · rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
        exact basicOpenEmbedding_comp_affineSpaceIndexedByToSpec k (P.dim + N) σ Fsec pA' hσcomp
      · exact hasSmoothCoordCodim_basicOpenEmbedding hsm k (P.dim + N)
          (P.codimBound + (N - r)) σ Fsec hσcodim }⟩

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem isZariskiLocalAtSource_locallyOfFiniteType :
    IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) := by
  have hrh : HasRingHomProperty (@LocallyOfFiniteType.{u}) RingHom.FiniteType := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) _ hrh

private theorem isZariskiLocalAtSource_flat :
    IsZariskiLocalAtSource (@Flat.{u}) := by
  have hrh : HasRingHomProperty (@Flat.{u}) RingHom.Flat := inferInstance
  exact @HasRingHomProperty.instIsZariskiLocalAtSource (@Flat.{u}) _ hrh

private theorem locallyOfFiniteType_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, LocallyOfFiniteType (f i)) :
    LocallyOfFiniteType (Limits.Sigma.desc f) := by
  have := isZariskiLocalAtSource_locallyOfFiniteType
  exact IsZariskiLocalAtSource.sigmaDesc hf

private theorem flat_sigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Z : Scheme.{u}}
    (f : ∀ i, X i ⟶ Z) (hf : ∀ i, Flat (f i)) : Flat (Limits.Sigma.desc f) := by
  have := isZariskiLocalAtSource_flat
  exact IsZariskiLocalAtSource.sigmaDesc hf

private theorem exists_etaleCover_closedEmbeddingIntoAffineSpace_of_localCharts (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k]
    (hsnc : ∀ (A : Scheme.{u}) (q : A ⟶ Spec (CommRingCat.of k)),
      AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q [])
    (Y V : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G)
    (H : EmbeddingDatum k V pV) (Q : ClosedEmbeddingIntoAffineSpace H)
    (u : V ⟶ Y) (r : ℕ) (hu : u ≫ pY = pV)
    (ι : Type u) [Fintype ι] [DecidableEq ι] (pt : ι → ↥V)
    (ch : ∀ i, PresentedLocalChart P H u r (pt i))
    (N : ℕ) (hN : ∀ i, (ch i).threshold ≤ N)
    (hcov : (⨆ i, (ch i).chartDomain) = ⊤) :
    ∃ (V'' : Scheme.{u}) (pV'' : V'' ⟶ Spec (CommRingCat.of k)) (c : V'' ⟶ V),
      AlgebraicGeometry.IsAffine V'' ∧ AlgebraicGeometry.IsReduced V'' ∧
      AlgebraicGeometry.LocallyOfFiniteType pV'' ∧ AlgebraicGeometry.QuasiCompact pV'' ∧
      AlgebraicGeometry.Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ pV = pV'' ∧
      (∃ (G' : EmbeddingDatum k V'' pV'') (f : G'.ambient ⟶ G.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace G') ∧
        AlgebraicGeometry.Smooth f ∧ f ≫ G.ambientStruct = G'.ambientStruct ∧
        CategoryTheory.IsPullback G'.emb (c ≫ u) f G.emb) ∧
      (∃ (H' : EmbeddingDatum k V'' pV'') (g : H'.ambient ⟶ H.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace H') ∧
        AlgebraicGeometry.Smooth g ∧ g ≫ H.ambientStruct = H'.ambientStruct ∧
        CategoryTheory.IsPullback H'.emb c g H.emb) := by
  classical
  have hsubs : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstance
  have hDaff : ∀ i, IsAffine (((ch i).chartDomain).toScheme) := fun i =>
    (ch i).isAffineOpen_chartDomain
  have hambaff : ∀ i, IsAffine ((ch i).ambient) := fun i => (ch i).isAffine_ambient
  have hBaff : ∀ i, IsAffine ((H.ambient.basicOpen ((ch i).func)).toScheme) := fun i =>
    (isAffineOpen_top H.ambient).basicOpen ((ch i).func)
  have hVaff : IsAffine (sigmaOpens V fun i => (ch i).chartDomain) :=
    isAffine_sigmaOpens V _ fun i => (ch i).isAffineOpen_chartDomain
  have hVcs : CompactSpace ↥(sigmaOpens V fun i => (ch i).chartDomain) := inferInstance
  obtain ⟨e, he⟩ : ∃ e : ι → k, Function.Injective e := by
    refine ⟨fun i => ((Fintype.equivFin ι i : ℕ) : k), fun a b hab => ?_⟩
    have h2 : (Fintype.equivFin ι a : ℕ) = (Fintype.equivFin ι b : ℕ) := Nat.cast_injective hab
    exact (Fintype.equivFin ι).injective (Fin.eq_of_val_eq h2)
  refine ⟨sigmaOpens V (fun i => (ch i).chartDomain),
    (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV,
    sigmaOpensDesc V (fun i => (ch i).chartDomain),
    hVaff, inferInstance, inferInstance,
    quasiCompact_of_compactSpace_of_subsingleton .., inferInstance,
    surjective_sigmaOpensDesc V _ hcov, rfl, ?_, ?_⟩
  · have hpullbackG : IsPullback (Limits.Sigma.map fun i => (ch i).imm)
        ((sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ u)
        (Limits.Sigma.desc fun i => (ch i).toAmbient) G.emb := by
      have h0 : IsPullback (Limits.Sigma.map fun i => (ch i).imm)
          (Limits.Sigma.desc fun i => ((ch i).chartDomain).ι ≫ u)
          (Limits.Sigma.desc fun i => (ch i).toAmbient) G.emb :=
        isPullback_sigmaMap_sigmaDesc G.emb (fun i => (ch i).ambient)
          (fun i => ((ch i).chartDomain).toScheme) (fun i => (ch i).imm)
          (fun i => ((ch i).chartDomain).ι ≫ u) (fun i => (ch i).toAmbient)
          (fun i => (ch i).isPullback)
      have hdescu : (Limits.Sigma.desc fun i => ((ch i).chartDomain).ι ≫ u)
          = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ u := by
        refine Limits.Sigma.hom_ext _ _ fun i => ?_
        simp
      rwa [hdescu] at h0
    have hsmfG : Smooth (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      smooth_sigmaDesc _ fun i => (ch i).smooth_toAmbient
    have hstructeq : (Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct
        = Limits.Sigma.desc fun i => (ch i).ambientStruct := by
      refine Limits.Sigma.hom_ext _ _ fun i => ?_
      simp [(ch i).comp_eq]
    have hsmstructG :
        Smooth ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) := by
      rw [hstructeq]
      exact smooth_sigmaDesc _ fun i => (ch i).smooth_ambientStruct
    have hlftstructG :
        LocallyOfFiniteType ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) := by
      rw [hstructeq]
      exact locallyOfFiniteType_sigmaDesc _ fun i => (ch i).locallyOfFiniteType_ambientStruct
    have hGaff : IsAffine (∐ fun i => (ch i).ambient) := inferInstance
    have hGcs : CompactSpace ↥(∐ fun i => (ch i).ambient) := inferInstance
    have hqcstructG :
        QuasiCompact ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct) :=
      quasiCompact_of_compactSpace_of_subsingleton ..
    have hCIembG : IsClosedImmersion (Limits.Sigma.map fun i => (ch i).imm) :=
      MorphismProperty.of_isPullback (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
        hpullbackG.flip G.isClosedImmersion_emb
    have hqcGemb : QuasiCompact G.emb := inferInstance
    have hqcembG : QuasiCompact (Limits.Sigma.map fun i => (ch i).imm) :=
      quasiCompact_of_isPullback hpullbackG.flip
    have hflatfG : Flat (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      flat_sigmaDesc _ fun i => inferInstance
    have hkerG : (Limits.Sigma.map fun i => (ch i).imm).ker
        = G.emb.ker.comap (Limits.Sigma.desc fun i => (ch i).toAmbient) :=
      ker_eq_comap_ker_of_isPullback_of_flat hpullbackG.flip
    have hnzG : NonzeroOnComponents (Limits.Sigma.map fun i => (ch i).imm).ker := by
      rw [hkerG]
      exact NonzeroOnComponents.comap_of_flat G.nonzeroOnComponents_ker _
    have hcompG : (Limits.Sigma.map fun i => (ch i).imm) ≫
        ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct)
        = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV := by
      rw [← Category.assoc, hpullbackG.w, Category.assoc, G.comp_eq, Category.assoc, hu]
    refine ⟨embeddingDatumOfClosedImmersion (∐ fun i => (ch i).ambient)
        ((Limits.Sigma.desc fun i => (ch i).toAmbient) ≫ G.ambientStruct)
        (Limits.Sigma.map fun i => (ch i).imm) hnzG hcompG (hsnc _ _ hsmstructG),
      Limits.Sigma.desc fun i => (ch i).toAmbient, ⟨?_⟩, hsmfG, rfl, hpullbackG⟩
    have hpres : ∀ i, ∃ σ : (ch i).ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (P.dim + N + 1))),
        IsClosedImmersion σ ∧
        σ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1))) = (ch i).ambientStruct ∧
        HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))) σ
          (P.codimBound + (N - r) + 1) := fun i => (ch i).presentation N (hN i)
    choose σ hσCI hσcomp hσcod using hpres
    have hσCI' : ∀ i, IsClosedImmersion (σ i) := hσCI
    have hCIunionG :
        IsClosedImmersion (coproductSliceMap k (P.dim + N + 1) e (fun i => (ch i).ambient) σ) :=
      isClosedImmersion_coproductSliceMap k (P.dim + N + 1) e he (fun i => (ch i).ambient) σ
    have hCIfinG :
        IsClosedImmersion (coproductSliceMapReindexed k (P.dim + N + 1) e (fun i => (ch i).ambient) σ) :=
      inferInstance
    refine ⟨P.codimBound + (N - r) + 1 + 1, P.dim + N + 1 + 1,
      coproductSliceMapReindexed k (P.dim + N + 1) e (fun i => (ch i).ambient) σ, by omega, by omega,
      hCIfinG, ?_, ?_⟩
    · refine coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec k (P.dim + N + 1) e (fun i => (ch i).ambient) σ _ ?_
      intro i
      show Limits.Sigma.ι (fun j => (ch j).ambient) i ≫
          ((Limits.Sigma.desc fun j => (ch j).toAmbient) ≫ G.ambientStruct) =
          σ i ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (P.dim + N + 1)))
      simp [(ch i).comp_eq, hσcomp i]
    · exact hasSmoothCoordCodim_coproductSliceMapReindexed hsm k (P.dim + N + 1)
        (P.codimBound + (N - r) + 1) e he (fun i => (ch i).ambient) σ hσcod
  · have hpullbackH : IsPullback
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func)))
        (sigmaOpensDesc V fun i => (ch i).chartDomain)
        (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) H.emb :=
      isPullback_sigmaMap_sigmaDesc H.emb
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => ((ch i).chartDomain).toScheme)
        (fun i => H.emb ∣_ H.ambient.basicOpen ((ch i).func))
        (fun i => ((ch i).chartDomain).ι)
        (fun i => (H.ambient.basicOpen ((ch i).func)).ι)
        (fun i => (ch i).isPullback_morphismRestrict_basicOpen)
    have hsmg : Smooth (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      smooth_sigmaDesc _ fun i => inferInstance
    have hlftg : LocallyOfFiniteType
        (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      inferInstance
    have hflatg : Flat (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      flat_sigmaDesc _ fun i => inferInstance
    have hHaff : IsAffine (sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      isAffine_sigmaOpens H.ambient _ fun i =>
        (isAffineOpen_top H.ambient).basicOpen ((ch i).func)
    have hHcs :
        CompactSpace ↥(sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      inferInstance
    have hsmq : Smooth
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := inferInstance
    have hlftq : LocallyOfFiniteType
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := inferInstance
    have hqcq : QuasiCompact
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
          H.ambientStruct) := quasiCompact_of_compactSpace_of_subsingleton ..
    have hCIembH : IsClosedImmersion
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) :=
      MorphismProperty.of_isPullback (P := (@IsClosedImmersion : MorphismProperty Scheme.{u}))
        hpullbackH.flip H.isClosedImmersion_emb
    have hqcHemb : QuasiCompact H.emb := inferInstance
    have hqcembH : QuasiCompact
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) :=
      quasiCompact_of_isPullback hpullbackH.flip
    have hkerH :
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))).ker
          = H.emb.ker.comap
            (sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) :=
      ker_eq_comap_ker_of_isPullback_of_flat hpullbackH.flip
    have hnzH : NonzeroOnComponents
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))).ker := by
      rw [hkerH]
      exact NonzeroOnComponents.comap_of_flat H.nonzeroOnComponents_ker _
    have hcompH :
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func))) ≫
          ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫
            H.ambientStruct)
          = (sigmaOpensDesc V fun i => (ch i).chartDomain) ≫ pV := by
      rw [← Category.assoc, hpullbackH.w, Category.assoc, H.comp_eq]
    refine ⟨embeddingDatumOfClosedImmersion
        (sigmaOpens H.ambient fun i => H.ambient.basicOpen ((ch i).func))
        ((sigmaOpensDesc H.ambient fun i => H.ambient.basicOpen ((ch i).func)) ≫ H.ambientStruct)
        (Limits.Sigma.map fun i => (H.emb ∣_ H.ambient.basicOpen ((ch i).func)))
        hnzH hcompH (hsnc _ _ hsmq),
      sigmaOpensDesc H.ambient (fun i => H.ambient.basicOpen ((ch i).func)), ⟨?_⟩, hsmg, rfl,
      hpullbackH⟩
    have hCIrho : ∀ i, IsClosedImmersion
        (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) :=
      fun i => inferInstance
    have hrhocomp : ∀ i,
        (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) ≫
            affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1)))
          = (H.ambient.basicOpen ((ch i).func)).ι ≫ H.ambientStruct := by
      intro i
      rw [Category.assoc, affineSpaceIsoOfEquiv_hom_comp_toSpec]
      exact basicOpenEmbedding_comp_affineSpaceIndexedByToSpec k Q.dim Q.toAffine ((ch i).func) H.ambientStruct
        Q.toAffine_comp
    have hrhocod : ∀ i,
        HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1))))
          (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
          (Q.codimBound + 1) :=
      fun i => hasSmoothCoordCodim_basicOpenEmbedding hsm k Q.dim Q.codimBound Q.toAffine
        ((ch i).func) Q.locallyConstCodim
    have hCIunionH : IsClosedImmersion
        (coproductSliceMap k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
          (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)) :=
      isClosedImmersion_coproductSliceMap k (Q.dim + 1) e he
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
    have hCIfinH : IsClosedImmersion
        (coproductSliceMapReindexed k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
          (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)) :=
      inferInstance
    refine ⟨Q.codimBound + 1 + 1, Q.dim + 1 + 1,
      coproductSliceMapReindexed k (Q.dim + 1) e (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom),
      by omega, by omega, hCIfinH, ?_, ?_⟩
    · refine coproductSliceMapReindexed_comp_affineSpaceIndexedByToSpec k (Q.dim + 1) e
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) _ ?_
      intro i
      show Limits.Sigma.ι (fun j => (H.ambient.basicOpen ((ch j).func)).toScheme) i ≫
          ((sigmaOpensDesc H.ambient fun j => H.ambient.basicOpen ((ch j).func)) ≫
            H.ambientStruct) =
          (basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
            (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom) ≫
            affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (Q.dim + 1)))
      rw [hrhocomp i]
      simp
    · exact hasSmoothCoordCodim_coproductSliceMapReindexed hsm k (Q.dim + 1) (Q.codimBound + 1) e he
        (fun i => (H.ambient.basicOpen ((ch i).func)).toScheme)
        (fun i => basicOpenEmbedding k Q.dim Q.toAffine ((ch i).func) ≫
          (affineSpaceIsoOfEquiv (uliftFinSumEquiv.{u} Q.dim 1) (Spec (CommRingCat.of k))).hom)
        hrhocod

theorem exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k]
    (hsnc : ∀ (A : Scheme.{u}) (q : A ⟶ Spec (CommRingCat.of k)),
      AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q [])
    (Y V : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k))
    (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (G : EmbeddingDatum k Y pY) (P : ClosedEmbeddingIntoAffineSpace G)
    (H : EmbeddingDatum k V pV) (Q : ClosedEmbeddingIntoAffineSpace H)
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    ∃ (V'' : Scheme.{u}) (pV'' : V'' ⟶ Spec (CommRingCat.of k)) (c : V'' ⟶ V),
      AlgebraicGeometry.IsAffine V'' ∧ AlgebraicGeometry.IsReduced V'' ∧
      AlgebraicGeometry.LocallyOfFiniteType pV'' ∧ AlgebraicGeometry.QuasiCompact pV'' ∧
      AlgebraicGeometry.Etale c ∧ AlgebraicGeometry.Surjective c ∧ c ≫ pV = pV'' ∧
      (∃ (G' : EmbeddingDatum k V'' pV'') (f : G'.ambient ⟶ G.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace G') ∧
        AlgebraicGeometry.Smooth f ∧ f ≫ G.ambientStruct = G'.ambientStruct ∧
        CategoryTheory.IsPullback G'.emb (c ≫ u) f G.emb) ∧
      (∃ (H' : EmbeddingDatum k V'' pV'') (g : H'.ambient ⟶ H.ambient),
        Nonempty (ClosedEmbeddingIntoAffineSpace H') ∧
        AlgebraicGeometry.Smooth g ∧ g ≫ H.ambientStruct = H'.ambientStruct ∧
        CategoryTheory.IsPullback H'.emb c g H.emb) := by
  classical
  have hVcs : CompactSpace ↥V := inferInstance
  have hch : ∀ y : ↥V, Nonempty (PresentedLocalChart P H u r y) := fun y =>
    nonempty_presentedLocalChart hS hsm k Y V pY pV G P H u r hu y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun y : ↥V => ((((hch y).some.chartDomain) : V.Opens) : Set ↥V))
    (fun y => ((hch y).some.chartDomain).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, (hch x).some.mem_domain⟩)
  have hfin : Fintype { y : ↥V // y ∈ t } := FinsetCoe.fintype t
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : { y : ↥V // y ∈ t }, ((hch i.1).some).threshold ≤ N :=
    ⟨Finset.univ.sup fun i : { y : ↥V // y ∈ t } => ((hch i.1).some).threshold,
      fun i => Finset.le_sup
        (f := fun i : { y : ↥V // y ∈ t } => ((hch i.1).some).threshold) (Finset.mem_univ i)⟩
  refine exists_etaleCover_closedEmbeddingIntoAffineSpace_of_localCharts hsm k hsnc Y V pY pV G P H Q u r hu
    { y : ↥V // y ∈ t } (fun i => i.1) (fun i => (hch i.1).some) N hN ?_
  refine TopologicalSpace.Opens.ext ?_
  rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
  refine Set.eq_univ_of_univ_subset fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxy⟩

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isPullbackBlowupSequence_presentedSelection_of_smooth (E : EmbeddedResolutionRule.{u}) (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q [])
    (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsAffine V]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsReduced V]
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    (u : V ⟶ Y) (r : ℕ) [AlgebraicGeometry.SmoothOfRelativeDimension r u]
    (hu : u ≫ pY = pV) :
    IsPullbackBlowupSequence u (E k V pV (C.sel k V pV)) (E k Y pY (C.sel k Y pY)) := by
  obtain ⟨V'', pV'', c, hV''aff, hV''red, hV''ft, hV''qc, hcet, hcsurj, hcpV,
      ⟨G', f, hG'pres, hfsm, hfcomp, hfpb⟩, ⟨H', g, hH'pres, hgsm, hgcomp, hgpb⟩⟩ :=
    exists_etaleCover_closedEmbeddingIntoAffineSpace_of_smooth hS hsm k (fun A q hq => hsnc k A q hq)
      Y V pY pV (C.sel k Y pY) (C.pres k Y pY) (C.sel k V pV) (C.pres k V pV) u r hu
  have := hV''aff
  have := hV''red
  have := hV''ft
  have := hV''qc
  have := hcet
  have := hcsurj
  have := hfsm
  have := hgsm
  have : AlgebraicGeometry.Smooth u := AlgebraicGeometry.SmoothOfRelativeDimension.smooth r u
  have : AlgebraicGeometry.Flat u := inferInstance
  have : AlgebraicGeometry.Flat c := inferInstance
  have s1 : IsPullbackBlowupSequence (c ≫ u) (E k V'' pV'' G') (E k Y pY (C.sel k Y pY)) :=
    hsbc k Y V'' pY pV'' (C.sel k Y pY) G' f (c ≫ u) hfcomp hfpb
  have s2 : IsPullbackBlowupSequence c (E k V'' pV'' H') (E k V pV (C.sel k V pV)) :=
    hsbc k V V'' pV pV'' (C.sel k V pV) H' g c hgcomp hgpb
  have heq : (E k V'' pV'' G').Isomorphic (E k V'' pV'' H') :=
    hinv k V'' pV'' G' H' hG'pres.some hH'pres.some
  have s2' : IsStrictPullbackBlowupSeq c (E k V'' pV'' H') (E k V pV (C.sel k V pV)) :=
    s2.isStrictPullback_of_surjective
      (fun i hi => hprop k V pV (C.sel k V pV) i hi)
  have hBu : IsStrictPullbackBlowupSeq u ((E k Y pY (C.sel k Y pY)).baseChange u)
      (E k Y pY (C.sel k Y pY)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (E k Y pY (C.sel k Y pY)) u
  have hB' : IsPullbackBlowupSequence u ((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups
      (E k Y pY (C.sel k Y pY)) := hBu.isPullbackSequenceOfBlowups_withoutIsoBlowups
  have hCc : IsStrictPullbackBlowupSeq c
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c)
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) c
  have hC : IsPullbackBlowupSequence (c ≫ u)
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c)
      (E k Y pY (C.sel k Y pY)) := hB'.comp_isStrictPullbackSequenceOfBlowups hCc
  have heq2 : (E k V'' pV'' G').Isomorphic
      ((((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups).baseChange c) := s1.isomorphic hC
  have hdesc : (E k V pV (C.sel k V pV)).Isomorphic
      (((E k Y pY (C.sel k Y pY)).baseChange u).withoutIsoBlowups) :=
    IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic s2' hCc (heq.symm.trans heq2)
  exact hB'.of_isomorphic hdesc.symm

theorem isCompatibleWithOpenImmersions_toAffineResolutionRule (E : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithOpenImmersions (E.toAffineResolutionRule C.sel) := by
  intro k _ _ Y V pY pV _ _ _ _ _ _ _ _ φ _ hφ
  have : AlgebraicGeometry.SmoothOfRelativeDimension 0 φ := inferInstance
  exact isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y V pY pV
    φ 0 hφ

theorem isCompatibleWithEtaleCovers_toAffineResolutionRule (E : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u})
    (hinv : E.IsIndependentOfPresentedEmbedding) (hsbc : E.IsCompatibleWithSmoothAmbientMaps)
    (hprop : E.HasProperCenters)
    (hS : SmoothPullbackHasLocalAmbientEmbedding.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithEtaleCovers (E.toAffineResolutionRule C.sel) := by
  intro k _ _ Y W pY pW _ _ _ _ _ _ _ _ φ _ hφ hsurj
  have : AlgebraicGeometry.SmoothOfRelativeDimension 0 φ := inferInstance
  have : AlgebraicGeometry.Surjective φ := ⟨hsurj⟩
  have hpb : IsPullbackBlowupSequence φ (E k W pW (C.sel k W pW)) (E k Y pY (C.sel k Y pY)) :=
    isPullbackBlowupSequence_presentedSelection_of_smooth E C hinv hsbc hprop hS hsm hsnc k Y W pY pW
      φ 0 hφ
  exact hpb.isStrictPullback_of_surjective
    (fun i hi => hprop k Y pY (C.sel k Y pY) i hi)

end FunctorialResolution.EmbeddedResolution

end
