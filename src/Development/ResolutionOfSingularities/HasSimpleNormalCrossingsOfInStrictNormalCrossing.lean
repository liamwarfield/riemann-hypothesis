module

public import Development.ResolutionOfSingularities.Statements
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsClopen
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothStrictTransformComponents
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.PrincipalizationWithRadicalCenters
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SingularPreimageBoundary
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GlobalResolutionFromAffine

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.HironakaTheorem
section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineCentersOverSingularLocus
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem smooth_opens_ι {X : Scheme.{u}} (U : X.Opens) :
    AlgebraicGeometry.Smooth U.ι := by
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  exact (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso _) :
    (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth)

private theorem smooth_ι_comp_of_le_smoothLocus {X Z : Scheme.{u}} (f : X ⟶ Z)
    [AlgebraicGeometry.LocallyOfFinitePresentation f] (U : X.Opens)
    (hU : U ≤ AlgebraicGeometry.Scheme.Hom.smoothLocus f) :
    AlgebraicGeometry.Smooth (U.ι ≫ f) := by
  rw [← AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff]
  refine le_antisymm le_top ?_
  intro x _
  have hx : (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.stalkMap f (U.ι x))).FormallySmooth := hU x.2
  have hg : (CommRingCat.Hom.hom
      (AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth :=
    RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have heq : (CommRingCat.Hom.hom
        (AlgebraicGeometry.Scheme.Hom.stalkMap (U.ι ≫ f) x)).FormallySmooth =
      (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap f (U.ι x) ≫
        AlgebraicGeometry.Scheme.Hom.stalkMap U.ι x)).FormallySmooth :=
    congrArg (fun φ => (CommRingCat.Hom.hom φ).FormallySmooth)
      (AlgebraicGeometry.Scheme.Hom.stalkMap_comp U.ι f x)
  exact Eq.mpr heq (RingHom.FormallySmooth.comp hx hg)

private theorem mem_smoothLocusComplement_iff {X Z : Scheme.{u}} (f : X ⟶ Z)
    [AlgebraicGeometry.LocallyOfFinitePresentation f] (x : ↥X) :
    x ∈ (↑(smoothLocusComplement f) : Set ↥X) ↔
      x ∉ (↑(AlgebraicGeometry.Scheme.Hom.smoothLocus f) : Set ↥X) :=
  Iff.rfl

private theorem ker_morphismRestrict {X W : Scheme.{u}} (f : X ⟶ W)
    [AlgebraicGeometry.IsClosedImmersion f] (V : W.Opens) :
    AlgebraicGeometry.Scheme.Hom.ker (f ∣_ V) =
      (AlgebraicGeometry.Scheme.Hom.ker f).comap V.ι :=
  OpenImmersionRestriction.ker_eq_comap_ker_of_isPullback_isOpenImmersion f V.ι (f ∣_ V) ((f ⁻¹ᵁ V).ι)
    (AlgebraicGeometry.isPullback_morphismRestrict f V).flip

private theorem inducedBlowupsWithoutIso_eq_withoutIsoBlowups {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY)
    (h : S.TransitionsAreBlowups) : S.inducedBlowupsWithoutIso h = (S.inducedBlowups h).withoutIsoBlowups := rfl

private noncomputable def restrictEmbeddingDatumBasicOpen {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u}) (r : Γ(D.ambient, ⊤)) :
    EmbeddingDatum k (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) where
  ambient := (D.ambient.basicOpen r).toScheme
  ambientStruct := (D.ambient.basicOpen r).ι ≫ D.ambientStruct
  emb := D.emb ∣_ D.ambient.basicOpen r
  isAffine_ambient := (AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r
  smooth_ambientStruct := by
    have := D.smooth_ambientStruct
    have := smooth_opens_ι (D.ambient.basicOpen r)
    infer_instance
  locallyOfFiniteType_ambientStruct := inferInstance
  quasiCompact_ambientStruct := by
    have : AlgebraicGeometry.IsAffine (D.ambient.basicOpen r).toScheme :=
      (AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r
    exact inferInstance
  isClosedImmersion_emb := inferInstance
  nonzeroOnComponents_ker := by
    rw [ker_morphismRestrict]
    exact D.nonzeroOnComponents_ker.comap_of_isOpenImmersion _
  comp_eq := by
    rw [← Category.assoc, AlgebraicGeometry.morphismRestrict_ι, Category.assoc, D.comp_eq]
  sncEmpty := by
    have := D.smooth_ambientStruct
    have := smooth_opens_ι (D.ambient.basicOpen r)
    exact hsnc k _ _ inferInstance

private theorem isPullbackSeq_of_smooth
    (A : PrincipalizationAlgorithm.{u}) (hA : IsFunctorialPrincipalization A) (hw : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y Y' : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (p' : Y' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] [AlgebraicGeometry.QuasiCompact p]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType p'] [AlgebraicGeometry.QuasiCompact p']
    [AlgebraicGeometry.IsReduced Y'] [AlgebraicGeometry.IsAffine Y']
    (D : EmbeddingDatum k Y p) (D' : EmbeddingDatum k Y' p')
    (φ : D'.ambient ⟶ D.ambient) (hsmφ : AlgebraicGeometry.Smooth φ) (ψ : Y' ⟶ Y)
    (hφ : φ ≫ D.ambientStruct = D'.ambientStruct)
    (hsq : IsPullback D'.emb ψ φ D.emb) :
    IsPullbackBlowupSequence ψ (embeddedResolutionRuleOfPrincipalization A hw k Y' p' D')
      (embeddedResolutionRuleOfPrincipalization A hw k Y p D) := by
  have := hsmφ
  exact embeddedResolutionRule_isPullbackBlowupSequence_of_smooth A hA hw k Y Y' p p' D D' φ ψ hφ hsq

private theorem centersLieOver_of_withoutIsoBlowups {X : Scheme.{u}} (s : SequenceOfBlowups X) (Z : Set ↥X)
    (h : s.withoutIsoBlowups.CentersLieOver Z) : s.CentersLieOver Z := by
  intro i hi x hx
  have hne : s.center i ≠ ⊤ := by
    intro h0
    have h1 : (s.center i).support = ⊥ :=
      (AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff _).mpr h0
    have h2 : x ∈ ((⊥ : TopologicalSpace.Closeds ↥(s.schemeAt i)) : Set ↥(s.schemeAt i)) := by
      rw [← h1]; exact hx
    exact h2
  obtain ⟨j, hj, hji⟩ := s.exists_nontrivialIndex_eq_of_center_ne_top hi hne
  subst hji
  have h1 := h j (by rw [SequenceOfBlowups.withoutIsoBlowups_length]; exact hj) x
    (by rw [SequenceOfBlowups.withoutIsoBlowups_center]; exact hx)
  rwa [SequenceOfBlowups.withoutIsoBlowups_projectionToBase] at h1

private theorem blowupSequence_centersLieOver_congr {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] {S T : EmbeddedBlowupSequence k Y pY} (e : S = T)
    (hS : S.TransitionsAreBlowups) (hT : T.TransitionsAreBlowups) (Z : Set ↥Y)
    (h : (S.inducedBlowups hS).CentersLieOver Z) : (T.inducedBlowups hT).CentersLieOver Z := by
  subst e
  exact h

private theorem quasiCompact_of_embeddingDatum {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY) :
    AlgebraicGeometry.QuasiCompact pY := by
  rw [← D.comp_eq]
  infer_instance

theorem centerOffDetached_eq_top_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).centerOffDetached t = ⊤ := by
  have : AlgebraicGeometry.QuasiCompact pY := quasiCompact_of_embeddingDatum D
  have hiso := OpenImmersionRestriction.detachedLocusIsOpen_toEmbeddedBlowupSequence OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment hres hB hrad
    (OpenImmersionRestriction.chartIsolationHypotheses_reducedVanishingAssignment (canonicalPrincipalization hres hrad)) k Y pY D
  have hnoe : NoetherianSpace
      ↥((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).strictTransform t) :=
    EmbeddedBlowupSequence.noetherianSpace_strictTransform_of_isNoetherian _
      (EmbeddedBlowupSequence.isNoetherian_schemeAt (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad))) t
      (le_of_lt ht)
  have hopen : IsOpen ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t) :=
    hiso t ht
  apply (Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).mpr
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  have h1 := EmbeddedBlowupSequence.support_centerOffDetached_subset_preimage
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t hy
  have h2 : y ∈ (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).detachedLocus t :=
    OpenImmersionRestriction.mem_detachedLocus_of_mem_support_ambientCenter hres hB hrad D hsm t ht y h1
  have h3 := EmbeddedBlowupSequence.support_centerOffDetached_subset_detachedClosureCompl
    (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)) t hnoe hopen hy
  rw [EmbeddedBlowupSequence.detachedClosureCompl_coe, EmbeddedBlowupSequence.detachedClosure_coe] at h3
  exact h3 h2

theorem toEmbeddedBlowupSequence_center_eq_top_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) (t : ℕ)
    (ht : t < (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).length) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).center t = ⊤ := by
  rw [EmbeddedBlowupSequence.inducedBlowups_center, EmbeddedBlowupSequence.totalCenter_eq,
    centerOffDetached_eq_top_of_smooth hres hB hrad D hsm t ht]
  exact AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty ..

private theorem withoutIsoBlowups_length_eq_zero_of_smooth
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (D : EmbeddingDatum k Y pY)
    (hsm : AlgebraicGeometry.Smooth pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).lengthWithoutIsoBlowups = 0 := by
  by_contra hne
  have h0 : 0 < ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).lengthWithoutIsoBlowups :=
    Nat.pos_of_ne_zero hne
  have h1 := SequenceOfBlowups.nontrivialIndex_lt_length _ h0
  have h2 := SequenceOfBlowups.center_nontrivialIndex_ne_top _ h0
  rw [EmbeddedBlowupSequence.inducedBlowups_length] at h1
  exact h2 (toEmbeddedBlowupSequence_center_eq_top_of_smooth hres hB hrad D hsm hbl _ h1)

private theorem centersLieOver_embeddedResolutionRuleOfPrincipalization
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hA : IsFunctorialPrincipalization (canonicalPrincipalization hres hrad))
    (hw : TransitionsAreBlowupsForEmbeddings (canonicalPrincipalization hres hrad))
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFinitePresentation pY]
    (D : EmbeddingDatum k Y pY) :
    (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  intro i hi x hx
  by_contra hns
  have hy : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
      (↑(AlgebraicGeometry.Scheme.Hom.smoothLocus pY) : Set ↥Y) := by
    by_contra h
    exact hns ((mem_smoothLocusComplement_iff pY _).mpr h)
  obtain ⟨W, hWopen, hW⟩ :=
    ((AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding D.emb).isInducing).isOpen_iff.mp
      (AlgebraicGeometry.Scheme.Hom.smoothLocus pY).isOpen
  have hWy :
      D.emb
        ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
        ∈ W := by
    have h2 :
        (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
          ⇑D.emb ⁻¹' W := by
      rw [hW]; exact hy
    exact h2
  obtain ⟨U', hU'mem, hxU', hU'le⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_basicOpen D.ambient)
      (show D.emb
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
          ∈ (⟨W, hWopen⟩ : D.ambient.Opens) from hWy)
  obtain ⟨r, hr⟩ := hU'mem
  have hyV : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
      D.emb ⁻¹ᵁ D.ambient.basicOpen r := by
    have h3 :
        D.emb
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x)
          ∈ D.ambient.basicOpen r := by
      rw [hr]; exact hxU'
    exact h3
  have hVle : (D.emb ⁻¹ᵁ D.ambient.basicOpen r) ≤
      AlgebraicGeometry.Scheme.Hom.smoothLocus pY := by
    intro z hz
    have h3 : D.emb z ∈ D.ambient.basicOpen r := hz
    rw [hr] at h3
    have h5 : z ∈ ⇑D.emb ⁻¹' W := hU'le h3
    rw [hW] at h5
    exact h5
  have hVaff : AlgebraicGeometry.IsAffine (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme :=
    ((AlgebraicGeometry.isAffineOpen_top D.ambient).basicOpen r).preimage D.emb
  have hsmV : AlgebraicGeometry.Smooth ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) :=
    smooth_ι_comp_of_le_smoothLocus pY _ hVle
  have hqcV : AlgebraicGeometry.QuasiCompact ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) :=
    inferInstance
  have hlen0 : (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) (restrictEmbeddingDatumBasicOpen D hsnc r)).length = 0 := by
    rw [embeddedResolutionRuleOfPrincipalization_apply, inducedBlowupsWithoutIso_eq_withoutIsoBlowups, SequenceOfBlowups.withoutIsoBlowups_length]
    exact withoutIsoBlowups_length_eq_zero_of_smooth hres hB hrad (restrictEmbeddingDatumBasicOpen D hsnc r) hsmV _
  have hps := isPullbackSeq_of_smooth (canonicalPrincipalization hres hrad) hA hw k Y
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).toScheme pY
      ((D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι ≫ pY) D (restrictEmbeddingDatumBasicOpen D hsnc r)
      (D.ambient.basicOpen r).ι (smooth_opens_ι (D.ambient.basicOpen r))
      (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι rfl
      (AlgebraicGeometry.isPullback_morphismRestrict D.emb (D.ambient.basicOpen r))
  obtain ⟨ρ, e, h1, h2, h3, h4, h5, h6, h7⟩ := hps
  have hmemrange :
      (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i x ∈
        Set.range ⇑(D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact hyV
  obtain ⟨x', hx'eq⟩ := hmemrange
  obtain ⟨z, hz1, hz2⟩ :=
    AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι)
      (g := (embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i)
      x' x hx'eq
  have hex : ∃ w, w ∈
      (((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center i).comap
        (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase
            i))).support := by
    refine ⟨z, ?_⟩
    have hmem : z ∈
        (↑((((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center
          i).comap (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
            ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase
              i))).support) : Set _) := by
      rw [FunctorialResolution.EmbeddedResolution.support_comap]
      show (Limits.pullback.snd (D.emb ⁻¹ᵁ D.ambient.basicOpen r).ι
          ((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).projectionToBase i)) z
          ∈ (↑((embeddedResolutionRuleOfPrincipalization (canonicalPrincipalization hres hrad) hw k Y pY D).center
                i).support : Set _)
      rw [hz2]
      exact hx
    exact hmem
  obtain ⟨j, hj, -⟩ := (h4 i hi).mp hex
  rw [hlen0] at hj
  exact absurd hj (Nat.not_lt_zero j)

theorem toEmbeddedBlowupSequence_centersLieOver_smoothLocusComplement
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hB : (canonicalAlgorithmRules hres).ReducesInductivelyOnDimension)
    (hrad : SmoothSubschemeIdealIsRadical.{u})
    (hA : IsFunctorialPrincipalization (canonicalPrincipalization hres hrad))
    (hw : TransitionsAreBlowupsForEmbeddings (canonicalPrincipalization hres hrad))
    (hsnc : NilIsStrictNormalCrossingsOfSmooth.{u})
    {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.LocallyOfFinitePresentation pY]
    (D : EmbeddingDatum k Y pY)
    (hbl : (D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).TransitionsAreBlowups) :
    ((D.toEmbeddedBlowupSequence (canonicalPrincipalization hres hrad)).inducedBlowups hbl).CentersLieOver
      (↑(smoothLocusComplement pY) : Set ↥Y) := by
  apply centersLieOver_of_withoutIsoBlowups
  have h := centersLieOver_embeddedResolutionRuleOfPrincipalization hres hB hrad hA hw hsnc D
  rw [embeddedResolutionRuleOfPrincipalization_apply] at h
  exact h

theorem affineCentersLieOverSingularLocus_principalizationWithRadicalCenters :
    AffineCentersLieOverSingularLocus.{u} principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters := by
  intro k _ _ Y pY _ _ _ _
  unfold FunctorialResolution.EmbeddedResolution.AffineSpacePrincipalizationData.InducedCentersLieOverSingularLocus
  have hbl0 :
      ((affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
          k Y pY).toEmbeddedBlowupSequence principalizationWithRadicalCenters).TransitionsAreBlowups :=
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters k Y pY _
  have key := toEmbeddedBlowupSequence_centersLieOver_smoothLocusComplement strictTransformIsBlowupOfClosedSubscheme
    canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical
    (isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
      smoothSubschemeIdealIsRadical
      (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect))
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters nilIsStrictNormalCrossingsOfSmooth
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
      k Y pY) hbl0
  rw [← AffineSpacePrincipalizationData.embeddedInducedBlowups_eq]
  exact blowupSequence_centersLieOver_congr
    (affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence principalizationWithRadicalCenters affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth k Y pY) hbl0 _ _ key

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineBoundaryStrictNormalCrossings
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem centersHaveStrictNormalCrossingsWithBoundary {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    S.CentersHaveStrictNormalCrossingsWithBoundary := fun i hi => S.principalizationSequence.center_snc i hi

private theorem smooth_schemeAtToSpec {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    ∀ i, i ≤ S.ambientLength → AlgebraicGeometry.Smooth (S.schemeAtToSpec i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have : AlgebraicGeometry.Smooth S.ambientToSpec := S.ambient_smooth
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_zero]
      infer_instance
  | succ n ih =>
      intro hn
      have hlt : n < S.ambientLength := hn
      have hsm0 : AlgebraicGeometry.Smooth (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) :=
        ih (Nat.le_of_lt hlt)
      have hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := smooth_comp_of_isBlowupAlongIdealSheaf hZE hb
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc]
      exact hres

private theorem boundaryInStrictNormalCrossingPosition {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    S.BoundaryInStrictNormalCrossingPosition := by
  intro i
  induction i with
  | zero =>
      intro _
      have : AlgebraicGeometry.Smooth (S.schemeAtToSpec 0) :=
        smooth_schemeAtToSpec S 0 (Nat.zero_le _)
      have h0 : S.boundary 0 = ([] : List (S.ambientLevel 0).IdealSheafData) := by
        rw [AffineSpacePrincipalizationData.boundary_def, IdealBlowupSequence.boundary_zero]
        rfl
      rw [h0]
      exact inStrictNormalCrossingPosition_nil (S.schemeAtToSpec 0)
  | succ n ih =>
      intro hn
      have hlt : n < S.ambientLength := hn
      have : AlgebraicGeometry.IsNoetherian (S.ambientLevel (n + 1)) :=
        isNoetherian_ambientLevel S (n + 1) hn
      have : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (n + 1)) := inferInstance
      have hE : InStrictNormalCrossingPosition (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec)
          (S.principalizationSequence.boundary n) := ih (Nat.le_of_lt hlt)
      have hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := inStrictNormalCrossingPosition_strictTransform_append
        (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.transitionMapSucc n)
        (S.ambientBlowups.center n) (S.principalizationSequence.boundary n) hb hE hZE
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc,
        AffineSpacePrincipalizationData.boundary_def, S.principalizationSequence.boundary_succ n hlt]
      exact hres

theorem affineCentersHaveStrictNormalCrossingsWithBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact centersHaveStrictNormalCrossingsWithBoundary (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

theorem affineAllLevelsSmooth (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineAllLevelsSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact smooth_schemeAtToSpec (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

theorem affineBoundaryInStrictNormalCrossingPosition (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact boundaryInStrictNormalCrossingPosition (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.ClosedEmbeddingsIntoAffineSpace
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) := by
  simp
  rfl

private theorem appTop_add {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : Γ(Y, ⊤)) :
    f.appTop (a + b) = f.appTop a + f.appTop b :=
  map_add (CommRingCat.Hom.hom f.appTop) a b

private theorem appTop_sub {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : Γ(Y, ⊤)) :
    f.appTop (a - b) = f.appTop a - f.appTop b :=
  map_sub (CommRingCat.Hom.hom f.appTop) a b

private theorem appTop_id_apply {X : Scheme.{u}} (x : Γ(X, ⊤)) :
    (𝟙 X : X ⟶ X).appTop x = x := by
  simp

private theorem exists_iso_affineSpace_sum_comp_eq_of_coord {S : Scheme.{u}} (n m : ℕ)
    {Y : Scheme.{u}}
    (p : Y ⟶ S)
    (e₁ : Y ⟶ AffineSpace (ULift.{u} (Fin n)) S)
    (e₂ : Y ⟶ AffineSpace (ULift.{u} (Fin m)) S)
    (h₁ : e₁ ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = p)
    (h₂ : e₂ ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S) = p)
    (F : Fin m → Γ(AffineSpace (ULift.{u} (Fin n)) S, ⊤))
    (hF : ∀ b : Fin m, e₁.appTop (F b)
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))))
    (G : Fin n → Γ(AffineSpace (ULift.{u} (Fin m)) S, ⊤))
    (hG : ∀ a : Fin n, e₂.appTop (G a)
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
    (L R : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S)
    (hLover : L ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p)
    (hRover : R ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p)
    (hLinl : ∀ a : Fin n, L.appTop (AffineSpace.coord S
        (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
    (hLinr : ∀ b : Fin m, L.appTop (AffineSpace.coord S
        (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = 0)
    (hRinl : ∀ a : Fin n, R.appTop (AffineSpace.coord S
        (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = 0)
    (hRinr : ∀ b : Fin m, R.appTop (AffineSpace.coord S
        (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) :
    ∃ Φ : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ≅ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      Φ.hom ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧ L ≫ Φ.hom = R := by
  obtain ⟨pr₁, hpr₁, hpr₁c⟩ :
      ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin n)) S,
        q ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ a : Fin n, q.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n)))
            = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
        (fun a : ULift.{u} (Fin n) =>
          AffineSpace.coord S (ULift.up (Sum.inl a.down) : ULift.{u} (Fin n ⊕ Fin m))),
      AffineSpace.homOfVector_over _ _, fun a => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  obtain ⟨pr₂, hpr₂, hpr₂c⟩ :
      ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin m)) S,
        q ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ b : Fin m, q.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))
            = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
        (fun b : ULift.{u} (Fin m) =>
          AffineSpace.coord S (ULift.up (Sum.inr b.down) : ULift.{u} (Fin n ⊕ Fin m))),
      AffineSpace.homOfVector_over _ _, fun b => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  have mkHom : ∀ v : ULift.{u} (Fin n ⊕ Fin m) → Γ(AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, ⊤),
      ∃ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
            ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
        w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ i : ULift.{u} (Fin n ⊕ Fin m), w.appTop (AffineSpace.coord S i) = v i :=
    fun v => ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) v,
      AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  obtain ⟨σ, hσ, hσc⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
        + pr₁.appTop (F b)) i.down)
  obtain ⟨σ', hσ', hσ'c⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
        - pr₁.appTop (F b)) i.down)
  obtain ⟨τ, hτ, hτc⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n =>
      AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
        - pr₂.appTop (G a))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)
  obtain ⟨τ', hτ', hτ'c⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n =>
      AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
        + pr₂.appTop (G a))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)
  have hσinl : ∀ a : Fin n,
      σ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun a => hσc _
  have hσinr : ∀ b : Fin m,
      σ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
            + pr₁.appTop (F b) := fun b => hσc _
  have hσ'inl : ∀ a : Fin n,
      σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun a => hσ'c _
  have hσ'inr : ∀ b : Fin m,
      σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
            - pr₁.appTop (F b) := fun b => hσ'c _
  have hτinl : ∀ a : Fin n,
      τ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
            - pr₂.appTop (G a) := fun a => hτc _
  have hτinr : ∀ b : Fin m,
      τ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun b => hτc _
  have hτ'inl : ∀ a : Fin n,
      τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
            + pr₂.appTop (G a) := fun a => hτ'c _
  have hτ'inr : ∀ b : Fin m,
      τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun b => hτ'c _
  have hfix₁ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
        ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) →
      (∀ a : Fin n,
        w.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
          = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) →
      ∀ x : Γ(AffineSpace (ULift.{u} (Fin n)) S, ⊤),
        w.appTop (pr₁.appTop x) = pr₁.appTop x := by
    intro w hw hwc x
    have hcomp : w ≫ pr₁ = pr₁ := by
      refine AffineSpace.hom_ext ?_ ?_
      · rw [Category.assoc, hpr₁, hw]
      · rintro ⟨a⟩
        rw [comp_appTop_apply, hpr₁c a, hwc a]
    rw [← comp_appTop_apply, hcomp]
  have hfix₂ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
        ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) →
      (∀ b : Fin m,
        w.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
          = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) →
      ∀ x : Γ(AffineSpace (ULift.{u} (Fin m)) S, ⊤),
        w.appTop (pr₂.appTop x) = pr₂.appTop x := by
    intro w hw hwc x
    have hcomp : w ≫ pr₂ = pr₂ := by
      refine AffineSpace.hom_ext ?_ ?_
      · rw [Category.assoc, hpr₂, hw]
      · rintro ⟨b⟩
        rw [comp_appTop_apply, hpr₂c b, hwc b]
    rw [← comp_appTop_apply, hcomp]
  have hσσ' : σ ≫ σ' = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ', hσ, Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσ'inl a, hσinl a, appTop_id_apply]
      · rw [comp_appTop_apply, hσ'inr b, appTop_sub, hσinr b,
          hfix₁ σ hσ hσinl (F b), appTop_id_apply]
        ring
  have hσ'σ : σ' ≫ σ = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ, hσ', Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσinl a, hσ'inl a, appTop_id_apply]
      · rw [comp_appTop_apply, hσinr b, appTop_add, hσ'inr b,
          hfix₁ σ' hσ' hσ'inl (F b), appTop_id_apply]
        ring
  have hττ' : τ ≫ τ' = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ', hτ, Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτ'inl a, appTop_add, hτinl a,
          hfix₂ τ hτ hτinr (G a), appTop_id_apply]
        ring
      · rw [comp_appTop_apply, hτ'inr b, hτinr b, appTop_id_apply]
  have hτ'τ : τ' ≫ τ = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ, hτ', Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτinl a, appTop_sub, hτ'inl a,
          hfix₂ τ' hτ' hτ'inr (G a), appTop_id_apply]
        ring
      · rw [comp_appTop_apply, hτinr b, hτ'inr b, appTop_id_apply]
  obtain ⟨D, hDover, hcoordEq⟩ :
      ∃ d : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
        d ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p ∧
          ∀ i : ULift.{u} (Fin n ⊕ Fin m), d.appTop (AffineSpace.coord S i)
            = Sum.elim
                (fun a : Fin n =>
                  e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
                (fun b : Fin m =>
                  e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) i.down :=
    ⟨AffineSpace.homOfVector p (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
        (fun a : Fin n => e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
        (fun b : Fin m => e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))))
        i.down),
      AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  have hDinl : ∀ a : Fin n,
      D.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) := fun a => hcoordEq _
  have hDinr : ∀ b : Fin m,
      D.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) := fun b => hcoordEq _
  have hLpr₁ : L ≫ pr₁ = e₁ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hpr₁, hLover, h₁]
    · rintro ⟨a⟩
      rw [comp_appTop_apply, hpr₁c a, hLinl a]
  have hLF : ∀ b : Fin m, L.appTop (pr₁.appTop (F b))
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) := by
    intro b
    rw [← comp_appTop_apply, hLpr₁, hF b]
  have hDpr₂ : D ≫ pr₂ = e₂ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hpr₂, hDover, h₂]
    · rintro ⟨b⟩
      rw [comp_appTop_apply, hpr₂c b, hDinr b]
  have hcompG : ∀ a : Fin n, D.appTop (pr₂.appTop (G a))
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) := by
    intro a
    rw [← comp_appTop_apply, hDpr₂, hG a]
  have hA : L ≫ σ = D := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ, hLover, hDover]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσinl a, hLinl a, hDinl a]
      · rw [comp_appTop_apply, hσinr b, appTop_add, hLinr b, hLF b, hDinr b, zero_add]
  have hB : D ≫ τ = R := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ, hDover, hRover]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτinl a, appTop_sub, hDinl a, hcompG a, hRinl a, sub_self]
      · rw [comp_appTop_apply, hτinr b, hDinr b, hRinr b]
  refine ⟨⟨σ ≫ τ, τ' ≫ σ', ?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc τ τ' σ', hττ', Category.id_comp, hσσ']
  · rw [Category.assoc, ← Category.assoc σ' σ τ, hσ'σ, Category.id_comp, hτ'τ]
  · show (σ ≫ τ) ≫ _ = _
    rw [Category.assoc, hτ, hσ]
  · show L ≫ (σ ≫ τ) = R
    rw [← Category.assoc, hA, hB]

theorem closedEmbeddingsRelatedByAutomorphism : ClosedEmbeddingsRelatedByAutomorphism.{u} := by
  intro k hk Y hY p hp n m e₁ he₁ e₂ he₂ h₁ h₂
  have : IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin n))) := by
    unfold affineSpaceIndexedBy; infer_instance
  have : IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin m))) := by
    unfold affineSpaceIndexedBy; infer_instance
  choose F hF using fun b : Fin m =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine e₁).2
      (e₂.appTop (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up b : ULift.{u} (Fin m))))
  choose G hG using fun a : Fin n =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine e₂).2
      (e₁.appTop (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up a : ULift.{u} (Fin n))))
  exact exists_iso_affineSpace_sum_comp_eq_of_coord n m p e₁ e₂ h₁ h₂ F hF G hG
    (AffineSpace.homOfVector p (coordVectorInl n m e₁))
    (AffineSpace.homOfVector p (coordVectorInr n m e₂))
    (AffineSpace.homOfVector_over _ _) (AffineSpace.homOfVector_over _ _)
    (fun a => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun b => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun a => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun b => AffineSpace.homOfVector_appTop_coord _ _ _)

end FunctorialResolution.EmbeddedResolution
end

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem isStrongResolution_canonicalAffineResolutionRule (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] :
    IsStrongResolution k Y p (canonicalAffineResolutionRule k Y p) := by
  have hIso : EmbeddedPrincipalizationDiscardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters
  have hsmooth : AffineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    affineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
  have hCen : AffineCentersLieOverSingularLocus principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :=
    affineCentersLieOverSingularLocus_principalizationWithRadicalCenters
  show IsStrongResolution k Y p
    (affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters k Y p)
  exact isStrongResolution_blowupSequenceWithoutIsos_ofAffine principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    (affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization principalizationWithRadicalCenters.{u}
      isFunctorialPrincipalization_principalizationWithRadicalCenters affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth)
    hsmooth
    (affineSmoothLocusPreimageDenseInDetached principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    hCen
    (affineDetachedClopenInCenter principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedComponentsNotInBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth hIso hsmooth
      embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters hCen)
    (affineCentersHaveStrictNormalCrossingsWithBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineAllLevelsSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineBoundaryInStrictNormalCrossingPosition principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictNormalCrossingsRestrictToClopen Blowup.blowupIsProper k Y p

theorem strongResolutionOfSingularitiesCharZero :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm principalizationWithRadicalCenters.{u}
    affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    isFunctorialPrincipalization_principalizationWithRadicalCenters
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters
    embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    closedEmbeddingsRelatedByAutomorphism
    isStrongResolution_canonicalAffineResolutionRule

end FunctorialResolution.EmbeddedResolution
end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace FunctorialResolution

theorem functorialResolutionCharZero : FunctorialResolutionCharZero.{u} := by
  obtain ⟨R, h1, h2, h3⟩ := EmbeddedResolution.strongResolutionOfSingularitiesCharZero.{u}
  exact ⟨fun k _ _ X f _ _ _ =>
    ⟨(R k X f).length, (R k X f).tower, (R k X f).isoZero, (R k X f).center, (R k X f).isBlowup⟩, h1, h2, h3⟩

theorem inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {E : List X.IdealSheafData} (h : HasSimpleNormalCrossings p E) :
    FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition p E := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨U, hx, m, c, hc, he, a, h1, h2, h3⟩ := h.2 x
  exact ⟨U, hx, m, ⟨c, hc, he⟩, a, h1, h2, h3⟩

theorem hasSimpleNormalCrossingsWith_of_hasStrictNormalCrossingsWith {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData} {E : List X.IdealSheafData}
    (h : FunctorialResolution.EmbeddedResolution.HasStrictNormalCrossingsWith p Z E) : HasSimpleNormalCrossingsWith p Z E := by
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, h1, h2, h3, h4⟩ := h x hx
  exact ⟨U, hxU, m, c.map, c.comp_struct, c.isEtale, a, S, h1, h2, h3, h4⟩

noncomputable def blowupSequenceOfIdealBlowupSequence {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {E : List X.IdealSheafData}
    (M : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence p I E) : BlowupSequence X :=
  ⟨M.length, M.tower, M.isoZero, M.center, M.isBlowup⟩

theorem hasSimpleNormalCrossings_of_inStrictNormalCrossingPosition {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {E : List X.IdealSheafData} (h : FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition p E) :
    HasSimpleNormalCrossings p E := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨U, hx, m, c, a, h1, h2, h3⟩ := h.2 x
  exact ⟨U, hx, m, c.map, c.comp_struct, c.isEtale, a, h1, h2, h3⟩

theorem isPrincipalizingSequence_of_idealBlowupSequence {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    {I : X.IdealSheafData} {E : List X.IdealSheafData}
    (M : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence p I E) (hE : FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition p E) (hM : M.lastIdeal = ⊤) :
    IsPrincipalizingSequence p I E (blowupSequenceOfIdealBlowupSequence M) := by
  have : AlgebraicGeometry.IsNoetherian X := FunctorialResolution.EmbeddedResolution.isNoetherian_of_locallyOfFiniteType p
  have key : ∀ i, i ≤ M.length →
      I.comap ((blowupSequenceOfIdealBlowupSequence M).structMap i) =
        (blowupSequenceOfIdealBlowupSequence M).exceptionalProduct i *
          (show ((blowupSequenceOfIdealBlowupSequence M).obj i).IdealSheafData from M.ideal i) := by
    intro i
    induction i with
    | zero =>
      intro _
      change _ = ⊤ * _
      rw [← Scheme.IdealSheafData.one_eq_top, one_mul]
      exact M.ideal_zero.symm
    | succ n ih =>
      intro hn
      have hlt : n < M.length := hn
      have hcomp : (blowupSequenceOfIdealBlowupSequence M).structMap (n + 1) =
          (blowupSequenceOfIdealBlowupSequence M).blowupMap n ≫ (blowupSequenceOfIdealBlowupSequence M).structMap n :=
        ((blowupSequenceOfIdealBlowupSequence M).structMap_down (Nat.le_succ n)).symm
      have hsucc : (M.center n).comap ((blowupSequenceOfIdealBlowupSequence M).blowupMap n) *
          (show ((blowupSequenceOfIdealBlowupSequence M).obj (n + 1)).IdealSheafData from M.ideal (n + 1)) =
          (show ((blowupSequenceOfIdealBlowupSequence M).obj n).IdealSheafData from M.ideal n).comap
            ((blowupSequenceOfIdealBlowupSequence M).blowupMap n) := M.ideal_succ n hlt
      rw [hcomp, Scheme.IdealSheafData.comap_comp, ih hlt.le, Scheme.IdealSheafData.comap_mul, ← hsucc,
        ← mul_assoc]
      rfl
  refine ⟨M.ideal, M.boundary, M.ideal_zero, M.boundary_zero, M.center_smooth,
    fun i hi => hasSimpleNormalCrossingsWith_of_hasStrictNormalCrossingsWith (M.center_snc i hi), M.ideal_vanishes,
    M.ideal_succ, M.boundary_succ, hM, ?_, fun i hi => M.smooth_structureMorphism i hi,
    fun i hi => hasSimpleNormalCrossings_of_inStrictNormalCrossingPosition (M.inStrictNormalCrossingPosition_boundary_of_isNoetherian hE i hi)⟩
  have hfin : (show ((blowupSequenceOfIdealBlowupSequence M).obj M.length).IdealSheafData from M.ideal M.length) = ⊤ := hM
  refine (key M.length le_rfl).trans ?_
  rw [hfin, ← Scheme.IdealSheafData.one_eq_top, mul_one]
  rfl

noncomputable def principalizationRuleOfAlgorithm (A : EmbeddedResolution.PrincipalizationAlgorithm.{u}) : PrincipalizationRuleCharZero.{u} :=
  fun k _ _ X p _ _ _ I hI E hE =>
    blowupSequenceOfIdealBlowupSequence (A k X p I hI E (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE))

theorem functorialPrincipalizationCharZero_of_algorithm (A : EmbeddedResolution.PrincipalizationAlgorithm.{u}) (h : FunctorialResolution.EmbeddedResolution.IsFunctorialPrincipalization A) :
    FunctorialPrincipalizationCharZero.{u} := by
  refine ⟨principalizationRuleOfAlgorithm A, ?_, ?_, ?_⟩
  · intro k _ _ X p _ _ _ I hI E hE
    exact isPrincipalizingSequence_of_idealBlowupSequence _ (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE)
      (h.lastIdeal_eq_top k X p I hI E (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE))
  · intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ φ _ hφ hI' hE'
    exact h.smooth_pullback k X p I hI E (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE) X' p' φ hφ hI'
      (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE')
  · intro k _ _ X p _ _ _ I hI E hE K _ _ _ hI' hE'
    exact h.base_change k X p I hI E (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE) K (algebraMap k K) hI'
      (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE')

theorem functorialPrincipalizationCharZero : FunctorialPrincipalizationCharZero.{u} :=
  functorialPrincipalizationCharZero_of_algorithm FunctorialResolution.EmbeddedResolution.principalizationWithRadicalCenters FunctorialResolution.EmbeddedResolution.isFunctorialPrincipalization_principalizationWithRadicalCenters

end FunctorialResolution
