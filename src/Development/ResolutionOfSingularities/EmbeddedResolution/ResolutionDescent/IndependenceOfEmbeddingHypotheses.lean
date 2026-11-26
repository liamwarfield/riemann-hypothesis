module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EnlargeAmbientSpace
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedBlowupsFlatBaseChange

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinateCodimensionCriterion
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def castAddImage (c d : ℕ) : Finset (Fin (c + d)) :=
  (Finset.univ : Finset (Fin c)).image (Fin.castAdd d)

theorem castAddImage_eq_image_castAdd (c d : ℕ) :
    castAddImage c d = (Finset.univ : Finset (Fin c)).image (Fin.castAdd d) := rfl

theorem card_castAddImage (c d : ℕ) : (castAddImage c d).card = c := by
  have hinj : Function.Injective (Fin.castAdd d : Fin c → Fin (c + d)) := by
    intro a b hab
    have hv : ((Fin.castAdd d a : Fin (c + d)) : ℕ) = ((Fin.castAdd d b : Fin (c + d)) : ℕ) :=
      congrArg (fun z : Fin (c + d) => (z : ℕ)) hab
    exact Fin.ext hv
  rw [castAddImage_eq_image_castAdd, Finset.card_image_of_injective _ hinj, Finset.card_univ,
    Fintype.card_fin]

private theorem mem_image_ι_of_mem {X' : Scheme.{u}} (U : X'.Opens)
    (V : U.toScheme.Opens) (y : X') (hy : y ∈ U) (h : (⟨y, hy⟩ : ↥U) ∈ V) :
    y ∈ U.ι ''ᵁ V :=
  ⟨⟨y, hy⟩, h, rfl⟩

private theorem range_ι_comp_ι_eq_image {X' : Scheme.{u}} (U : X'.Opens) (V : U.toScheme.Opens) :
    Set.range ((V.ι ≫ U.ι).base) = (↑(U.ι ''ᵁ V) : Set ↥X') := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨_, w.2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

private def etaleChartTop (k : Type u) [Field k] (c : ℕ) :
    EtaleChart (affineSpaceFinToSpec k c) (⊤ : (affineSpaceFin k c).Opens) c where
  map := (⊤ : (affineSpaceFin k c).Opens).ι
  comp_struct := rfl
  isEtale := inferInstance

private theorem etaleChartTop_map (k : Type u) [Field k] (c : ℕ) :
    (etaleChartTop k c).map = (⊤ : (affineSpaceFin k c).Opens).ι := rfl

private theorem restrictIdeal_top_coordSubspaceIdeal_univ (k : Type u) [Field k] (c : ℕ) :
    restrictIdeal (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c)))
      (⊤ : (affineSpaceFin k c).Opens) = (etaleChartTop k c).coordIdeal Finset.univ := by
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, etaleChartTop_map]

theorem exists_etaleChart_image_of_restrictIdeal_eq {X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (U : X'.Opens) (V : U.toScheme.Opens) (n : ℕ)
    (ch : EtaleChart (U.ι ≫ p) V n) (D : X'.IdealSheafData) (S : Finset (Fin n))
    (h : restrictIdeal (restrictIdeal D U) V = ch.coordIdeal S) :
    ∃ ch' : EtaleChart p (U.ι ''ᵁ V) n, restrictIdeal D (U.ι ''ᵁ V) = ch'.coordIdeal S := by
  have hr : Set.range ((U.ι ''ᵁ V).ι).base = Set.range ((V.ι ≫ U.ι).base) := by
    rw [Scheme.Opens.range_ι, ← range_ι_comp_ι_eq_image]
  let φ : (U.ι ''ᵁ V).toScheme ≅ V.toScheme :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq ((U.ι ''ᵁ V).ι) (V.ι ≫ U.ι) hr
  have hfac : φ.hom ≫ (V.ι ≫ U.ι) = (U.ι ''ᵁ V).ι :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hr
  have hcs : (φ.hom ≫ ch.map) ≫ affineSpaceFinToSpec k n = (U.ι ''ᵁ V).ι ≫ p := by
    calc (φ.hom ≫ ch.map) ≫ affineSpaceFinToSpec k n
        = φ.hom ≫ (ch.map ≫ affineSpaceFinToSpec k n) := Category.assoc _ _ _
      _ = φ.hom ≫ (V.ι ≫ (U.ι ≫ p)) := by rw [ch.comp_struct]
      _ = (φ.hom ≫ (V.ι ≫ U.ι)) ≫ p := by simp only [Category.assoc]
      _ = (U.ι ''ᵁ V).ι ≫ p := by rw [hfac]
  have : AlgebraicGeometry.Etale ch.map := ch.isEtale
  have hkey : (D.comap U.ι).comap V.ι = (coordSubspaceIdeal k n S).comap ch.map := by
    rw [← restrictIdeal_eq_comap_ι, ← restrictIdeal_eq_comap_ι, h, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  refine ⟨⟨φ.hom ≫ ch.map, hcs, inferInstance⟩, ?_⟩
  rw [restrictIdeal_eq_comap_ι, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  calc D.comap (U.ι ''ᵁ V).ι
      = ((D.comap U.ι).comap V.ι).comap φ.hom := by
        rw [← hfac, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    _ = ((coordSubspaceIdeal k n S).comap ch.map).comap φ.hom := by rw [hkey]
    _ = (coordSubspaceIdeal k n S).comap (φ.hom ≫ ch.map) := by
        rw [Scheme.IdealSheafData.comap_comp]

theorem exists_etaleChart_of_restrictIdeal_ker_eq_comap
    {X X' : Scheme.{u}} {k : Type u} [Field k] (p : X' ⟶ Spec (CommRingCat.of k))
    (τ : X ⟶ X') (c : ℕ) (U : X'.Opens) (q : U.toScheme ⟶ affineSpaceFin k c)
    [AlgebraicGeometry.Smooth q] (hq : q ≫ affineSpaceFinToSpec k c = U.ι ≫ p)
    (hker : restrictIdeal τ.ker U =
      (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).comap q)
    (x : X) (hx : τ.base x ∈ U) :
    ∃ (V : U.toScheme.Opens) (_ : IsAffineOpen V) (_ : (⟨τ.base x, hx⟩ : ↥U) ∈ V) (d : ℕ)
      (ch : EtaleChart (U.ι ≫ p) V (c + d)),
      restrictIdeal (restrictIdeal τ.ker U) V = ch.coordIdeal (castAddImage c d) := by
  have : AlgebraicGeometry.Smooth (affineSpaceFinToSpec k c) := affineSpaceIsSmooth ..
  obtain ⟨V, hVU, d, ch, hVaff, hyV, hcoord⟩ :=
    exists_etaleChart_comap_coord_eq (affineSpaceFinToSpec k c) q (etaleChartTop k c)
      (⟨τ.base x, hx⟩ : ↥U) (by trivial)
  have hidtop : (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).ideal
      ⟨⊤, isAffineOpen_top (affineSpaceFin k c)⟩
      = Ideal.span ((etaleChartTop k c).coord ''
          ((Finset.univ : Finset (Fin c)) : Set (Fin c))) :=
    EtaleChart.ideal_eq_span_coord (etaleChartTop k c) (isAffineOpen_top (affineSpaceFin k c))
      (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))) Finset.univ
      (restrictIdeal_top_coordSubspaceIdeal_univ k c)
  have hspanV : (restrictIdeal τ.ker U).ideal ⟨V, hVaff⟩
      = Ideal.span (ch.coord ''
          ((castAddImage c d : Finset (Fin (c + d))) : Set (Fin (c + d)))) := by
    rw [hker,
      Scheme.IdealSheafData.comap_ideal_eq_map_appLE
        (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))) q
        ⟨⊤, isAffineOpen_top (affineSpaceFin k c)⟩ ⟨V, hVaff⟩ hVU,
      hidtop, Ideal.map_span]
    congr 1
    rw [Set.image_image, castAddImage_eq_image_castAdd, Finset.coe_image, Set.image_image]
    exact Set.image_congr (fun j _ => (hcoord j).symm)
  have hcs : ch.map ≫ affineSpaceFinToSpec k (c + d) = V.ι ≫ (U.ι ≫ p) := by
    rw [ch.comp_struct, hq]
  refine ⟨V, hVaff, hyV, d, ⟨ch.map, hcs, ch.isEtale⟩, ?_⟩
  exact restrictIdeal_eq_coordIdeal_of_ideal_eq_span hVaff _ _ (castAddImage c d) hspanV

theorem hasEtaleCoordCodim_of_locally_smooth_over_affineSpace {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] (τ : X ⟶ X') (c : ℕ)
    (h : ∀ x : X, ∃ (U : X'.Opens) (_ : τ.base x ∈ U) (q : U.toScheme ⟶ affineSpaceFin k c),
      AlgebraicGeometry.Smooth q ∧ q ≫ affineSpaceFinToSpec k c = U.ι ≫ p ∧
        restrictIdeal τ.ker U =
          (coordSubspaceIdeal k c (Finset.univ : Finset (Fin c))).comap q) :
    HasEtaleCoordCodim p τ c := by
  intro x
  obtain ⟨U, hxU, q, hqsm, hqc, hker⟩ := h x
  have := hqsm
  obtain ⟨V, hVaff, hxV, d, ch, hch⟩ :=
    exists_etaleChart_of_restrictIdeal_ker_eq_comap p τ c U q hqc hker x hxU
  obtain ⟨ch', hch'⟩ :=
    exists_etaleChart_image_of_restrictIdeal_eq p U V (c + d) ch τ.ker (castAddImage c d) hch
  exact ⟨U.ι ''ᵁ V, mem_image_ι_of_mem U V (τ.base x) hxU hxV, c + d, ch',
    castAddImage c d, card_castAddImage c d, hch'⟩

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IndependenceOfEmbedding
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private def affineSpaceIndexedByIsoOfEquiv (k : Type u) [Field k] {N M : Type u} (σ : N ≃ M) :
    affineSpaceIndexedBy k M ≅ affineSpaceIndexedBy k N where
  hom := AffineSpace.reindex σ (Spec (CommRingCat.of k))
  inv := AffineSpace.reindex σ.symm (Spec (CommRingCat.of k))
  hom_inv_id := by
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord, Equiv.apply_symm_apply]
      simp
  inv_hom_id := by
    refine AffineSpace.hom_ext ?_ ?_
    · simp
    · intro i
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.reindex_appTop_coord,
        AffineSpace.reindex_appTop_coord, Equiv.symm_apply_apply]
      simp

private def uliftFinAddEquivUliftSum (n m : ℕ) :
    ULift.{u, 0} (Fin (n + m)) ≃ ULift.{u, 0} (Fin n ⊕ Fin m) :=
  Equiv.ulift.trans (finSumFinEquiv.symm.trans Equiv.ulift.symm)

private theorem locallyOfFiniteType_affineSpaceIndexedByToSpec (k : Type u) [Field k] (N : Type u)
    [Finite N] : AlgebraicGeometry.LocallyOfFiniteType (affineSpaceIndexedByToSpec k N) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

private theorem quasiCompact_affineSpaceIndexedByToSpec (k : Type u) [Field k] (N : Type u) :
    AlgebraicGeometry.QuasiCompact (affineSpaceIndexedByToSpec k N) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

private theorem irreducibleSpace_affineSpaceIndexedBy (k : Type u) [Field k] (N : Type u) :
    IrreducibleSpace ↥(affineSpaceIndexedBy k N) := by
  have : IrreducibleSpace ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum k))
  infer_instance

private theorem flat_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : CategoryTheory.IsIso f) :
    AlgebraicGeometry.Flat f := by
  have := hf
  have : AlgebraicGeometry.IsOpenImmersion f := inferInstance
  infer_instance

private theorem principalizationAlgorithm_toSequenceOfBlowups_congr (Alg : PrincipalizationAlgorithm.{u}) (k : Type u) [Field k]
    [CharZero k] (X : Scheme.{u}) (q : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth q] [AlgebraicGeometry.LocallyOfFiniteType q]
    [AlgebraicGeometry.QuasiCompact q] (I J : X.IdealSheafData) (hI : NonzeroOnComponents I)
    (hJ : NonzeroOnComponents J) (E F : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition q E)
    (hF : InStrictNormalCrossingPosition q F) (hIJ : I = J) (hEF : E = F) :
    (Alg k X q I hI E hE).toSequenceOfBlowups = (Alg k X q J hJ F hF).toSequenceOfBlowups := by
  subst hIJ
  subst hEF
  rfl

theorem smooth_affineSpaceIndexedByToSpec_finSumFin (hsm : AffineSpaceIsSmooth.{u}) (k : Type u)
    [Field k] (n m : ℕ) :
    AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m))) := by
  have hs : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + m)))) :=
    hsm k (n + m)
  have h : AffineSpace.reindex (uliftFinAddEquivUliftSum n m) (Spec (CommRingCat.of k)) ≫
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + m))) =
      affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)) := by
    simp [affineSpaceIndexedByToSpec]
  have : CategoryTheory.IsIso (AffineSpace.reindex (uliftFinAddEquivUliftSum n m) (Spec (CommRingCat.of k))) :=
    ⟨AffineSpace.reindex (uliftFinAddEquivUliftSum n m).symm (Spec (CommRingCat.of k)),
      (affineSpaceIndexedByIsoOfEquiv k (uliftFinAddEquivUliftSum n m)).hom_inv_id,
      (affineSpaceIndexedByIsoOfEquiv k (uliftFinAddEquivUliftSum n m)).inv_hom_id⟩
  have hiso : AlgebraicGeometry.Smooth
      (AffineSpace.reindex (uliftFinAddEquivUliftSum n m) (Spec (CommRingCat.of k))) :=
    inferInstance
  rw [← h]
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.Smooth) _ _ hiso hs

theorem isomorphic_embeddedResolutionRuleOfPrincipalization_of_iso (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] (D D' : EmbeddingDatum k Y p)
    (Φ : D.ambient ≅ D'.ambient) (hΦ : Φ.hom ≫ D'.ambientStruct = D.ambientStruct)
    (hemb : D.emb ≫ Φ.hom = D'.emb) :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D).Isomorphic (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D') := by
  have : AlgebraicGeometry.QuasiCompact D.emb := inferInstance
  have : AlgebraicGeometry.QuasiCompact D'.emb := inferInstance
  have hiso : CategoryTheory.IsIso Φ.inv := ⟨Φ.hom, Φ.inv_hom_id, Φ.hom_inv_id⟩
  have : AlgebraicGeometry.Flat Φ.inv := flat_of_isIso Φ.inv hiso
  have : AlgebraicGeometry.Smooth Φ.inv := inferInstance
  have hsq : D'.emb ≫ Φ.inv = D.emb := by
    rw [← hemb, Category.assoc, Φ.hom_inv_id, Category.comp_id]
  have hpbk : IsPullback (𝟙 Y) D'.emb D.emb Φ.inv :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hsq]⟩
  have hker : D'.emb.ker = D.emb.ker.comap Φ.inv := ker_eq_comap_ker_of_isPullback_of_flat hpbk
  have hφp : Φ.inv ≫ D.ambientStruct = D'.ambientStruct := by
    rw [← hΦ, ← Category.assoc, Φ.inv_hom_id, Category.id_comp]
  have hI' : NonzeroOnComponents (D.emb.ker.comap Φ.inv) := by
    rw [← hker]
    exact D'.nonzeroOnComponents_ker
  have hpbseq := hAlg.smooth_pullback k D.ambient D.ambientStruct D.emb.ker
    D.nonzeroOnComponents_ker ([] : List D.ambient.IdealSheafData) D.sncEmpty
    D'.ambient D'.ambientStruct Φ.inv hφp hI' D'.sncEmpty
  have hseq : (Alg k D'.ambient D'.ambientStruct D'.emb.ker D'.nonzeroOnComponents_ker
        ([] : List D'.ambient.IdealSheafData) D'.sncEmpty).toSequenceOfBlowups =
      (Alg k D'.ambient D'.ambientStruct (D.emb.ker.comap Φ.inv) hI'
        (List.map (fun Z => Z.comap Φ.inv) ([] : List D.ambient.IdealSheafData))
        D'.sncEmpty).toSequenceOfBlowups :=
    principalizationAlgorithm_toSequenceOfBlowups_congr Alg k D'.ambient D'.ambientStruct _ _ _ _ _ _ _ _ hker rfl
  have hpb2 : IsPullbackBlowupSequence Φ.inv (D'.toEmbeddedBlowupSequence Alg).ambientSeq
      (D.toEmbeddedBlowupSequence Alg).ambientSeq := by
    rw [EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, EmbeddingDatum.ambientBlowups_eq_toSequenceOfBlowups, hseq]
    exact hpbseq
  have hpbemb : IsPullback (𝟙 Y) (D'.toEmbeddedBlowupSequence Alg).emb (D.toEmbeddedBlowupSequence Alg).emb Φ.inv :=
    hpbk
  have hisoC : CategoryTheory.IsIso
      (show (D'.toEmbeddedBlowupSequence Alg).ambient ⟶ (D.toEmbeddedBlowupSequence Alg).ambient from Φ.inv) :=
    ⟨Φ.hom, Φ.inv_hom_id, Φ.hom_inv_id⟩
  have hflatC : AlgebraicGeometry.Flat
      (show (D'.toEmbeddedBlowupSequence Alg).ambient ⟶ (D.toEmbeddedBlowupSequence Alg).ambient from Φ.inv) :=
    flat_of_isIso _ hisoC
  have hres : IsPullbackBlowupSequence (𝟙 Y) (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D')
      (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D) :=
    ChartFlatBaseChange.isPullbackBlowupSequence_inducedBlowupsWithoutIso
      (chartFlatBaseChangeOfIsPullbackSeq (D.toEmbeddedBlowupSequence Alg) (D'.toEmbeddedBlowupSequence Alg) Φ.inv (𝟙 Y)
        hpbemb hpb2) (hw k Y p D) (hw k Y p D')
  exact (isomorphic_of_isPullbackSequenceOfBlowups_id _ _ hres
    (hasProperCenters_embeddedResolutionRuleOfPrincipalization Alg hw k Y p D)).symm

def LocallyConstCodimImpliesConstantCodim : Prop :=
  ∀ (k : Type u) [Field k] (X X' : Scheme.{u}) (q : X' ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth q] (τ : X ⟶ X') [AlgebraicGeometry.IsClosedImmersion τ] (c : ℕ),
    HasSmoothCoordCodim q τ c → HasEtaleCoordCodim q τ c

def LinearEmbeddingsHaveLocallyConstCodim : Prop :=
  ∀ (k : Type u) [Field k] (n m : ℕ),
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
        (affineSpaceInl k n m) m ∧
      HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin m)))
        (affineSpaceInrEmbedding k n m) n

theorem isomorphic_embeddedResolutionRuleOfPrincipalization (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u})
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hcod : LocallyConstCodimImpliesConstantCodim.{u})
    (hlin : LinearEmbeddingsHaveLocallyConstCodim.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] (D D' : EmbeddingDatum k Y p)
    (P : ClosedEmbeddingIntoAffineSpace D) (P' : ClosedEmbeddingIntoAffineSpace D') :
    (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D).Isomorphic (embeddedResolutionRuleOfPrincipalization Alg hw k Y p D') := by
  have hsA : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) :=
    hsm k P.dim
  have hsA' : AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) :=
    hsm k P'.dim
  have hsB : AlgebraicGeometry.Smooth
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))) :=
    smooth_affineSpaceIndexedByToSpec_finSumFin hsm k P.dim P'.dim
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))
  have := locallyOfFiniteType_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))
  have := quasiCompact_affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have := irreducibleSpace_affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim))
  have := irreducibleSpace_affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim))
  have := irreducibleSpace_affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))
  have hciL : AlgebraicGeometry.IsClosedImmersion (affineSpaceInl k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInl k P.dim P'.dim
  have hciR : AlgebraicGeometry.IsClosedImmersion (affineSpaceInrEmbedding k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInrEmbedding k P.dim P'.dim
  have : AlgebraicGeometry.IsClosedImmersion (D.emb ≫ P.toAffine) := inferInstance
  have : AlgebraicGeometry.IsClosedImmersion (D'.emb ≫ P'.toAffine) := inferInstance
  have hker1 : NonzeroOnComponents (Scheme.Hom.ker (D.emb ≫ P.toAffine)) :=
    nonzeroOnComponents_ker_comp D.emb P.toAffine D.nonzeroOnComponents_ker
  have hker1' : NonzeroOnComponents (Scheme.Hom.ker (D'.emb ≫ P'.toAffine)) :=
    nonzeroOnComponents_ker_comp D'.emb P'.toAffine D'.nonzeroOnComponents_ker
  have hsnc1 : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
  have hsnc1' : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
  have hsncB : InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      ([] : List
        (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim))).IdealSheafData) :=
    inStrictNormalCrossingPosition_nil (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
  have hcd1 : HasEtaleCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)))
      P.toAffine P.codimBound :=
    hcod k D.ambient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.codimBound
      P.locallyConstCodim
  have hcd1' : HasEtaleCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)))
      P'.toAffine P'.codimBound :=
    hcod k D'.ambient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.codimBound
      P'.locallyConstCodim
  have hker2 : NonzeroOnComponents
      (Scheme.Hom.ker ((D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim)) :=
    nonzeroOnComponents_ker_comp (D.emb ≫ P.toAffine) (affineSpaceInl k P.dim P'.dim) hker1
  have hker2' : NonzeroOnComponents
      (Scheme.Hom.ker ((D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim)) :=
    nonzeroOnComponents_ker_comp (D'.emb ≫ P'.toAffine) (affineSpaceInrEmbedding k P.dim P'.dim) hker1'
  have hcd2 : HasEtaleCoordCodim
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) P'.dim :=
    hcod k (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) P'.dim (hlin k P.dim P'.dim).1
  have hcd2' : HasEtaleCoordCodim
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) P.dim :=
    hcod k (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) P.dim (hlin k P.dim P'.dim).2
  have hciL2 : AlgebraicGeometry.IsClosedImmersion
      (show (D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
            (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp
            hker1 hsnc1).ambient ⟶
          affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)) from
        affineSpaceInl k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInl k P.dim P'.dim
  have hciR2 : AlgebraicGeometry.IsClosedImmersion
      (show (D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
            (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp
            hker1' hsnc1').ambient ⟶
          affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)) from
        affineSpaceInrEmbedding k P.dim P'.dim) :=
    isClosedImmersion_affineSpaceInrEmbedding k P.dim P'.dim
  have e1 := D.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1 hsnc1
    P.codimBound P.one_le_codimBound hcd1
  have e2 := (D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1
      hsnc1).isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInl k P.dim P'.dim) (affineSpaceInl_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2 hsncB
      P'.dim P'.one_le_dim hcd2
  have e1' := D'.isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
    (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
    (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
    hsnc1' P'.codimBound P'.one_le_codimBound hcd1'
  have e2' := (D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
      hsnc1').isomorphic_embeddedResolutionRule_enlargeAmbient Alg hAlg hw
      (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
      (affineSpaceInrEmbedding k P.dim P'.dim) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2' hsncB
      P.dim P.one_le_dim hcd2'
  have hc1 : (D.emb ≫ P.toAffine) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim)) = p := by
    rw [Category.assoc, P.toAffine_comp, D.comp_eq]
  have hc2 : (D'.emb ≫ P'.toAffine) ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim)) = p := by
    rw [Category.assoc, P'.toAffine_comp, D'.comp_eq]
  obtain ⟨Φ, hΦ1, hΦ2⟩ :=
    hcmp k Y p P.dim P'.dim (D.emb ≫ P.toAffine) (D'.emb ≫ P'.toAffine) hc1 hc2
  have hembL : (D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim =
      AffineSpace.homOfVector p (coordVectorInl P.dim P'.dim (D.emb ≫ P.toAffine)) :=
    comp_affineSpaceInl P.dim P'.dim p (D.emb ≫ P.toAffine) hc1
  have hembR : (D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim =
      AffineSpace.homOfVector p (coordVectorInr P.dim P'.dim (D'.emb ≫ P'.toAffine)) :=
    comp_affineSpaceInrEmbedding P.dim P'.dim p (D'.emb ≫ P'.toAffine) hc2
  have hfin : ((D.emb ≫ P.toAffine) ≫ affineSpaceInl k P.dim P'.dim) ≫ Φ.hom =
      (D'.emb ≫ P'.toAffine) ≫ affineSpaceInrEmbedding k P.dim P'.dim := by
    rw [hembL, hembR]
    exact hΦ2
  have e3 := isomorphic_embeddedResolutionRuleOfPrincipalization_of_iso Alg hAlg hw k Y p
    ((D.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim))) P.toAffine P.toAffine_comp hker1
        hsnc1).enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceInl k P.dim P'.dim) (affineSpaceInl_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2 hsncB)
    ((D'.enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P'.dim))) P'.toAffine P'.toAffine_comp hker1'
        hsnc1').enlargeAmbient (affineSpaceIndexedBy k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin P.dim ⊕ Fin P'.dim)))
        (affineSpaceInrEmbedding k P.dim P'.dim) (affineSpaceInrEmbedding_comp_affineSpaceIndexedByToSpec k P.dim P'.dim) hker2' hsncB)
    Φ hΦ1 hfin
  exact e1.trans (e2.trans (e3.trans (e1'.trans e2').symm))

theorem isIndependentOfPresentedEmbedding_of_locallyConstCodim (Alg : PrincipalizationAlgorithm.{u}) (hAlg : IsFunctorialPrincipalization Alg)
    (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u})
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) (hcod : LocallyConstCodimImpliesConstantCodim.{u})
    (hlin : LinearEmbeddingsHaveLocallyConstCodim.{u}) :
    (embeddedResolutionRuleOfPrincipalization Alg hw).IsIndependentOfPresentedEmbedding := by
  intro k _ _ Y p _ _ _ _ D D' P P'
  exact isomorphic_embeddedResolutionRuleOfPrincipalization Alg hAlg hw hsm hcmp hcod hlin k Y p D D' P P'

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem locallyConstCodimImpliesConstantCodim : LocallyConstCodimImpliesConstantCodim.{u} := by
  intro k _ X X' q _ τ _ c h
  exact hasEtaleCoordCodim_of_locally_smooth_over_affineSpace q τ c h

theorem linearEmbeddingsHaveLocallyConstCodim_of_affineSpaceIsSmooth (hsm : AffineSpaceIsSmooth.{u}) :
    LinearEmbeddingsHaveLocallyConstCodim.{u} := by
  intro k _ n m
  exact ⟨hasSmoothCoordCodim_affineSpaceInl hsm k n m, hasSmoothCoordCodim_affineSpaceInrEmbedding hsm k n m⟩

theorem isIndependentOfPresentedEmbedding_embeddedResolutionRule (Alg : PrincipalizationAlgorithm.{u})
    (hAlg : IsFunctorialPrincipalization Alg) (hw : TransitionsAreBlowupsForEmbeddings Alg) (hsm : AffineSpaceIsSmooth.{u})
    (hcmp : ClosedEmbeddingsRelatedByAutomorphism.{u}) :
    (embeddedResolutionRuleOfPrincipalization Alg hw).IsIndependentOfPresentedEmbedding :=
  isIndependentOfPresentedEmbedding_of_locallyConstCodim Alg hAlg hw hsm hcmp
    locallyConstCodimImpliesConstantCodim (linearEmbeddingsHaveLocallyConstCodim_of_affineSpaceIsSmooth hsm)

end FunctorialResolution.EmbeddedResolution

end
