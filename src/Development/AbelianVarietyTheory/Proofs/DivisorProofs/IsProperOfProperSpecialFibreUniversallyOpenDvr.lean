module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphismsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteD
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageClosureCompleteDVRSpecialFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageClosureCompleteDVRSpecialFibre
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibProperClosed

theorem isClosed_image_closure : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y P : Scheme.{0}) (q : Y ⟶ P)
    (s : P ⟶ Spec (CommRingCat.of O)) (C : Set Y), IsProper s → IsImmersion q →
    IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) →
    IsIrreducible C → (∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O) →
    IsClosed (q '' closure C) := by
  intro O _ _ _ hI Y P q s C hs hq hk hC hy
  set U : Set P := coborder (Set.range q) with hUdef
  have hUo : IsOpen U := q.isLocallyClosed_range.isOpen_coborder
  have hqU : Set.range q = U ∩ closure (Set.range q) := (coborder_inter_closure).symm
  have hZsub : closure (q '' C) ⊆ closure (Set.range q) := closure_mono (Set.image_subset_range _ _)
  have himg : q '' closure C = closure (q '' C) ∩ U := by
    rw [q.isEmbedding.isInducing.closure_eq_preimage_closure_image, Set.image_preimage_eq_inter_range, hqU]
    ext x
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2, hZsub h1⟩
  have hZc : IsClosed (closure (q '' C)) := isClosed_closure
  have hZirr : IsIrreducible (closure (q '' C)) := (hC.image q q.continuous.continuousOn).closure

  have hZk : _root_.IsPreconnected (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) := by
    let I := Scheme.IdealSheafData.vanishingIdeal (⟨closure (q '' C), hZc⟩ : TopologicalSpace.Closeds P)
    have hrange : Set.range I.subschemeι = closure (q '' C) := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
    haveI : IsProper (I.subschemeι ≫ s) := inferInstance
    have hne : Nonempty I.subscheme := by
      obtain ⟨c, hc⟩ := hC.nonempty
      have : q c ∈ Set.range I.subschemeι := by rw [hrange]; exact subset_closure ⟨c, hc, rfl⟩
      obtain ⟨w, -⟩ := this
      exact ⟨w⟩
    have hpc : _root_.IsPreconnected (Set.univ : Set I.subscheme) := by
      rw [← I.subschemeι.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hrange]
      exact hZirr.2.isPreconnected
    haveI : ConnectedSpace I.subscheme := { toPreconnectedSpace := ⟨hpc⟩, toNonempty := hne }
    haveI hsp := GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms GlobalTheory.T.formalAlgebraisation_morphisms' O _
      (I.subschemeι ≫ s) inferInstance inferInstance
    have hT : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s)) =
        (I.subschemeι ≫ s) ⁻¹' {IsLocalRing.closedPoint O} := by
      have h := Scheme.Pullback.range_fst (I.subschemeι ≫ s)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
      rw [GlobalTheory.SpecialConn.range_residue] at h
      exact h
    have hR : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (I.subschemeι ≫ s) ≫ I.subschemeι) =
        closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hT, ← hrange, Set.inter_comm,
        ← Set.image_preimage_eq_inter_range]
      rfl
    rw [← hR]
    exact isPreconnected_range (Scheme.Hom.continuous _)

  have hkU : IsClosed ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U) := by
    let res := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))
    haveI : IsClosedImmersion res :=
      IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
    haveI : IsProper (pullback.snd (q ≫ s) res ≫ res) := inferInstance
    haveI : IsProper ((pullback.fst (q ≫ s) res ≫ q) ≫ s) := by
      rw [Category.assoc, pullback.condition]; infer_instance
    haveI : IsProper (pullback.fst (q ≫ s) res ≫ q) := IsProper.of_comp _ s
    have hF : Set.range (pullback.fst (q ≫ s) res) = (q ≫ s) ⁻¹' {IsLocalRing.closedPoint O} := by
      have h := Scheme.Pullback.range_fst (q ≫ s) res
      rw [GlobalTheory.SpecialConn.range_residue] at h
      exact h
    have hcl := (pullback.fst (q ≫ s) res ≫ q).isClosedMap _
      ((isClosed_closure (s := C)).preimage (pullback.fst (q ≫ s) res).continuous)
    have e : (pullback.fst (q ≫ s) res ≫ q) '' (pullback.fst (q ≫ s) res ⁻¹' closure C) =
        (closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range, hF]
      change q '' (closure C ∩ q ⁻¹' (s ⁻¹' {IsLocalRing.closedPoint O})) = _
      rw [Set.image_inter_preimage, himg]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rw [← e]; exact hcl
  have hne : ((closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O}) ∩ U).Nonempty := by
    obtain ⟨y, hyC, hy⟩ := hy
    have h1 : q y ∈ closure (q '' C) ∩ U := himg ▸ ⟨y, hyC, rfl⟩
    exact ⟨q y, ⟨h1.1, hy⟩, h1.2⟩
  have hZkU : closure (q '' C) ∩ s ⁻¹' {IsLocalRing.closedPoint O} ⊆ U := by
    intro z hz
    by_contra hzU
    obtain ⟨w, hw, hw1, hw2⟩ := hZk U _ hUo hkU.isOpen_compl
        (fun x _ => by
          by_cases h : x ∈ U
          · exact Or.inl h
          · exact Or.inr fun h' => h h'.2)
        (by obtain ⟨x, hx1, hx2⟩ := hne; exact ⟨x, hx1, hx2⟩) ⟨z, hz, fun h => hzU h.2⟩
    exact hw2 ⟨hw, hw1⟩
  have hZU : closure (q '' C) ⊆ U := by
    intro z hz
    by_contra hzU
    have hcl : IsClosed (s '' (closure (q '' C) \ U)) := s.isClosedMap _ (hZc.sdiff hUo)
    have hsp : s z ⤳ IsLocalRing.closedPoint O :=
      (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (s z).2.ne_top)
    obtain ⟨z', ⟨hz'Z, hz'U⟩, hz'⟩ := hsp.mem_closed hcl ⟨z, ⟨hz, hzU⟩, rfl⟩
    exact hz'U (hZkU ⟨hz'Z, hz'⟩)
  rw [himg, Set.inter_eq_left.2 hZU]
  exact hZc

end GlobalTheory.FibProperClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageClosureCompleteDVRSpecialFibreStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_image_closure_completeDVR_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y P : Scheme.{0}) (q : Y ⟶ P) (s : P ⟶ Spec (CommRingCat.of O)) (C : Set Y), IsProper s → IsImmersion q → IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsIrreducible C → (∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O) → IsClosed (q '' closure C) := by
  first | exact @GlobalTheory.FibProperClosed.isClosed_image_closure | exact GlobalTheory.FibProperClosed.isClosed_image_closure | (intros; apply GlobalTheory.FibProperClosed.isClosed_image_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfClosedCoverInUniversallyClose
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfClosedCoverInUniversallyClose
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem universallyClosed_of_closed_cover_in_universallyClosed :
    ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y),
      UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) →
        π '' T = Set.univ → UniversallyClosed f := by
  intro S X Y P f π q s T hs hq hcomm hT hqT hπT
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : TopologicalSpace.Closeds Y)
  have hrange : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hcl : IsClosedImmersion (I.subschemeι ≫ q) := by
    refine .of_isPreimmersion _ ?_
    have : Set.range (I.subschemeι ≫ q) = q '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [this]; exact hqT
  have : UniversallyClosed ((I.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc, ← hcomm, ← Category.assoc]
    infer_instance
  have : Surjective (I.subschemeι ≫ π) := by
    constructor
    have : Set.range (I.subschemeι ≫ π) = π '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [← Set.range_eq_univ, this]; exact hπT
  exact UniversallyClosed.of_comp_surjective (I.subschemeι ≫ π) f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfClosedCoverInUniversallyCloseStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universallyClosed_of_closed_image_cover : ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y), UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) → π '' T = Set.univ → UniversallyClosed f := by
  first | exact @GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed | exact GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed | (intros; apply GlobalTheory.universallyClosed_of_closed_cover_in_universallyClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteD
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibreProper

theorem isProper_of_irreducible_of_isProper_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of O)), IrreducibleSpace X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → (∃ x : X, f x = IsLocalRing.closedPoint O) → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsProper f := by
  intro O _ _ _ _ X f hirr hsep hlft hqc hx hfib
  obtain ⟨x₀, hx₀⟩ := hx
  have hne : Nonempty X := ⟨x₀⟩
  obtain ⟨Y, P, π, q, s, U, hπ, hUne, hiso, hproj, hq, hcomm⟩ :=
    GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver O X f hsep hlft hqc hne
  have hs : IsProper s := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
    infer_instance
  set C : Set Y := π ⁻¹' (U : Set X) with hC
  have hsurj : Function.Surjective (π ∣_ U) := fun y =>
    ⟨(inv (π ∣_ U)) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩

  have hUsub : (U : Set X) ⊆ π '' C := by
    intro u hu
    obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
    refine ⟨v.1, v.2, ?_⟩
    have := congrArg Subtype.val hv
    rwa [morphismRestrict_base_coe] at this

  have hUirr : IsIrreducible (U : Set X) :=
    ⟨hUne, (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have hCirr : IsIrreducible C := by
    haveI : IrreducibleSpace (U : Set X) := Subtype.irreducibleSpace hUirr
    haveI : IrreducibleSpace (π ⁻¹ᵁ U).toScheme :=
      (Scheme.homeoOfIso (asIso (π ∣_ U))).irreducibleSpace_iff.2 (inferInstanceAs (IrreducibleSpace (U : Set X)))
    have h := (IrreducibleSpace.isIrreducible_univ (π ⁻¹ᵁ U).toScheme).image (fun y => (π ⁻¹ᵁ U).ι y)
      ((π ⁻¹ᵁ U).ι.continuous.continuousOn)
    convert h using 1
    ext y
    constructor
    · intro hy; exact ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨v, -, rfl⟩; exact v.2

  have hπT : π '' closure C = Set.univ := by
    have hcl : IsClosed (π '' closure C) := π.isClosedMap _ isClosed_closure
    have hd : Dense (U : Set X) := U.isOpen.dense hUne
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hd.closure_eq]
    exact closure_minimal (hUsub.trans (Set.image_mono subset_closure)) hcl
  have hmeet : ∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O := by
    obtain ⟨y, hy, hyx⟩ : x₀ ∈ π '' closure C := hπT ▸ Set.mem_univ x₀
    refine ⟨y, hy, ?_⟩
    rw [hcomm, Scheme.Hom.comp_apply, hyx, hx₀]
  have hfib' : IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) := by
    rw [hcomm, (Iso.eq_inv_comp (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) π)).2
      (pullbackRightPullbackFstIso_hom_snd (f := f) (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) (f' := π))]
    infer_instance
  have hclosed := GlobalTheory.T.isClosed_image_closure_completeDVR_specialFibre O Y P q s C hs hq hfib' hCirr hmeet
  have huc : UniversallyClosed f :=
    GlobalTheory.T.universallyClosed_of_closed_image_cover _ X Y P f π q s (closure C) inferInstance hq hcomm isClosed_closure hclosed hπT
  exact ⟨⟩

end GlobalTheory.FibreProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteDStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_irreducible_properSpecialFibre_completeDvr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of O)), IrreducibleSpace X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → (∃ x : X, f x = IsLocalRing.closedPoint O) → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre | exact GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre | (intros; apply GlobalTheory.FibreProper.isProper_of_irreducible_of_isProper_specialFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvr
open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.FibreProperDvr

theorem isProper_of_specialFibre : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    UniversallyOpen f → GeometricallyIrreducible f →
    IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)))) → IsProper f := by
  intro W _ _ _ X f h1 h2 h3 h4 h5 h6
  obtain ⟨⟨hdom, hdvr⟩, hcpl, -, hloc, -⟩ := ReciprocityTheory.CA.Pt.completionDVR W
  let O := AdicCompletion (maximalIdeal W) W
  haveI : Module.Flat W O := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat W O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let g : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of W) := Spec.map (CommRingCat.ofHom (algebraMap W O))
  have gfl : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have gsurj : Surjective g := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := W) (B := O)⟩
  haveI : IrreducibleSpace (Spec (CommRingCat.of O)) := inferInstance
  haveI : IrreducibleSpace ↥(pullback f g) := inferInstance

  let k := CommRingCat.ofHom (IsLocalRing.residue W)
  let kO := CommRingCat.ofHom (IsLocalRing.residue O)
  let ψ := CommRingCat.ofHom (IsLocalRing.ResidueField.map (algebraMap W O))
  have hsq : Spec.map kO ≫ g = Spec.map ψ ≫ Spec.map k := by
    simp only [g, ← Spec.map_comp]
    congr 1
  have hsp : IsProper (pullback.snd (pullback.snd f g) (Spec.map kO)) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd f g (Spec.map kO)]
    have : IsProper (pullback.snd f (Spec.map kO ≫ g)) := by
      rw [hsq, ← MorphismProperty.cancel_left_of_respectsIso @IsProper
        (pullbackLeftPullbackSndIso f (Spec.map k) (Spec.map ψ)).hom, pullbackLeftPullbackSndIso_hom_snd]
      infer_instance
    infer_instance
  have hex : ∃ x : ↥(pullback f g), (pullback.snd f g) x = IsLocalRing.closedPoint O :=
    (pullback.snd f g).surjective _
  have hp : IsProper (pullback.snd f g) :=
    GlobalTheory.T.isProper_of_irreducible_properSpecialFibre_completeDvr O (pullback f g) (pullback.snd f g) inferInstance inferInstance inferInstance inferInstance hex hsp
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) g :=
    ⟨⟨gsurj, gfl⟩, inferInstance⟩
  have : UniversallyClosed f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu hp.toUniversallyClosed
  exact ⟨⟩

end GlobalTheory.FibreProperDvr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfProperSpecialFibreUniversallyOpenDvrStatement
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_properSpecialFibre_universallyOpen_dvr : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → UniversallyOpen f → GeometricallyIrreducible f → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)))) → IsProper f := by
  first | exact @GlobalTheory.FibreProperDvr.isProper_of_specialFibre | exact GlobalTheory.FibreProperDvr.isProper_of_specialFibre | (intros; apply GlobalTheory.FibreProperDvr.isProper_of_specialFibre <;> assumption)
end
