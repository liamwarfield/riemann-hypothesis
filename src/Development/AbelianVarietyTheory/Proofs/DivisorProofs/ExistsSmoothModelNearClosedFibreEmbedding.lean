module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProjectiveEmbeddingFactorsProperStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartProductAtClosedPointClosedFibre

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFieldPointsClosedFibreSameProjectiveImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFieldPointsClosedFibreSameProjectiveImage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

namespace ClosedInj

theorem epi_spMap_field {Ω Ω' : Type} [Field Ω] [Field Ω'] (io : Ω →+* Ω') : Epi (spMap io) := by
  have : Flat (spMap io) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := io.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (spMap io) := ⟨fun t ↦ ⟨IsLocalRing.closedPoint Ω', Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_residue_factor {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] (y : Sp Ω ⟶ Sp R)
    (hy : ∀ t, y t = closedPoint R) : ∃ κ : ResidueField R →+* Ω, y = spMap (κ.comp (residue R)) := by
  set φ : R →+* Ω := (Spec.preimage y).hom with hφ
  have hyφ : y = spMap φ := (Spec.map_preimage y).symm
  have hker : ∀ a : R, a ∈ maximalIdeal R → φ a = 0 := by
    intro a ha
    have h1 := hy (IsLocalRing.closedPoint Ω)
    rw [hyφ] at h1
    have h2 : (PrimeSpectrum.comap φ (IsLocalRing.closedPoint Ω)).asIdeal = maximalIdeal R := by
      exact congrArg PrimeSpectrum.asIdeal h1
    rw [← h2] at ha
    have : φ a ∈ maximalIdeal Ω := ha
    rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at this
  have : IsLocalHom φ := ⟨fun a ha => by
    by_contra h
    have := hker a ((IsLocalRing.mem_maximalIdeal a).2 h)
    rw [this] at ha
    exact not_isUnit_zero ha⟩
  exact ⟨ResidueField.lift φ, by rw [ResidueField.lift_comp_residue]; exact hyφ⟩

end ClosedInj


open ClosedInj in
theorem Emb.eq_of_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ E.H.toScheme), (∀ t, M.π (G'.hom (E.H.ι (p t))) = closedPoint R) → p ≫ E.H.ι ≫ G'.hom = p' ≫ E.H.ι ≫ G'.hom → p ≫ E.f = p' ≫ E.f → p = p' := by
  intro R _ _ _ M G' _ E Ω _ p p' hcl hs hf
  set s : Sp Ω ⟶ M.S := p ≫ E.H.ι ≫ G'.hom with hsdef
  obtain ⟨κ, hκ⟩ := exists_residue_factor (s ≫ M.π) (fun t => by simpa [s] using hcl t)
  obtain ⟨Ω', _, io, e, l, -, hl, hlf⟩ := E.fib Ω s κ hκ
  let q : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ s) :=
    pullback.lift (spMap io ≫ p ≫ E.H.ι) (𝟙 _) (by simp [s])
  let q' : Sp Ω' ⟶ pullback G'.hom (spMap io ≫ s) :=
    pullback.lift (spMap io ≫ p' ≫ E.H.ι) (𝟙 _) (by simp [s, hs])
  have hq : q ≫ l = spMap io ≫ p := by
    rw [← cancel_mono E.H.ι]
    simp only [Category.assoc]
    erw [hl]
    exact pullback.lift_fst _ _ _
  have hq' : q' ≫ l = spMap io ≫ p' := by
    rw [← cancel_mono E.H.ι]
    simp only [Category.assoc]
    erw [hl]
    exact pullback.lift_fst _ _ _
  have hfst : q ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) =
      q' ≫ e.hom.left ≫ pullback.fst E.Y.hom (spMap (io.comp κ)) := by
    have := E.imm
    rw [← cancel_mono E.j]
    simp only [Category.assoc]
    rw [← hlf, ← Category.assoc q, hq, ← Category.assoc q', hq', Category.assoc, Category.assoc, hf]
  have hw : e.hom.left ≫ pullback.snd E.Y.hom (spMap (io.comp κ)) = pullback.snd G'.hom (spMap io ≫ s) :=
    Over.w e.hom
  have hqe : q ≫ e.hom.left = q' ≫ e.hom.left := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simp only [Category.assoc]
      rw [hw]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  have hqq : q = q' := by
    have := congrArg (· ≫ e.inv.left) hqe
    simpa [← Over.comp_left] using this
  have h2 : spMap io ≫ p = spMap io ≫ p' := by rw [← hq, ← hq', hqq]
  have := epi_spMap_field io
  exact (cancel_epi (spMap io)).1 h2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFieldPointsClosedFibreSameProjectiveImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_fieldPoints_closedFibre_same_projective_image : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ E.H.toScheme), (∀ t, M.π (G'.hom (E.H.ι (p t))) = closedPoint R) → p ≫ E.H.ι ≫ G'.hom = p' ≫ E.H.ι ≫ G'.hom → p ≫ E.f = p' ≫ E.f → p = p' := by
  first | exact @GlobalTheory.Mum.Emb.eq_of_closedFibre | exact GlobalTheory.Mum.Emb.eq_of_closedFibre | (intros; apply GlobalTheory.Mum.Emb.eq_of_closedFibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackRestrictISupOfForallRestrict
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackRestrictISupOfForallRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isPullback_iSup_of_forall : ∀ (P' X T S : Scheme.{0}) (a : X ⟶ P') (p : X ⟶ S) (q : P' ⟶ T) (π : S ⟶ T), a ≫ q = p ≫ π → ∀ (I : Type) (V : I → P'.Opens), (∀ i, IsPullback (a ∣_ V i) ((a ⁻¹ᵁ V i).ι ≫ p) ((V i).ι ≫ q) π) → IsPullback (a ∣_ (⨆ i, V i)) ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ((⨆ i, V i).ι ≫ q) π := by
  intro P' X T S a p q π w I V hV
  have hw : (a ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι ≫ q = ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ≫ π := by
    rw [morphismRestrict_ι_assoc, Category.assoc, w]
  set U := ⨆ i, V i with hUdef
  let L := pullback.lift (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ p) hw
  let Wo : I → U.toScheme.Opens := fun i => U.ι ⁻¹ᵁ V i
  let O : I → (pullback (U.ι ≫ q) π).Opens := fun i => pullback.fst (U.ι ≫ q) π ⁻¹ᵁ Wo i
  have hO : (⨆ i, O i) = ⊤ := by
    simp only [O, Wo]
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, ← hUdef, Scheme.Opens.ι_preimage_self,
      Scheme.Hom.preimage_top]
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  have hr1 : ∀ i, Set.range ((Wo i).ι ≫ U.ι) = Set.range (V i).ι := by
    intro i
    ext x
    simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨⟨x, hle i hx⟩, hx⟩, rfl⟩
  have hpt : ∀ z, U.ι (pullback.fst (U.ι ≫ q) π (L z)) = a ((a ⁻¹ᵁ U).ι z) := by
    intro z
    have h := congr($(show L ≫ pullback.fst (U.ι ≫ q) π ≫ U.ι = (a ⁻¹ᵁ U).ι ≫ a by
      rw [pullback.lift_fst_assoc, morphismRestrict_ι]) z)
    simpa using h
  have key : ∀ i, IsIso (L ∣_ O i) := by
    intro i
    let e := IsOpenImmersion.isoOfRangeEq ((Wo i).ι ≫ U.ι) (V i).ι (hr1 i)
    have he : e.hom ≫ (V i).ι = (Wo i).ι ≫ U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
    let j : (a ⁻¹ᵁ V i).toScheme ⟶ (a ⁻¹ᵁ U).toScheme := X.homOfLE (a.preimage_mono (hle i))
    have hj : j ≫ (a ⁻¹ᵁ U).ι = (a ⁻¹ᵁ V i).ι := Scheme.homOfLE_ι _ _
    have outer : IsPullback ((j ≫ L) ≫ pullback.snd (U.ι ≫ q) π) ((a ∣_ V i) ≫ e.inv) π
        ((Wo i).ι ≫ U.ι ≫ q) := by
      have h0 := (hV i).flip
      have e1 : (j ≫ L) ≫ pullback.snd (U.ι ≫ q) π = (a ⁻¹ᵁ V i).ι ≫ p := by
        rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hj]
      rw [e1]
      refine IsPullback.of_iso h0 (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp
      · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
        rw [← reassoc_of% he, Iso.inv_hom_id_assoc]
    have hv : IsPullback (j ≫ L) ((a ∣_ V i) ≫ e.inv) (pullback.fst (U.ι ≫ q) π) (Wo i).ι := by
      refine IsPullback.of_right (h₁₂ := pullback.snd (U.ι ≫ q) π) (h₂₂ := U.ι ≫ q) (v₁₃ := π) outer ?_
        (IsPullback.of_hasPullback (U.ι ≫ q) π).flip
      rw [← cancel_mono U.ι]
      simp only [Category.assoc, L, pullback.lift_fst_assoc, morphismRestrict_ι, reassoc_of% hj]
      rw [← he, Iso.inv_hom_id_assoc, morphismRestrict_ι]
    have R := (isPullback_morphismRestrict (pullback.fst (U.ι ≫ q) π) (Wo i)).flip
    have hr2 : Set.range ((L ⁻¹ᵁ O i).ι ≫ (a ⁻¹ᵁ U).ι) = Set.range (a ⁻¹ᵁ V i).ι := by
      ext x
      simp only [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨y, rfl⟩
        have hy := y.2
        change U.ι (pullback.fst (U.ι ≫ q) π (L y.1)) ∈ V i at hy
        rw [hpt] at hy
        exact hy
      · intro hx
        refine ⟨⟨⟨x, hle i hx⟩, ?_⟩, rfl⟩
        change U.ι (pullback.fst (U.ι ≫ q) π (L ⟨x, hle i hx⟩)) ∈ V i
        exact (congrArg (· ∈ V i) (hpt _)).mpr hx
    let f₁ := IsOpenImmersion.isoOfRangeEq _ _ hr2
    have hkey : L ∣_ O i = f₁.hom ≫ (hv.isoIsPullback _ _ R).hom := by
      rw [← cancel_mono (O i).ι, morphismRestrict_ι, Category.assoc, IsPullback.isoIsPullback_hom_fst,
        ← Category.assoc f₁.hom]
      congr 1
      rw [← cancel_mono (a ⁻¹ᵁ U).ι, Category.assoc, hj, IsOpenImmersion.isoOfRangeEq_hom_fac]
    rw [hkey]
    infer_instance
  have hiso : IsIso L :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) O hO key
  exact IsPullback.of_iso_pullback ⟨hw⟩ (asIso L) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackRestrictISupOfForallRestrictStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_restrict_iSup_of_forall_restrict : ∀ (P' X T S : Scheme.{0}) (a : X ⟶ P') (p : X ⟶ S) (q : P' ⟶ T) (π : S ⟶ T), a ≫ q = p ≫ π → ∀ (I : Type) (V : I → P'.Opens), (∀ i, IsPullback (a ∣_ V i) ((a ⁻¹ᵁ V i).ι ≫ p) ((V i).ι ≫ q) π) → IsPullback (a ∣_ (⨆ i, V i)) ((a ⁻¹ᵁ (⨆ i, V i)).ι ≫ p) ((⨆ i, V i).ι ≫ q) π := by
  first | exact @GlobalTheory.Mum.isPullback_iSup_of_forall | exact GlobalTheory.Mum.isPullback_iSup_of_forall | (intros; apply GlobalTheory.Mum.isPullback_iSup_of_forall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothISupOpensCompOfForallSmooth
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothISupOpensCompOfForallSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.smooth_iSup_comp (P' T : Scheme.{0}) (q : P' ⟶ T) (I : Type) (V : I → P'.Opens)
    (h : ∀ i, Smooth ((V i).ι ≫ q)) : Smooth ((⨆ i, V i).ι ≫ q) := by
  have hloc : IsZariskiLocalAtSource @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  set U := ⨆ i, V i with hUdef
  have hle : ∀ i, V i ≤ U := fun i => le_iSup V i
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth.{0}) (fun i => U.ι ⁻¹ᵁ V i) ?_ ?_
  · apply top_unique
    intro x _
    have hx : (U.ι x : P') ∈ (⨆ i, V i : P'.Opens) := x.2
    rw [TopologicalSpace.Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have hrange : Set.range ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) = Set.range (V i).ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι]
      ext y
      simp only [Set.mem_image, SetLike.mem_coe, Scheme.Hom.mem_preimage]
      exact ⟨by rintro ⟨x, hx, rfl⟩; exact hx, fun hy => ⟨⟨y, hle i hy⟩, hy, rfl⟩⟩
    rw [← Category.assoc, ← IsOpenImmersion.isoOfRangeEq_hom_fac ((U.ι ⁻¹ᵁ V i).ι ≫ U.ι) (V i).ι hrange,
      Category.assoc]
    haveI := h i
    infer_instance
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothISupOpensCompOfForallSmoothStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth : ∀ (P' T : Scheme.{0}) (q : P' ⟶ T) (I : Type) (V : I → P'.Opens), (∀ i, Smooth ((V i).ι ≫ q)) → Smooth ((⨆ i, V i).ι ≫ q) := by
  first | exact @GlobalTheory.Mum.smooth_iSup_comp | exact GlobalTheory.Mum.smooth_iSup_comp | (intros; apply GlobalTheory.Mum.smooth_iSup_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedPointsClosedFibreMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedPointsClosedFibreMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem mem_of_closedPoints_closedFibre_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (T : Scheme.{0}) (q : T ⟶ Sp R),
    LocallyOfFiniteType q → ∀ U : T.Opens, (∀ x : T, IsClosed ({x} : Set T) → q x = closedPoint R → x ∈ U) →
    ∀ x : T, q x = closedPoint R → x ∈ U := by
  intro R _ _ T q hq U hU x hx
  by_contra hxU
  set c : Sp R := closedPoint R
  have hc : IsClosed ({c} : Set (Sp R)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 (IsLocalRing.maximalIdeal.isMaximal R)
  have hft : LocallyOfFiniteType (q.fiberToSpecResidueField c) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : JacobsonSpace (q.fiber c) := LocallyOfFiniteType.jacobsonSpace (q.fiberToSpecResidueField c)
  let e := q.fiberι c
  have hemb : Topology.IsClosedEmbedding e := by
    refine ⟨IsPreimmersion.isEmbedding e, ?_⟩
    rw [Scheme.Hom.range_fiberι]
    exact hc.preimage q.continuous
  let Z : Set T := closure {x} ∩ (U : Set T)ᶜ
  have hZ : IsClosed Z := isClosed_closure.inter U.isOpen.isClosed_compl
  obtain ⟨x', hx'⟩ : x ∈ Set.range e := by
    rw [Scheme.Hom.range_fiberι]; exact hx
  have hne : (e ⁻¹' Z).Nonempty := ⟨x', by
    show e x' ∈ Z
    rw [hx']; exact ⟨subset_closure rfl, hxU⟩⟩
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints hne (hZ.preimage e.continuous).isLocallyClosed
  have hyc' : IsClosed ({e y} : Set T) := by
    rw [← Set.image_singleton]
    exact hemb.isClosedMap _ hyc
  have hqy : q (e y) = c := by
    have : e y ∈ Set.range e := ⟨y, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  exact hyZ.2 (hU _ hyc' hqy)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedPointsClosedFibreMemStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_of_closedPoints_closedFibre_mem' : ∀ (R : Type) [CommRing R] [IsLocalRing R] (T : Scheme.{0}) (q : T ⟶ Sp R), LocallyOfFiniteType q → ∀ U : T.Opens, (∀ x : T, IsClosed ({x} : Set T) → q x = closedPoint R → x ∈ U) → ∀ x : T, q x = closedPoint R → x ∈ U := by
  first | exact @GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem | exact GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem | (intros; apply GlobalTheory.Mum.mem_of_closedPoints_closedFibre_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothModelNearClosedFibreEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u ∧ l ≫ E.f = pullback.fst _ _ ≫ fU := by
  intro R _ _ _ hR M G' _ _ hG E
  have hRn : IsNoetherianRing R := hR.1
  have hRi : IsIntegrallyClosed R := hR.2.2.1
  obtain ⟨hΓ, hsurj⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  obtain ⟨P', b, X, a, hPn, hbs, hbl, hap, -, hab, hcomm, hX, hlift⟩ := GlobalTheory.T.closedFibre_projectiveEmbedding_factors_proper R hR M G' hG E
  have hsq : a ≫ b ≫ PSpace.str R E.N = (X.ι ≫ E.H.ι ≫ G'.hom) ≫ M.π := by
    rw [← Category.assoc, hcomm, Category.assoc, E.f_over]; simp only [Category.assoc]
  have hpt : ∀ w : X.toScheme, (b ≫ PSpace.str R E.N) (a w) = M.π (G'.hom (E.H.ι (X.ι w))) := by
    intro w
    have := congrArg (fun f => f w) hsq
    simpa [Scheme.Hom.comp_apply] using this
  have key : ∀ c : {x : P' // IsClosed ({x} : Set P') ∧ (b ≫ PSpace.str R E.N) x = closedPoint R},
      ∃ V : P'.Opens, c.1 ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧
        IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
    rintro ⟨x, hx1, hx2⟩
    refine GlobalTheory.T.exists_smooth_open_nbhd_isPullback_at_closedPoint R hR M G' hG E P' b X a hbs hbl hap hab hcomm hΓ hsurj x hx1 hx2 ?_ (hlift x hx1 hx2)
    intro Ω _ p p' hr he hs
    have hc : ∀ t, M.π (G'.hom (E.H.ι ((p ≫ X.ι) t))) = closedPoint R := by
      intro t
      have ht : (p ≫ a) t = x := by
        have : (p ≫ a) t ∈ Set.range (p ≫ a) := ⟨t, rfl⟩
        rw [hr] at this; exact this
      have := hpt (p t)
      rw [Scheme.Hom.comp_apply] at ht
      rw [ht, hx2] at this
      rw [Scheme.Hom.comp_apply]; exact this.symm
    have hf : (p ≫ X.ι) ≫ E.f = (p' ≫ X.ι) ≫ E.f := by
      rw [Category.assoc, Category.assoc, ← hcomm, ← Category.assoc, he, Category.assoc]
    have := GlobalTheory.T.eq_of_fieldPoints_closedFibre_same_projective_image R M G' E Ω (p ≫ X.ι) (p' ≫ X.ι) hc (by simpa only [Category.assoc] using hs) hf
    exact (cancel_mono X.ι).1 this
  choose V hxV hVs hVp using key
  set U : P'.Opens := ⨆ c, V c with hUdef
  have hUp : IsPullback (a ∣_ U) ((a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (U.ι ≫ b ≫ PSpace.str R E.N) M.π :=
    GlobalTheory.T.isPullback_restrict_iSup_of_forall_restrict _ _ _ _ a _ _ _ hsq _ V hVp
  have hUs : Smooth (U.ι ≫ b ≫ PSpace.str R E.N) := GlobalTheory.T.smooth_iSup_opens_comp_of_forall_smooth _ _ _ _ V hVs
  have hlft : LocallyOfFiniteType (b ≫ PSpace.str R E.N) := by
    have : IsProper (PSpace.str R E.N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N
    infer_instance
  have hU0 : ∀ y : P', (b ≫ PSpace.str R E.N) y = closedPoint R → y ∈ U := by
    refine GlobalTheory.T.mem_of_closedPoints_closedFibre_mem' R P' (b ≫ PSpace.str R E.N) hlft U ?_
    intro y hy1 hy2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy1, hy2⟩, hxV _⟩
  have hsep : IsSeparated (U.ι ≫ b ≫ PSpace.str R E.N) := by
    have : IsProper (PSpace.str R E.N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R E.N
    infer_instance
  have hqc : QuasiCompact (U.ι ≫ b ≫ PSpace.str R E.N) := by
    haveI := hPn
    have : CompactSpace U := isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set P'))
    exact (quasiCompact_iff_compactSpace _).2 this
  let e := hUp.isoPullback
  refine ⟨Near.mk (Over.mk (U.ι ≫ b ≫ PSpace.str R E.N)) hUs hsep hqc
      (e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.H.ι) inferInstance ?_ ?_,
    U.ι ≫ b, e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι, ?_, ?_⟩
  · have := hUp.isoPullback_inv_snd
    exact this
  · intro g hg
    obtain ⟨z, rfl⟩ : g ∈ Set.range E.H.ι := by rw [Scheme.Opens.range_ι]; exact E.H_all g hg
    obtain ⟨w, rfl⟩ : z ∈ Set.range X.ι := by rw [Scheme.Opens.range_ι]; exact hX z hg
    have hw : a w ∈ U := hU0 _ (by rw [hpt]; exact hg)
    obtain ⟨w', rfl⟩ : w ∈ Set.range (a ⁻¹ᵁ U).ι := by rw [Scheme.Opens.range_ι]; exact hw
    refine ⟨e.hom w', ?_⟩
    rw [← Scheme.Hom.comp_apply e.hom, Iso.hom_inv_id_assoc]
    simp only [Scheme.Hom.comp_apply]
  · simp only [Category.assoc]
  · show e.inv ≫ (a ⁻¹ᵁ U).ι ≫ X.ι ≫ E.f = pullback.fst (U.ι ≫ b ≫ PSpace.str R E.N) M.π ≫ U.ι ≫ b
    rw [← hcomm, ← Category.assoc ((a ⁻¹ᵁ U).ι), ← morphismRestrict_ι,
      ← Category.assoc e.inv]
    simp only [Category.assoc]
    rw [← Category.assoc e.inv (a ∣_ U), hUp.isoPullback_inv_fst]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothModelNearClosedFibreEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_model_near_closedFibre_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u ∧ l ≫ E.f = pullback.fst _ _ ≫ fU := by
  first | exact @GlobalTheory.Mum.exists_near | exact GlobalTheory.Mum.exists_near | (intros; apply GlobalTheory.Mum.exists_near <;> assumption)
end
