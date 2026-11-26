module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheaf

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem imageIdealSheaf_eq_ker_subschemeι_comp {S X : Scheme.{u}} (f : S ⟶ X) (Z : S.IdealSheafData) :
    imageIdealSheaf f Z = Scheme.Hom.ker (Z.subschemeι ≫ f) :=
  rfl

theorem support_imageIdealSheaf_eq_image_support {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] (Z : S.IdealSheafData) :
    (↑(imageIdealSheaf ι Z).support : Set ↥X) = ⇑ι '' (↑Z.support : Set ↥S) := by
  have hqc : AlgebraicGeometry.QuasiCompact (Z.subschemeι ≫ ι) := inferInstance
  have hcl := AlgebraicGeometry.Scheme.Hom.isClosedEmbedding ι
  have hrange : Set.range ⇑Z.subschemeι = (↑Z.support : Set ↥S) :=
    AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι Z
  have hcomp : Set.range ⇑(Z.subschemeι ≫ ι) = ⇑ι '' (↑Z.support : Set ↥S) := by
    rw [← hrange]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨⇑Z.subschemeι y, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have hclosed : IsClosed (⇑ι '' (↑Z.support : Set ↥S)) :=
    hcl.isClosedMap _ Z.support.2
  have hsup : (↑(AlgebraicGeometry.Scheme.Hom.ker (Z.subschemeι ≫ ι)).support : Set ↥X)
      = closure (Set.range ⇑(Z.subschemeι ≫ ι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [imageIdealSheaf_eq_ker_subschemeι_comp, hsup, hcomp, hclosed.closure_eq]

private theorem exists_iso_ker_subscheme {W X : Scheme.{u}} (g : W ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion g] :
    ∃ e : W ≅ (Scheme.Hom.ker g).subscheme,
      e.hom ≫ (Scheme.Hom.ker g).subschemeι = g :=
  ⟨asIso (Scheme.Hom.toImage g), Scheme.Hom.toImage_imageι g⟩

private theorem smooth_of_smooth_iso_hom_comp {A A' B : Scheme.{u}} (e : A ≅ A') (p : A' ⟶ B)
    (h : AlgebraicGeometry.Smooth (e.hom ≫ p)) : AlgebraicGeometry.Smooth p := by
  have : AlgebraicGeometry.Smooth (e.hom ≫ p) := h
  have h2 : AlgebraicGeometry.Smooth (e.inv ≫ e.hom ≫ p) := inferInstance
  simpa using h2

theorem smooth_imageIdealSheaf_subschemeι_comp {S X B : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] (Z : S.IdealSheafData) (f : X ⟶ B)
    (h : AlgebraicGeometry.Smooth (Z.subschemeι ≫ ι ≫ f)) :
    AlgebraicGeometry.Smooth ((imageIdealSheaf ι Z).subschemeι ≫ f) := by
  have : AlgebraicGeometry.IsClosedImmersion (Z.subschemeι ≫ ι) := inferInstance
  obtain ⟨e, he⟩ := exists_iso_ker_subscheme (Z.subschemeι ≫ ι)
  rw [imageIdealSheaf_eq_ker_subschemeι_comp ι Z]
  refine smooth_of_smooth_iso_hom_comp e _ ?_
  rw [← Category.assoc, he, Category.assoc]
  exact h

namespace BlowupSequenceData

theorem projectionToBase_prepend_zero {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = CategoryStruct.id X := by
  rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.prepend_isoObjZero, CategoryTheory.Iso.refl_hom]

theorem projectionToBase_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).projectionToBase (t + 1) = d.projectionToBase t := by
  induction t with
  | zero =>
    have e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (0 + 1)
        = (BlowupSequenceData.prepend Z hZ d).map 0 ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 :=
      BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) 0
    have e2 : (BlowupSequenceData.prepend Z hZ d).projectionToBase 0 = (BlowupSequenceData.prepend Z hZ d).isoZero.hom :=
      BlowupSequenceData.projectionToBase_zero (BlowupSequenceData.prepend Z hZ d)
    have e3 : (BlowupSequenceData.prepend Z hZ d).isoZero = Iso.refl X :=
      BlowupSequenceData.prepend_isoObjZero Z hZ d
    have e4 : (BlowupSequenceData.prepend Z hZ d).map 0 = d.isoZero.hom :=
      BlowupSequenceData.prepend_blowupMorphism_zero Z hZ d
    have e5 : d.projectionToBase 0 = d.isoZero.hom := BlowupSequenceData.projectionToBase_zero d
    rw [e1, e2, e3, e4, e5]
    exact Category.comp_id _
  | succ n ih =>
    have e1 : (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1 + 1)
        = (BlowupSequenceData.prepend Z hZ d).map (n + 1) ≫ (BlowupSequenceData.prepend Z hZ d).projectionToBase (n + 1) :=
      BlowupSequenceData.projectionToBase_succ (BlowupSequenceData.prepend Z hZ d) (n + 1)
    have e2 : (BlowupSequenceData.prepend Z hZ d).map (n + 1) = d.map n :=
      BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n
    rw [e1, e2, ih]
    exact (BlowupSequenceData.projectionToBase_succ d n).symm

theorem controlledTransform_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X)
    (I I₁ : X.IdealSheafData) (m : ℕ)
    (h1 : (BlowupSequenceData.prepend Z hZ d).controlledTransform I m 1 = I₁.comap d.isoZero.hom) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).controlledTransform I m (t + 1) = d.controlledTransform I₁ m t := by
  induction t with
  | zero => exact h1.trans (d.controlledTransform_zero I₁ m).symm
  | succ n ih =>
    rewrite [BlowupSequenceData.controlledTransform_succ (BlowupSequenceData.prepend Z hZ d) I m (n + 1),
      BlowupSequenceData.controlledTransform_succ d I₁ m n, ih,
      BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n, BlowupSequenceData.prepend_center_succ Z hZ d n]
    rfl

theorem boundary_prepend_succ {X : Scheme.{u}} (Z : X.IdealSheafData)
    (hZ : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id X) Z) (d : BlowupSequenceData X)
    (E E₁ : List X.IdealSheafData)
    (h1 : (BlowupSequenceData.prepend Z hZ d).boundaryFrom E 1
      = List.map (fun D => D.comap d.isoZero.hom) E₁) (t : ℕ) :
    (BlowupSequenceData.prepend Z hZ d).boundaryFrom E (t + 1) = d.boundaryFrom E₁ t := by
  induction t with
  | zero =>
      rw [BlowupSequenceData.boundary_zero]
      exact h1
  | succ n ih =>
      rw [BlowupSequenceData.boundary_succ (BlowupSequenceData.prepend Z hZ d) E (n + 1),
        BlowupSequenceData.boundary_succ d E₁ n, ih, BlowupSequenceData.prepend_blowupMorphism_succ Z hZ d n,
        BlowupSequenceData.prepend_center_succ Z hZ d n]
      all_goals rfl

end BlowupSequenceData

namespace DivisorReduction

theorem smooth_ambientBlowupSeq_center_comp (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) (ht : t < s.length) :
    AlgebraicGeometry.Smooth
      (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).subschemeι ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)) := by
  have hsm := s.center_smooth t ht
  have hemb := embeddingIntoAmbient_comp_projectionToBase hres hno T j hj I₀ E₀ s hpr t
  have h2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)
      = s.projectionToBase t ≫ (divisorEmbedding T j hj I₀ E₀ ≫ T.structMap) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg
          (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ T.scheme) => g ≫ T.structMap)
          hemb).trans (Category.assoc _ _ _))
  have key : AlgebraicGeometry.Smooth ((s.center t).subschemeι ≫
      (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap))) :=
    Eq.mpr
      (congrArg
        (fun g : ((MarkedBlowupSequenceData.ofMarkedSequence s).obj t ⟶ Spec (CommRingCat.of T.base)) =>
          AlgebraicGeometry.Smooth ((s.center t).subschemeι ≫ g)) h2)
      hsm
  exact Eq.mpr
    (congrArg
      (fun Z : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData =>
        AlgebraicGeometry.Smooth (Z.subschemeι ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap)))
      (ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t))
    (smooth_imageIdealSheaf_subschemeι_comp (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)
      ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap) key)

theorem support_ambientBlowupSeq_center_eq_image (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (t : ℕ) :
    (↑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support :
        Set ↥((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t)) =
      ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ''
        (↑((MarkedBlowupSequenceData.ofMarkedSequence s).center t).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj t)) := by
  have h1 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t =
      imageIdealSheaf (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t) :=
    ambientBlowupSeq_center_eq_imageIdealSheaf hres hno T j hj I₀ E₀ s hpr t
  have h2 : (MarkedBlowupSequenceData.ofMarkedSequence s).center t = s.center t :=
    MarkedBlowupSequenceData.ofMarkedSequence_center s t
  rw [h1, h2]
  exact support_imageIdealSheaf_eq_image_support
    (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryComponentsInOrderLocus
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem le_ker_comp_subschemeι {X : Scheme.{u}} (D : X.IdealSheafData) {W : Scheme.{u}}
    (g : W ⟶ D.subscheme) : D ≤ AlgebraicGeometry.Scheme.Hom.ker (g ≫ D.subschemeι) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι D).ge.trans
    (AlgebraicGeometry.Scheme.Hom.le_ker_comp g _)

abbrev boundaryComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x | connectedComponent x ⊆
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult}

abbrev boundaryComponentsInOrderLocusOpens (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    (T.boundary.get ⟨j, hj⟩).subscheme.Opens :=
  ⟨boundaryComponentsInOrderLocus T j hj, h⟩

theorem one_le_mult_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) : 1 ≤ T.mult :=
  hV.one_le_mult

theorem isSmoothDivisor_boundary_comap_isoObjZero (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (s : T.SequenceOfBlowups) :
    IsSmoothDivisor (s.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap s.isoZero.hom) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  have hD : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem
  rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
  exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso T.structMap s.toSequenceOfBlowups.isoZero _ hD

theorem containedComponentsIdeal_eq_ker_of_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj =
      AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :=
  containedComponentsIdeal_eq_ker_ι_comp_subschemeι_of_isOpen T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen_locus (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : ¬ IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj = ⊤ :=
  containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent T j hj h

theorem support_containedComponentsIdeal_subset_support_boundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) :
    ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆
      ((T.boundary.get ⟨j, hj⟩).support : Set ↥T.scheme) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h]
    exact SetLike.coe_subset_coe.mpr
      (AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
        (le_ker_comp_subschemeι (T.boundary.get ⟨j, hj⟩) (boundaryComponentsInOrderLocusOpens T j hj h).ι))
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot]
    exact Set.empty_subset _

def PreimageSupportEqComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) : Prop :=
  ∀ h : IsOpen (boundaryComponentsInOrderLocus T j hj),
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
        ((AlgebraicGeometry.Scheme.Hom.ker
            ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
              (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme) =
      boundaryComponentsInOrderLocus T j hj

theorem isOpen_preimage_support_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (hc : PreimageSupportEqComponentsInOrderLocus T j hj) :
    IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h, hc h]
    exact h
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot,
      Set.preimage_empty]
    exact isOpen_empty

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem ker_embeddingIntoAmbientBlowupSequence_zero {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0) =
      (AlgebraicGeometry.Scheme.Hom.ker ι).comap
        (ambientBlowupSequence ι s hres hno hcen).isoZero.hom := by
  have h1 : embeddingIntoAmbientBlowupSequence ι s hres hno hcen 0 = s.isoZero.hom ≫ ι :=
    embeddingIntoAmbientBlowupSequence_zero ι s hres hno hcen
  have h2 : (AlgebraicGeometry.Scheme.Hom.ker ι).comap
      (ambientBlowupSequence ι s hres hno hcen).isoZero.hom
      = AlgebraicGeometry.Scheme.Hom.ker ι := by
    rw [ambientBlowupSequence_isoObjZero]
    exact AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  rw [h1, h2]
  exact Scheme.Hom.ker_comp_of_isIso s.isoZero.hom ι

private theorem forall_le_ker_embeddingIntoAmbient_eq_boundary_get {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι) :
    ∀ t : ℕ, t ≤ s.length →
      ∀ hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length,
        AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
          ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ := by
  intro t
  induction t with
  | zero =>
      intro _ hjt
      simp only [List.get_eq_getElem] at hE ⊢
      rw [ker_embeddingIntoAmbientBlowupSequence_zero]
      simp only [BlowupSequenceData.boundary_zero, List.getElem_map, hE]
  | succ n ih =>
      intro hn hjt
      have hn' : n < s.length := hn
      have hjn : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E n).length := by
        rw [BlowupSequenceData.boundary_length]; omega
      rw [ker_embeddingIntoAmbientBlowupSequence_succ ι s hres hno hcen n hn', ih (le_of_lt hn') hjn]
      simp only [List.get_eq_getElem, BlowupSequenceData.boundary_succ]
      rw [List.getElem_append_left (by simpa using hjn), List.getElem_map]

theorem ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (s : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < s.length, ∀ T ∈ irreducibleComponents ↥(s.obj i), ¬T ⊆ ↑(s.center i).support)
    (E : List X.IdealSheafData) (j : ℕ) (hj : j < E.length)
    (hE : E.get ⟨j, hj⟩ = AlgebraicGeometry.Scheme.Hom.ker ι)
    (t : ℕ) (ht : t ≤ s.length)
    (hjt : j < ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).length) :
    AlgebraicGeometry.Scheme.Hom.ker (embeddingIntoAmbientBlowupSequence ι s hres hno hcen t) =
      ((ambientBlowupSequence ι s hres hno hcen).boundaryFrom E t).get ⟨j, hjt⟩ :=
  forall_le_ker_embeddingIntoAmbient_eq_boundary_get ι s hres hno hcen E j hj hE t ht hjt

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})

theorem ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr 0) =
      (T.boundary.get ⟨j, hj⟩).comap (pushedMarkedSeq hres hno T j hj s hpr hmk).isoZero.hom := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  exact h0

theorem ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr 0) =
      ((T.boundary.get ⟨j, hj⟩).comap
          (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom).comap
        ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0) := by
  have h0 := ker_embeddingIntoAmbientBlowupSequence_zero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h0
  have hA : (T.boundary.get ⟨j, hj⟩).comap
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom = T.boundary.get ⟨j, hj⟩ :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_id _
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0
      = (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
          (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).isoZero.hom := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism, BlowupSequenceData.toMarkedBlowupSequenceData_blowupMorphism,
      BlowupSequenceData.prepend_blowupMorphism_zero]
    exact rfl
  rw [hA, hB]
  exact h0

theorem isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hob : T.IsOrderBoundedByMult) (_hbal : T.IsBalanced hV.locallyOfFiniteType)
    (j : ℕ) (hj : j < T.boundary.length) (_hpre : containedComponentsIdeal T j hj = ⊤)
    (_hlow : (restrictToDivisor T j hj).IsAdmissible)
    [AlgebraicGeometry.IsNoetherian T.scheme] (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (t : ℕ) (ht : t ≤ s.length) :
    IsSmoothDivisor ((pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToSpec t)
      (AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t)) := by
  have hjt : j < ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).length := by
    rw [BlowupSequenceData.boundary_length]; omega
  have htS : t ≤ (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact ht
  have hker : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) =
      ((ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t).get
          ⟨j, hjt⟩ :=
    ker_embeddingIntoAmbientBlowupSequence_eq_boundary_get (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr T.boundary j hj
      (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _).symm t htS hjt
  have hbd : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_boundary, BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
    exact rfl
  have hpl : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).length =
      s.toSequenceOfBlowups.length := by
    have hh := ambientBlowupSequence_length (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length] at hh
    exact hh
  have htlen : t ≤ (pushedMarkedSeq hres hno T j hj s hpr hmk).toSequenceOfBlowups.length := by
    rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length, hpl]
    exact ht
  have hsnc := MarkedSequenceOfBlowups.inStrictNormalCrossingPosition_projectionToSpec_boundary effectiveCartierSupportContainsNoComponent hV
    (pushedMarkedSeq hres hno T j hj s hpr hmk) t htlen
  have key : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (ambientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr).boundaryFrom T.boundary t := by
    rw [hker]
    exact List.getElem_mem _
  have key2 : AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbientBlowupSequence (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t) ∈
      (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t := by
    rw [hbd]
    exact key
  exact ((inStrictNormalCrossingPosition_iff _ _).mp hsnc).1 _ key2

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DerivBalancedFactor
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_affineOpen_ideal_eq_top_of_not_mem_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (y : ↥X) (hy : y ∉ I.support) :
    ∃ V : X.affineOpens, y ∈ V.1 ∧ I.ideal V = ⊤ := by
  obtain ⟨U, hyU, -⟩ :=
    Scheme.exists_affineOpens_mem_le (X := X) (x := y) (U := ⊤) trivial
  have hny := hy
  rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hyU,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff] at hny
  push Not at hny
  obtain ⟨s, hs, hys⟩ := hny
  refine ⟨X.affineBasicOpen s, hys, ?_⟩
  let _ : Algebra Γ(X, U.1) Γ(X, X.basicOpen s) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom.toAlgebra
  have hloc : IsLocalization.Away s Γ(X, X.basicOpen s) := U.2.isLocalization_basicOpen s
  have hunit : IsUnit (algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) s) :=
    IsLocalization.map_units (M := Submonoid.powers s) Γ(X, X.basicOpen s)
      ⟨s, Submonoid.mem_powers s⟩
  have hmem : algebraMap Γ(X, U.1) Γ(X, X.basicOpen s) s ∈ I.ideal (X.affineBasicOpen s) := by
    rw [← I.map_ideal_basicOpen U s]
    exact Ideal.mem_map_of_mem _ hs
  exact Ideal.eq_top_of_isUnit_mem _ hmem hunit

theorem not_mem_support_of_mem_support_of_pow_mul {X : Scheme.{u}}
    (Z I I₀ : X.IdealSheafData) (m : ℕ) (hfac : I = Z ^ m * I₀)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) {x : ↥X} (hx : x ∈ Z.support) :
    x ∉ I₀.support := by
  intro hx0
  have hZ : stalkIdeal Z x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal Z x).mp hx
  have hI0 : stalkIdeal I₀ x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal I₀ x).mp hx0
  have hIle : stalkIdeal I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ (m + 1) := by
    rw [hfac, stalkIdeal_mul, stalkIdeal_pow, pow_succ]
    exact Ideal.mul_mono (Ideal.pow_right_mono hZ m) hI0
  have h1 := (le_orderAt_iff I x (m + 1)).mpr hIle
  have h3 : ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞) := le_trans h1 (hord x)
  have h4 : m + 1 ≤ m := by exact_mod_cast h3
  omega

theorem isDerivBalanced_of_pow_mul (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (Z I I₀ : X.IdealSheafData) (m : ℕ) (hfac : I = Z ^ m * I₀)
    (hord : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞)) (hbal : IsDerivBalanced k p I m) :
    IsDerivBalanced k p I₀ m := by
  refine (isDerivBalanced_iff k p I₀ m).mpr ?_
  intro i hi
  refine le_of_forall_exists_affineOpen ?_
  intro y
  by_cases hyZ : y ∈ Z.support
  · obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support I₀ y
      (not_mem_support_of_mem_support_of_pow_mul Z I I₀ m hfac hord hyZ)
    refine ⟨V, hyV, ?_⟩
    have htop : (I₀ ^ (m - i)).ideal V = ⊤ := by
      rw [Scheme.IdealSheafData.ideal_pow]
      show I₀.ideal V ^ (m - i) = ⊤
      rw [hV, ← Ideal.one_eq_top, one_pow]
    rw [htop]
    exact le_top
  · obtain ⟨V, hyV, hV⟩ := exists_affineOpen_ideal_eq_top_of_not_mem_support Z y hyZ
    refine ⟨V, hyV, ?_⟩
    have hIV : I.ideal V = I₀.ideal V := by
      rw [hfac, Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_pow]
      show Z.ideal V ^ m * I₀.ideal V = I₀.ideal V
      rw [hV, ← Ideal.one_eq_top, one_pow, one_mul]
    have hder : (derivIdealSheafIterate k p i I).ideal V
        = (derivIdealSheafIterate k p i I₀).ideal V := by
      rw [derivIdealSheafIterate_ideal, derivIdealSheafIterate_ideal, hIV]
    have hb : ((derivIdealSheafIterate k p i I).ideal V) ^ m ≤ (I.ideal V) ^ (m - i) := by
      have hb0 := Scheme.IdealSheafData.le_def.mp ((isDerivBalanced_iff k p I m).mp hbal i hi) V
      rwa [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow] at hb0
    rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_pow]
    show ((derivIdealSheafIterate k p i I₀).ideal V) ^ m ≤ (I₀.ideal V) ^ (m - i)
    rw [← hIV, ← hder]
    exact hb

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformPowers
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace BlowupSequenceData

private theorem pow_controlledTransform_le_pow_controlledTransform_of_dvd {X : Scheme.{u}} (d : BlowupSequenceData X)
    (K A : X.IdealSheafData) (m l : ℕ) (hbase : K ^ m ≤ A ^ (m - l)) (t : ℕ)
    (ht : t ≤ d.length)
    (hdivA : ∀ i < t, ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * B = (d.controlledTransform A m i).comap (d.map i))
    (hdivK : ∀ i < t, ∃ B : (d.obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ (m - l) * B =
        (d.controlledTransform K (m - l) i).comap (d.map i)) :
    d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l) := by
  revert ht hdivA hdivK
  induction t with
  | zero =>
      intro _ _ _
      rw [BlowupSequenceData.controlledTransform_zero, BlowupSequenceData.controlledTransform_zero,
        ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_pow]
      exact Scheme.IdealSheafData.comap_mono (f := d.isoZero.hom) hbase
  | succ n ih =>
      intro ht hdivA hdivK
      have hn : n < d.length := lt_of_lt_of_le (Nat.lt_succ_self n) ht
      have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (d.map n) (d.center n)) :=
        isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal (d.isBlowup n hn)
      exact pow_controlledTransform_le_pow_controlledTransform_succ d K A m l n hcart
        (hdivK n (Nat.lt_succ_self n)) (hdivA n (Nat.lt_succ_self n))
        (ih (le_of_lt hn) (fun i hi => hdivA i (Nat.lt_succ_of_lt hi))
          (fun i hi => hdivK i (Nat.lt_succ_of_lt hi)))

theorem exists_pow_mul_eq_comap_controlledTransform {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (d : BlowupSequenceData X) (p : X ⟶ Spec (CommRingCat.of k)) (A : X.IdealSheafData) (n t : ℕ)
    (ht : t < d.length) [AlgebraicGeometry.IsLocallyNoetherian (d.obj (t + 1))]
    [AlgebraicGeometry.Smooth (d.projectionToBase t ≫ p)]
    (E : List (d.obj t).IdealSheafData)
    (hE : HasStrictNormalCrossingsWith (d.projectionToBase t ≫ p) (d.center t) E)
    (hord : ↑(d.center t).support ⊆ orderAtLeastLocus (d.controlledTransform A n t) n) :
    ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ n * B = (d.controlledTransform A n t).comap (d.map t) := by
  have hle : d.controlledTransform A n t ≤ d.center t ^ n :=
    le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase t ≫ p) (d.center t) (d.controlledTransform A n t) E hE n hord
  obtain ⟨B, hB, -⟩ :=
    existsUnique_pow_mul_eq_comap_of_isBlowupAlongIdealSheaf (d.map t) (d.center t) (d.controlledTransform A n t) n
      (d.isBlowup t ht) hle
  exact ⟨B, hB⟩

end BlowupSequenceData

namespace DivisorReduction

theorem pow_ambientDerivIdeal_le_pow_controlledTransform
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (j : ℕ) (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hbal : IsDerivBalanced T.base T.structMap I₀ T.mult)
    (l : ℕ) (hl : l < T.mult) (t : ℕ) (ht : t ≤ s.length)
    (hdivA : ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ T.mult * B =
        ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i))
    (hdivD : ∀ i < t, ∃ B : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (i + 1)).IdealSheafData,
      Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center i) ^ (T.mult - l) * B =
        (ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l i).comap
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map i)) :
    ambientDerivIdeal hres hno T j hj I₀ E₀ s hpr l t ^ T.mult ≤
      (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform I₀ T.mult t ^ (T.mult - l) := by
  have ht' : t ≤ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).length := by
    rw [ambientBlowupSeq_length hres hno T j hj I₀ E₀ s hpr]
    exact ht
  exact BlowupSequenceData.pow_controlledTransform_le_pow_controlledTransform_of_dvd (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr)
    (derivIdealSheafIterate T.base T.structMap l I₀) I₀ T.mult l
    (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hl) t ht' hdivA hdivD

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusComparison
section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealSheafClosedSubscheme
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

private theorem comp_app_apply {X Y Z : Scheme.{u}} (u : X ⟶ Y) (q : Y ⟶ Z) (U : Z.Opens)
    (a : Γ(Z, U)) : ((u ≫ q).app U).hom a = (u.app (q ⁻¹ᵁ U)).hom ((q.app U).hom a) := by
  have h : (u ≫ q).app U = q.app U ≫ u.app (q ⁻¹ᵁ U) := Scheme.Hom.comp_app u q U
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) a

private theorem comap_le_of_map_ideal_le {S X : Scheme.{u}} (ι : S ⟶ X) [IsAffineHom ι]
    (L : X.IdealSheafData) (D : S.IdealSheafData)
    (h : ∀ U : X.affineOpens, Ideal.map (ι.app (U : X.Opens)).hom (L.ideal U)
        ≤ D.ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩) :
    L.comap ι ≤ D := by
  have key : ∀ (U : X.affineOpens), L.ideal U
      ≤ RingHom.ker ((D.subschemeι ≫ ι).app (U : X.Opens)).hom := by
    intro U a ha
    have h1 := h U (Ideal.mem_map_of_mem _ ha)
    have h2 : (Scheme.Hom.ker D.subschemeι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩
        = RingHom.ker (D.subschemeι.app (ι ⁻¹ᵁ (U : X.Opens))).hom := by
      rw [Scheme.Hom.ker_apply]
    rw [Scheme.IdealSheafData.ker_subschemeι] at h2
    rw [h2] at h1
    refine RingHom.mem_ker.mpr ?_
    rw [comp_app_apply]
    exact RingHom.mem_ker.mp h1
  have hle : L ≤ Scheme.Hom.ker (D.subschemeι ≫ ι) := by
    unfold Scheme.Hom.ker
    exact Scheme.IdealSheafData.le_ofIdeals_iff.mpr key
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
  exact hle

private theorem derivIdealIterate_mono_of_le (k : Type u) [CommRing k] {T : Type u} [CommRing T]
    [Algebra k T] (r : ℕ) {I J : Ideal T} (h : I ≤ J) :
    derivIdealIterate k r I ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact h
  | succ r ih =>
      rw [derivIdealIterate_succ, derivIdealIterate_succ]
      exact derivIdeal_mono k ih

private theorem app_comp_sectionsAlgebraMap (k : Type u) [CommRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens) :
    (ι.app U).hom.comp (sectionsAlgebraMap k p U) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) := by
  have happ : ι.appLE U (ι ⁻¹ᵁ U) le_rfl = ι.app U := Scheme.Hom.appLE_eq_app ι
  have hc : p.appLE ⊤ U (le_preimage_top k p U) ≫ ι.appLE U (ι ⁻¹ᵁ U) le_rfl
      = (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) :=
    Scheme.Hom.appLE_comp_appLE ι p ⊤ U (ι ⁻¹ᵁ U) (le_preimage_top k p U) le_rfl
  have hmor : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (le_preimage_top k p U))
        ≫ ι.app U
      = (Scheme.ΓSpecIso (CommRingCat.of k)).inv
        ≫ (ι ≫ p).appLE ⊤ (ι ⁻¹ᵁ U) (le_preimage_top k (ι ≫ p) (ι ⁻¹ᵁ U)) := by
    rw [Category.assoc, ← happ, hc]
  rw [sectionsAlgebraMap_eq k p U, sectionsAlgebraMap_eq k (ι ≫ p) (ι ⁻¹ᵁ U)]
  exact congrArg CommRingCat.Hom.hom hmor

private theorem app_sectionsAlgebraMap (k : Type u) [CommRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (ι : S ⟶ X) (U : X.Opens) (a : k) :
    (ι.app U).hom (sectionsAlgebraMap k p U a) = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ U) a :=
  DFunLike.congr_fun (app_comp_sectionsAlgebraMap k p ι U) a

end FunctorialResolution.EmbeddedResolution
section -- restored from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.LogDerivativeIdealQuotient
namespace FunctorialResolution.EmbeddedResolution

variable (k : Type*) [CommRing k] {S T : Type*} [CommRing S] [CommRing T]
  [Algebra k S] [Algebra k T]

theorem map_logDerivIdeal_ker_le_derivIdeal_map (f : S →ₐ[k] T)
    (hf : Function.Surjective f) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdeal k (RingHom.ker f.toRingHom) J)
      ≤ derivIdeal k (Ideal.map f.toRingHom J) := by
  rw [Ideal.map_le_iff_le_comap, logDerivIdeal_le_iff]
  constructor
  · intro x hx
    rw [Ideal.mem_comap]
    exact le_derivIdeal k (Ideal.map f.toRingHom J) (Ideal.mem_map_of_mem f.toRingHom hx)
  · intro D hD x hx
    have hD' : ∀ s ∈ RingHom.ker f.toRingHom, D s ∈ RingHom.ker f.toRingHom :=
      (mem_tangentDerivations k (RingHom.ker f.toRingHom) D).mp hD
    have hmem : f x ∈ Ideal.map f.toRingHom J := Ideal.mem_map_of_mem f.toRingHom hx
    have h2 := derivation_apply_mem_derivIdeal k (Ideal.map f.toRingHom J)
      (derivationOfSurjective f hf D hD') hmem
    rw [derivationOfSurjective_apply] at h2
    rw [Ideal.mem_comap]
    exact h2

theorem map_logDerivIdealIterate_ker_le_derivIdealIterate_map (f : S →ₐ[k] T)
    (hf : Function.Surjective f) (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k (RingHom.ker f.toRingHom) r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  induction r with
  | zero => exact le_rfl
  | succ r ih =>
      rw [logDerivIdealIterate_succ, derivIdealIterate_succ]
      exact (map_logDerivIdeal_ker_le_derivIdeal_map k f hf _).trans (derivIdeal_mono k ih)

theorem map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker (f : S →ₐ[k] T)
    (hf : Function.Surjective f) {P : Ideal S} (hP : P = RingHom.ker f.toRingHom)
    (r : ℕ) (J : Ideal S) :
    Ideal.map f.toRingHom (logDerivIdealIterate k P r J)
      ≤ derivIdealIterate k r (Ideal.map f.toRingHom J) := by
  subst hP
  exact map_logDerivIdealIterate_ker_le_derivIdealIterate_map k f hf r J

end FunctorialResolution.EmbeddedResolution
end
namespace FunctorialResolution.EmbeddedResolution

private theorem map_logDerivIdealSheafIterate_ideal_le
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) (U : X.affineOpens) :
    Ideal.map (ι.app (U : X.Opens)).hom ((logDerivIdealSheafIterate k p ι.ker r A).ideal U)
      ≤ (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι)).ideal
          ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
  have hcomm : ∀ a : k,
      (ι.app (U : X.Opens)).hom
          (@algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens)) a)
        = @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) a := by
    intro a
    have e1 : @algebraMap k _ _ _ (sectionsAlgebra k p (U : X.Opens))
        = sectionsAlgebraMap k p (U : X.Opens) :=
      algebraMap_sectionsAlgebra k p (U : X.Opens)
    have e2 : @algebraMap k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
        = sectionsAlgebraMap k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)) :=
      algebraMap_sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))
    rw [e1, e2]
    exact app_sectionsAlgebraMap k p ι (U : X.Opens) a
  have hmapLE : ∀ (V : S.affineOpens) (e : (V : S.Opens) ≤ ι ⁻¹ᵁ (U : X.Opens)),
      Ideal.map (ι.appLE (U : X.Opens) (V : S.Opens) e).hom (A.ideal U)
        ≤ (A.comap ι).ideal V := by
    intro V e
    apply Scheme.IdealSheafData.map_appLE_le_comap_ideal
  have hmap : Ideal.map (ι.app (U : X.Opens)).hom (A.ideal U)
      ≤ (A.comap ι).ideal ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ := by
    rw [Scheme.Hom.app_eq_appLE]
    exact hmapLE ⟨ι ⁻¹ᵁ (U : X.Opens), U.2.preimage ι⟩ le_rfl
  have halg := @map_logDerivIdealIterate_le_derivIdealIterate_map_of_eq_ker k _ _ _ _ _
      (sectionsAlgebra k p (U : X.Opens))
      (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens)))
      (@AlgHom.mk k _ _ _ _ _ (sectionsAlgebra k p (U : X.Opens))
        (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) (ι.app (U : X.Opens)).hom hcomm)
      (Scheme.Hom.app_surjective ι (U : X.Opens) U.2) _ rfl r (A.ideal U)
  rw [logDerivIdealSheafIterate_ideal, Scheme.Hom.ker_apply, derivIdealSheafIterate_ideal]
  refine le_trans halg ?_
  exact @derivIdealIterate_mono_of_le k _ _ _ (sectionsAlgebra k (ι ≫ p) (ι ⁻¹ᵁ (U : X.Opens))) r _ _
    hmap

private theorem logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  comap_le_of_map_ideal_le ι (logDerivIdealSheafIterate k p ι.ker r A)
    (derivIdealSheafIterate k (ι ≫ p) r (A.comap ι))
    (map_logDerivIdealSheafIterate_ideal_le k p ι A r)

theorem comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate
    (k : Type u) [CommRing k] [IsNoetherianRing k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (ι : S ⟶ X) [IsClosedImmersion ι] [LocallyOfFiniteType (ι ≫ p)]
    (A : X.IdealSheafData) (r : ℕ) :
    (logDerivIdealSheafIterate k p ι.ker r A).comap ι
      ≤ derivIdealSheafIterate k (ι ≫ p) r (A.comap ι) :=
  logDerivIdealSheafIterate_comap_le_derivIdealSheafIterate k p ι A r

end FunctorialResolution.EmbeddedResolution
end

universe u

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

section

variable (k : Type u) [Field k] [CharZero k] {X S : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (ι : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι]
    [AlgebraicGeometry.Smooth (ι ≫ p)]

theorem base_mem_orderAtLeastLocus_of_mem_comap
    (m : ℕ) (hm : 1 ≤ m) (A : X.IdealSheafData) (K : ℕ → X.IdealSheafData)
    (hdom : derivIdealSheafIterate k p (m - 1) A
      ≤ ⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l))
    (hbal : ∀ l < m, K l ^ m ≤ A ^ (m - l))
    (y : S) (hy : y ∈ orderAtLeastLocus (A.comap ι) m) :
    ι.base y ∈ orderAtLeastLocus A m := by
  have hsupp : ι.base y ∈
      (⨆ l ≤ m - 1, logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)).support := by
    refine mem_support_iSup_le_nat (m - 1)
      (fun l => logDerivIdealSheafIterate k p ι.ker (m - 1 - l) (K l)) (ι.base y) ?_
    intro l hl
    have hlm : l < m := by omega
    have hml : 1 ≤ m - l := by omega
    apply (Scheme.IdealSheafData.mem_support_comap).mp
    refine Scheme.IdealSheafData.support_antitone
      (comap_logDerivIdealSheafIterate_ker_le_derivIdealSheafIterate k p ι (K l) (m - 1 - l)) ?_
    have hpow : ((K l).comap ι) ^ m ≤ (A.comap ι) ^ (m - l) := by
      have h1 : (K l ^ m).comap ι ≤ (A ^ (m - l)).comap ι :=
        Scheme.IdealSheafData.comap_mono ι (hbal l hlm)
      rwa [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow] at h1
    have hy2 : y ∈ orderAtLeastLocus ((K l).comap ι) (m - l) :=
      orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le k (ι ≫ p) ((K l).comap ι) (A.comap ι) l m hlm hpow hy
    have hstep := support_derivIdealSheafIterate_eq_orderAtLeastLocus k (ι ≫ p) ((K l).comap ι) hml
    rw [← hstep] at hy2
    have hexp : m - 1 - l = m - l - 1 := by omega
    rw [hexp]
    exact hy2
  rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus k p A hm]
  exact Scheme.IdealSheafData.support_antitone hdom hsupp

end

end FunctorialResolution.EmbeddedResolution
end
