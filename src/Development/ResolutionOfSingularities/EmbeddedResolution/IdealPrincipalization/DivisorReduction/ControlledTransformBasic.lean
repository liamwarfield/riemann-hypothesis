module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsEraseMember
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem iSup_le_zero_nat {Y : Scheme.{u}} (G : ℕ → Y.IdealSheafData) :
    (⨆ l, ⨆ _ : l ≤ 0, G l) = G 0 := by
  simp only [Nat.le_zero]
  exact iSup_iSup_eq_left

namespace BlowupSequenceData

theorem controlledTransform_congr {X : Scheme.{u}} (d : BlowupSequenceData X) (I I' : X.IdealSheafData)
    (h : I.comap (d.projectionToBase 0) = I'.comap (d.projectionToBase 0)) (m t : ℕ) :
    d.controlledTransform I m t = d.controlledTransform I' m t := by
  induction t with
  | zero =>
    rw [controlledTransform_zero, controlledTransform_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [controlledTransform_succ, controlledTransform_succ, ih]

theorem boundary_congr {X : Scheme.{u}} (d : BlowupSequenceData X) (E E' : List X.IdealSheafData)
    (h : List.map (fun D => D.comap (d.projectionToBase 0)) E = List.map (fun D => D.comap (d.projectionToBase 0)) E')
    (t : ℕ) :
    d.boundaryFrom E t = d.boundaryFrom E' t := by
  induction t with
  | zero =>
    rw [boundary_zero, boundary_zero, ← d.projectionToBase_zero]
    exact h
  | succ t ih =>
    rw [boundary_succ, boundary_succ, ih]

theorem pow_controlledTransform_le_pow_controlledTransform_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (K A : X.IdealSheafData) (m l t : ℕ)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Blowup.exceptionalIdeal (d.map t) (d.center t)))
    (hK : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ (m - l) * B =
        (d.controlledTransform K (m - l) t).comap (d.map t))
    (hA : ∃ B : (d.obj (t + 1)).IdealSheafData,
      Blowup.exceptionalIdeal (d.map t) (d.center t) ^ m * B = (d.controlledTransform A m t).comap (d.map t))
    (hle : d.controlledTransform K (m - l) t ^ m ≤ d.controlledTransform A m t ^ (m - l)) :
    d.controlledTransform K (m - l) (t + 1) ^ m ≤ d.controlledTransform A m (t + 1) ^ (m - l) := by
  have hpowMul := d.pow_exceptionalIdeal_mul_controlledTransform_succ K (m - l) t hK
  have hAs := d.pow_exceptionalIdeal_mul_controlledTransform_succ A m t hA
  have hcomap : (d.controlledTransform K (m - l) t ^ m).comap (d.map t) ≤
      (d.controlledTransform A m t ^ (m - l)).comap (d.map t) :=
    Scheme.IdealSheafData.comap_mono _ hle
  rw [Scheme.IdealSheafData.comap_pow, Scheme.IdealSheafData.comap_pow, ← hpowMul, ← hAs,
    mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (m - l) m] at hcomap
  exact (hcart.pow (m * (m - l))).le_of_mul_le_mul hcomap

end BlowupSequenceData

theorem orderAtLeastLocus_subset_orderAtLeastLocus_of_pow_le (k : Type u) [Field k] [CharZero k]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (K A : Y.IdealSheafData) (l m : ℕ) (hlm : l < m) (h : K ^ m ≤ A ^ (m - l)) :
    orderAtLeastLocus A m ⊆ orderAtLeastLocus K (m - l) := by
  intro x hx
  rw [mem_orderAtLeastLocus_iff] at hx
  rw [mem_orderAtLeastLocus_iff]
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by omega)
  have hml : 1 ≤ m - l := by omega
  have h1 : orderAt (A ^ (m - l)) x ≤ orderAt (K ^ m) x := orderAt_le_of_le h x
  rw [orderAt_pow k p A (m - l) x, orderAt_pow k p K m x] at h1
  have h2 : ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x :=
    (natCast_mul_le_mul_iff hml m (orderAt A x)).mpr hx
  have h3 : ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) * orderAt K x := by
    calc ((m : ℕ) : ℕ∞) * ((m - l : ℕ) : ℕ∞)
        = ((m - l : ℕ) : ℕ∞) * ((m : ℕ) : ℕ∞) := mul_comm _ _
      _ ≤ ((m - l : ℕ) : ℕ∞) * orderAt A x := h2
      _ ≤ ((m : ℕ) : ℕ∞) * orderAt K x := h1
  exact (natCast_mul_le_mul_iff hm (m - l) (orderAt K x)).mp h3

theorem comap_iSup_le_nat {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) (n : ℕ) (G : ℕ → Y.IdealSheafData) :
    (⨆ l ≤ n, G l).comap f = ⨆ l ≤ n, (G l).comap f := by
  induction n with
  | zero => rw [iSup_le_zero_nat, iSup_le_zero_nat]
  | succ n ih =>
    rw [Nat.iSup_le_succ, Nat.iSup_le_succ, Scheme.IdealSheafData.comap_sup, ih]

theorem mem_support_iSup_le_nat {Y : Scheme.{u}} (n : ℕ) (G : ℕ → Y.IdealSheafData) (y : Y)
    (h : ∀ l ≤ n, y ∈ (G l).support) : y ∈ (⨆ l ≤ n, G l).support := by
  revert h
  induction n with
  | zero =>
    intro h
    rw [iSup_le_zero_nat]
    exact h 0 le_rfl
  | succ n ih =>
    intro h
    rw [Nat.iSup_le_succ, mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_sup]
    refine sup_le ?_ ?_
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp
        (ih fun l hl => h l (hl.trans (Nat.le_succ n)))
    · exact (mem_support_iff_stalkIdeal_le_maximalIdeal _ _).mp (h (n + 1) le_rfl)

namespace DivisorReduction

variable (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (I₀ : T.scheme.IdealSheafData)
    (E₀ : List T.scheme.IdealSheafData) (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)

noncomputable abbrev divisorEmbedding : (restrictToBoundaryDivisor T j hj I₀ E₀).scheme ⟶ T.scheme :=
  (T.boundary.get ⟨j, hj⟩).subschemeι

noncomputable abbrev ambientBlowupSeqStructureMorphism (t : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t ⟶ Spec (CommRingCat.of T.base) :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t ≫ T.structMap

noncomputable abbrev ambientDerivIdeal [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    (l t : ℕ) : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj t).IdealSheafData :=
  (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).controlledTransform
    (derivIdealSheafIterate T.base T.structMap l I₀) (T.mult - l) t

theorem embeddingIntoAmbient_comp_projectionToBase (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀ := by
  induction t with
  | zero =>
    have h0 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero = Iso.refl T.scheme :=
      ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr
    rw [BlowupSequenceData.projectionToBase_zero, h0, embeddingIntoAmbient_zero, MarkedSequenceOfBlowups.projectionToBase_zero, Iso.refl_hom]
    exact Category.comp_id _
  | succ t ih =>
    have hmap := embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr t
    have hstruct : s.transitionMapSucc t ≫ s.projectionToBase t = s.projectionToBase (t + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact SequenceOfBlowups.transitionMap_comp_projectionToBase s.toSequenceOfBlowups (Nat.le_succ t)
    have e1 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase (t + 1) =
        embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      congrArg (fun f => embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫ f)
        (BlowupSequenceData.projectionToBase_succ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr) t)
    have e2 : embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      (Category.assoc _ _ _).symm
    have e3 : (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (t + 1) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map t) ≫
            (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t :=
      congrArg (fun f => f ≫ (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) hmap
    have e4 : (s.transitionMapSucc t ≫ embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
        s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) :=
      Category.assoc _ _ _
    have e5 : s.transitionMapSucc t ≫ (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
          (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t) =
        s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) :=
      congrArg (fun f => s.transitionMapSucc t ≫ f) ih
    have e6 : s.transitionMapSucc t ≫ (s.projectionToBase t ≫ divisorEmbedding T j hj I₀ E₀) =
        (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ :=
      (Category.assoc _ _ _).symm
    have e7 : (s.transitionMapSucc t ≫ s.projectionToBase t) ≫ divisorEmbedding T j hj I₀ E₀ =
        s.projectionToBase (t + 1) ≫ divisorEmbedding T j hj I₀ E₀ :=
      congrArg (fun f => f ≫ divisorEmbedding T j hj I₀ E₀) hstruct
    exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem noetherianSpace_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme := by
  have := hV.isNoetherian
  exact (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding
    (T.boundary.get ⟨j, hj⟩).subschemeι).toIsEmbedding.toIsInducing.noetherianSpace

abbrev divisorComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x : ↥(T.boundary.get ⟨j, hj⟩).subscheme |
    connectedComponent x ⊆
      ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult}

theorem isClosed_divisorComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsClosed (divisorComponentsInOrderLocus T j hj) := by
  have := noetherianSpace_boundary_subscheme T hV j hj
  exact TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
    ↥(T.boundary.get ⟨j, hj⟩).subscheme
    (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult)

theorem containedComponentsIdeal_eq_openSubschemeKer (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.containedComponentsIdeal T j hj =
      openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩ :=
  DivisorReduction.containedComponentsIdeal_eq_ker T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : ¬ IsOpen (divisorComponentsInOrderLocus T j hj)) :
    DivisorReduction.containedComponentsIdeal T j hj = ⊤ :=
  DivisorReduction.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

theorem isSmoothDivisor_boundary_get (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  exact ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem

theorem support_containedComponentsIdeal_subset_orderAtLeastLocus (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) ⊆ orderAtLeastLocus T.ideal T.mult := by
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hcl : IsClosed (((⟨divisorComponentsInOrderLocus T j hj, h⟩ :
        (T.boundary.get ⟨j, hj⟩).subscheme.Opens) :
          Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)) := isClosed_divisorComponentsInOrderLocus T hV j hj
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
      support_openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩ hcl]
    rintro y ⟨x, hx, rfl⟩
    have hx' : connectedComponent x ⊆
        ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult := hx
    exact hx' mem_connectedComponent
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    intro x hx
    have hx' : x ∈ (⊤ : T.scheme.IdealSheafData).support := hx
    rw [mem_support_iff_stalkIdeal_ne_top] at hx'
    exact absurd (stalkIdeal_top x) hx'

theorem smooth_subschemeι_containedComponentsIdeal_comp (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Smooth ((DivisorReduction.containedComponentsIdeal T j hj).subschemeι ≫ T.structMap) := by
  have hsmp : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hsm : AlgebraicGeometry.Smooth
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
      ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).1
        (isSmoothDivisor_boundary_get T hV j hj)).2
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
    exact smooth_subschemeι_openSubschemeKer_comp (T.boundary.get ⟨j, hj⟩)
      ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj) T.structMap
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    exact ((isSmoothDivisor_iff T.structMap (⊤ : T.scheme.IdealSheafData)).1
      (isSmoothDivisor_top T.structMap)).2

theorem exists_etaleChart_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (x : ↥T.scheme)
    (hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support) :
    ∃ (U : T.scheme.Opens) (_ : x ∈ U) (n : ℕ) (c : EtaleChart T.structMap U n)
      (a : ℕ → Option (Fin n)) (b : Fin n),
      a j = some b ∧
      (∀ (i : ℕ) (hi : i < T.boundary.length), a i = none →
        restrictIdeal (T.boundary.get ⟨i, hi⟩) U = ⊤) ∧
      (∀ (i : ℕ) (hi : i < T.boundary.length) (t : Fin n), a i = some t →
        restrictIdeal (T.boundary.get ⟨i, hi⟩) U = c.coordIdeal {t}) ∧
      (∀ (i i' : ℕ), i < T.boundary.length → i' < T.boundary.length →
        ∀ t : Fin n, a i = some t → a i' = some t → i = i') ∧
      restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) U = c.coordIdeal {b} := by
  classical
  by_cases hopen : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hWclosed : IsClosed (divisorComponentsInOrderLocus T j hj) := isClosed_divisorComponentsInOrderLocus T hV j hj
    have hpre : DivisorReduction.containedComponentsIdeal T j hj =
        openSubschemeKer (T.boundary.get ⟨j, hj⟩)
          (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) :=
      containedComponentsIdeal_eq_openSubschemeKer T j hj hopen
    have h1 : x ∈ ((openSubschemeKer (T.boundary.get ⟨j, hj⟩)
        (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ :
          (T.boundary.get ⟨j, hj⟩).subscheme.Opens)).support : Set ↥T.scheme) := by
      rw [← hpre]
      exact hx
    rw [support_openSubschemeKer (T.boundary.get ⟨j, hj⟩)
      (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) hWclosed] at h1
    obtain ⟨U₀, hxU₀, hU₀⟩ := exists_opens_preimage_subschemeι_le (T.boundary.get ⟨j, hj⟩)
      (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) x h1
    obtain ⟨U₁, hxU₁, n, c, a, hinj, hnone, hsome⟩ :=
      (((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).2 x).exists_etaleChart
    have hUle : U₀ ⊓ U₁ ≤ U₁ := inf_le_right
    have hxU : x ∈ U₀ ⊓ U₁ := ⟨hxU₀, hxU₁⟩
    have hpreU : ((T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹ᵁ (U₀ ⊓ U₁)) ≤
        (⟨divisorComponentsInOrderLocus T j hj, hopen⟩ : (T.boundary.get ⟨j, hj⟩).subscheme.Opens) := by
      intro y hy
      exact hU₀ hy.1
    have hrestr : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (U₀ ⊓ U₁) =
        restrictIdeal (T.boundary.get ⟨j, hj⟩) (U₀ ⊓ U₁) := by
      rw [hpre]
      exact restrictIdeal_openSubschemeKer_of_preimage_le _ _ hWclosed _ hpreU
    have hajne : a j ≠ none := by
      intro haj
      have h2 : restrictIdeal (T.boundary.get ⟨j, hj⟩) U₁ = ⊤ := by
        simpa only [List.get_eq_getElem] using hnone j hj haj
      have h3 : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj) (U₀ ⊓ U₁) = ⊤ := by
        rw [hrestr]
        exact restrictIdeal_eq_top_of_le _ hUle h2
      exact notMem_support_of_restrictIdeal_eq_top _ _ x hxU h3 hx
    obtain ⟨b, hb⟩ : ∃ b : Fin n, a j = some b := by
      cases h : a j with
      | none => exact absurd h hajne
      | some b => exact ⟨b, rfl⟩
    refine ⟨U₀ ⊓ U₁, hxU, n, c.restrict hUle, a, b, hb, ?_, ?_, ?_, ?_⟩
    · intro i hi hai
      refine restrictIdeal_eq_top_of_le _ hUle ?_
      simpa only [List.get_eq_getElem] using hnone i hi hai
    · intro i hi t hai
      refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {t} ?_
      simpa only [List.get_eq_getElem] using hsome i hi t hai
    · intro i i' hi hi' t h4 h5
      exact hinj i hi i' hi' t h4 h5
    · rw [hrestr]
      refine restrictIdeal_eq_restrict_coordIdeal_of_le hUle c _ {b} ?_
      simpa only [List.get_eq_getElem] using hsome j hj b hb
  · exfalso
    rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj hopen] at hx
    exact (mem_support_iff_stalkIdeal_ne_top (⊤ : T.scheme.IdealSheafData) x).1 hx
      (stalkIdeal_top x)

theorem isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (DivisorReduction.containedComponentsIdeal T j hj) := by
  have hsmp : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h]
    exact isLocallyGeneratedByNonZeroDivisor_openSubschemeKer (T.boundary.get ⟨j, hj⟩)
      ⟨divisorComponentsInOrderLocus T j hj, h⟩ (isClosed_divisorComponentsInOrderLocus T hV j hj)
      (((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).1
        (isSmoothDivisor_boundary_get T hV j hj)).1)
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen T j hj h]
    exact ((isSmoothDivisor_iff T.structMap (⊤ : T.scheme.IdealSheafData)).1
      (isSmoothDivisor_top T.structMap)).1

theorem hasStrictNormalCrossingsWith_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    HasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.boundary := by
  refine hasStrictNormalCrossingsWith_of_forall_exists_etaleChart ?_
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZ⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  refine ⟨U, hxU, n, c, a, {b}, ?_, ?_, ?_, hZ⟩
  · intro i hi i' hi' t hti hti'
    exact hinj i i' hi hi' t hti hti'
  · intro i hi hni
    exact hnone i hi hni
  · intro i hi t hti
    exact hsome i hi t hti

theorem isBlowupAlongIdealSheaf_id_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) :=
  Blowup.isBlowupAlongIdealSheaf_id_of_isLocallyGeneratedByNonZeroDivisor _ (isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj)

theorem exists_mul_pow_containedComponentsIdeal_eq_ideal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    ∃ J : T.scheme.IdealSheafData,
      DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * J = T.ideal := by
  have := hV.isNoetherian
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hle : T.ideal ≤ DivisorReduction.containedComponentsIdeal T j hj ^ T.mult :=
    le_pow_of_hasStrictNormalCrossingsWith T.structMap (DivisorReduction.containedComponentsIdeal T j hj) T.ideal T.boundary
      (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj) T.mult (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
  exact Blowup.IsLocallyGeneratedByNonZeroDivisor.exists_mul_eq
    ((isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj).pow T.mult) hle

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.StrictTransformRestriction
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem ker_le_ker_of_comp_eq {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    (h : e ≫ g = f) : g.ker ≤ f.ker := by
  subst h
  exact Scheme.Hom.le_ker_comp e g

theorem comap_strictTransform_of_iso {X X₁ X₁' : Scheme.{u}} (π : X₁ ⟶ X)
    (f : X₁' ≅ X₁) (Z D : X.IdealSheafData) (_hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (Z.comap π))
    [QuasiCompact (strictTransformι π Z D)]
    [QuasiCompact (strictTransformι (f.hom ≫ π) Z D)] :
    (Blowup.strictTransform π Z D).comap f.hom = Blowup.strictTransform (f.hom ≫ π) Z D := by
  have hRHS : Blowup.strictTransform (f.hom ≫ π) Z D
      = Blowup.strictTransform f.hom (Z.comap π) (D.comap π) :=
    strictTransform_eq_of_comap_eq (f.hom ≫ π) f.hom Z D (Z.comap π) (D.comap π)
      (by rw [Scheme.IdealSheafData.comap_comp])
      (by rw [Scheme.IdealSheafData.comap_comp])
  obtain ⟨m₀, hiso, hm₀⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso f.hom (D.comap π)
  have := hiso
  have hsupp : ((Z.comap π).comap f.hom).support.compl
      = f.hom ⁻¹ᵁ (Z.comap π).support.compl := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have h1 : m₀ ⁻¹ᵁ strictTransformOpens π Z D
      = ((D.comap π).comap f.hom).subschemeι ⁻¹ᵁ (f.hom ⁻¹ᵁ (Z.comap π).support.compl) :=
    congrArg (fun w => w ⁻¹ᵁ (Z.comap π).support.compl) hm₀
  have hV' : strictTransformOpens f.hom (Z.comap π) (D.comap π)
      = m₀ ⁻¹ᵁ strictTransformOpens π Z D := by
    rw [h1]
    exact congrArg (fun W => ((D.comap π).comap f.hom).subschemeι ⁻¹ᵁ W) hsupp
  have hm₀2 : m₀ ≫ ((D.comap π).subschemeι ≫ inv f.hom)
      = ((D.comap π).comap f.hom).subschemeι := by
    rw [← Category.assoc, hm₀, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hm₀3 : inv m₀ ≫ ((D.comap π).comap f.hom).subschemeι
      = (D.comap π).subschemeι ≫ inv f.hom := by
    rw [IsIso.inv_comp_eq, hm₀2]
  have hinvle : strictTransformOpens π Z D
      ≤ inv m₀ ⁻¹ᵁ strictTransformOpens f.hom (Z.comap π) (D.comap π) := by
    rw [hV']
    have h3 : inv m₀ ⁻¹ᵁ (m₀ ⁻¹ᵁ strictTransformOpens π Z D)
        = (inv m₀ ≫ m₀) ⁻¹ᵁ strictTransformOpens π Z D := rfl
    rw [h3, IsIso.inv_hom_id]
    simp
  have hfac1 : (Scheme.Hom.resLE m₀ (strictTransformOpens π Z D)
        (strictTransformOpens f.hom (Z.comap π) (D.comap π)) (le_of_eq hV'))
      ≫ (strictTransformι π Z D ≫ inv f.hom)
      = strictTransformι f.hom (Z.comap π) (D.comap π) := by
    rw [strictTransformι_eq_ι_comp_subschemeι π Z D,
      strictTransformι_eq_ι_comp_subschemeι f.hom (Z.comap π) (D.comap π),
      ← Category.assoc, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc,
      Category.assoc, hm₀2]
  have hfac2 : (Scheme.Hom.resLE (inv m₀)
        (strictTransformOpens f.hom (Z.comap π) (D.comap π))
        (strictTransformOpens π Z D) hinvle)
      ≫ strictTransformι f.hom (Z.comap π) (D.comap π)
      = strictTransformι π Z D ≫ inv f.hom := by
    rw [strictTransformι_eq_ι_comp_subschemeι f.hom (Z.comap π) (D.comap π),
      strictTransformι_eq_ι_comp_subschemeι π Z D, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
      Category.assoc, hm₀3, Category.assoc]
  have hcomp : (strictTransformι π Z D ≫ inv f.hom) ≫ f.hom
      = strictTransformι π Z D := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have : QuasiCompact (strictTransformι π Z D ≫ inv f.hom) := inferInstance
  have : QuasiCompact ((strictTransformι π Z D ≫ inv f.hom) ≫ f.hom) := by
    rw [hcomp]
    infer_instance
  have hL := Blowup.comap_ker_comp_of_isOpenImmersion
    (strictTransformι π Z D ≫ inv f.hom) f.hom
  rw [hcomp] at hL
  rw [hRHS, strictTransform_eq_ker_strictTransformι π Z D, hL,
    strictTransform_eq_ker_strictTransformι f.hom (Z.comap π) (D.comap π)]
  exact le_antisymm (ker_le_ker_of_comp_eq _ _ _ hfac1) (ker_le_ker_of_comp_eq _ _ _ hfac2)

theorem exists_iso_subscheme_of_ker_eq_strictTransform {X X₁ S S₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι)) :
    ∃ (e : S ≅ (Scheme.Hom.ker ι).subscheme)
      (e₁ : S₁ ≅ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subscheme),
      e.hom ≫ (Scheme.Hom.ker ι).subschemeι = ι ∧
        e₁.hom ≫ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι = ι₁ ∧
        e₁.hom ≫ strictTransformSubschemeLift π Z (Scheme.Hom.ker ι) = ρ ≫ e.hom := by
  have hkH : (Scheme.Hom.ker ι).subschemeι.ker = Scheme.Hom.ker ι :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hkT : (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι.ker
      = Blowup.strictTransform π Z (Scheme.Hom.ker ι) :=
    Scheme.IdealSheafData.ker_subschemeι _
  have hu : IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH) ≫
      (Scheme.Hom.ker ι).subschemeι = ι := IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH)) :=
    IsClosedImmersion.isIso_of_ker_eq ι (Scheme.Hom.ker ι).subschemeι _ hu hkH.symm
  have hu₁ : IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
        (le_of_eq (hkT.trans hker.symm)) ≫
      (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι = ι₁ :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
      (le_of_eq (hkT.trans hker.symm))) :=
    IsClosedImmersion.isIso_of_ker_eq ι₁ (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι _
      hu₁ (hker.trans hkT.symm)
  refine ⟨asIso (IsClosedImmersion.lift (Scheme.Hom.ker ι).subschemeι ι (le_of_eq hkH)),
    asIso (IsClosedImmersion.lift (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι ι₁
      (le_of_eq (hkT.trans hker.symm))), hu, hu₁, ?_⟩
  rw [← cancel_mono (Scheme.Hom.ker ι).subschemeι, Category.assoc,
    strictTransformSubschemeLift_comp_subschemeι π Z (Scheme.Hom.ker ι), ← Category.assoc]
  simp only [asIso_hom]
  rw [hu₁, Category.assoc, hu, hsq]

theorem comap_strictTransform_of_closedImmersion_commSq {X X₁ S S₁ : Scheme.{u}}
    {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    [IsLocallyNoetherian X₁] [IsLocallyNoetherian S₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι))
    (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (Scheme.Hom.ker ι :: E))
    (hHZ : Scheme.Hom.ker ι ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (D : X.IdealSheafData) (hD : D ∈ E) :
    (Blowup.strictTransform π Z D).comap ι₁ =
      Blowup.strictTransform ρ (Z.comap ι) (D.comap ι) := by
  obtain ⟨e, e₁, he, he₁, hcomm⟩ :=
    exists_iso_subscheme_of_ker_eq_strictTransform π Z ι ι₁ ρ hsq hker
  have : IsLocallyNoetherian (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subscheme :=
    isLocallyNoetherian_subscheme _
  have hq := isBlowupAlongIdealSheaf_strictTransformSubschemeLift π Z (Scheme.Hom.ker ι) hπ
  have hfinal : (e₁.hom ≫ strictTransformSubschemeLift π Z (Scheme.Hom.ker ι)) ≫
      (Scheme.Hom.ker ι).subschemeι = ρ ≫ ι := by
    rw [Category.assoc, strictTransformSubschemeLift_comp_subschemeι, ← Category.assoc, he₁, hsq]
  have hmain := comap_strictTransform_eq_strictTransformSubschemeLift p π Z (Scheme.Hom.ker ι) E hsnc hHZ hπ D hD
  have h1 : (Blowup.strictTransform π Z D).comap ι₁
      = ((Blowup.strictTransform π Z D).comap
          (Blowup.strictTransform π Z (Scheme.Hom.ker ι)).subschemeι).comap e₁.hom := by
    rw [← he₁, Scheme.IdealSheafData.comap_comp]
  rw [h1, hmain, comap_strictTransform_of_iso
    (strictTransformSubschemeLift π Z (Scheme.Hom.ker ι)) e₁ (Z.comap (Scheme.Hom.ker ι).subschemeι)
    (D.comap (Scheme.Hom.ker ι).subschemeι) hq.1]
  refine strictTransform_eq_of_comap_eq _ ρ _ _ _ _ ?_ ?_
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfinal]
  · rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hfinal]

theorem comap_exceptionalIdeal_of_commSq {X X₁ S S₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S) (hsq : ι₁ ≫ π = ρ ≫ ι)
    (Z : X.IdealSheafData) :
    (Blowup.exceptionalIdeal π Z).comap ι₁ = Blowup.exceptionalIdeal ρ (Z.comap ι) := by
  rw [Blowup.exceptionalIdeal_eq_comap, Blowup.exceptionalIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, hsq]

theorem map_comap_strictTransform_append_exceptionalIdeal {X X₁ S S₁ : Scheme.{u}}
    {k : Type u} [Field k] (p : X ⟶ Spec (CommRingCat.of k)) (π : X₁ ⟶ X)
    (Z : X.IdealSheafData) (ι : S ⟶ X) (ι₁ : S₁ ⟶ X₁) (ρ : S₁ ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι₁]
    [IsLocallyNoetherian X₁] [IsLocallyNoetherian S₁]
    (hsq : ι₁ ≫ π = ρ ≫ ι)
    (hker : Scheme.Hom.ker ι₁ = Blowup.strictTransform π Z (Scheme.Hom.ker ι))
    (E : List X.IdealSheafData)
    (hsnc : HasStrictNormalCrossingsWith p Z (Scheme.Hom.ker ι :: E))
    (hHZ : Scheme.Hom.ker ι ≤ Z) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) :
    (List.map (Blowup.strictTransform π Z) E ++ [Blowup.exceptionalIdeal π Z]).map
        (fun A => A.comap ι₁) =
      List.map (Blowup.strictTransform ρ (Z.comap ι)) (List.map (fun D => D.comap ι) E) ++
        [Blowup.exceptionalIdeal ρ (Z.comap ι)] := by
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · refine List.map_congr_left ?_
    intro D hD
    exact comap_strictTransform_of_closedImmersion_commSq p π Z ι ι₁ ρ hsq hker E hsnc hHZ hπ D hD
  · rw [comap_exceptionalIdeal_of_commSq π ι ι₁ ρ hsq Z]

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.UntwistedDivisorRestriction
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isClopen_of_pairwise_disjoint_irreducibleComponents {S : Type*} [TopologicalSpace S]
    [NoetherianSpace S]
    (hsep : ∀ C₁ ∈ irreducibleComponents S, ∀ C₂ ∈ irreducibleComponents S,
      C₁ ≠ C₂ → Disjoint C₁ C₂)
    {K : Set S} (hK : K ∈ irreducibleComponents S) : IsClopen K := by
  have hKc : IsClosed K := isClosed_of_mem_irreducibleComponents K hK
  have hcompl : Kᶜ = ⋃₀ (irreducibleComponents S \ {K}) := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩, ?_⟩
      · simp only [Set.mem_singleton_iff]
        intro h
        exact hx (by rw [← h]; exact (irreducibleComponent_property x).2.1 rfl)
      · exact (irreducibleComponent_property x).2.1 rfl
    · rintro ⟨C, ⟨hC, hCK⟩, hxC⟩ hxK
      have hne : C ≠ K := by
        intro h
        exact hCK (by simp [h])
      exact Set.disjoint_left.mp (hsep C hC K hK hne) hxC hxK
  have hfin : (irreducibleComponents S \ {K}).Finite :=
    Set.Finite.subset NoetherianSpace.finite_irreducibleComponents Set.sdiff_subset
  refine ⟨hKc, ?_⟩
  rw [← isClosed_compl_iff, hcompl, Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)

theorem connectedComponent_subset_of_mem_irreducibleComponents {S : Type*} [TopologicalSpace S]
    [NoetherianSpace S]
    (hsep : ∀ C₁ ∈ irreducibleComponents S, ∀ C₂ ∈ irreducibleComponents S,
      C₁ ≠ C₂ → Disjoint C₁ C₂)
    {K : Set S} (hK : K ∈ irreducibleComponents S) {x : S} (hx : x ∈ K) :
    connectedComponent x ⊆ K :=
  (isClopen_of_pairwise_disjoint_irreducibleComponents hsep hK).connectedComponent_subset hx

namespace DivisorReduction

private theorem smooth_subschemeι_comp_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := List.getElem_mem hj
  have hDiv : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hV.snc).1 _ hmem
  exact ((isSmoothDivisor_iff _ _).mp hDiv).2

private theorem noetherianSpace_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) :
    NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme := by
  have := hV.isNoetherian
  have : NoetherianSpace ↥T.scheme := inferInstance
  exact (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
    (T.boundary.get ⟨j, hj⟩).subschemeι).isInducing.noetherianSpace

private theorem ker_ι_comp_ne_top {X Z : Scheme.{u}} (hX : NoetherianSpace ↥X) (V : X.Opens)
    (g : X ⟶ Z) (x : ↥X) (hx : x ∈ V) :
    AlgebraicGeometry.Scheme.Hom.ker (V.ι ≫ g) ≠ ⊤ := by
  have := hX
  have : NoetherianSpace ↥V.toScheme := inferInstanceAs (NoetherianSpace ↥(V : Set ↥X))
  intro h
  have : AlgebraicGeometry.QuasiCompact (V.ι ≫ g) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hx' : x ∈ Set.range ⇑V.ι := by simpa using hx
  obtain ⟨y, hy⟩ := hx'
  have h3 : ⇑g x ∈ ((AlgebraicGeometry.Scheme.Hom.ker (V.ι ≫ g)).support : Set ↥Z) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
    exact subset_closure ⟨y, by simp [hy]⟩
  rw [h] at h3
  simp at h3

theorem nonzeroOnComponents_comap_lowerIdealWithoutBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hBalanced : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ) (hj : j < T.boundary.length)
    (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    NonzeroOnComponents
      ((DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  classical
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    smooth_subschemeι_comp_structureMorphism T hV j hj
  have hNoe : NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have := hNoe
  have hbal : IsDerivBalanced T.base T.structMap T.ideal T.mult := hBalanced
  have hcs : orderAtLeastLocus T.ideal T.mult = (T.ideal.support : Set ↥T.scheme) :=
    orderAtLeastLocus_eq_support_of_isDerivBalanced T.base T.structMap T.ideal T.mult hbal hV.one_le_mult
  have hdisj : ∀ C₁ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      C₁ ≠ C₂ → Disjoint C₁ C₂ :=
    irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  rw [DivisorReduction.containedComponentsIdeal_eq_ker T j hj hopen] at hZ
  have hI : DivisorReduction.lowerIdealWithoutBlowup T = T.ideal := by
    show T.ideal.comap (𝟙 T.scheme) = T.ideal
    simp
  rw [hI, nonzeroOnComponents_iff]
  intro C hC hsub
  obtain ⟨x, hxC⟩ := hC.1.nonempty
  have hCsub : C ⊆ ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult := by
    intro y hy
    have h1 : y ∈ ((T.ideal.comap (T.boundary.get ⟨j, hj⟩).subschemeι).support :
        Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := hsub hy
    rw [Set.mem_preimage, hcs]
    simpa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] using h1
  have hxV : connectedComponent x ⊆
      ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    fun z hz => hCsub (connectedComponent_subset_of_mem_irreducibleComponents hdisj hC hxC hz)
  exact absurd hZ (ker_ι_comp_ne_top hNoe _ _ x hxV)

theorem isAdmissible_restrictToDivisor (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hOB : T.IsOrderBoundedByMult) (hBalanced : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ)
    (hj : j < T.boundary.length) (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    (DivisorReduction.restrictToDivisor T j hj).IsAdmissible := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    smooth_subschemeι_comp_structureMorphism T hV j hj
  have := hsm
  have hlft : AlgebraicGeometry.LocallyOfFiniteType
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hqc : AlgebraicGeometry.QuasiCompact
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hsnc0 : InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      ((T.boundary.eraseIdx j).map fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) :=
    inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx T.structMap T.boundary hV.snc j hj
  have hbd : DivisorReduction.lowerBoundaryWithoutBlowup T = T.boundary := by
    show List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary = T.boundary
    simp
  have hsnc : InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
        (List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
    rw [hbd, List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hj))]
    exact hsnc0
  exact ⟨hV.charZero, hlft,
    nonzeroOnComponents_comap_lowerIdealWithoutBlowup T hV hBalanced j hj hZ, hV.one_le_mult, hqc, hsm, hsnc⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end
