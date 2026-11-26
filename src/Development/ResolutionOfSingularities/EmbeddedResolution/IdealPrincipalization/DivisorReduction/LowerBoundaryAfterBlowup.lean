module

public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformBasic

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryAfterBlowup
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionBoundary

private theorem mem_closeds_compl {α : Type u} [TopologicalSpace α]
    (S : TopologicalSpace.Closeds α) (x : α) : x ∈ S.compl ↔ x ∉ S := Iff.rfl

private theorem saturation_top_eq_top {Y : Scheme.{u}} (F : Y.IdealSheafData) :
    saturation F (⊤ : Y.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform (𝟙 Y) F (⊤ : Y.IdealSheafData)
  rw [strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.comap_id] at h
  exact top_le_iff.mp h

private theorem restrictIdeal_mul {X : Scheme.{u}} (A B : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (A * B) U = restrictIdeal A U * restrictIdeal B U :=
  Scheme.IdealSheafData.comap_mul A B U.ι

private theorem restrictIdeal_strictTransform_id {X : Scheme.{u}} [IsLocallyNoetherian X]
    (Z D : X.IdealSheafData) (U : X.Opens) :
    restrictIdeal (Blowup.strictTransform (𝟙 X) Z D) U =
      saturation (restrictIdeal Z U) (restrictIdeal D U) := by
  have h1 := restrictIdeal_strictTransform (𝟙 X) Z D U
  have h2 := strictTransform_comp_ι U (𝟙 U.toScheme) Z D
  rw [Category.id_comp] at h2
  rw [h1, Category.comp_id, h2, strictTransform_eq_saturation, Scheme.IdealSheafData.comap_id,
    Scheme.IdealSheafData.comap_id]

private theorem map_eq_self_of_getElem {α : Type u} (g : α → α) : ∀ l : List α,
    (∀ (i : ℕ) (h : i < l.length), g (l[i]'h) = l[i]'h) → l.map g = l := by
  intro l h
  refine List.ext_getElem (List.length_map _) ?_
  intro i _ hi
  simpa only [List.getElem_map] using h i hi

private theorem eraseIdx_map_eq {α : Type u} (g : α → α) : ∀ (l : List α) (j : ℕ),
    (∀ (i : ℕ) (h : i < l.length), i ≠ j → g (l[i]'h) = l[i]'h) →
    (l.map g).eraseIdx j = l.eraseIdx j := by
  intro l j h
  rw [List.eraseIdx_map]
  apply map_eq_self_of_getElem
  intro k hk
  obtain ⟨i, hi, hij, heq⟩ := List.mem_eraseIdx_iff_getElem.mp (List.getElem_mem hk)
  rw [← heq]
  exact h i hi hij

theorem strictTransform_comap_boundary_of_ne (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (i : ℕ) (hi : i < T.boundary.length) (hij : i ≠ j) :
    Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨i, hi⟩).comap (𝟙 T.scheme)) = T.boundary.get ⟨i, hi⟩ := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support
  · obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
      exists_etaleChart_containedComponentsIdeal T hV j hj x hx
    refine ⟨U, hxU, ?_⟩
    rw [restrictIdeal_strictTransform_id, hZU]
    cases hai : a i with
    | none =>
        rw [hnone i hi hai]
        exact saturation_top_eq_top _
    | some t =>
        have htb : t ≠ b := by
          intro e
          apply hij
          refine hinj i j hi hj b ?_ hab
          rw [hai, e]
        have ht := hsome i hi t hai
        have hq1 : QuasiCompact
            (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩)) :=
          quasiCompact_saturationι_of_isLocallyNoetherian _ _
        have hq2 := quasiCompact_saturationι_restrictIdeal
          (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩) U
        rw [hZU, ht] at hq2
        have := hq2
        rw [ht]
        exact c.saturation_coordIdeal_of_ne t b htb
  · refine ⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl,
      (mem_closeds_compl _ _).mpr hx, ?_⟩
    have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨i, hi⟩)
      (DivisorReduction.containedComponentsIdeal T j hj).support.compl
      (fun y hy => by
        have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
          (mem_closeds_compl _ y).mp hy
        simpa using h')
    rw [hst, Scheme.IdealSheafData.comap_id]

theorem isSmoothDivisor_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    IsSmoothDivisor T.structMap (DivisorReduction.containedComponentsIdeal T j hj) :=
  ⟨isLocallyGeneratedByNonZeroDivisor_containedComponentsIdeal T hV j hj, smooth_subschemeι_containedComponentsIdeal_comp T hV j hj⟩

theorem strictTransform_mul_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
          ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme)) *
        DivisorReduction.containedComponentsIdeal T j hj =
      T.boundary.get ⟨j, hj⟩ := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id]
  refine eq_of_locally_restrictIdeal_eq _ _ fun x => ?_
  by_cases hx : x ∈ (DivisorReduction.containedComponentsIdeal T j hj).support
  · obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
      exists_etaleChart_containedComponentsIdeal T hV j hj x hx
    refine ⟨U, hxU, ?_⟩
    have hDj := hsome j hj b hab
    have hq1 : QuasiCompact
        (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) :=
      quasiCompact_saturationι_of_isLocallyNoetherian _ _
    have hq2 := quasiCompact_saturationι_restrictIdeal
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U
    rw [hZU, hDj] at hq2
    have := hq2
    rw [restrictIdeal_mul, restrictIdeal_strictTransform_id, hZU, hDj,
      c.saturation_coordIdeal_self b, Scheme.IdealSheafData.top_mul]
  · refine ⟨(DivisorReduction.containedComponentsIdeal T j hj).support.compl,
      (mem_closeds_compl _ _).mpr hx, ?_⟩
    have hZtop : restrictIdeal (DivisorReduction.containedComponentsIdeal T j hj)
        (DivisorReduction.containedComponentsIdeal T j hj).support.compl = ⊤ := by
      have h := restrictIdeal_exceptionalIdeal_eq_top_of_notMem_support (𝟙 T.scheme)
        (DivisorReduction.containedComponentsIdeal T j hj) (DivisorReduction.containedComponentsIdeal T j hj).support.compl
        (fun y hy => by
          have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
            (mem_closeds_compl _ y).mp hy
          simpa using h')
      rwa [exceptionalIdeal_id] at h
    have hst := restrictIdeal_strictTransform_eq_comap_of_notMem_support (𝟙 T.scheme)
      (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)
      (DivisorReduction.containedComponentsIdeal T j hj).support.compl
      (fun y hy => by
        have h' : y ∉ (DivisorReduction.containedComponentsIdeal T j hj).support :=
          (mem_closeds_compl _ y).mp hy
        simpa using h')
    rw [restrictIdeal_mul, hst, Scheme.IdealSheafData.comap_id, hZtop,
      Scheme.IdealSheafData.mul_top]

theorem disjoint_support_strictTransform_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    Disjoint
      ((Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
          ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme))).support : Set ↥T.scheme)
      (((DivisorReduction.containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  have := hV.isNoetherian
  rw [Scheme.IdealSheafData.comap_id, Set.disjoint_right]
  intro x hx
  obtain ⟨U, hxU, n, c, a, b, hab, hnone, hsome, hinj, hZU⟩ :=
    exists_etaleChart_containedComponentsIdeal T hV j hj x hx
  have hDj := hsome j hj b hab
  have hq1 : QuasiCompact
      (saturationι (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩)) :=
    quasiCompact_saturationι_of_isLocallyNoetherian _ _
  have hq2 := quasiCompact_saturationι_restrictIdeal
    (DivisorReduction.containedComponentsIdeal T j hj) (T.boundary.get ⟨j, hj⟩) U
  rw [hZU, hDj] at hq2
  have := hq2
  have hres : restrictIdeal (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
      (T.boundary.get ⟨j, hj⟩)) U = ⊤ := by
    rw [restrictIdeal_strictTransform_id, hZU, hDj]
    exact c.saturation_coordIdeal_self b
  exact notMem_support_of_mem_opens_of_restrictIdeal_eq_top _ U hres x hxU

theorem take_eraseIdx_lowerBoundaryAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    ((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1) =
      T.boundary.eraseIdx j := by
  have hlist : (T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
        (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) =
      T.boundary.map (fun D =>
        Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme))) := by
    simp only [List.map_map, Function.comp_def]
  have key := eraseIdx_map_eq
    (fun D : T.scheme.IdealSheafData =>
      Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) (D.comap (𝟙 T.scheme)))
    T.boundary j
    (fun i h hij => strictTransform_comap_boundary_of_ne T hV j hj i h hij)
  have hlen : j < (T.boundary.map (fun D =>
      Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
        (D.comap (𝟙 T.scheme)))).length := by
    simpa using hj
  show ((((T.boundary.map (fun D => D.comap (𝟙 T.scheme))).map
        (Blowup.strictTransform (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj))) ++
      [Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)]).eraseIdx j).take
      (T.boundary.length - 1) = T.boundary.eraseIdx j
  rw [hlist, List.eraseIdx_append_of_lt_length hlen, key]
  exact List.take_left' (List.length_eraseIdx_of_lt hj)

theorem inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) :
    InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      ((((DivisorReduction.lowerBoundaryAfterBlowup T j hj).eraseIdx j).take (T.boundary.length - 1)).map
        fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  rw [take_eraseIdx_lowerBoundaryAfterBlowup T hV j hj]
  exact inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx_of_eq T.structMap T.boundary hV.snc j hj
    (T.boundary.get ⟨j, hj⟩) rfl

end DivisorReductionBoundary

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionProperties
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure DivisorReductionProperties (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : Prop where
  isMarked_pushedTop :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                      (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).IsMarked
                  T.structMap T.ideal T.mult T.boundary
  isMarked_pushedPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                        (DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealAfterBlowup T j hj)
                          (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
                    T.structMap T.ideal T.mult T.boundary
  valid_lowerPre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ → (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible
  orderAt_ctrlIdeal_le_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                ∀ i ≤ s.length,
                  ∀ (x : ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj
                            (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).obj i)),
                    orderAt ((DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealWithoutBlowup T)
                          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult i) x ≤ (T.mult : ℕ∞)
  orderAt_ctrlIdeal_le_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  ∀ i ≤ s.length + 1,
                    ∀ (x : ↥((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                              (DivisorReduction.ambientBlowupSeq hres hno T j hj
                                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).obj i)),
                      orderAt ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                            (DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult i) x ≤ (T.mult : ℕ∞)
  coSupport_inter_ker_eq_empty_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                orderAtLeastLocus (s.ideal s.length) T.mult = ∅ →
                  orderAtLeastLocus ((DivisorReduction.ambientBlowupSeq hres hno T j hj
                          (DivisorReduction.lowerIdealWithoutBlowup T)
                          (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult s.length) T.mult ∩
                      ↑(AlgebraicGeometry.Scheme.Hom.ker
                          (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                            (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr s.length)).support = ∅
  coSupport_inter_ker_eq_empty_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  orderAtLeastLocus (s.ideal s.length) T.mult = ∅ →
                    orderAtLeastLocus ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                            (DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult (s.length + 1)) T.mult ∩
                        (((AlgebraicGeometry.Scheme.Hom.ker
                            (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr s.length)).support :
                          Set ↥((DivisorReduction.ambientBlowupSeq hres hno T j hj
                              (DivisorReduction.lowerIdealAfterBlowup T j hj)
                              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr).obj s.length))) = ∅
  isPullbackSeq_ambientTower :
    ∀ (X Y S S' : AlgebraicGeometry.Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X) (ψ : S' ⟶ S)
      [AlgebraicGeometry.IsClosedImmersion σ] [AlgebraicGeometry.IsClosedImmersion σ']
      [AlgebraicGeometry.Flat φ] [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.IsNoetherian Y],
      CategoryTheory.IsPullback σ' ψ φ σ →
        ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent) (hc' : d'.CentersContainNoComponent),
          IsPullbackBlowupSequence ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
            IsPullbackBlowupSequence φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
              (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  isStrictPullbackSeq_ambientTower :
    ∀ (X Y S S' : AlgebraicGeometry.Scheme.{u}) (σ : S ⟶ X) (σ' : S' ⟶ Y) (φ : Y ⟶ X) (ψ : S' ⟶ S)
      [AlgebraicGeometry.IsClosedImmersion σ] [AlgebraicGeometry.IsClosedImmersion σ']
      [AlgebraicGeometry.Flat φ] [AlgebraicGeometry.IsNoetherian X]
      [AlgebraicGeometry.IsNoetherian Y],
      CategoryTheory.IsPullback σ' ψ φ σ →
        ∀ (d : BlowupSequenceData S) (d' : BlowupSequenceData S') (hc : d.CentersContainNoComponent) (hc' : d'.CentersContainNoComponent),
          IsStrictPullbackBlowupSeq ψ d'.toSequenceOfBlowups d.toSequenceOfBlowups →
            IsStrictPullbackBlowupSeq φ (ambientBlowupSequence σ' d' hres hno hc').toSequenceOfBlowups
              (ambientBlowupSequence σ d hres hno hc).toSequenceOfBlowups
  comap_ctrlIdeal_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj = ⊤ →
            (DivisorReduction.restrictToDivisor T j hj).IsAdmissible →
              ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
                (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                ∀ i ≤ s.length,
                  ((DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
                        T.ideal T.mult i).comap
                      (DivisorReduction.embeddingIntoAmbient hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
                        (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr i) = s.ideal i
  comap_ctrlIdeal_pre :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible), T.IsOrderBoundedByMult →
      T.IsBalanced hV.locallyOfFiniteType →
        ∀ (j : ℕ) (hj : j < T.boundary.length),
          DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤ →
            ∀ (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryTheory.CategoryStruct.id T.scheme)
                (DivisorReduction.containedComponentsIdeal T j hj)),
              (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible →
                ∀ [AlgebraicGeometry.IsNoetherian T.scheme]
                  (s : (DivisorReduction.restrictTwistedToDivisor T j hj).SequenceOfBlowups)
                  (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent),
                  ∀ i ≤ s.length,
                    ((BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
                              (DivisorReduction.ambientBlowupSeq hres hno T j hj
                                (DivisorReduction.lowerIdealAfterBlowup T j hj)
                                (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
                          T.ideal T.mult (i + 1)).comap
                        (DivisorReduction.embeddingIntoAmbient hres hno T j hj
                          (DivisorReduction.lowerIdealAfterBlowup T j hj)
                          (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr i) = s.ideal i
  preIdeal_baseChange :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (L : Type u) [Field L] [CharZero L] (f : T.base →+* L),
        (T.baseChange L f).IsAdmissible →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hj' : j < (T.baseChange L f).boundary.length),
            DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
              (DivisorReduction.containedComponentsIdeal T j hj).comap
                (CategoryTheory.Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))
  preIdeal_pullbackAlong :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : AlgebraicGeometry.Scheme.{u})
        (q : Y ⟶ AlgebraicGeometry.Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h],
        CategoryTheory.CategoryStruct.comp h T.structMap = q →
          (T.pullbackAlong Y q h).IsAdmissible →
            ∀ (j : ℕ) (hj : j < T.boundary.length)
              (hj' : j < (T.pullbackAlong Y q h).boundary.length),
              DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
                (DivisorReduction.containedComponentsIdeal T j hj).comap h
  preIdeal_eq_top_of_imageIdeal :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length)
        (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData),
        T.mult = 1 →
          (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
                (CategoryTheory.CategoryStruct.comp (T.boundary.get ⟨j, hj⟩).subschemeι
                  T.structMap) J
                (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
                  (T.boundary.eraseIdx j))).IsAdmissible →
            T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J →
              DivisorReduction.containedComponentsIdeal T j hj = ⊤

theorem DivisorReductionProperties.toDivisorReductionStepProperties {hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}}
    {hno : BlowupPreservesNoetherian.{u}} (h : DivisorReductionProperties hres hno) :
    DivisorReductionStepProperties hres hno :=
  { exists_ideal_mul_preIdeal_pow := fun T hV _ j hj =>
      exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
    isMarked_pushedTop := h.isMarked_pushedTop
    isMarked_pushedPre := h.isMarked_pushedPre
    isBlowup_id_preIdeal := fun T hV j hj => isBlowupAlongIdealSheaf_id_containedComponentsIdeal T hV j hj
    valid_lowerTop := fun T hV hOB hbal j hj hZ =>
      DivisorReduction.isAdmissible_restrictToDivisor T hV hOB hbal j hj hZ
    valid_lowerPre := h.valid_lowerPre
    orderAt_ctrlIdeal_le_top := h.orderAt_ctrlIdeal_le_top
    orderAt_ctrlIdeal_le_pre := h.orderAt_ctrlIdeal_le_pre
    coSupport_inter_ker_eq_empty_top := h.coSupport_inter_ker_eq_empty_top
    coSupport_inter_ker_eq_empty_pre := h.coSupport_inter_ker_eq_empty_pre
    isPullbackSeq_ambientTower := h.isPullbackSeq_ambientTower
    isStrictPullbackSeq_ambientTower := h.isStrictPullbackSeq_ambientTower
    comap_ctrlIdeal_top := h.comap_ctrlIdeal_top
    comap_ctrlIdeal_pre := h.comap_ctrlIdeal_pre
    preIdeal_baseChange := h.preIdeal_baseChange
    preIdeal_pullbackAlong := h.preIdeal_pullbackAlong
    preIdeal_eq_top_of_imageIdeal := h.preIdeal_eq_top_of_imageIdeal
    smooth_preIdeal := fun T hV j hj => smooth_subschemeι_containedComponentsIdeal_comp T hV j hj
    hasSNCWith_preIdeal := fun T hV j hj => hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj
    support_preIdeal_subset := fun T hV j hj => support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj }

end FunctorialResolution.EmbeddedResolution

end
end
