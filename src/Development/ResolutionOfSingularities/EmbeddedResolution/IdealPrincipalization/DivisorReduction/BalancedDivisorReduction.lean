module

public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsHypersurfaceRestriction
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.AmbientBlowupFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SubschemeMapFlatness
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryAfterBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealAfterBlowup

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderMonotone
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem isLocallyNoetherian_of_smooth_over_field (k : Type u) [Field k]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth q] :
    IsLocallyNoetherian Y :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian q

theorem smooth_projectionToBase_comp_and_orderAt_controlledTransform_le (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (hd : d.IsMarked p I m E) (hI : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞))
    (t : ℕ) (ht : t ≤ d.length) :
    AlgebraicGeometry.Smooth (d.projectionToBase t ≫ p) ∧
      ∀ x : ↥(d.obj t), orderAt (d.controlledTransform I m t) x ≤ (m : ℕ∞) := by
  revert ht
  induction t with
  | zero =>
      intro _
      refine ⟨?_, ?_⟩
      · rw [BlowupSequenceData.projectionToBase_zero]
        infer_instance
      · intro x
        rw [BlowupSequenceData.controlledTransform_zero, orderAt_comap_of_isOpenImmersion]
        exact hI _
  | succ s ih =>
      intro hs
      have hs' : s < d.length := hs
      obtain ⟨ihsm, ihord⟩ := ih (le_of_lt hs')
      have : AlgebraicGeometry.Smooth (d.projectionToBase s ≫ p) := ihsm
      have hπ : Blowup.IsBlowupAlongIdealSheaf (d.map s) (d.center s) := d.isBlowup s hs'
      have hsnc : HasStrictNormalCrossingsWith (d.projectionToBase s ≫ p) (d.center s) (d.boundaryFrom E s) := hd.center_snc s hs'
      have hsm1 : AlgebraicGeometry.Smooth (d.projectionToBase (s + 1) ≫ p) := by
        rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
        exact smooth_comp_of_isBlowupAlongIdealSheaf hsnc hπ
      refine ⟨hsm1, ?_⟩
      have : AlgebraicGeometry.Smooth (d.projectionToBase (s + 1) ≫ p) := hsm1
      have : IsLocallyNoetherian (d.obj (s + 1)) :=
        isLocallyNoetherian_of_smooth_over_field k (d.projectionToBase (s + 1) ≫ p)
      have hIle : d.controlledTransform I m s ≤ (d.center s) ^ m :=
        le_pow_of_hasStrictNormalCrossingsWith (d.projectionToBase s ≫ p) (d.center s) (d.controlledTransform I m s) (d.boundaryFrom E s)
          hsnc m (hd.center_order s hs')
      have hEq : d.controlledTransform I m (s + 1)
          = controlledTransform (d.map s) (d.center s) (d.controlledTransform I m s) m hπ hIle :=
        eq_controlledTransform_of_mul_eq_comap (d.map s) (d.center s) (d.controlledTransform I m s) m hπ hIle
          (d.controlledTransform I m (s + 1)) (d.pow_exceptionalIdeal_mul_controlledTransform_succ I m s (hd.divisible s hs'))
      intro x
      rw [hEq]
      exact orderAt_controlledTransform_le_of_forall_le k (d.projectionToBase s ≫ p) (d.map s) (d.center s)
        (d.boundaryFrom E s) hsnc hπ (d.controlledTransform I m s) m hIle ihord x

theorem orderAt_controlledTransform_le_of_isMarked (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    (I : X.IdealSheafData) (m : ℕ) (E : List X.IdealSheafData) (d : BlowupSequenceData X)
    (hd : d.IsMarked p I m E) (hI : ∀ x : ↥X, orderAt I x ≤ (m : ℕ∞))
    (t : ℕ) (ht : t ≤ d.length) (x : ↥(d.obj t)) :
    orderAt (d.controlledTransform I m t) x ≤ (m : ℕ∞) :=
  (smooth_projectionToBase_comp_and_orderAt_controlledTransform_le k p I m E d hd hI t ht).2 x

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsFunctoriality
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isIrreducible_connectedComponent_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (z : ↥(T.boundary.get ⟨j, hj⟩).subscheme) :
    IsIrreducible (connectedComponent z) := by
  have : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hsd : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    isSmoothDivisor_boundary_get T hV j hj
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp hsd).2
  have hsep := irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
    ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have h1 : connectedComponent z ⊆ irreducibleComponent z :=
    connectedComponent_subset_of_mem_irreducibleComponents hsep
      (irreducibleComponent_mem_irreducibleComponents z) mem_irreducibleComponent
  have h2 : irreducibleComponent z ⊆ connectedComponent z :=
    (isIrreducible_irreducibleComponent (x := z)).2.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  rw [Set.Subset.antisymm h1 h2]
  exact isIrreducible_irreducibleComponent

theorem openSubschemeKer_comap_of_flat_of_noetherian {X Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.Flat g] (D : X.IdealSheafData) (A : Set X) (hA : IsClosed A)
    (hirr : ∀ w : ↥D.subscheme, IsIrreducible (connectedComponent w))
    (hN : TopologicalSpace.NoetherianSpace ↥D.subscheme)
    (hN' : TopologicalSpace.NoetherianSpace ↥(D.comap g).subscheme)
    (hopen : IsOpen {w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A})
    (hopen' : IsOpen {w : ↥(D.comap g).subscheme |
      connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}) :
    openSubschemeKer (D.comap g)
        ⟨{w : ↥(D.comap g).subscheme |
            connectedComponent w ⊆ ⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A)}, hopen'⟩ =
      (openSubschemeKer D
        ⟨{w : ↥D.subscheme | connectedComponent w ⊆ ⇑D.subschemeι.base ⁻¹' A}, hopen⟩).comap g := by
  have := hN
  have := hN'
  exact openSubschemeKer_comap g D A hA ⟨_, hopen⟩ ⟨_, hopen'⟩ rfl rfl
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset ↥D.subscheme
      (⇑D.subschemeι.base ⁻¹' A))
    (TopologicalSpace.NoetherianSpace.isClosed_setOf_connectedComponent_subset
      ↥(D.comap g).subscheme
      (⇑(D.comap g).subschemeι.base ⁻¹' (⇑g.base ⁻¹' A))) hirr

private theorem get_eq_comap_get_of_eq_map {X Y : Scheme.{u}} (g : Y ⟶ X) (E : List X.IdealSheafData)
    (F : List Y.IdealSheafData) (hF : F = E.map (fun D => D.comap g)) (j : ℕ)
    (hj : j < E.length) (hj' : j < F.length) :
    F.get ⟨j, hj'⟩ = (E.get ⟨j, hj⟩).comap g := by
  subst hF
  simp [List.get_eq_getElem]

private theorem containedComponentsIdeal_comap_of_flat (T T' : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hV' : T'.IsAdmissible) (g : T'.scheme ⟶ T.scheme) (hflat : AlgebraicGeometry.Flat g) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < T'.boundary.length)
    (hD : T'.boundary.get ⟨j, hj'⟩ = (T.boundary.get ⟨j, hj⟩).comap g)
    (hcs : orderAtLeastLocus T'.ideal T'.mult = ⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)
    (hcl : IsClosed (orderAtLeastLocus T.ideal T.mult)) :
    DivisorReduction.containedComponentsIdeal T' j hj' = (DivisorReduction.containedComponentsIdeal T j hj).comap g := by
  have := hflat
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  have hopen' := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T' hV' j hj'
  have hirr : ∀ w : ↥(T.boundary.get ⟨j, hj⟩).subscheme, IsIrreducible (connectedComponent w) :=
    fun w => isIrreducible_connectedComponent_boundary_subscheme T hV j hj w
  have hN : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have hN' : TopologicalSpace.NoetherianSpace ↥(T'.boundary.get ⟨j, hj'⟩).subscheme :=
    noetherianSpace_boundary_subscheme T' hV' j hj'
  have key : ∀ (D' : T'.scheme.IdealSheafData), D' = (T.boundary.get ⟨j, hj⟩).comap g →
      ∀ (S' : Set ↥D'.subscheme),
        S' = {w : ↥D'.subscheme | connectedComponent w ⊆
            ⇑D'.subschemeι.base ⁻¹' (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} →
        ∀ (hop' : IsOpen S'), TopologicalSpace.NoetherianSpace ↥D'.subscheme →
          openSubschemeKer D' ⟨S', hop'⟩ =
            (openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, hopen⟩).comap g := by
    rintro D' rfl S' rfl hop' hNN
    exact openSubschemeKer_comap_of_flat_of_noetherian g (T.boundary.get ⟨j, hj⟩)
      (orderAtLeastLocus T.ideal T.mult) hcl hirr hN hNN hopen hop'
  have hset : divisorComponentsInOrderLocus T' j hj' =
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹'
          (⇑g.base ⁻¹' orderAtLeastLocus T.ideal T.mult)} :=
    congrArg (fun A : Set ↥T'.scheme =>
      {w : ↥(T'.boundary.get ⟨j, hj'⟩).subscheme | connectedComponent w ⊆
        ⇑(T'.boundary.get ⟨j, hj'⟩).subschemeι.base ⁻¹' A}) hcs
  rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen, containedComponentsIdeal_eq_openSubschemeKer T' j hj' hopen']
  exact key _ hD _ hset hopen' hN'

theorem containedComponentsIdeal_pullbackAlong_of_smooth (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth h]
    (hq : h ≫ T.structMap = q) (hV' : (T.pullbackAlong Y q h).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.pullbackAlong Y q h).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.pullbackAlong Y q h) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap h := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hfl : AlgebraicGeometry.Flat h := inferInstance
  have hD : (T.pullbackAlong Y q h).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap h :=
    get_eq_comap_get_of_eq_map h T.boundary (T.pullbackAlong Y q h).boundary
      (MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h) j hj hj'
  have hcs : orderAtLeastLocus (T.pullbackAlong Y q h).ideal (T.pullbackAlong Y q h).mult =
      ⇑h.base ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h hq T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat T (T.pullbackAlong Y q h) hV hV' h hfl j hj hj' hD hcs hcl

theorem containedComponentsIdeal_baseChange (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (L : Type u) [Field L]
    [CharZero L] (f : T.base →+* L) (hV' : (T.baseChange L f).IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (hj' : j < (T.baseChange L f).boundary.length) :
    DivisorReduction.containedComponentsIdeal (T.baseChange L f) j hj' =
      (DivisorReduction.containedComponentsIdeal T j hj).comap
        (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := by
  have : CharZero T.base := hV.charZero
  have : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  have hfl : AlgebraicGeometry.Flat (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    flat_fieldBaseChangeProjection T L f
  have hD : (T.baseChange L f).boundary.get ⟨j, hj'⟩ =
      (T.boundary.get ⟨j, hj⟩).comap (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    get_eq_comap_get_of_eq_map (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) T.boundary
      (T.baseChange L f).boundary (MarkedIdealWithBoundary.baseChange_boundary T L f) j hj hj'
  have hcs : orderAtLeastLocus (T.baseChange L f).ideal (T.baseChange L f).mult =
      ⇑(pullback.fst T.structMap (specMapOfFieldHom T.base L f)).base ⁻¹'
        orderAtLeastLocus T.ideal T.mult :=
    orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal T.mult
  have hcl : IsClosed (orderAtLeastLocus T.ideal T.mult) :=
    isClosed_orderAtLeastLocus T.base T.structMap T.ideal T.mult
  exact containedComponentsIdeal_comap_of_flat T (T.baseChange L f) hV hV'
    (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hfl j hj hj' hD hcs hcl

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.OrderLocusDisjointBoundary
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    {S X : Scheme.{u}} (ι : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι]
    (J : X.IdealSheafData) (m : ℕ) (h : orderAtLeastLocus (J.comap ι) m = ∅) :
    orderAtLeastLocus J m ∩ (↑(Scheme.Hom.ker ι).support : Set ↥X) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hker
  have hcl : IsClosed (Set.range ⇑ι.base) :=
    (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding ι).isClosed_range
  have hmem : x ∈ closure (Set.range ⇑ι.base) := by
    rw [Scheme.Hom.support_ker ι] at hker
    exact hker
  rw [hcl.closure_eq] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hxo : (m : ℕ∞) ≤ orderAt J x := hx
  have hyo : (m : ℕ∞) ≤ orderAt (J.comap ι) y := by
    refine le_trans ?_ (orderAt_le_orderAt_comap ι J y)
    rw [hy]
    exact hxo
  have hy' : y ∈ orderAtLeastLocus (J.comap ι) m := hyo
  rw [h] at hy'
  exact hy'

theorem orderAtLeastLocus_inter_support_ker_eq_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length) (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hdiv : ∀ i < s.length,
      ∃ B : ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).obj
          (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).map i)
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).center i) ^ T.mult *
            B =
          (((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
              (lowerIdealWithoutBlowup T) T.mult i).comap
            ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).map i)))
    (hempty : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
          ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
            T.ideal T.mult s.length)
          T.mult ∩
        (↑(Scheme.Hom.ker
              (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr
                s.length)).support :
          Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).obj s.length)) =
      ∅ := by
  have hid : lowerIdealWithoutBlowup T = T.ideal := by
    show T.ideal.comap (CategoryStruct.id T.scheme) = T.ideal
    simp
  have hcomap := comap_controlledTransform_embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr s.length le_rfl hdiv
  have hctrl :
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
          T.ideal T.mult s.length =
        (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
          (lowerIdealWithoutBlowup T) T.mult s.length :=
    congrArg
      (fun I => (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).controlledTransform
        I T.mult s.length) hid.symm
  refine orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr s.length) _ T.mult ?_
  rw [hctrl, hcomap]
  exact hempty

theorem orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (hno : BlowupPreservesNoetherian.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (CategoryStruct.id T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hdiv : ∀ i < s.length,
      ∃ B : ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj
          (i + 1)).IdealSheafData,
        Blowup.exceptionalIdeal
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).map i)
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).center i) ^
              T.mult * B =
          (((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).controlledTransform
              (lowerIdealAfterBlowup T j hj) T.mult i).comap
            ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).map i)))
    (hone :
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).controlledTransform
          T.ideal T.mult 1 =
        (lowerIdealAfterBlowup T j hj).comap
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).isoZero.hom)
    (hempty : orderAtLeastLocus (s.ideal s.length) T.mult = ∅) :
    orderAtLeastLocus
          ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
                (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s
                  hpr)).controlledTransform
            T.ideal T.mult (s.length + 1))
          T.mult ∩
        (↑(Scheme.Hom.ker
              (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr
                s.length)).support :
          Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj
            s.length)) =
      ∅ := by
  have h1 := BlowupSequenceData.controlledTransform_prepend_succ (containedComponentsIdeal T j hj) hb
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
    T.ideal (lowerIdealAfterBlowup T j hj) T.mult hone s.length
  have h2 := comap_controlledTransform_embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr s.length le_rfl hdiv
  refine orderAtLeastLocus_inter_ker_support_eq_empty_of_comap
    (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr s.length)
    _ T.mult ?_
  rw [h1, h2]
  exact hempty

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.TwistedDivisorRestriction
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem orderAt_le_mult (T : MarkedIdealWithBoundary.{u}) (hOB : T.IsOrderBoundedByMult) (x : ↥T.scheme) :
    orderAt T.ideal x ≤ (T.mult : ℕ∞) := hOB x

private theorem isDerivBalanced_of_isBalanced (T : MarkedIdealWithBoundary.{u})
    (h : AlgebraicGeometry.LocallyOfFiniteType T.structMap) (hbal : T.IsBalanced h) :
    IsDerivBalanced T.base T.structMap T.ideal T.mult := hbal

private theorem mem_support_of_mem_support_comap {X Y : Scheme.{u}} (f : Y ⟶ X)
    (I : X.IdealSheafData) {y : ↥Y} (hy : y ∈ (I.comap f).support) : f y ∈ I.support := by
  rw [Scheme.IdealSheafData.support_comap] at hy
  exact hy

private theorem disjoint_irreducibleComponents_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    ∀ C₁ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
        C₁ ≠ C₂ → Disjoint C₁ C₂ := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp
      (isSmoothDivisor_boundary_get T hV j hj)).2
  have h := irreducibleComponentsDisjointOfSmooth
  unfold IrreducibleComponentsDisjointOfSmooth at h
  exact h T.base _ _ hsm

private theorem containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := by
  have hex : ∃ B, DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * B = T.ideal :=
    exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  have h := pow_mul_residualByPow T.ideal (DivisorReduction.containedComponentsIdeal T j hj) T.mult hex
  simpa [DivisorReduction.lowerIdealAfterBlowup, exceptionalIdeal_id,
    Scheme.IdealSheafData.comap_id] using h

theorem nonzeroOnComponents_comap_lowerIdealAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hOB : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ)
    (hj : j < T.boundary.length) :
    NonzeroOnComponents
      ((DivisorReduction.lowerIdealAfterBlowup T j hj).comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.smooth
  have : TopologicalSpace.NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    EmbeddedResolution.noetherianSpace_boundary_subscheme T hV j hj
  have hfact : DivisorReduction.containedComponentsIdeal T j hj ^ T.mult *
      DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup T hV j hj
  have horder : ∀ x : ↥T.scheme, orderAt T.ideal x =
      (T.mult : ℕ∞) * orderAt (DivisorReduction.containedComponentsIdeal T j hj) x +
        orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj) x := by
    intro x
    rw [← hfact, orderAt_mul T.base T.structMap, orderAt_pow T.base T.structMap]
  rw [nonzeroOnComponents_iff]
  intro C hC hsub
  obtain ⟨x, hx⟩ := hC.1.1
  by_cases hcase : ∀ y ∈ C, (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ orderAtLeastLocus T.ideal T.mult
  · have hsep := disjoint_irreducibleComponents_boundary_subscheme T hV j hj
    have hcc : connectedComponent x ⊆ C :=
      connectedComponent_subset_of_mem_irreducibleComponents hsep hC hx
    have hxrel : x ∈ divisorComponentsInOrderLocus T j hj := by
      intro z hz
      exact hcase z (hcc hz)
    have hopen : IsOpen (divisorComponentsInOrderLocus T j hj) := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
    have hcl : IsClosed (divisorComponentsInOrderLocus T j hj) := isClosed_divisorComponentsInOrderLocus T hV j hj
    have hZsupp : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
        (DivisorReduction.containedComponentsIdeal T j hj).support := by
      rw [containedComponentsIdeal_eq_openSubschemeKer T j hj hopen]
      have hmem : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
          ((openSubschemeKer (T.boundary.get ⟨j, hj⟩)
            ⟨divisorComponentsInOrderLocus T j hj, hopen⟩).support : Set ↥T.scheme) := by
        rw [support_openSubschemeKer _ _ hcl]
        exact ⟨x, hxrel, rfl⟩
      exact hmem
    have hxsupp : (T.boundary.get ⟨j, hj⟩).subschemeι x ∈
        (DivisorReduction.lowerIdealAfterBlowup T j hj).support :=
      mem_support_of_mem_support_comap _ _ (hsub hx)
    have h1 : (1 : ℕ∞) ≤ orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι x) :=
      (one_le_orderAt_iff_mem_support _ _).mpr hxsupp
    have h2 : (1 : ℕ∞) ≤ orderAt (DivisorReduction.containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι x) :=
      (one_le_orderAt_iff_mem_support _ _).mpr hZsupp
    have h3 : (T.mult : ℕ∞) + 1 ≤ orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) := by
      calc (T.mult : ℕ∞) + 1 = (T.mult : ℕ∞) * 1 + 1 := by rw [mul_one]
        _ ≤ (T.mult : ℕ∞) * orderAt (DivisorReduction.containedComponentsIdeal T j hj)
              ((T.boundary.get ⟨j, hj⟩).subschemeι x) +
            orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
              ((T.boundary.get ⟨j, hj⟩).subschemeι x) := by
          gcongr
        _ = orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) := (horder _).symm
    have h4 : orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι x) ≤ (T.mult : ℕ∞) :=
      orderAt_le_mult T hOB _
    have h5 : (T.mult : ℕ∞) + 1 ≤ (T.mult : ℕ∞) := le_trans h3 h4
    have h6 : T.mult + 1 ≤ T.mult := by exact_mod_cast h5
    omega
  · push Not at hcase
    obtain ⟨y, hyC, hy⟩ := hcase
    have hy0 : orderAt T.ideal ((T.boundary.get ⟨j, hj⟩).subschemeι y) = 0 := by
      by_contra h0
      have hm : 1 ≤ T.mult := by
        by_contra hn
        have : T.mult = 0 := by omega
        apply hy
        rw [mem_orderAtLeastLocus_iff, this]
        exact zero_le
      have hlt : T.mult - 1 < T.mult := by omega
      have hbal' := isDerivBalanced_of_isBalanced T hV.locallyOfFiniteType hbal
      have hpow := IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal' hlt
      have hsub : T.mult - (T.mult - 1) = 1 := by omega
      rw [hsub, pow_one] at hpow
      have hord := orderAt_le_of_le hpow ((T.boundary.get ⟨j, hj⟩).subschemeι y)
      rw [orderAt_pow T.base T.structMap] at hord
      have hne : orderAt (derivIdealSheafIterate T.base T.structMap (T.mult - 1) T.ideal)
          ((T.boundary.get ⟨j, hj⟩).subschemeι y) ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hord
        exact h0 (le_antisymm hord zero_le)
      have hmem : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈
          (derivIdealSheafIterate T.base T.structMap (T.mult - 1) T.ideal).support := by
        by_contra hc
        exact hne ((orderAt_eq_zero_iff_not_mem_support _ _).mpr hc)
      apply hy
      rw [← support_derivIdealSheafIterate_eq_orderAtLeastLocus T.base T.structMap T.ideal hm]
      exact hmem
    have hle : orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι y) ≤ 0 := by
      rw [← hy0, horder]
      exact le_add_self
    have hJ0 : orderAt (DivisorReduction.lowerIdealAfterBlowup T j hj)
        ((T.boundary.get ⟨j, hj⟩).subschemeι y) = 0 := le_antisymm hle zero_le
    have hmem : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈
        (DivisorReduction.lowerIdealAfterBlowup T j hj).support :=
      mem_support_of_mem_support_comap _ _ (hsub hyC)
    rw [← one_le_orderAt_iff_mem_support, hJ0] at hmem
    simp at hmem

theorem isAdmissible_restrictTwistedToDivisor (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hOB : T.IsOrderBoundedByMult) (hbal : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ)
    (hj : j < T.boundary.length) (_hZ : DivisorReduction.containedComponentsIdeal T j hj ≠ ⊤) :
    (DivisorReduction.restrictTwistedToDivisor T j hj).IsAdmissible := by
  have := hV.charZero
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have := hV.smooth
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    ((isSmoothDivisor_iff T.structMap (T.boundary.get ⟨j, hj⟩)).mp
      (isSmoothDivisor_boundary_get T hV j hj)).2
  have := hsm
  have hlft : AlgebraicGeometry.LocallyOfFiniteType
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hqc : AlgebraicGeometry.QuasiCompact
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  exact
    { charZero := hV.charZero
      locallyOfFiniteType := hlft
      nonzeroOnComponents := nonzeroOnComponents_comap_lowerIdealAfterBlowup T hV hOB hbal j hj
      one_le_mult := hV.one_le_mult
      quasiCompact := hqc
      smooth := hsm
      snc := DivisorReductionBoundary.inStrictNormalCrossingPosition_comap_lowerBoundaryAfterBlowup T hV j hj }

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdealTop
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

theorem containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ) (hj : j < T.boundary.length)
    (J : (T.boundary.get ⟨j, hj⟩).subscheme.IdealSheafData)
    (hm : T.mult = 1)
    (hlow : (T.withSchemeIdealBoundary (T.boundary.get ⟨j, hj⟩).subscheme
        ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) J
        (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (T.boundary.eraseIdx j))).IsAdmissible)
    (hpush : T.ideal = imageIdealSheaf (T.boundary.get ⟨j, hj⟩).subschemeι J) :
    DivisorReduction.containedComponentsIdeal T j hj = ⊤ := by
  by_cases h : IsOpen (divisorComponentsInOrderLocus T j hj)
  · have hnz : NonzeroOnComponents J := hlow.nonzeroOnComponents
    have hcomap : T.ideal.comap (T.boundary.get ⟨j, hj⟩).subschemeι = J := by
      rw [hpush]
      exact Blowup.comap_map_of_isClosedImmersion _ J
    have hsub : ∀ y : ↥(T.boundary.get ⟨j, hj⟩).subscheme,
        (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ (T.ideal.support : Set ↥T.scheme) →
        y ∈ (J.support : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := by
      intro y hy
      have h1 := (one_le_orderAt_iff_mem_support T.ideal
        ((T.boundary.get ⟨j, hj⟩).subschemeι y)).mpr hy
      have h2 := orderAt_le_orderAt_comap (T.boundary.get ⟨j, hj⟩).subschemeι T.ideal y
      rw [hcomap] at h2
      exact (one_le_orderAt_iff_mem_support J y).mp (le_trans h1 h2)
    have hempty : divisorComponentsInOrderLocus T j hj = ∅ := by
      ext x
      refine ⟨fun hx => ?_, fun hx => ((Set.mem_empty_iff_false x).mp hx).elim⟩
      exfalso
      obtain ⟨C, hCpre, hxC, hCmax⟩ :=
        exists_preirreducible ({x} : Set ↥(T.boundary.get ⟨j, hj⟩).subscheme)
          isIrreducible_singleton.2
      have hxC' : x ∈ C := hxC rfl
      have hC : C ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
        ⟨⟨⟨x, hxC'⟩, hCpre⟩, fun u hu hCu => le_of_eq (hCmax u hu.2 hCu)⟩
      refine hnz C hC ?_
      intro y hyC
      have hyc : y ∈ connectedComponent x :=
        hCpre.isPreconnected.subset_connectedComponent hxC' hyC
      have h1 := hx hyc
      rw [hm] at h1
      have h1' : (T.boundary.get ⟨j, hj⟩).subschemeι y ∈ orderAtLeastLocus T.ideal 1 := h1
      exact hsub y ((mem_orderAtLeastLocus_one_iff T.ideal _).mp h1')
    rw [containedComponentsIdeal_eq_openSubschemeKer T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty,
      support_openSubschemeKer (T.boundary.get ⟨j, hj⟩) ⟨divisorComponentsInOrderLocus T j hj, h⟩
        (isClosed_divisorComponentsInOrderLocus T hV j hj), Set.image_eq_empty]
    exact hempty
  · exact EmbeddedResolution.containedComponentsIdeal_eq_top_of_not_isOpen T j hj h

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem lowerIdealWithoutBlowup_eq_ideal (T : MarkedIdealWithBoundary.{u}) :
    DivisorReduction.lowerIdealWithoutBlowup T = T.ideal := by
  show T.ideal.comap (CategoryTheory.CategoryStruct.id T.scheme) = T.ideal
  exact Scheme.IdealSheafData.comap_id _

private theorem orderAt_le_mult_of_isOrderBoundedByMult (T : MarkedIdealWithBoundary.{u}) (hOB : T.IsOrderBoundedByMult) :
    ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) := hOB

private theorem isDerivBalanced_of_isBalanced (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hbal : T.IsBalanced hV.locallyOfFiniteType) :
    ∀ [_inst : AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsDerivBalanced T.base T.structMap T.ideal T.mult := by
  intro _
  exact hbal

private theorem goingUpInvariant_length_of_isBalanced (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (hlift : StrictNormalCrossingsLiftFromDivisor.{u})
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (hbal : T.IsBalanced hV.locallyOfFiniteType)
    [AlgebraicGeometry.IsNoetherian T.scheme]
    [AlgebraicGeometry.Smooth T.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
    [CharZero T.base]
    (j : ℕ) (hj : j < T.boundary.length)
    (hVlow : (DivisorReduction.restrictToDivisor T j hj).IsAdmissible)
    (s : (DivisorReduction.restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).CentersContainNoComponent) :
    DivisorReduction.GoingUpInvariant hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
      (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr s.length := by
  have hbalLower : IsDerivBalanced T.base T.structMap (DivisorReduction.lowerIdealWithoutBlowup T) T.mult := by
    rw [lowerIdealWithoutBlowup_eq_ideal]
    exact hbal
  have hE₀ : InStrictNormalCrossingPosition T.structMap (DivisorReduction.lowerBoundaryWithoutBlowup T) := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    exact hV.snc
  have hjE : j < (DivisorReduction.lowerBoundaryWithoutBlowup T).length := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    exact hj
  have hget : (DivisorReduction.lowerBoundaryWithoutBlowup T)[j]'hjE = T.boundary[j]'hj := by
    simp [DivisorReduction.lowerBoundaryWithoutBlowup_eq T]
  have hlen : ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j).length = T.boundary.length - 1 := by
    rw [DivisorReduction.lowerBoundaryWithoutBlowup_eq]
    simp [List.length_eraseIdx, hj]
  have htrunc : List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j)
      = (DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j := by
    rw [← hlen, List.take_length]
  exact DivisorReduction.goingUpInvariant_of_le hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
    (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr hbalLower hV.one_le_mult hVlow hlift hE₀ hjE hget
    htrunc s.length le_rfl

theorem divisorReductionProperties_of_blowupPreservesNoetherian (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) : DivisorReductionProperties hres hno := by
  have hlift : StrictNormalCrossingsLiftFromDivisor.{u} := hasStrictNormalCrossingsWith_ker_cons_of_comap
  exact
    { isMarked_pushedTop := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr
        have := inst
        exact DivisorReduction.isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow s hpr
      isMarked_pushedPre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr
        have := inst
        exact DivisorReduction.isMarked_prepend_ambientBlowupSeq hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
          s hpr
          (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
          (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
          (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
          (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
          (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
            (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
      valid_lowerPre := by
        intro T hV hOB hbal j hj hZ
        exact DivisorReduction.isAdmissible_restrictTwistedToDivisor T hV hOB hbal j hj hZ
      orderAt_ctrlIdeal_le_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr i hi x
        have := inst
        have := hV.charZero
        have := hV.smooth
        exact orderAt_controlledTransform_le_of_isMarked T.base T.structMap T.ideal T.mult T.boundary
          (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealWithoutBlowup T)
            (DivisorReduction.lowerBoundaryWithoutBlowup T) s hpr)
          (DivisorReduction.isMarked_ambientBlowupSeq_of_containedComponentsIdeal_eq_top hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow
            s hpr)
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) i
          (by rw [DivisorReduction.ambientBlowupSeq_length]; exact hi) x
      orderAt_ctrlIdeal_le_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr i hi x
        have := inst
        have := hV.charZero
        have := hV.smooth
        exact orderAt_controlledTransform_le_of_isMarked T.base T.structMap T.ideal T.mult T.boundary
          (BlowupSequenceData.prepend (DivisorReduction.containedComponentsIdeal T j hj) hb
            (DivisorReduction.ambientBlowupSeq hres hno T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
              (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr))
          (DivisorReduction.isMarked_prepend_ambientBlowupSeq hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
            s hpr
            (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
            (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
            (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
            (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
            (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
              (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)))
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) i
          (by rw [BlowupSequenceData.prepend_length, DivisorReduction.ambientBlowupSeq_length]; exact hi) x
      coSupport_inter_ker_eq_empty_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr hempty
        have := inst
        have := hV.charZero
        have := hV.smooth
        have := hV.locallyOfFiniteType
        have hgoingUp := goingUpInvariant_length_of_isBalanced hres hno hlift T hV hbal j hj hVlow s hpr
        exact DivisorReduction.orderAtLeastLocus_inter_support_ker_eq_empty hres hno T j hj s hpr
          (fun i hi => hgoingUp.exists_exceptionalIdeal_pow_mul_eq_comap_controlledTransform i hi) hempty
      coSupport_inter_ker_eq_empty_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr hempty
        have := inst
        have := hV.charZero
        have := hV.smooth
        have := hV.locallyOfFiniteType
        obtain ⟨U₀, hU, hsupp, hbalPre, hinv⟩ :=
          DivisorReduction.exists_isClosed_opens_goingUpInvariantOnOpen hres hno hlift T hV
            (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
            s hpr
            (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
            (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
            (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
            (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
            (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
              (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
        exact DivisorReduction.orderAtLeastLocus_controlledTransform_inter_ker_support_eq_empty hres hno T j hj hb s hpr
          (fun i hi => (hinv s.length le_rfl).exists_pow_mul_eq_comap_controlledTransform i hi)
          (DivisorReduction.controlledTransform_prepend_ambientBlowupSeq_one hres hno T j hj hb s hpr) hempty
      isPullbackSeq_ambientTower := by
        intro X Y S S' σ σ' φ ψ _ _ _ _ _ hsq d d' hc hc' hpb
        exact isPullbackBlowupSequence_ambientBlowupSequence_of_flat hres hno σ σ' φ ψ hsq d d' hc hc' hpb
      isStrictPullbackSeq_ambientTower := by
        intro X Y S S' σ σ' φ ψ _ _ _ _ _ hsq d d' hc hc' hpb
        exact isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat hres hno σ σ' φ ψ hsq d d' hc hc' hpb
      comap_ctrlIdeal_top := by
        intro T hV hOB hbal j hj hZ hVlow inst s hpr i hi
        have := inst
        exact DivisorReduction.comap_controlledTransform_of_containedComponentsIdeal_eq_top hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hVlow
          s hpr i hi
      comap_ctrlIdeal_pre := by
        intro T hV hOB hbal j hj hZ hb hVlow inst s hpr i hi
        have := inst
        exact DivisorReduction.comap_controlledTransform_prepend_ambientBlowupSeq hres hno hlift T hV
          (orderAt_le_mult_of_isOrderBoundedByMult T hOB) (isDerivBalanced_of_isBalanced T hV hbal) j hj hZ hb hVlow
          s hpr
          (smooth_subschemeι_containedComponentsIdeal_comp T hV j hj)
          (hasStrictNormalCrossingsWith_containedComponentsIdeal T hV j hj)
          (support_containedComponentsIdeal_subset_orderAtLeastLocus T hV j hj)
          (exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj)
          (DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
            (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj))
          i hi
      preIdeal_baseChange := by
        intro T hV L _ _ f hV' j hj hj'
        exact containedComponentsIdeal_baseChange T hV L f hV' j hj hj'
      preIdeal_pullbackAlong := by
        intro T hV Y q h _ hq hV' j hj hj'
        exact containedComponentsIdeal_pullbackAlong_of_smooth T hV Y q h hq hV' j hj hj'
      preIdeal_eq_top_of_imageIdeal := by
        intro T hV j hj J hm hlow hpush
        exact DivisorReduction.containedComponentsIdeal_eq_top_of_eq_imageIdealSheaf T hV j hj J hm hlow hpush }

end FunctorialResolution.EmbeddedResolution

end
