module

public import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupLiftCongruence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.WeakTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.RadicalCenterIdeal

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

structure MaxContactCoverProperties : Prop where
  strictTransform_admissible :
    ∀ (k : Type u) [Field k] [CharZero k] {P P₁ : Scheme.{u}}
      (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.IsLocallyNoetherian P₁]
      (π : P₁ ⟶ P) [AlgebraicGeometry.LocallyOfFiniteType (π ≫ p)]
      (Z : P.IdealSheafData) (E : List P.IdealSheafData),
      HasStrictNormalCrossingsWith p Z E → Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ (A : P.IdealSheafData) (A₁ : P₁.IdealSheafData) (μ : ℕ), 1 ≤ μ →
        (∀ x : ↥P, orderAt A x ≤ (μ : ℕ∞)) →
        (Z.support : Set ↥P) ⊆ orderAtLeastLocus A μ →
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        ∀ H : P.IdealSheafData, IsMaxContactHypersurface k p A μ H →
          IsMaxContactHypersurface k (π ≫ p) A₁ μ (Blowup.strictTransform π Z H)
  coSupport_le_preimage :
    ∀ {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z : X.IdealSheafData), Blowup.IsBlowupAlongIdealSheaf π Z →
      ∀ (A : X.IdealSheafData) (A₁ : X₁.IdealSheafData) (μ : ℕ),
        Blowup.exceptionalIdeal π Z ^ μ * A₁ = A.comap π →
        (Z.support : Set ↥X) ⊆ orderAtLeastLocus A μ →
        orderAtLeastLocus A₁ μ ⊆ (⇑π.base) ⁻¹' orderAtLeastLocus A μ
  schemeDim_level_le :
    ∀ T : MarkedIdealWithBoundary.{u}, T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      krullDimSucc (s.toSequenceOfBlowups.schemeAt i) ≤ T.krullDimSucc
  exists_goodCover :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∃ D : MaxContactReduction.FiniteOpenCoverWithIdeals T,
        MaxContactReduction.IsMaxContactCover T D hv.locallyOfFiniteType
          (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)
  hasSNCWith_cons :
    ∀ (k : Type u) [Field k] {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
      [AlgebraicGeometry.Smooth p] (Z H : P.IdealSheafData) (N : List P.IdealSheafData),
      AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) →
      InStrictNormalCrossingPosition p (H :: N) → HasStrictNormalCrossingsWith p Z N → H ≤ Z →
      HasStrictNormalCrossingsWith p Z (H :: N)
  valid_level :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      (T.transformAt s i).IsAdmissible
  orderAt_level_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
        ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞)
  coverTriple_dim_le :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      krullDimSucc (MaxContactCoverData.coverTriple T hv).scheme ≤ T.krullDimSucc
  coverTriple_valid :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      (MaxContactCoverData.coverTriple T hv).IsAdmissible
  coverContact_admissible :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      ∀ [AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap],
        IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
          (MaxContactCoverData.coverTriple T hv).structMap
          (MaxContactCoverData.coverTriple T hv).ideal (MaxContactCoverData.tunedMult T)
          (MaxContactCoverData.coverMaxContactIdeal T hv)
  coverContact_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible),
      MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
        (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T) →
      InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
        [MaxContactCoverData.coverMaxContactIdeal T hv]
  tuning : TunedSheafProperties.{u}

theorem MaxContactCoverProperties.krullDimSucc_schemeAt_le_dim (hf : MaxContactCoverProperties.{u}) {S : MarkedIdealWithBoundary.{u}} (hv : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) (i : ℕ) (hi : i ≤ s.length) :
    krullDimSucc (s.obj i) ≤ S.krullDimSucc :=
  hf.schemeDim_level_le S hv s.toMarkedSequenceOfBlowups i (by simpa using hi)

theorem MaxContactCoverProperties.derivedTriple_dim_le (hf : MaxContactCoverProperties.{u}) {T S : MarkedIdealWithBoundary.{u}} (hv : S.IsAdmissible)
    (s : MarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType (s.proj s.length ≫ S.structMap))
    (extra : List (s.obj s.length).IdealSheafData) (keep : ℕ) (hdim : S.krullDimSucc ≤ T.krullDimSucc) :
    (MaxContactCoverData.derivedTriple S s hft extra keep).krullDimSucc ≤ T.krullDimSucc :=
  le_trans (hf.krullDimSucc_schemeAt_le_dim hv s s.length le_rfl) hdim

private theorem isMaxContactHypersurface_of_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p q : X ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.LocallyOfFiniteType q] (h : p = q) {A : X.IdealSheafData} {m : ℕ}
    {H : X.IdealSheafData} (hH : IsMaxContactHypersurface k p A m H) :
    IsMaxContactHypersurface k q A m H := by
  subst h
  exact hH

theorem MaxContactCoverProperties.isMaxContactHypersurface_strictTransform_succ (hf : MaxContactCoverProperties.{u}) {T : MarkedIdealWithBoundary.{u}}
    (hv : T.IsAdmissible) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec i)]
    [AlgebraicGeometry.LocallyOfFiniteType (s.projectionToSpec (i + 1))]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hH : IsMaxContactHypersurface T.base (s.projectionToSpec i) (s.ideal i) T.mult H) :
    IsMaxContactHypersurface T.base (s.projectionToSpec (i + 1)) (s.ideal (i + 1)) T.mult
      (Blowup.strictTransform (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) H) := by
  have hi' : i ≤ s.toSequenceOfBlowups.length := le_of_lt hi
  have hvi := hf.valid_level T hv s i hi'
  have hvi1 := hf.valid_level T hv s (i + 1) hi
  have : CharZero T.base := hv.charZero
  have : AlgebraicGeometry.Smooth (s.projectionToSpec i) := hvi.smooth
  have hno : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (i + 1)) := hvi1.isNoetherian
  have : AlgebraicGeometry.IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (i + 1)) := inferInstance
  have : AlgebraicGeometry.LocallyOfFiniteType
      (s.toSequenceOfBlowups.transitionMapSucc i ≫ s.projectionToSpec i) := by
    rw [← MarkedSequenceOfBlowups.projectionToSpec_succ]
    infer_instance
  have hsnc : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (s.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc i hi
  have key := hf.strictTransform_admissible T.base (s.projectionToSpec i)
    (s.toSequenceOfBlowups.transitionMapSucc i) (s.toSequenceOfBlowups.center i) (s.boundary i) hsnc
    (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism i hi) (s.ideal i) (s.ideal (i + 1)) T.mult
    hv.one_le_mult (hf.orderAt_level_le T hv hord s i hi') (s.center_order i hi)
    (s.ideal_succ i hi) H hH
  exact isMaxContactHypersurface_of_eq (MarkedSequenceOfBlowups.projectionToSpec_succ s i).symm key

theorem MaxContactCoverProperties.hasStrictNormalCrossingsWith_cons_of_le_center (hf : MaxContactCoverProperties.{u}) {T : MarkedIdealWithBoundary.{u}}
    (s : T.SequenceOfBlowups) (i : ℕ) (hi : i < s.toSequenceOfBlowups.length)
    [AlgebraicGeometry.Smooth (s.projectionToSpec i)]
    (H : (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (N : List (s.toSequenceOfBlowups.schemeAt i).IdealSheafData)
    (hsnc : InStrictNormalCrossingPosition (s.projectionToSpec i) (H :: N))
    (hZN : HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) N)
    (hHZ : H ≤ s.toSequenceOfBlowups.center i) :
    HasStrictNormalCrossingsWith (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) (H :: N) := by
  have hsm : AlgebraicGeometry.Smooth
      ((s.toSequenceOfBlowups.center i).subschemeι ≫ s.projectionToSpec i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_smooth i hi
  exact hf.hasSNCWith_cons T.base (s.projectionToSpec i) (s.toSequenceOfBlowups.center i) H N hsm hsnc hZN hHZ

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_eq_empty_of_comap_eq_empty {A B : Scheme.{u}} (f : A ⟶ B)
    [AlgebraicGeometry.Surjective f] (J : B.IdealSheafData) (μ : ℕ)
    (h : orderAtLeastLocus (J.comap f) μ = ∅) : orderAtLeastLocus J μ = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  obtain ⟨y, rfl⟩ := f.surjective x
  have hmem : y ∈ orderAtLeastLocus (J.comap f) μ := by
    rw [mem_orderAtLeastLocus_iff]
    exact le_trans ((mem_orderAtLeastLocus_iff J μ (f.base y)).mp hx)
      (orderAt_le_orderAt_comap f J y)
  rw [h] at hmem
  simp at hmem

namespace MaxContactFunctoriality

theorem OrderReductionHypotheses.dropTrivialBoundary {P : ℕ → Prop} {T : MarkedIdealWithBoundary.{u}} (h : OrderReductionHypotheses P T)
    {hinv : ComapIsoInvariance.{u}} {A : ℕ → PrincipalizationAssignment.{u}} {B : PrincipalizationAssignment.{u}}
    (hd : DescentHypotheses hinv P A B) : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := by
  refine ⟨?_, ?_, ?_, hd.valid_trim T h.valid⟩
  · have hdim := h.dim_prop
    rwa [← MaxContactReduction.dropTrivialBoundary_dim T] at hdim
  · intro x
    exact h.orderLE x
  · exact h.coSupport_nonempty

section

variable (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
  (B : PrincipalizationAssignment.{u})

theorem isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T)
    (d : BlowupSequenceData T.scheme) :
    (d.IsMarked T.structMap T.ideal T.mult T.boundary ↔
      d.IsMarked T.structMap (MaxContactCoverData.balancedTunedIdeal T h.valid)
        (MaxContactCoverData.tunedMult T) T.boundary) ∧
    (d.IsMarked T.structMap T.ideal T.mult T.boundary →
      ∀ i ≤ d.length,
        orderAtLeastLocus (d.controlledTransform (MaxContactCoverData.balancedTunedIdeal T h.valid)
            (MaxContactCoverData.tunedMult T) i) (MaxContactCoverData.tunedMult T) =
          orderAtLeastLocus (d.controlledTransform T.ideal T.mult i) T.mult) := by
  have := h.valid.charZero
  have := h.valid.smooth
  have := h.valid.locallyOfFiniteType
  have h2 := hd.tuning
  unfold IsMarkedIffBalancedTunedSheaf at h2
  have key := h2 T.base T.scheme T.structMap T.ideal T.mult h.valid.one_le_mult
    ⟨(orderLE_iff T.ideal T.mult).mpr h.orderLE, h.coSupport_nonempty⟩ T.boundary d
  exact ⟨key.1, key.2.1⟩

theorem exists_blowupSequenceData_isStrictPullback_cover (hstar : CoverSequenceProperties hinv P A)
    (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) :
    ∃ (d : BlowupSequenceData T.scheme)
      (hm : d.IsMarked T.structMap T.ideal T.mult T.boundary),
      IsStrictPullbackBlowupSeq
          (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
          (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
            (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups
          d.toSequenceOfBlowups ∧
        maxContactPrincipalization hinv A T =
          (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm).toMarkedSequenceOfBlowups := by
  obtain ⟨d0, hpb0⟩ := hstar.descends (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd)
  obtain ⟨d, hdesc⟩ :
      ∃ e : BlowupSequenceData (MaxContactReduction.dropTrivialBoundary T).scheme,
        MaxContactReduction.descendStrictPullback (MaxContactReduction.dropTrivialBoundary T)
            (MaxContactCoverData.coverTriple (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
            (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
            (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))) = some e :=
    MaxContactCoverData.exists_descendStrictPullback_eq_some _ _ ⟨d0, hpb0⟩
  have hpb : IsStrictPullbackBlowupSeq
      (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
      (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
        (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups d.toSequenceOfBlowups :=
    MaxContactCoverData.isStrictPullbackBlowupSeq_of_descendStrictPullback_eq_some _ _ hdesc
  have hm0 : d.IsMarked (MaxContactReduction.dropTrivialBoundary T).structMap
      (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid)
      (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
      (MaxContactReduction.dropTrivialBoundary T).boundary :=
    hd.isMarked (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) d hpb
  have hm1 : d.IsMarked T.structMap T.ideal T.mult (MaxContactReduction.dropTrivialBoundary T).boundary :=
    ((isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) d).1).mpr hm0
  have hm : d.IsMarked T.structMap T.ideal T.mult T.boundary :=
    hd.isMarked_of_trim T h.valid d T.ideal T.mult hm1
  refine ⟨d, hm, hpb, ?_⟩
  exact MaxContactCoverData.reduceOrder_eq_toMarkedSequence hinv T (lowerDimensionalFamily A T) h.valid
    h.orderAtLeastLocus_ne_empty (h.dropTrivialBoundary hd).valid d hdesc hm

theorem length_eq_zero_of_orderAtLeastLocus_eq_empty (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (_hdim : P T.krullDimSucc)
    (_hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (hemp : orderAtLeastLocus T.ideal T.mult = ∅) :
    (maxContactPrincipalization hinv A T).length = 0 := by
  have h1 : MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T) = MaxContactReduction.emptyMarkedSeq T :=
    MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
  rw [maxContactPrincipalization_apply, h1, MaxContactCoverData.emptyMarkedSeq_length]

theorem center_support_nonempty (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hdim : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (i : ℕ) (hi : i < (maxContactPrincipalization hinv A T).length) :
    (↑((maxContactPrincipalization hinv A T).center i).support :
      Set ↥((maxContactPrincipalization hinv A T).schemeAt i)).Nonempty := by
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · exfalso
    have hb : maxContactPrincipalization hinv A T = MaxContactReduction.emptyMarkedSeq T :=
      MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
    rw [hb, MaxContactCoverData.emptyMarkedSeq_length] at hi
    exact Nat.not_lt_zero i hi
  · have h : OrderReductionHypotheses P T := ⟨hdim, hord, Set.nonempty_iff_ne_empty.mpr hemp, hv⟩
    obtain ⟨d, hm, hpb, heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T h
    have hstarseq : ∀ j : ℕ,
        j < (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups.length →
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd).valid hinv
              (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toBlowupSequenceData.toSequenceOfBlowups.center j ≠ ⊤ := by
      intro j hj
      rw [BlowupSequenceData.toSequenceOfBlowups_length] at hj
      exact hstar.center_ne_top (MaxContactReduction.dropTrivialBoundary T) (h.dropTrivialBoundary hd) j hj
    have hdseq := hpb.center_ne_top_of_forall_center_ne_top hstarseq
    rw [heq] at hi ⊢
    rw [BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups] at hi ⊢
    exact (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mpr (hdseq i hi)

private theorem orderAtLeastLocus_controlledTransform_eq_empty_of_flat_surjective {k : Type u} [Field k] {X' X : Scheme.{u}}
    {q : X' ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X}
    (hflat : AlgebraicGeometry.Flat g) (hsurj : AlgebraicGeometry.Surjective g)
    {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (t : MarkedBlowupSequenceData q (I.comap g) m (List.map (fun Z => Z.comap g) E))
    (D : StrictPullbackBlowupSeq g t.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hdiv : ∀ i < d.length, ∃ Bb,
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ m * Bb = (d.controlledTransform I m i).comap (d.map i))
    (hres : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus (d.controlledTransform I m d.length) m = ∅ := by
  have := hflat
  have := hsurj
  have : AlgebraicGeometry.Surjective (t.strictPullbackComparisonMap D t.length le_rfl) :=
    MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap t D t.length le_rfl
  have hid : t.ideal t.length
      = (d.controlledTransform I m t.length).comap (t.strictPullbackComparisonMap D t.length le_rfl) :=
    MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform t D hdiv t.length le_rfl
  have hlen : t.length = d.length := MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq t D
  have h0 : orderAtLeastLocus ((d.controlledTransform I m t.length).comap (t.strictPullbackComparisonMap D t.length le_rfl)) m = ∅ := by
    rw [← hid]
    exact hres
  have h1 := orderAtLeastLocus_eq_empty_of_comap_eq_empty (t.strictPullbackComparisonMap D t.length le_rfl)
    (d.controlledTransform I m t.length) m h0
  rwa [hlen] at h1

theorem isResolution_of_orderAt_le_mult (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hdim : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) :
    (maxContactPrincipalization hinv A T).IsResolution := by
  rw [MarkedSequenceOfBlowups.isResolution_iff, MarkedSequenceOfBlowups.lastIdeal_eq]
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have h1 : MaxContactReduction.reduceOrder hinv T (lowerDimensionalFamily A T) = MaxContactReduction.emptyMarkedSeq T :=
      MaxContactReduction.reduceOrder_of_orderAtLeastLocus_eq_empty hinv T (lowerDimensionalFamily A T) hv hemp
    rw [maxContactPrincipalization_apply, h1, MaxContactCoverData.emptyMarkedSeq_length, MarkedSequenceOfBlowups.ideal_zero,
      hinv.coSupport_comap, hemp, Set.preimage_empty]
  · have h : OrderReductionHypotheses P T := ⟨hdim, hord, Set.nonempty_iff_ne_empty.mpr hemp, hv⟩
    have h' : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := h.dropTrivialBoundary hd
    obtain ⟨d, hm, hpb, heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T h
    rw [heq]
    simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, MarkedBlowupSequenceData.toMarkedSequence_length,
      BlowupSequenceData.toMarkedBlowupSequenceData_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_length]
    have hm0 : d.IsMarked (MaxContactReduction.dropTrivialBoundary T).structMap
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
        (MaxContactReduction.dropTrivialBoundary T).boundary :=
      hd.isMarked (MaxContactReduction.dropTrivialBoundary T) h' d hpb
    have htc := (isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) h' d).2
      ((isMarked_balancedTunedIdeal_iff_and_orderAtLeastLocus_eq hinv P A B hd (MaxContactReduction.dropTrivialBoundary T) h' d).1.mpr hm0) d.length le_rfl
    have D : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) h'.valid hinv
          (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T))).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups := by
      rw [MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups]
      exact hpb.toStrictPullbackBlowupSeq
    have key : orderAtLeastLocus (d.controlledTransform
        (MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T)) d.length)
        (MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T)) = ∅ :=
      orderAtLeastLocus_controlledTransform_eq_empty_of_flat_surjective (hd.flat_coverMap (MaxContactReduction.dropTrivialBoundary T) h')
        (hd.surjective_coverMap (MaxContactReduction.dropTrivialBoundary T) h')
        (I := MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) h'.valid)
        (m := MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T))
        (E := (MaxContactReduction.dropTrivialBoundary T).boundary) (d := d)
        (MaxContactCoverData.coverMarkedBlowupData (MaxContactReduction.dropTrivialBoundary T) h'.valid hinv
          (lowerDimensionalFamily A (MaxContactReduction.dropTrivialBoundary T)))
        D hm0.divisible (hstar.resolves (MaxContactReduction.dropTrivialBoundary T) h')
    exact htc.symm.trans key

theorem orderAt_ideal_le_mult (hd : DescentHypotheses hinv P A B) (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (_hdim : P T.krullDimSucc) (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (i : ℕ) (hi : i ≤ (maxContactPrincipalization hinv A T).length)
    (x : ↥((maxContactPrincipalization hinv A T).schemeAt i)) :
    orderAt ((maxContactPrincipalization hinv A T).ideal i) x ≤ (T.mult : ℕ∞) :=
  hd.order_le T hv hord (maxContactPrincipalization hinv A T) i hi x

end

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometry
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OrderReductionCorrectness

theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform.{u} := EmbeddedResolution.blowupLiftEqOnControlledTransform

theorem le_of_support_subset_of_smooth : ∀ (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData),
    AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) →
    ∀ J : X.IdealSheafData,
      (((Z.support : Set ↥X)) ⊆ ((J.support : Set ↥X))) → J ≤ Z :=
  smoothSubschemeIdealIsRadical

theorem isLocallyNoetherian_schemeAt : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → AlgebraicGeometry.IsLocallyNoetherian (s.schemeAt i) := by
  intro T hT s i hi
  have : AlgebraicGeometry.IsNoetherian (s.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s i hi
  infer_instance

theorem isBalanced_comap_of_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
    ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
      [AlgebraicGeometry.LocallyOfFiniteType q],
    IsDerivBalanced T.base T.structMap T.ideal T.mult →
    IsDerivBalanced T.base q (T.ideal.comap h) T.mult := by
  intro T hT Y q f _ hq _ _ hbal
  subst hq
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  refine isDerivBalanced_of_pow_le T.base (f ≫ T.structMap) ?_
  intro i hi
  rw [derivIdealSheafIterate_comap T.base T.structMap f i T.ideal,
    ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_pow]
  exact Scheme.IdealSheafData.comap_mono f (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hi)

theorem maxContactIdealComapLeControlled : MaxContactIdealComapLeControlled.{u} := by
  intro k _ _ X X₁ p _ _ π Z E hZ hπ _ _ _ A μ hμ hA A₁ hA₁
  have hct : A₁ = controlledTransform π Z A μ hπ hA :=
    eq_controlledTransform_of_mul_eq_comap π Z A μ hπ hA A₁ hA₁
  have key := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A μ hA
    (μ - 1) (Nat.sub_le μ 1)
  have hsub : μ - (μ - 1) = 1 := by omega
  rw [hsub, pow_one] at key
  simp only [maxContactIdeal_eq_derivIdealSheafIterate]
  rw [hct]
  exact key

theorem existsMaxContactControlledTransforms : ExistsMaxContactControlledTransforms.{u} :=
  existsMaxContactControlledTransforms_of_comapLeControlled maxContactIdealComapLeControlled

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_ideal :
    ∀ (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ orderAtLeastLocus (s.ideal i) T.mult →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T s i
  induction i with
  | zero =>
      intro _ x hx
      rw [s.ideal_zero, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hx
      rw [SequenceOfBlowups.projectionToBase_zero]
      exact hx
  | succ n ih =>
      intro hn x hx
      have hn' : n < s.length := hn
      have h1 : (s.transitionMapSucc n).base x ∈ orderAtLeastLocus (s.ideal n) T.mult :=
        OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n)
          (s.isBlowupAlongIdealSheaf_blowupMorphism n hn') (s.ideal n) (s.ideal (n + 1)) T.mult
          (s.ideal_succ n hn') (s.center_order n hn') hx
      have h2 := ih (le_of_lt hn') _ h1
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      exact h2

theorem projectionToBase_mem_orderAtLeastLocus_of_mem_center : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : Set ↥(s.schemeAt i))) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T hT s i hi x hx
  exact projectionToBase_mem_orderAtLeastLocus_of_mem_ideal T s i (le_of_lt hi) x (s.center_order i hi hx)

theorem isStrictPullback_of_isPullback_of_center_nonempty : ∀ (X' X : Scheme.{u}) (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X), IsPullbackBlowupSequence φ s' s →
    (∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty) →
    (∀ i : ℕ, i < s.length → ∀ x ∈ (((s.center i).support : Set ↥(s.schemeAt i))),
      (s.projectionToBase i).base x ∈ Set.range φ.base) →
    IsStrictPullbackBlowupSeq φ s' s := by
  intro X' X φ s' s hpb hne hran
  exact hpb.isStrictPullback_of_support_comap_center_nonempty (support_comap_center_nonempty_of_mem_range φ s hne hran)

end OrderReductionCorrectness

end FunctorialResolution.EmbeddedResolution

end
end
