module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.FieldExtensionBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionBaseChange

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionTrivialCases
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem SequenceOfBlowups.isomorphic_of_length_eq_zero {X : Scheme.{u}} (B B' : SequenceOfBlowups X)
    (h : B.length = 0) (h' : B'.length = 0) : B.Isomorphic B' := by
  have hl : (BlowupSequenceData.ofSequenceOfBlowups B).length = 0 := by
    rw [BlowupSequenceData.ofSequenceOfBlowups_length]; exact h
  have hl' : (BlowupSequenceData.ofSequenceOfBlowups B').length = 0 := by
    rw [BlowupSequenceData.ofSequenceOfBlowups_length]; exact h'
  have hz : ∀ i : ℕ, i ≤ (BlowupSequenceData.ofSequenceOfBlowups B).length → i = 0 := by
    intro i hi
    rw [hl] at hi
    exact Nat.le_zero.mp hi
  have hrfl1 : ∀ p : (BlowupSequenceData.ofSequenceOfBlowups B).obj 0 = (BlowupSequenceData.ofSequenceOfBlowups B).obj 0,
      eqToIso p = Iso.refl ((BlowupSequenceData.ofSequenceOfBlowups B).obj 0) := fun _ => rfl
  have hrfl2 : ∀ p : (BlowupSequenceData.ofSequenceOfBlowups B').obj 0 = (BlowupSequenceData.ofSequenceOfBlowups B').obj 0,
      eqToIso p = Iso.refl ((BlowupSequenceData.ofSequenceOfBlowups B').obj 0) := fun _ => rfl
  have key : (BlowupSequenceData.ofSequenceOfBlowups B).toSequenceOfBlowups.Isomorphic (BlowupSequenceData.ofSequenceOfBlowups B').toSequenceOfBlowups := by
    refine BlowupSequenceData.toSequenceOfBlowups_isomorphic_of_iso (BlowupSequenceData.ofSequenceOfBlowups B) (BlowupSequenceData.ofSequenceOfBlowups B')
      (by rw [hl, hl'])
      (fun i hi => eqToIso (congrArg (BlowupSequenceData.ofSequenceOfBlowups B).obj (hz i hi)) ≪≫
        (BlowupSequenceData.ofSequenceOfBlowups B).isoZero ≪≫ (BlowupSequenceData.ofSequenceOfBlowups B').isoZero.symm ≪≫
          eqToIso (congrArg (BlowupSequenceData.ofSequenceOfBlowups B').obj (hz i hi).symm)) ?_ ?_ ?_
    · simp only [hrfl1, hrfl2, Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Category.assoc,
        Category.id_comp, Category.comp_id, Iso.inv_hom_id]
    · intro i hi
      exact absurd hi (by rw [hl]; exact Nat.not_lt_zero i)
    · intro i hi
      exact absurd hi (by rw [hl]; exact Nat.not_lt_zero i)
  exact ((BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic B).symm.trans key).trans (BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic B')

theorem principalizationAssignment_mk_isomorphic (f : PrincipalizationAssignment.{u}) (T : MarkedIdealWithBoundary.{u})
    (p : T.scheme ⟶ Spec (CommRingCat.of T.base)) (I : T.scheme.IdealSheafData) (m : ℕ)
    (E : List T.scheme.IdealSheafData) (hp : p = T.structMap) (hI : I = T.ideal)
    (hm : m = T.mult) (hE : E = T.boundary) :
    (f { base := T.base, instField := T.instField, scheme := T.scheme, structMap := p,
          ideal := I, mult := m, boundary := E }).toSequenceOfBlowups.Isomorphic (f T).toSequenceOfBlowups := by
  subst hp
  subst hI
  subst hm
  subst hE
  exact SequenceOfBlowups.isomorphic_refl _

private theorem orderAtLeastLocus_append_eq_empty {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ} {E : List X.IdealSheafData}
    (s : MarkedBlowupSequenceData p I m E)
    (t : MarkedBlowupSequenceData (s.proj s.length ≫ p) (s.ideal s.length) m (s.boundary s.length))
    (hinv : ComapIsoInvariance.{u}) (ht : 0 < t.length)
    (h : orderAtLeastLocus (t.ideal t.length) m = ∅) :
    orderAtLeastLocus ((s.append t hinv).ideal (s.append t hinv).length) m = ∅ := by
  have hlen : (s.append t hinv).length = s.length + t.length :=
    MarkedBlowupSequenceData.append_length s t hinv
  rw [hlen, MarkedBlowupSequenceData.append_ideal_length_add_length s t hinv ht]
  exact orderAtLeastLocus_comap_eqToHom_eq_empty _ _ _ h

theorem orderReductionSeq_isomorphic_of_boundary_nil (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (hmon : MonomialPrincipalizationHypotheses hinv) {n : ℕ} {A B : PrincipalizationAssignment.{u}}
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) {T : MarkedIdealWithBoundary.{u}} (hT : T.IsAdmissible)
    (hdim : T.krullDimSucc ≤ n) (hE : T.boundary = [])
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) :
    (orderReductionSeq hinv T (principalizationOfDimLe T A)).toSequenceOfBlowups.Isomorphic (A T).toSequenceOfBlowups := by
  by_cases hcs : orderAtLeastLocus T.ideal T.mult = ∅
  · exact SequenceOfBlowups.isomorphic_of_length_eq_zero _ _
      (orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A hcs)
      (hspec.trivial_of_coSupport_empty T hT hdim hord hcs)
  · obtain ⟨x₁, hx₁⟩ : (orderAtLeastLocus T.ideal T.mult).Nonempty := Set.nonempty_iff_ne_empty.mpr hcs
    have : Nonempty ↥T.scheme := ⟨x₁⟩
    obtain ⟨x₀, hx₀⟩ := exists_orderAt_eq_maxOrder T.ideal hord
    have hmax : maxOrder T.ideal = T.mult := by
      refine le_antisymm ?_ ?_
      · have h := hord x₀
        rw [hx₀] at h
        exact_mod_cast h
      · have h1 : (T.mult : ℕ∞) ≤ orderAt T.ideal x₁ := hx₁
        have h2 := orderAt_le_maxOrder T.ideal hord x₁
        have h3 : (T.mult : ℕ∞) ≤ ((maxOrder T.ideal : ℕ) : ℕ∞) := le_trans h1 h2
        exact_mod_cast h3
    have hJ0 : lastNonMonomialPart T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
        = T.ideal :=
      hG.nonMonomialPart_eq_ideal_of_boundary_eq_nil T hT hE
    have hμ0 : maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
        = T.mult := by
      have h := congrArg (fun N => maxOrder N) hJ0
      exact h.trans hmax
    have hmem : ((maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) : ℕ) : ℕ∞)
        ≤ orderAt (lastNonMonomialPart T
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)) x₁ := by
      rw [hμ0, hJ0]
      exact hx₁
    have hcont : NonMonomialOrderReductionContinues T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) :=
      ⟨le_of_eq hμ0.symm, ⟨x₁, hmem⟩⟩
    have hlt := maxOrderNonMonomial_extendByNonMonomialPart_lt hG hinv hspec hT hdim
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont
    rw [hμ0] at hlt
    have hnot : ¬ NonMonomialOrderReductionContinues T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)) := by
      intro hc
      have h1 : T.mult ≤ maxOrderNonMonomial T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)) := hc.1
      omega
    have hzero : nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) 0
        = emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary := by
      simp only [nonMonomialOrderReductionIter]
    have hstepc : ∀ j : ℕ, NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) →
        nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1)
          = extendByNonMonomialPart hinv T (principalizationOfDimLe T A) (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) := by
      intro j hj
      simp only [nonMonomialOrderReductionIter]
      split_ifs with h
      · rfl
      · exact absurd hj h
    have hstepn : ∀ j : ℕ, ¬ NonMonomialOrderReductionContinues T (nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j) →
        nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1) = nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) j := by
      intro j hj
      simp only [nonMonomialOrderReductionIter]
      split_ifs with h
      · exact absurd h hj
      · rfl
    have hloop : ∀ j : ℕ, nonMonomialOrderReductionIter hinv T (principalizationOfDimLe T A) (j + 1)
        = extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) := by
      intro j
      induction j with
      | zero =>
          rw [hstepc 0 (by rw [hzero]; exact hcont), hzero]
      | succ j ih =>
          rw [hstepn (j + 1) (by rw [ih]; exact hnot), ih]
    have hnonMonomialEq : nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)
        = extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) := by
      simp only [nonMonomialOrderReduction]
      exact hloop _
    have hconcat := extendByNonMonomialPart_eq_append hG hinv hspec hT hdim
      (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont
    have ht1pos : 0 < (continuationByNonMonomialPart hG hspec hT hdim
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).length := by
      rw [continuationByNonMonomialPart_length hG hspec hT hdim _ hcont]
      exact seqAtEnd_lastNonMonomialPart_length_pos hG hspec hT hdim _ hcont
    have hcong : ∀ (Y : Scheme.{u}) (d : BlowupSequenceData Y) (I₁ I₂ : Y.IdealSheafData) (m₁ m₂ j : ℕ),
        I₁ = I₂ → m₁ = m₂ → d.controlledTransform I₁ m₁ j = d.controlledTransform I₂ m₂ j := by
      intro Y d I₁ I₂ m₁ m₂ j h1 h2
      rw [h1, h2]
    have hcs2 : ∀ (Y : Scheme.{u}) (Jy : Y.IdealSheafData) (m₁ m₂ : ℕ), m₁ = m₂ →
        orderAtLeastLocus Jy m₁ = ∅ → orderAtLeastLocus Jy m₂ = ∅ := by
      intro Y Jy m₁ m₂ h hh
      subst h
      exact hh
    have hnonMonomialLast : (nonMonomialTriple T
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).IsAdmissible :=
      isAdmissible_nonMonomialTriple hG hT _ hcont
    have hdimLast : (nonMonomialTriple T
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).krullDimSucc ≤ n :=
      le_trans (tripleAtLength_dim_le hG hT _ _ _) hdim
    have hboundaryLast : (nonMonomialTriple T
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).IsOrderBoundedByMult := by
      rw [MarkedIdealWithBoundary.IsOrderBoundedByMult.eq_def]
      intro x
      exact orderAt_lastNonMonomialPart_le_maxOrderNonMonomial hG hT
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) x
    have hresolves : MarkedSequenceOfBlowups.IsResolution
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))) :=
      hspec.resolves _ hnonMonomialLast hdimLast hboundaryLast
    have hlocus : orderAtLeastLocus
        ((A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).ideal
          (A (nonMonomialTriple T
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length) T.mult = ∅ := by
      have h := (MarkedSequenceOfBlowups.isResolution_iff _).mp hresolves
      rw [MarkedSequenceOfBlowups.lastIdeal_eq] at h
      exact hcs2 _ _ _ _ hμ0 h
    have hid : (continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).ideal
        (continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).length
        = (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).ideal
          (A (nonMonomialTriple T
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length := by
      have h1 := MarkedBlowupSequenceData.toBlowupSequenceData_controlledTransform_eq
        (MarkedBlowupSequenceData.ofMarkedSequence
          (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))))
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length
        (le_of_eq (MarkedBlowupSequenceData.ofMarkedSequence_length _).symm)
      have h2 := MarkedBlowupSequenceData.ofMarkedSequence_ideal
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)))
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length
      have h3 := hcong _
        (MarkedBlowupSequenceData.ofMarkedSequence
          (A (nonMonomialTriple T
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)))).toBlowupSequenceData
        ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).ideal
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length)
        (lastNonMonomialPart T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))
        T.mult (maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))
        (A (nonMonomialTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).length
        hJ0.symm hμ0.symm
      exact h3.trans (h1.trans h2)
    have hG1 : orderAtLeastLocus ((continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).ideal
        (continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hcont).length) T.mult = ∅ := by
      rw [hid]
      exact hlocus
    have hG2 : orderAtLeastLocus ((extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).ideal
        (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).length) T.mult = ∅ := by
      rw [hconcat]
      exact orderAtLeastLocus_append_eq_empty _ _ hinv ht1pos hG1
    have hmaxOn : ∀ (Y : Scheme.{u}) (N : Y.IdealSheafData),
        maxOrderOn N (∅ : Set ↥Y) = 0 := by
      intro Y N
      rw [maxOrderOn.eq_def]
      simp
    have hnc2 : ¬ CompanionIdealReductionContinues T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)) := by
      intro hc
      have h1 : 1 ≤ maxOrderOn
          (lastNonMonomialPart T (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)))
          (orderAtLeastLocus ((extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
            (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).ideal
            (extendByNonMonomialPart hinv T (principalizationOfDimLe T A)
              (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)).length) T.mult) := hc
      rw [hG2, hmaxOn] at h1
      omega
    have hnc2' : ¬ CompanionIdealReductionContinues T (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) := by
      rw [hnonMonomialEq]
      exact hnc2
    have hcompanionStep : ∀ (s : MarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) (j : ℕ),
        ¬ CompanionIdealReductionContinues T (companionIdealReductionIter hinv T (principalizationOfDimLe T A) s j) →
        companionIdealReductionIter hinv T (principalizationOfDimLe T A) s (j + 1)
          = companionIdealReductionIter hinv T (principalizationOfDimLe T A) s j := by
      intro s j hj
      simp only [companionIdealReductionIter]
      split_ifs with h
      · exact absurd h hj
      · rfl
    have hcompanionIter : ∀ j : ℕ, companionIdealReductionIter hinv T (principalizationOfDimLe T A) (nonMonomialOrderReduction hinv T (principalizationOfDimLe T A)) j
        = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
      intro j
      induction j with
      | zero => simp only [companionIdealReductionIter]
      | succ j ih =>
          rw [hcompanionStep _ j (by rw [ih]; exact hnc2'), ih]
    have hcompanionEq : companionIdealReduction hinv T (principalizationOfDimLe T A) = nonMonomialOrderReduction hinv T (principalizationOfDimLe T A) := by
      simp only [companionIdealReduction]
      exact hcompanionIter _
    have hG3 : orderAtLeastLocus ((companionIdealReduction hinv T (principalizationOfDimLe T A)).ideal
        (companionIdealReduction hinv T (principalizationOfDimLe T A)).length) T.mult = ∅ := by
      rw [hcompanionEq, hnonMonomialEq]
      exact hG2
    have hmonomialLen : (orderReductionMonomialSequence hinv T A).length = 0 := by
      show (MarkedBlowupSequenceData.ofMarkedSequence
        (monomialPrincipalization hinv (orderReductionMonomialTriple hinv T A))).length = 0
      rw [MarkedBlowupSequenceData.ofMarkedSequence_length]
      exact hmon.trivial_of_coSupport_empty _
        (isLocallyMonomialTriple_tripleAtLength_companionIdealReduction hG hinv hspec hT hdim) hG3
    have hAlg : orderReductionSeq hinv T (principalizationOfDimLe T A)
        = (orderReductionData hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups := by
      unfold orderReductionSeq
      rw [if_neg hcs]
    rw [hAlg]
    have e1 : ((orderReductionData hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
        ((companionIdealReduction hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups := by
      rw [orderReductionData_eq_append hinv T A]
      exact MarkedBlowupSequenceData.append_isomorphic_of_length_eq_zero _ _ hinv hmonomialLen
    have e2 : ((companionIdealReduction hinv T (principalizationOfDimLe T A)).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
        ((continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
          hcont).toMarkedSequenceOfBlowups).toSequenceOfBlowups := by
      rw [hcompanionEq, hnonMonomialEq, hconcat]
      exact MarkedBlowupSequenceData.emptyMarkedBlowupSequenceData_append_isomorphic T.structMap T.ideal T.mult T.boundary _ hinv
    have e3 : ((continuationByNonMonomialPart hG hspec hT hdim
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary)
          hcont).toMarkedSequenceOfBlowups).toSequenceOfBlowups.Isomorphic
        (A (nonMonomialTriple T
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).toSequenceOfBlowups := by
      simp only [continuationByNonMonomialPart, BlowupSequenceData.toMarkedBlowupSequenceData_toSequenceOfBlowups,
        MarkedBlowupSequenceData.blowupSequenceData_ofMarkedSequence]
      exact BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _
    have e4 : (A (nonMonomialTriple T
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))).toSequenceOfBlowups.Isomorphic
        (A T).toSequenceOfBlowups :=
      principalizationAssignment_mk_isomorphic A T
        ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).proj
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length ≫ T.structMap)
        (lastNonMonomialPart T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))
        (maxOrderNonMonomial T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary))
        ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).boundary
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length)
        (by rw [emptyMarkedBlowupSequenceData_projectionToBase, Category.id_comp]) hJ0 hμ0 rfl
    exact e1.trans (e2.trans (e3.trans e4))

end FunctorialResolution.EmbeddedResolution

end
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxOrderReduction

private theorem orderAtBaseFieldChangeInvariance_of_geometryHypotheses (hG : PrincipalizationGeometryHypotheses.{u}) :
    OrderAtBaseFieldChangeInvariance.{u} := by
  intro T hT L _ _ f B b pB hpB IB EB hTB Q a b' hpb A y
  subst hpB
  have hQ : IsPullback
      (Limits.pullback.fst b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
      (Limits.pullback.snd b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))) b
      (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    IsPullback.of_hasPullback _ _
  let E : Q ≅ Limits.pullback (b ≫ T.structMap) (specMapOfFieldHom T.base L f) :=
    hpb.isoIsPullback B (Limits.pullback T.structMap (specMapOfFieldHom T.base L f)) hQ ≪≫
      Limits.pullbackRightPullbackFstIso T.structMap (specMapOfFieldHom T.base L f) b
  have he : E.hom ≫ Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f) = a := by
    simp [E, Iso.trans_hom]
  have hcomp : A.comap a =
      (A.comap
        (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f))).comap E.hom := by
    rw [← he]
    simp [Scheme.IdealSheafData.comap_comp]
  have h1 : orderAt (A.comap a) y
      = orderAt (A.comap (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)))
          (E.hom.base y) := by
    rw [hcomp]
    exact FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isIso E.hom _ y
  have h2 := hG.orderAt_baseChange
    (MarkedIdealWithBoundary.mk T.base B (b ≫ T.structMap) IB T.mult EB) hTB L f A (E.hom.base y)
  have h3 : orderAt A
      ((Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)).base (E.hom.base y))
      = orderAt A (a y) := by
    rw [← he]
    simp
  exact h1.trans (h2.trans h3)

theorem monomialPrincipalization_spec (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) : MonomialPrincipalizationHypotheses hinv := by
  have h := isLocallyMonomialPrincipalization_monomialPrincipalization hG.monomialInputs hinv
      (orderAtBaseFieldChangeInvariance_of_geometryHypotheses hG) (fun _ => True)
  exact
    { cert := fun T hTm i hi => h.cert T hTm trivial i hi
      center_nonempty := fun T hTm i hi => h.center_nonempty T hTm trivial i hi
      resolves := fun T hTm => h.resolves T hTm trivial
      trivial_of_coSupport_empty := fun T hTm hc => h.trivial_of_coSupport_empty T hTm trivial hc }

theorem isMaxOrderReduction_orderReductionSeq (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) (fun T => orderReductionSeq hinv T (principalizationOfDimLe T A)) A := by
  have hmon : MonomialPrincipalizationHypotheses hinv := monomialPrincipalization_spec hG hinv
  refine
    { cert := fun T hT hdim i hi => certificate_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      orderRed_equiv := fun T hT hdim hE hord =>
        orderReductionSeq_isomorphic_of_boundary_nil hG hinv hmon hspec hT hdim hE hord
      center_nonempty := fun T hT hdim i hi =>
        center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      resolves := fun T hT hdim => isResolution_orderReductionSeq hG hinv hmon hspec hT hdim
      trivial_of_coSupport_empty := fun T hT hdim hc =>
        orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A hc
      base_change := ?_
      base_change_strict := ?_
      smooth_pullback := ?_
      smooth_pullback_strict := ?_ }
  · intro T hT hdim L _ _ f E' hE hT' hdim'
    exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
      (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
      (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
  · intro T hT hdim L _ _ f E' hE hT' hdim'
    have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
      (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
      (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
    have hsurj : AlgebraicGeometry.Surjective (baseChangeProj T L f) :=
      instSurjectivePullbackFstSpecMapField T.base L f T.scheme T.structMap
    exact hp.isStrictPullback_of_surjective fun i hi =>
      (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
        (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)
  · intro T hT hdim Y q h hsm hq E' hE hT' hdim'
    have := hsm
    exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
      hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)
  · intro T hT hdim Y q h hsm hsurj hq E' hE hT' hdim'
    have := hsm
    have := hsurj
    have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
      hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)
    exact hp.isStrictPullback_of_surjective fun i hi =>
      (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
        (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)

theorem isMaxOrderReduction_canonicalAlgorithmRules (hG : PrincipalizationGeometryHypotheses.{u})
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (n : ℕ) (A B : PrincipalizationAssignment.{u})
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) ((canonicalAlgorithmRules hres).maxOrderFamily A) A :=
  isMaxOrderReduction_orderReductionSeq hG comapIsoInvariance n A B hspec

end MaxOrderReduction

end FunctorialResolution.EmbeddedResolution

end
