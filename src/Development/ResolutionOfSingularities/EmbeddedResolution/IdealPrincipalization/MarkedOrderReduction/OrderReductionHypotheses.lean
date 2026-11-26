module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ExceptionalMonomialOrder
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MaxOrderReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponentsFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing

@[expose] public section

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplittingUniqueness
universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}}

theorem orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow [IsLocallyNoetherian X]
    (M : X.IdealSheafData) (η : X) (a : ℕ)
    (hM : stalkIdeal M η = IsLocalRing.maximalIdeal ↥(X.presheaf.stalk η) ^ a)
    (hfin : orderAt M η ≠ ⊤) :
    orderAt M η = (a : ℕ∞) := by
  have hnoe : IsNoetherianRing (X.presheaf.stalk η) := inferInstance
  have hbot : stalkIdeal M η ≠ ⊥ := fun h => hfin ((orderAt_eq_top_iff M η).mpr h)
  have hle : (a : ℕ∞) ≤ orderAt M η := (le_orderAt_iff M η a).mpr (le_of_eq hM)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hordn : orderAt M η = (n : ℕ∞) := hn.symm
  have han : a ≤ n := by
    rw [hordn] at hle
    exact_mod_cast hle
  have hna : n ≤ a := by
    by_contra hc
    push Not at hc
    have hc' : a + 1 ≤ n := by omega
    have h1 : ((a + 1 : ℕ) : ℕ∞) ≤ orderAt M η := by
      rw [hordn]
      exact_mod_cast hc'
    have h2 : stalkIdeal M η ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ (a + 1) :=
      (le_orderAt_iff M η (a + 1)).mp h1
    have hps : IsLocalRing.maximalIdeal (X.presheaf.stalk η) •
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a)
        = IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ (a + 1) := by
      rw [Ideal.smul_eq_mul, pow_succ, mul_comm]
    have hsm : (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) ≤
        IsLocalRing.maximalIdeal (X.presheaf.stalk η) •
          (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) := by
      rw [hps, ← hM]
      exact h2
    have hz : (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a) = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk η) ^ a)
        (IsNoetherian.noetherian _) hsm
        (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    exact hbot (by rw [hM, hz])
  rw [hordn]
  exact_mod_cast le_antisymm hna han

def IsMonomialOnOpen (E : List X.IdealSheafData) (M : X.IdealSheafData) (U : X.Opens)
    (a : Fin E.length → ℕ) : Prop :=
  restrictIdeal M U =
    ((List.finRange E.length).map (fun j => restrictIdeal (E.get j) U ^ a j)).prod

private theorem ideal_map_listProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (L : List (Ideal R)) :
    Ideal.map f L.prod = (L.map (fun I => Ideal.map f I)).prod :=
  map_list_prod (Ideal.mapHom f) L

private theorem eq_of_ideal_map_eq_of_ringHom_leftInverse {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (g : S →+* R) (hgf : ∀ z, g (f z) = z) {A B : Ideal R}
    (hAB : Ideal.map f A = Ideal.map f B) : A = B := by
  have hcomp : g.comp f = RingHom.id R := RingHom.ext hgf
  have hA : Ideal.map g (Ideal.map f A) = A := by rw [Ideal.map_map, hcomp, Ideal.map_id]
  have hB : Ideal.map g (Ideal.map f B) = B := by rw [Ideal.map_map, hcomp, Ideal.map_id]
  rw [← hA, ← hB, hAB]

private theorem hom_apply_hom_apply_of_comp_eq {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (k : A ⟶ C) (hk : f ≫ g = k) (z : A) : g.hom (f.hom z) = k.hom z := by
  rw [← hk, CommRingCat.hom_comp]
  rfl

private theorem inv_hom_apply_hom_apply {A B : CommRingCat.{u}} (f : A ⟶ B) [IsIso f]
    (z : A) : (inv f).hom (f.hom z) = z := by
  rw [hom_apply_hom_apply_of_comp_eq f (inv f) (𝟙 A) (IsIso.hom_inv_id f) z, CommRingCat.hom_id]
  rfl

theorem stalkIdeal_eq_prod_of_isMonomialOnOpen (E : List X.IdealSheafData) (M : X.IdealSheafData)
    (U : X.Opens) (a : Fin E.length → ℕ) (h : IsMonomialOnOpen E M U a) (x : X) (hx : x ∈ U) :
    stalkIdeal M x =
      ((List.finRange E.length).map (fun j => stalkIdeal (E.get j) x ^ a j)).prod := by
  have h' : restrictIdeal M U
      = ((List.finRange E.length).map (fun j => restrictIdeal (E.get j) U ^ a j)).prod := h
  have hxr : x ∈ Set.range (⇑U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, hy⟩ := hxr
  subst hy
  have hgf : ∀ z, (inv (U.ι.stalkMap y)).hom ((U.ι.stalkMap y).hom z) = z :=
    fun z => inv_hom_apply_hom_apply (U.ι.stalkMap y) z
  refine eq_of_ideal_map_eq_of_ringHom_leftInverse (U.ι.stalkMap y).hom (inv (U.ι.stalkMap y)).hom hgf ?_
  have hL : ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) (U.ι.base y) ^ a j)).map
        (fun I => Ideal.map (U.ι.stalkMap y).hom I)
      = ((List.finRange E.length).map (fun j => restrictIdeal (E.get j) U ^ a j)).map
        (fun I => stalkIdeal I y) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left ?_
    intro j _
    show Ideal.map (U.ι.stalkMap y).hom (stalkIdeal (E.get j) (U.ι.base y) ^ a j)
        = stalkIdeal (restrictIdeal (E.get j) U ^ a j) y
    rw [stalkIdeal_pow, restrictIdeal_eq_comap_ι, stalkIdeal_comap, Ideal.map_pow]
  rw [ideal_map_listProd, hL, ← stalkIdeal_listProd, ← h', restrictIdeal_eq_comap_ι,
    stalkIdeal_comap]

theorem orderAt_genericPoint_eq_of_isMonomialSplitting {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (_hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (_hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    {D : X.IdealSheafData} (hD : D ∈ E) {C : Set X} (hC : IsIrreducibleComponentOfSupport D C) :
    orderAt M hC.isIrreducible.genericPoint = orderAt I hC.isIrreducible.genericPoint := by
  have hmax' : ∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C := by
    intro C' h1 h2 h3
    have he := hC.maximal C' h1 h3 h2
    intro y hy
    rw [he] at hy
    exact hy
  have hNC : ¬ C ⊆ (N.support : Set X) :=
    hsplit.transversal D hD C hC.isIrreducible hC.subset_support hmax'
  have hηN : hC.isIrreducible.genericPoint ∉ N.support := by
    intro h
    refine hNC ?_
    rw [← hC.closure_genericPoint]
    exact (N.support.2).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
  have h0 : orderAt N hC.isIrreducible.genericPoint = 0 :=
    (orderAt_eq_zero_iff_not_mem_support N hC.isIrreducible.genericPoint).mpr hηN
  rw [hsplit.eq_mul, orderAt_mul k p M N hC.isIrreducible.genericPoint, h0, add_zero]

theorem exponent_le_orderAlongComponent {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (_hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (U : X.Opens) (a : Fin E.length → ℕ) (ha : IsMonomialOnOpen E M U a)
    (l : Fin E.length) {C' : Set X} (hC' : IsIrreducibleComponentOfSupport (E.get l) C')
    (x : X) (hxU : x ∈ U) (hxC : x ∈ C') :
    a l ≤ orderAlongComponent I hC'.isIrreducible := by
  have hxcl : x ∈ closure ({hC'.isIrreducible.genericPoint} : Set X) := by
    rw [hC'.closure_genericPoint]
    exact hxC
  have hηU : hC'.isIrreducible.genericPoint ∈ U := by
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hxcl (U : Set X) U.isOpen hxU
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzU
  have hprod : stalkIdeal M hC'.isIrreducible.genericPoint =
      ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j)).prod :=
    stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a ha hC'.isIrreducible.genericPoint hηU
  have hlen : (l : ℕ) <
      ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j)).length := by
    simp
  have hget : ((List.finRange E.length).map
        (fun j => stalkIdeal (E.get j) hC'.isIrreducible.genericPoint ^ a j))[(l : ℕ)]'hlen
      = stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ^ a l := by
    simp
  have h1 : stalkIdeal M hC'.isIrreducible.genericPoint ≤
      stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ^ a l := by
    rw [hprod, ← hget]
    exact Ideal.list_prod_le_getElem _ _ hlen
  have hle : stalkIdeal (E.get l) hC'.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC'.isIrreducible.genericPoint) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get l)
      hC'.isIrreducible.genericPoint).mp hC'.genericPoint_mem_support
  have h2 : (a l : ℕ∞) ≤ orderAt M hC'.isIrreducible.genericPoint :=
    (le_orderAt_iff M hC'.isIrreducible.genericPoint (a l)).mpr
      (h1.trans (Ideal.pow_right_mono hle (a l)))
  have hIM : I ≤ M := by
    rw [hsplit.eq_mul]
    refine (le_iff_forall_stalkIdeal_le _ _).mpr (fun y => ?_)
    rw [stalkIdeal_mul]
    exact Ideal.mul_le_inf.trans inf_le_left
  have h3 : orderAt M hC'.isIrreducible.genericPoint ≤
      orderAt I hC'.isIrreducible.genericPoint :=
    orderAt_le_of_le hIM hC'.isIrreducible.genericPoint
  have h4 : (a l : ℕ∞) ≤ (orderAlongComponent I hC'.isIrreducible : ℕ∞) := by
    rw [coe_orderAlongComponent_eq_orderAt_genericPoint hC' hI]
    exact h2.trans h3
  exact_mod_cast h4

private theorem ideal_listProd_le_mul_getElem_of_lt {R : Type*} [CommRing R] (L : List (Ideal R)) :
    ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length), i < j →
      L.prod ≤ (L[i]'hi) * (L[j]'hj) := by
  induction L with
  | nil =>
      intro i _ hi _ _
      simp at hi
  | cons A L ih =>
      intro i j hi hj hij
      cases i with
      | zero =>
          cases j with
          | zero => exact absurd hij (lt_irrefl 0)
          | succ j' =>
              have hj' : j' < L.length := by simpa using hj
              simp only [List.prod_cons, List.getElem_cons_zero, List.getElem_cons_succ]
              exact Ideal.mul_mono le_rfl (Ideal.list_prod_le_getElem L j' hj')
      | succ i' =>
          cases j with
          | zero => exact absurd hij (Nat.not_lt_zero _)
          | succ j' =>
              have hi' : i' < L.length := by simpa using hi
              have hj' : j' < L.length := by simpa using hj
              simp only [List.prod_cons, List.getElem_cons_succ]
              exact le_trans (le_trans Ideal.mul_le_inf inf_le_right)
                (ih i' j' hi' hj' (by omega))

private theorem ideal_listProd_le_mul_getElem_of_ne {R : Type*} [CommRing R] (L : List (Ideal R))
    (i j : ℕ) (hi : i < L.length) (hj : j < L.length) (hij : i ≠ j) :
    L.prod ≤ (L[i]'hi) * (L[j]'hj) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact ideal_listProd_le_mul_getElem_of_lt L i j hi hj h
  · rw [mul_comm]
    exact ideal_listProd_le_mul_getElem_of_lt L j i hj hi h

private theorem ideal_listProd_le_pow_add {R : Type*} [CommRing R] (m : Ideal R)
    (L : List (Ideal R)) (i j : ℕ) (hi : i < L.length) (hj : j < L.length) (hij : i ≠ j)
    (b c : ℕ) (hbi : (L[i]'hi) ≤ m ^ b) (hcj : (L[j]'hj) ≤ m ^ c) :
    L.prod ≤ m ^ (b + c) := by
  refine le_trans (ideal_listProd_le_mul_getElem_of_ne L i j hi hj hij) ?_
  rw [pow_add]
  exact Ideal.mul_mono hbi hcj

private theorem ideal_listProd_finRange_eq_of_ne_eq_top {R : Type*} [CommRing R] {n : ℕ}
    (f : Fin n → Ideal R) (j : Fin n) (h : ∀ l : Fin n, l ≠ j → f l = ⊤) :
    ((List.finRange n).map f).prod = f j := by
  rw [← Fin.prod_univ_def]
  refine Finset.prod_eq_single j (fun l _ hl => ?_) (fun hj => absurd (Finset.mem_univ j) hj)
  rw [h l hl, Ideal.one_eq_top]

theorem exponent_eq_orderAlongComponent {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (U : X.Opens) (a : Fin E.length → ℕ) (ha : IsMonomialOnOpen E M U a)
    (j : Fin E.length) {C : Set X} (hC : IsIrreducibleComponentOfSupport (E.get j) C)
    (x : X) (hxU : x ∈ U) (hxC : x ∈ C) :
    a j = orderAlongComponent I hC.isIrreducible := by
  have hD : E.get j ∈ E := by simp
  have hxcl : x ∈ closure ({hC.isIrreducible.genericPoint} : Set X) := by
    rw [hC.closure_genericPoint]
    exact hxC
  have hηU : hC.isIrreducible.genericPoint ∈ U := by
    obtain ⟨z, hzU, hz⟩ := mem_closure_iff.mp hxcl (U : Set X) U.isOpen hxU
    rw [Set.mem_singleton_iff] at hz
    rw [← hz]
    exact hzU
  have hηC : hC.isIrreducible.genericPoint ∈ C := hC.genericPoint_mem
  have hlocj : IsEtaleLocallyCoordinateDivisor p (E.get j) :=
    isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get j) hD
  have hjmax : stalkIdeal (E.get j) hC.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get j)
      hC.isIrreducible.genericPoint).mp hC.genericPoint_mem_support
  have hmemj : stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint =
      stalkIdeal (E.get j) hC.isIrreducible.genericPoint ^
        orderAlongComponent I hC.isIrreducible :=
    stalkIdeal_monomialPartAlongDivisor_of_mem p I hlocj hC hηC
  have hbj : stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint ≤
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^
        orderAlongComponent I hC.isIrreducible := by
    rw [hmemj]
    exact Ideal.pow_right_mono hjmax _
  have hPstalk : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) hC.isIrreducible.genericPoint)).prod :=
    stalkIdeal_monomialFactorIdeal E I hC.isIrreducible.genericPoint
  have hPord : orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint =
      (orderAlongComponent I hC.isIrreducible : ℕ∞) :=
    orderAt_monomialFactorIdeal_genericPoint p E I hE hI hD hC
  have hzero : ∀ l : Fin E.length, l ≠ j →
      stalkIdeal (E.get l) hC.isIrreducible.genericPoint ^ a l = ⊤ := by
    intro l hlj
    by_cases hs : hC.isIrreducible.genericPoint ∈ ((E.get l).support : Set X)
    · have hal : a l = 0 := by
        obtain ⟨C', hC', hηC'⟩ :=
          exists_isIrreducibleComponentOfSupport (E.get l) hC.isIrreducible.genericPoint hs
        have hDl : E.get l ∈ E := by simp
        have hlocl : IsEtaleLocallyCoordinateDivisor p (E.get l) :=
          isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get l) hDl
        have hle : a l ≤ orderAlongComponent I hC'.isIrreducible :=
          exponent_le_orderAlongComponent p E hE hI hsplit U a ha l hC'
            hC.isIrreducible.genericPoint hηU hηC'
        have hmeml : stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint =
            stalkIdeal (E.get l) hC.isIrreducible.genericPoint ^
              orderAlongComponent I hC'.isIrreducible :=
          stalkIdeal_monomialPartAlongDivisor_of_mem p I hlocl hC' hηC'
        have hlmax : stalkIdeal (E.get l) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
          (mem_support_iff_stalkIdeal_le_maximalIdeal (E.get l)
            hC.isIrreducible.genericPoint).mp hs
        have hbl : stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^ a l := by
          rw [hmeml]
          exact le_trans (Ideal.pow_right_mono hlmax _) (Ideal.pow_le_pow_right hle)
        have hjlen : (j : ℕ) <
            (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
              hC.isIrreducible.genericPoint)).length := by
          simp
        have hllen : (l : ℕ) <
            (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
              hC.isIrreducible.genericPoint)).length := by
          simp
        have hjne : (j : ℕ) ≠ (l : ℕ) := by
          intro hv
          apply hlj
          ext
          exact hv.symm
        have hgj : (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
            hC.isIrreducible.genericPoint))[(j : ℕ)]'hjlen =
            stalkIdeal (monomialPartAlongDivisor I (E.get j)) hC.isIrreducible.genericPoint := by
          simp
        have hgl : (E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D)
            hC.isIrreducible.genericPoint))[(l : ℕ)]'hllen =
            stalkIdeal (monomialPartAlongDivisor I (E.get l)) hC.isIrreducible.genericPoint := by
          simp
        have hPle : stalkIdeal (monomialFactorIdeal E I) hC.isIrreducible.genericPoint ≤
            IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) ^
              (orderAlongComponent I hC.isIrreducible + a l) := by
          rw [hPstalk]
          refine ideal_listProd_le_pow_add _ _ (j : ℕ) (l : ℕ) hjlen hllen hjne _ _ ?_ ?_
          · rw [hgj]
            exact hbj
          · rw [hgl]
            exact hbl
        have hord : ((orderAlongComponent I hC.isIrreducible + a l : ℕ) : ℕ∞) ≤
            orderAt (monomialFactorIdeal E I) hC.isIrreducible.genericPoint :=
          (le_orderAt_iff (monomialFactorIdeal E I) hC.isIrreducible.genericPoint
            (orderAlongComponent I hC.isIrreducible + a l)).mpr hPle
        rw [hPord] at hord
        have hnat : orderAlongComponent I hC.isIrreducible + a l ≤
            orderAlongComponent I hC.isIrreducible := by exact_mod_cast hord
        omega
      rw [hal, pow_zero, Ideal.one_eq_top]
    · have hstop : stalkIdeal (E.get l) hC.isIrreducible.genericPoint = ⊤ := by
        by_contra hcon
        exact hs ((mem_support_iff_stalkIdeal_ne_top (E.get l)
          hC.isIrreducible.genericPoint).mpr hcon)
      rw [hstop, ← Ideal.one_eq_top, one_pow]
  have hprod : stalkIdeal M hC.isIrreducible.genericPoint =
      ((List.finRange E.length).map
        (fun i => stalkIdeal (E.get i) hC.isIrreducible.genericPoint ^ a i)).prod :=
    stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a ha hC.isIrreducible.genericPoint hηU
  have hMstalk : stalkIdeal M hC.isIrreducible.genericPoint =
      stalkIdeal (E.get j) hC.isIrreducible.genericPoint ^ a j := by
    rw [hprod]
    exact ideal_listProd_finRange_eq_of_ne_eq_top
      (fun i => stalkIdeal (E.get i) hC.isIrreducible.genericPoint ^ a i) j hzero
  have hmaxj : stalkIdeal (E.get j) hC.isIrreducible.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk hC.isIrreducible.genericPoint) :=
    stalkIdeal_genericPoint_eq_maximalIdeal p (E.get j) hlocj hC.isIrreducible
      hC.subset_support hC.maximal
  have hMI : orderAt M hC.isIrreducible.genericPoint =
      orderAt I hC.isIrreducible.genericPoint :=
    orderAt_genericPoint_eq_of_isMonomialSplitting p E hE hI hsplit hD hC
  have hfin : orderAt M hC.isIrreducible.genericPoint ≠ ⊤ := by
    rw [hMI]
    exact orderAt_ne_top_of_nonzeroOnComponents I hI hC.isIrreducible.genericPoint
  have hMord : orderAt M hC.isIrreducible.genericPoint = (a j : ℕ∞) :=
    orderAt_eq_of_stalkIdeal_eq_maximalIdeal_pow M hC.isIrreducible.genericPoint (a j)
      (by rw [hMstalk, hmaxj]) hfin
  have hco : (orderAlongComponent I hC.isIrreducible : ℕ∞) =
      orderAt I hC.isIrreducible.genericPoint := coe_orderAlongComponent_eq_orderAt_genericPoint hC hI
  have hfinal : ((a j : ℕ) : ℕ∞) = ((orderAlongComponent I hC.isIrreducible : ℕ) : ℕ∞) := by
    rw [← hMord, hMI, ← hco]
  exact_mod_cast hfinal

private theorem map_finRange_get_eq_map {α : Type*} {β : Type*} (l : List α) (g : α → β) :
    (List.finRange l.length).map (fun j => g (l.get j)) = l.map g := by
  refine List.ext_getElem (by simp) ?_
  intro n h1 h2
  simp

theorem stalkIdeal_eq_stalkIdeal_monomialFactorIdeal {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N) (x : X) :
    stalkIdeal M x = stalkIdeal (monomialFactorIdeal E I) x := by
  obtain ⟨U, hxU, a, haU⟩ := hsplit.monomial x
  have hmon : IsMonomialOnOpen E M U a := by
    show M.comap U.ι
        = ((List.finRange E.length).map (fun j => (E.get j).comap U.ι ^ a j)).prod
    rw [haU, Fin.prod_univ_def]
  have hstep : ∀ j : Fin E.length,
      stalkIdeal (E.get j) x ^ a j = stalkIdeal (monomialPartAlongDivisor I (E.get j)) x := by
    intro j
    have hmem : E.get j ∈ E := by simp
    by_cases hx : x ∈ ((E.get j).support : Set X)
    · obtain ⟨C, hC, hxC⟩ := exists_isIrreducibleComponentOfSupport (E.get j) x hx
      have hloc : IsEtaleLocallyCoordinateDivisor p (E.get j) :=
        isEtaleLocallyCoordinateDivisor_of_inStrictNormalCrossingPosition p E hE (E.get j) hmem
      rw [stalkIdeal_monomialPartAlongDivisor_of_mem p I hloc hC hxC,
        exponent_eq_orderAlongComponent p E hE hI hsplit U a hmon j hC x hxU hxC]
    · have h1 : stalkIdeal (E.get j) x = ⊤ := by
        by_contra hne
        exact hx ((mem_support_iff_stalkIdeal_ne_top (E.get j) x).mpr hne)
      rw [stalkIdeal_monomialPartAlongDivisor_of_not_mem_support I (E.get j) hx, h1,
        ← Ideal.one_eq_top, one_pow]
  have hlist : (List.finRange E.length).map (fun j => stalkIdeal (E.get j) x ^ a j)
      = E.map (fun D => stalkIdeal (monomialPartAlongDivisor I D) x) := by
    rw [← map_finRange_get_eq_map E (fun D => stalkIdeal (monomialPartAlongDivisor I D) x)]
    exact List.map_congr_left (fun j _ => hstep j)
  rw [stalkIdeal_eq_prod_of_isMonomialOnOpen E M U a hmon x hxU,
    stalkIdeal_monomialFactorIdeal E I x, hlist]

theorem eq_monomialFactorIdeal {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N) :
    M = monomialFactorIdeal E I := by
  have hstalk : ∀ x : X, stalkIdeal M x = stalkIdeal (monomialFactorIdeal E I) x :=
    fun x => stalkIdeal_eq_stalkIdeal_monomialFactorIdeal p E hE hI hsplit x
  refine le_antisymm ?_ ?_
  · exact (le_iff_forall_stalkIdeal_le M (monomialFactorIdeal E I)).mpr
      (fun x => le_of_eq (hstalk x))
  · exact (le_iff_forall_stalkIdeal_le (monomialFactorIdeal E I) M).mpr
      (fun x => le_of_eq (hstalk x).symm)

theorem eq_nonMonomialFactorIdeal {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) {I M N : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N) :
    N = nonMonomialFactorIdeal E I := by
  have hM : M = monomialFactorIdeal E I := eq_monomialFactorIdeal p E hE hI hsplit
  have hF : Blowup.IsLocallyGeneratedByNonZeroDivisor (monomialFactorIdeal E I) :=
    isLocallyGeneratedByNonZeroDivisor_monomialFactorIdeal p E I hE
  have hIM : I ≤ monomialFactorIdeal E I := by
    rw [← hM, hsplit.eq_mul]
    refine (le_iff_forall_stalkIdeal_le _ _).mpr (fun y => ?_)
    rw [stalkIdeal_mul]
    exact Ideal.mul_le_inf.trans inf_le_left
  have hmul : monomialFactorIdeal E I * N
      = monomialFactorIdeal E I * nonMonomialFactorIdeal E I := by
    rw [nonMonomialFactorIdeal_eq_idealSheafColon, hF.mul_idealSheafColon hIM, ← hM]
    exact hsplit.eq_mul.symm
  exact hF.eq_of_mul_eq_mul hmul

theorem isMonomialSplitting_unique {k : Type u} [Field k] [CharZero k]
    [TopologicalSpace.NoetherianSpace ↥X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (E : List X.IdealSheafData) (hE : InStrictNormalCrossingPosition p E) {I M N M' N' : X.IdealSheafData}
    (hI : NonzeroOnComponents I) (hsplit : IsMonomialSplitting E I M N)
    (hsplit' : IsMonomialSplitting E I M' N') :
    M = M' ∧ N = N' :=
  ⟨(eq_monomialFactorIdeal p E hE hI hsplit).trans
      (eq_monomialFactorIdeal p E hE hI hsplit').symm,
    (eq_nonMonomialFactorIdeal p E hE hI hsplit).trans
      (eq_nonMonomialFactorIdeal p E hE hI hsplit').symm⟩

end FunctorialResolution.EmbeddedResolution

end
end

section -- merged from Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyBoundedOrder
universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem isOpen_setOf_stalkIdeal_eq_bot {X : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
    (J : X.IdealSheafData) :
    IsOpen {x : ↥X | stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x))} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  have hx' : stalkIdeal J x = (⊥ : Ideal (X.presheaf.stalk x)) := hx
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    have h1 : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top X]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h1
  have : IsNoetherianRing Γ(X, (U : X.Opens)) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U
  obtain ⟨s, hs⟩ : (J.ideal U).FG := IsNoetherian.noetherian (J.ideal U)
  have hzero : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) x hxU).hom g = 0 := by
    intro g hg
    have hgI : g ∈ J.ideal U := by
      rw [← hs]
      exact Submodule.subset_span (Finset.mem_coe.mpr hg)
    have hmem := germ_mem_stalkIdeal J x U hxU hgI
    rw [hx'] at hmem
    simpa using hmem
  have hWex : ∀ g : Γ(X, (U : X.Opens)), ∃ (W : X.Opens) (i : W ⟶ (U : X.Opens)),
      x ∈ W ∧ (g ∈ s → (X.presheaf.map i.op).hom g = 0) := by
    intro g
    by_cases hg : g ∈ s
    · obtain ⟨V, iV, hxV, hi⟩ :=
        X.toLocallyRingedSpace.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero
          (U : X.Opens) g ⟨x, hxU⟩ (hzero g hg)
      exact ⟨V, iV, hxV, fun _ => hi⟩
    · exact ⟨(U : X.Opens), 𝟙 _, hxU, fun h => absurd h hg⟩
  choose W i hxW hres using hWex
  refine ⟨((U : X.Opens) : Set ↥X) ∩
      ⋂ g ∈ (s : Set Γ(X, (U : X.Opens))), ((W g : X.Opens) : Set ↥X), ?_, ?_, ?_⟩
  · rintro y ⟨hyU, hyW⟩
    have hyW' : ∀ g ∈ s, y ∈ W g := fun g hg =>
      Set.mem_iInter₂.mp hyW g (Finset.mem_coe.mpr hg)
    have hmain : ∀ g ∈ s, (X.presheaf.germ (U : X.Opens) y hyU).hom g = 0 := by
      intro g hg
      have h3 : (X.presheaf.germ (W g) y (hyW' g hg)).hom
          ((X.presheaf.map (i g).op).hom g) = 0 := by
        rw [hres g hg, map_zero]
      exact (X.presheaf.germ_res_apply (i g) y (hyW' g hg) g).symm.trans h3
    show stalkIdeal J y = ⊥
    rw [stalkIdeal_eq_map_germ J y U hyU, ← le_bot_iff, Ideal.map_le_iff_le_comap, ← hs,
      Submodule.span_le]
    intro g hg
    have hg0 := hmain g (Finset.mem_coe.mp hg)
    have hmem : (X.presheaf.germ (U : X.Opens) y hyU).hom g ∈
        (⊥ : Ideal (X.presheaf.stalk y)) := by
      rw [hg0]
      exact Submodule.zero_mem _
    simpa using hmem
  · exact (TopologicalSpace.Opens.isOpen (U : X.Opens)).inter
      (Set.Finite.isOpen_biInter s.finite_toSet
        (fun g _ => TopologicalSpace.Opens.isOpen (W g)))
  · exact ⟨hxU, Set.mem_iInter₂.mpr (fun g _ => hxW g)⟩

private theorem isLocallyNoetherian_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible) :
    AlgebraicGeometry.IsLocallyNoetherian T.scheme := by
  have := hT.locallyOfFiniteType
  have : IsNoetherianRing T.base := inferInstance
  constructor
  intro U
  exact @isNoetherianRing_sections T.base _ _ T.scheme T.structMap _ U
    (sectionsAlgebra T.base T.structMap U.1)
    (algebraMap_sectionsAlgebra T.base T.structMap U.1)

private theorem stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J) (x : ↥T.scheme) :
    stalkIdeal J x ≠ ⊥ := by
  have := isLocallyNoetherian_of_isAdmissible T hT
  intro hbot
  obtain ⟨y, hyC, hyJ⟩ := Set.not_subset.mp
    (hJ (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x))
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed ((J.support : Set ↥T.scheme)) := J.support.2
  obtain ⟨z, hzC, hz1, hz2⟩ :=
    hirr.2 {w : ↥T.scheme | stalkIdeal J w = ⊥} ((J.support : Set ↥T.scheme)ᶜ)
      (isOpen_setOf_stalkIdeal_eq_bot J) hcl.isOpen_compl
      ⟨x, mem_irreducibleComponent, hbot⟩ ⟨y, hyC, hyJ⟩
  have hz1' : stalkIdeal J z = ⊥ := hz1
  have hztop : stalkIdeal J z = ⊤ := by
    by_contra hne
    exact hz2 ((mem_support_iff_stalkIdeal_ne_top J z).2 hne)
  have h1 : (1 : T.scheme.presheaf.stalk z) ∈ (⊥ : Ideal (T.scheme.presheaf.stalk z)) := by
    rw [← hz1', hztop]
    exact Submodule.mem_top
  rw [Ideal.mem_bot] at h1
  exact one_ne_zero h1

theorem exists_orderAt_le (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (J : T.scheme.IdealSheafData) (hJ : NonzeroOnComponents J) :
    ∃ B : ℕ, ∀ x : ↥T.scheme, orderAt J x ≤ (B : ℕ∞) := by
  have := hT.charZero
  have := hT.smooth
  have := hT.locallyOfFiniteType
  have := isLocallyNoetherian_of_isAdmissible T hT
  have hfin : ∀ x : ↥T.scheme, orderAt J x ≠ ⊤ := fun x =>
    orderAt_ne_top_of_stalkIdeal_ne_bot J x
      (stalkIdeal_ne_bot_of_isAdmissible_of_nonzeroOnComponents T hT J hJ x)
  have hclosed : ∀ m : ℕ, IsClosed (orderAtLeastLocus J m) := fun m =>
    isClosed_orderAtLeastLocus T.base T.structMap J m
  have hspec : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of T.base))) := by
    simp
  have hcpt : IsCompact (Set.univ : Set ↥T.scheme) := by
    have h := hT.quasiCompact.isCompact_preimage Set.univ isOpen_univ hspec
    simpa using h
  have hempty : (Set.univ : Set ↥T.scheme) ∩ (⋂ m : ℕ, orderAtLeastLocus J m) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨x, -, hx⟩
    have hx' := Set.mem_iInter.mp hx
    have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ orderAt J x := fun m => (mem_orderAtLeastLocus_iff J m x).1 (hx' m)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, orderAt J x = (n : ℕ∞) :=
      ⟨(orderAt J x).toNat, (ENat.natCast_toNat (hfin x)).symm⟩
    have h3 : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by
      rw [← hn]
      exact h1 (n + 1)
    have h4 : n + 1 ≤ n := by exact_mod_cast h3
    omega
  obtain ⟨u, hu⟩ := hcpt.elim_finite_subfamily_closed (fun m : ℕ => orderAtLeastLocus J m) hclosed (Set.disjoint_iff_inter_eq_empty.mpr hempty)
  have hMempty : ¬ ((Set.univ : Set ↥T.scheme) ∩ ⋂ i ∈ u, orderAtLeastLocus J i).Nonempty := by
    rw [Set.not_nonempty_iff_eq_empty]
    exact Set.disjoint_iff_inter_eq_empty.mp hu
  refine ⟨u.sup id, fun x => ?_⟩
  have hxnot : x ∉ orderAtLeastLocus J (u.sup id) := by
    intro hx
    refine hMempty ⟨x, Set.mem_univ x, ?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    exact orderAtLeastLocus_subset_of_le J (Finset.le_sup (f := id) hi) hx
  rw [mem_orderAtLeastLocus_iff] at hxnot
  exact le_of_lt (not_le.mp hxnot)

end FunctorialResolution.EmbeddedResolution
end

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure MonomialCaseHypotheses : Prop where
  card_lt_dim :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        (intersectionComponents T.boundary J).Nonempty → J.card < krullDimSucc T.scheme
  center_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            AlgebraicGeometry.Smooth
              ((componentUnionIdeal T.boundary J 𝒞 hop).subschemeι ≫ T.structMap)
  center_snc :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J).subschemeι ⁻¹' ⋃₀ 𝒞)),
            HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J 𝒞 hop) T.boundary
  blowup_total_transform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary, ∀ (x' : ↥X'),
                ∃ (U' : X'.Opens) (ε : ℕ),
                  x' ∈ U' ∧ (ε = 0 ∨ ε = 1) ∧
                    (ε = 1 ↔ ∃ V : T.scheme.Opens, π x' ∈ V ∧
                      (Z.support : Set ↥T.scheme) ∩ (V : Set ↥T.scheme) ⊆
                        (D.support : Set ↥T.scheme)) ∧
                    (D.comap π).comap U'.ι =
                      (Blowup.strictTransform π Z D).comap U'.ι *
                        (Blowup.exceptionalIdeal π Z).comap U'.ι ^ ε
  components_subset_divisor_iff :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        ∀ C ∈ intersectionComponents T.boundary J,
          ∀ (i : Fin T.boundary.length),
            C ⊆ ((T.boundary.get i).support : Set ↥T.scheme) ↔ i ∈ J
  transformed_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞))
            (X' : Scheme.{u}) (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                    (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                    (Finset.image
                      (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ (ξ' : ↥X'), IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              ((Blowup.exceptionalIdeal π
                                (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :
                                  Set ↥X')) ∧
                            ∀ (ξ : ↥T.scheme), IsGenericPoint ξ C → π ξ' = ξ
  stratum_smooth :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J : Finset (Fin T.boundary.length)),
        AlgebraicGeometry.Smooth ((intersectionIdeal T.boundary J).subschemeι ≫ T.structMap)
  orderAt_comap_off_exceptional :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData),
        Blowup.IsBlowupAlongIdealSheaf π Z →
          ∀ x' ∉ (Blowup.exceptionalIdeal π Z).support,
            ∀ (A : T.scheme.IdealSheafData), orderAt (A.comap π) x' = orderAt A (π x')
  orderAt_boundary_eq_one :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ D ∈ T.boundary, ∀ x ∈ D.support, orderAt D x = 1

theorem monomialGeometryHypotheses_of_monomialCaseHypotheses (hR : MonomialCaseHypotheses.{u}) :
    MonomialGeometryHypotheses.{u} := by
  exact {
    card_lt_dim := hR.card_lt_dim
    flat_comap_center := by
      intro T hT Y k' hk q g hg hT' J 𝒞 h𝒞 hop
      exact FunctorialResolution.EmbeddedResolution.comap_componentUnionIdeal_of_flat T hT Y k' q g hT' J 𝒞 h𝒞 hop
    center_smooth := hR.center_smooth
    center_snc := hR.center_snc
    center_support := by
      intro T hT J 𝒞 h𝒞 hop
      exact FunctorialResolution.EmbeddedResolution.componentUnionIdeal_support_eq_sUnion T hT J 𝒞 h𝒞 hop
    blowup_total_transform := hR.blowup_total_transform
    flat_components_down := by
      intro T hT Y k' hk q g hg hT' J C' hC'
      exact FunctorialResolution.EmbeddedResolution.exists_intersectionComponents_mapsTo_of_flat T hT Y k' q g hT' J C' hC'
    flat_components_up := by
      intro T hT Y k' hk q g hg hT' J C hC y hy
      exact FunctorialResolution.EmbeddedResolution.exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y k' q g hT' J C hC y hy
    smooth_components_down := by
      intro T hT Y q h hsm hq hV J C' hC'
      have : AlgebraicGeometry.Flat h := inferInstance
      have hV' : (T.pullbackOverField Y T.base q h).IsAdmissible := by
        rw [MarkedIdealWithBoundary.pullbackOverField_eq_pullbackAlong]
        exact hV
      have e : pullbackOverFieldIndex T Y T.base q h = pullbackAlongIndex T Y q h := by
        funext j
        apply Fin.ext
        rw [pullbackOverFieldIndex_val, pullbackAlongIndex_val]
      have hC'' : C' ∈ intersectionComponents (T.pullbackOverField Y T.base q h).boundary
          (Finset.image (pullbackOverFieldIndex T Y T.base q h) J) := by
        rw [e]
        exact hC'
      exact FunctorialResolution.EmbeddedResolution.exists_intersectionComponents_mapsTo_of_flat T hT Y T.base q h hV' J C' hC''
    smooth_components_up := by
      intro T hT Y q h hsm hq hV J C hC y hy
      have : AlgebraicGeometry.Flat h := inferInstance
      have hV' : (T.pullbackOverField Y T.base q h).IsAdmissible := by
        rw [MarkedIdealWithBoundary.pullbackOverField_eq_pullbackAlong]
        exact hV
      have e : pullbackOverFieldIndex T Y T.base q h = pullbackAlongIndex T Y q h := by
        funext j
        apply Fin.ext
        rw [pullbackOverFieldIndex_val, pullbackAlongIndex_val]
      obtain ⟨C', hC'mem, hyC', hgen⟩ :=
        FunctorialResolution.EmbeddedResolution.exists_mem_intersectionComponents_pullbackOverField_of_flat T hT Y T.base q h hV' J C hC y hy
      refine ⟨C', ?_, hyC', hgen⟩
      rw [← e]
      exact hC'mem
    components_disjoint := by
      intro T hT J C hC C' hC' hne
      exact FunctorialResolution.EmbeddedResolution.intersectionComponents_disjoint_of_smooth T J (hR.stratum_smooth T hT J) C C' hC hC' hne
    components_finite := by
      intro T hT J
      exact FunctorialResolution.EmbeddedResolution.intersectionComponents_finite T hT J
    components_subset_divisor_iff := hR.components_subset_divisor_iff
    transformed_components := hR.transformed_components
    level_schemeDim_le := by
      intro T hT s i hi
      have h := MarkedIdealWithBoundary.transformAt_dim_le FunctorialResolution.EmbeddedResolution.dimensionNonincreasingAlongBlowups hT s i hi
      rwa [MarkedIdealWithBoundary.transformAt_dim] at h
    stratum_smooth := hR.stratum_smooth
    level_valid := by
      intro T hT s i hi
      exact MarkedIdealWithBoundary.IsAdmissible.transformAt FunctorialResolution.EmbeddedResolution.effectiveCartierSupportContainsNoComponent hT s i hi
    orderAt_bounded := by
      intro T hT I hI
      exact FunctorialResolution.EmbeddedResolution.exists_orderAt_le T hT I hI
    orderAt_comap_off_exceptional := hR.orderAt_comap_off_exceptional
    orderAt_boundary_eq_one := hR.orderAt_boundary_eq_one
    sUnion_isOpen := by
      intro T hT J 𝒞 h𝒞
      exact FunctorialResolution.EmbeddedResolution.isOpen_preimage_sUnion_intersectionComponents T hT J (hR.stratum_smooth T hT J) 𝒞 h𝒞
    withBoundary_valid := by
      intro T hT E' hE
      apply MarkedIdealWithBoundary.validOfSameNontrivialBoundary <;> assumption
  }

structure OrderReductionHypotheses : Prop where
  controlledTransform_orderAt_le :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ (J : T.scheme.IdealSheafData) (c : ℕ),
                (∀ x ∈ Z.support, orderAt J x = (c : ℕ∞)) →
                  ∀ (J' : X'.IdealSheafData),
                    Blowup.exceptionalIdeal π Z ^ c * J' = J.comap π →
                      ∀ x' ∈ (Blowup.exceptionalIdeal π Z).support, orderAt J' x' ≤ (c : ℕ∞)
  strictTransform_components :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (Z.subschemeι ≫ T.structMap) →
          HasStrictNormalCrossingsWith T.structMap Z T.boundary →
            ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
              ∀ D ∈ T.boundary,
                ∀ C' : Set ↥X',
                  IsIrreducibleComponentOf C' ((Blowup.strictTransform π Z D).support : Set ↥X') →
                    ∃ (ξ' : ↥X') (C : Set ↥T.scheme),
                      C' = closure ({ξ'} : Set ↥X') ∧
                        ξ' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                          IsIrreducibleComponentOf C (D.support : Set ↥T.scheme) ∧
                            ¬ C ⊆ (Z.support : Set ↥T.scheme) ∧
                              C = closure ({π ξ'} : Set ↥T.scheme)
  monomial : MonomialCaseHypotheses.{u}

theorem geometricHypotheses_of_orderReductionHypotheses (hR : OrderReductionHypotheses.{u}) :
    PrincipalizationGeometryHypotheses.{u} := by
  exact {
    maxContactTransport := FunctorialResolution.EmbeddedResolution.isoInvariantOrderCertificateDescend
    exceptional_components_not_subset := by
      intro T hT Z hZsm hZsnc X' π hπ J c hord J' htr C' hC'
      have := hT.charZero
      have := hT.smooth
      have := hT.isNoetherian
      have := FunctorialResolution.EmbeddedResolution.isLocallyNoetherian_of_isBlowupAlongIdealSheaf π Z hπ
      refine FunctorialResolution.EmbeddedResolution.controlledTransform_not_subset_support T.structMap Z T.boundary hZsnc π hπ
        J c hord J' htr C' hC'.1 hC'.2.1 ?_
      intro S hirr hsub hsup
      exact hC'.2.2 S hirr hsup hsub
    orderAt_baseChange := by
      intro T hT L hL hLz f I y
      have := hT.charZero
      have := hT.smooth
      exact FunctorialResolution.EmbeddedResolution.orderAt_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) I y
    controlledTransform_orderAt_le := hR.controlledTransform_orderAt_le
    splitting_baseChange := by
      intro T hT L hL hLz f hV M N hs
      exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_comap_of_flat
        (CategoryTheory.Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)) hs
    splitting_smooth_pullback := by
      intro T hT Y q h hsm hq hV M N hs
      exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_comap_of_smooth h hs
    splitting_exists := by
      intro T hT
      have := hT.charZero
      have := hT.smooth
      have := hT.locallyOfFiniteType
      have := hT.quasiCompact
      have := hT.isNoetherian
      exact FunctorialResolution.EmbeddedResolution.exists_isMonomialSplitting T.structMap T.boundary hT.snc T.ideal
        hT.nonzeroOnComponents
    splitting_unique := by
      intro T hT M N M' N' hs hs'
      have := hT.charZero
      have := hT.smooth
      have := hT.locallyOfFiniteType
      have := hT.quasiCompact
      have := hT.isNoetherian
      exact FunctorialResolution.EmbeddedResolution.isMonomialSplitting_unique T.structMap T.boundary hT.snc
        hT.nonzeroOnComponents hs hs'
    strictTransform_components := hR.strictTransform_components
    monomialInputs := monomialGeometryHypotheses_of_monomialCaseHypotheses hR.monomial
  }

end FunctorialResolution.EmbeddedResolution

end
