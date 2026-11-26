module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAbsoluteValueCompleteSpaceOfDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfForallPowDvdGerm
universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.PrimeSection

theorem res_res {X : Scheme.{u}} {U V W : X.Opens} (h : W ≤ V) (h' : V ≤ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE h').op s) =
      X.presheaf.map (homOfLE (h.trans h')).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem germ_res {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V) (s : Γ(X, U)) :
    X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s) = X.presheaf.germ U x (h hx) s := by
  rw [X.presheaf.germ_res_apply (homOfLE h) x hx s]

theorem exists_unit_eq_res {X : Scheme.{u}} (t : Γ(X, ⊤)) :
    ∃ τ : Γ(X, X.basicOpen t)ˣ,
      (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t := by
  refine ⟨(X.toRingedSpace.isUnit_res_basicOpen t).unit, ?_⟩
  rfl

section Integral

variable {X : Scheme.{u}} [IsIntegral X]

theorem genericPoint_mem {W : X.Opens} {x : X} (hx : x ∈ W) : genericPoint X ∈ W := ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨x, trivial, hx⟩

theorem genericPoint_mem_basicOpen {W : X.Opens} {s : Γ(X, W)} (hs : s ≠ 0) :
    genericPoint X ∈ X.basicOpen s := by
  have hne : X.basicOpen s ≠ ⊥ := fun h => hs ((basicOpen_eq_bot_iff s).mp h)
  obtain ⟨x, hx⟩ : ∃ x, x ∈ X.basicOpen s := by
    by_contra hcon
    exact hne (eq_bot_iff.mpr fun x hx => (hcon ⟨x, hx⟩).elim)
  exact genericPoint_mem hx

theorem algebraMap_germ {W : X.Opens} {x : X} (hx : x ∈ W) (s : Γ(X, W)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ W x hx s) =
      X.presheaf.germ W (genericPoint X) (genericPoint_mem hx) s := by
  have : Nonempty W := ⟨⟨x, hx⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField]

theorem eq_of_germ_eq {W : X.Opens} {s s' : Γ(X, W)}
    (h : ∀ hW : genericPoint X ∈ W, X.presheaf.germ W _ hW s = X.presheaf.germ W _ hW s') :
    s = s' := by
  by_cases hW : genericPoint X ∈ W
  · exact germ_injective_of_isIntegral X (genericPoint X) hW (h hW)
  · refine TopCat.Presheaf.section_ext X.sheaf W s s' fun x hx => ?_
    exact (hW (genericPoint_mem hx)).elim

theorem res_inf_injective {D : X.Opens} (hD : genericPoint X ∈ D) (W : X.Opens) :
    Function.Injective (X.presheaf.map (homOfLE (inf_le_left : W ⊓ D ≤ W)).op) := by
  intro s s' hss
  refine eq_of_germ_eq fun hW => ?_
  have hWD : genericPoint X ∈ W ⊓ D := ⟨hW, hD⟩
  rw [← germ_res (inf_le_left : W ⊓ D ≤ W) hWD s, ← germ_res (inf_le_left : W ⊓ D ≤ W) hWD s', hss]

end Integral

variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))

include hη in
theorem mem_of_notMem_basicOpen {W : X.Opens} {x : X} (hx : x ∈ W) (hxt : x ∉ X.basicOpen t) :
    η ∈ W := ((hη x).mp hxt).mem_open W.isOpen hx


include hp in
theorem ne_zero : t ≠ 0 := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  intro ht
  have := (hp V hV hηV).ne_zero
  rw [ht, map_zero] at this
  exact this rfl

theorem mem_primeIdealOf_iff {U : X.Opens} (hU : IsAffineOpen U) (x : U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen s := by
  rw [hU.primeIdealOf_eq_map_closedPoint x, X.mem_basicOpen s x.1 x.2]
  change X.presheaf.germ U x.1 x.2 s ∈ IsLocalRing.maximalIdeal _ ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]


include hη hp in
theorem primeIdealOf_eq_span {U : X.Opens} (hU : IsAffineOpen U) (h : η ∈ U) :
    (hU.primeIdealOf ⟨η, h⟩).asIdeal =
      Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t} := by
  have hπ := hp U hU h
  have hηt : η ∉ X.basicOpen t := (hη η).mpr (specializes_refl η)
  have hP : (Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t}).IsPrime :=
    GlobalTheory.PrimeElement.isPrime_span hπ
  apply le_antisymm
  ·
    let P : PrimeSpectrum Γ(X, U) := ⟨_, hP⟩
    let y : U := hU.isoSpec.inv P
    have hy : hU.primeIdealOf y = P := by
      change hU.isoSpec.hom (hU.isoSpec.inv P) = P
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hyt : y.1 ∉ X.basicOpen t := by
      intro hyt
      have hmem : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∈ (hU.primeIdealOf y).asIdeal := by
        rw [hy]
        exact Ideal.subset_span rfl
      rw [mem_primeIdealOf_iff hU y, Scheme.basicOpen_res] at hmem
      exact hmem ⟨y.2, hyt⟩
    have hsp : (⟨η, h⟩ : U) ⤳ y :=
      (Topology.IsInducing.subtypeVal.specializes_iff).mp ((hη y.1).mp hyt)
    have hsp' := hsp.map hU.isoSpec.hom.continuous
    rw [← PrimeSpectrum.le_iff_specializes] at hsp'
    change (hU.primeIdealOf ⟨η, h⟩).asIdeal ≤ (hU.primeIdealOf y).asIdeal at hsp'
    rw [hy] at hsp'
    exact hsp'
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_primeIdealOf_iff hU ⟨η, h⟩,
      Scheme.basicOpen_res]
    exact fun hm => hηt hm.2


include hη hp in
theorem dvd_iff_notMem_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (h : η ∈ U) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∣ s ↔ η ∉ X.basicOpen s := by
  rw [← Ideal.mem_span_singleton, ← primeIdealOf_eq_span hη hp hU h]
  exact mem_primeIdealOf_iff hU ⟨η, h⟩ s

variable [IsIntegral X]


include hη hp in
theorem isDiscreteValuationRing_stalk [IsLocallyNoetherian X] :
    IsDiscreteValuationRing (X.presheaf.stalk η) ∧
      Irreducible (X.presheaf.germ ⊤ η trivial t) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  have hπ := hp U hU hηU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Nonempty U := ⟨⟨η, hηU⟩⟩
  have := GlobalTheory.PrimeElement.isPrime_span hπ
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨η, hηU⟩ : U)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk η) (Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t}) := by
    have h0 := hU.isLocalization_stalk ⟨η, hηU⟩
    unfold IsLocalization.AtPrime at h0 ⊢
    convert h0 using 3
    exact (primeIdealOf_eq_span hη hp hU hηU).symm
  refine ⟨GlobalTheory.PrimeElement.isDiscreteValuationRing (X.presheaf.stalk η) hπ.ne_zero, ?_⟩
  have hirr := GlobalTheory.PrimeElement.irreducible_algebraMap (X.presheaf.stalk η) hπ.ne_zero
  convert hirr using 1
  exact (germ_res le_top hηU t).symm

include hp in
theorem genericPoint_mem_inf {W : X.Opens} (h : η ∈ W) : genericPoint X ∈ W ⊓ X.basicOpen t := ⟨genericPoint_mem h, genericPoint_mem_basicOpen (ne_zero hp)⟩

private theorem exists_section_restrict_eq_of_germ_eq {V : X.Opens} (hV : IsAffineOpen V) (hηV : η ∈ V)
    (hπ : Prime (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (hq : (hV.primeIdealOf ⟨η, hηV⟩).asIdeal = Ideal.span {X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t})
    (hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (y : Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))) (z : X.presheaf.stalk η)
    (h : X.presheaf.germ _ (genericPoint X) hY y = algebraMap (X.presheaf.stalk η) X.functionField z) :
    ∃ r : Γ(X, V), X.presheaf.map (homOfLE (X.basicOpen_le _)).op r = y ∧
      (IsUnit y → IsUnit z → IsUnit r) := by
  have := GlobalTheory.PrimeElement.isPrime_span hπ
  have : Nonempty V := ⟨⟨η, hηV⟩⟩
  have : Nonempty (X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) := ⟨⟨_, hY⟩⟩
  let _ : Algebra Γ(X, V) Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))).op).hom.toAlgebra
  have : IsLocalization.Away (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) :=
    hV.isLocalization_basicOpen _
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨η, hηV⟩ : V)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk η) (Ideal.span {X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t}) := by
    have h0 := hV.isLocalization_stalk ⟨η, hηV⟩
    unfold IsLocalization.AtPrime at h0 ⊢
    convert h0 using 3
    exact hq.symm
  have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
      X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (germ_res (X.basicOpen_le _) hY a).symm
  have : FaithfulSMul Γ(X, V) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (X.germToFunctionField_injective V)
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk η) X.functionField :=
    functionField_isScalarTower X V ⟨η, hηV⟩
  have hh : algebraMap _ X.functionField y = algebraMap (X.presheaf.stalk η) X.functionField z := h
  obtain ⟨r, hr⟩ := GlobalTheory.PrimeElement.exists_algebraMap_eq (K := X.functionField) hπ.ne_zero hh
  refine ⟨r, hr, fun hy hz => ?_⟩
  obtain ⟨r', hr'u, hr'⟩ :=
    GlobalTheory.PrimeElement.exists_unit_algebraMap_eq (K := X.functionField) hπ.ne_zero hy hz hh
  have hinj := IsLocalization.injective
    (M := Submonoid.powers (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero)
  have hrr : r' = r := hinj (hr'.trans hr.symm)
  exact hrr ▸ hr'u


include hη in
theorem exists_res_eq {W : X.Opens} (r : Γ(X, W ⊓ X.basicOpen t))
    (hr : ∀ h : η ∈ W, ∃ z : X.presheaf.stalk η, algebraMap _ X.functionField z =
      X.presheaf.germ _ (genericPoint X) (genericPoint_mem_inf hp h) r) :
    ∃ s : Γ(X, W), X.presheaf.map (homOfLE inf_le_left).op s = r := by
  classical

  have hloc : ∀ x : {x // x ∈ W ∧ x ∉ X.basicOpen t}, ∃ V : X.Opens, IsAffineOpen V ∧ x.1 ∈ V ∧ V ≤ W := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open x.2.1 W.isOpen
    exact ⟨V, hV, hxV, hVW⟩
  choose V hV hxV hVW using hloc
  have hηV : ∀ x, η ∈ V x := fun x => mem_of_notMem_basicOpen hη (hxV x) x.2.2

  have hsec : ∀ x, ∃ sx : Γ(X, V x), X.presheaf.germ (V x) (genericPoint X) (genericPoint_mem (hxV x)) sx =
      X.presheaf.germ _ (genericPoint X) (genericPoint_mem_inf hp (hVW x (hηV x))) r := by
    intro x
    have hπ := hp (V x) (hV x) (hηV x)
    have hq := primeIdealOf_eq_span hη hp (hV x) (hηV x)
    have hYle : X.basicOpen (X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op t) ≤ W ⊓ X.basicOpen t := by
      rw [Scheme.basicOpen_res]
      exact fun y hy => ⟨hVW x hy.1, hy.2⟩
    have hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op t) := by
      rw [Scheme.basicOpen_res]
      exact genericPoint_mem_inf hp (hηV x)
    obtain ⟨z, hz⟩ := hr (hVW x (hηV x))
    obtain ⟨sx, hsx, -⟩ := exists_section_restrict_eq_of_germ_eq (hV x) (hηV x) hπ hq hY
      (X.presheaf.map (homOfLE hYle).op r) z (by rw [germ_res]; exact hz.symm)
    refine ⟨sx, ?_⟩
    rw [← germ_res (X.basicOpen_le _) hY sx, hsx, germ_res]
  choose sx hsx using hsec

  let O : Option {x // x ∈ W ∧ x ∉ X.basicOpen t} → X.Opens := fun i => i.elim (W ⊓ X.basicOpen t) V
  let f : ∀ i, Γ(X, O i) := fun i => Option.rec (motive := fun i => Γ(X, O i)) r sx i
  have hOW : ∀ i, O i ≤ W := by
    intro i
    cases i with
    | none => exact inf_le_left
    | some x => exact hVW x
  have hcov : W ≤ iSup O := by
    intro y hy
    by_cases hyt : y ∈ X.basicOpen t
    · exact (le_iSup O none) ⟨hy, hyt⟩
    · exact (le_iSup O (some ⟨y, hy, hyt⟩)) (hxV ⟨y, hy, hyt⟩)
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hgerm : ∀ i (hi : genericPoint X ∈ O i), X.presheaf.germ (O i) (genericPoint X) hi (f i) =
      X.presheaf.germ _ (genericPoint X) (⟨hOW i hi, hgD⟩ : genericPoint X ∈ W ⊓ X.basicOpen t) r := by
    intro i hi
    cases i with
    | none => rfl
    | some x => exact hsx x
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 O f := by
    intro i j
    refine eq_of_germ_eq fun hij => ?_
    change X.presheaf.germ _ _ hij (X.presheaf.map (Opens.infLELeft (O i) (O j)).op (f i)) =
      X.presheaf.germ _ _ hij (X.presheaf.map (Opens.infLERight (O i) (O j)).op (f j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hgerm i, hgerm j]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' O W (fun i => homOfLE (hOW i)) hcov f hcompat
  exact ⟨s, hs none⟩


include hη hp in
theorem isUnit_of_isUnit_res {W : X.Opens} {s : Γ(X, W)}
    (hs : IsUnit (X.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen t ≤ W)).op s))
    (hsη : η ∈ W → η ∈ X.basicOpen s) : IsUnit s := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ W s fun x hx => ?_
  change IsUnit (X.presheaf.germ W x hx s)
  by_cases hxt : x ∈ X.basicOpen t
  · have hx' : x ∈ W ⊓ X.basicOpen t := ⟨hx, hxt⟩
    rw [← germ_res inf_le_left hx' s]
    exact hs.map _
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW0⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
    have hVW : V ≤ W := hVW0
    have hηV : η ∈ V := mem_of_notMem_basicOpen hη hxV hxt
    have hηW : η ∈ W := hVW hηV
    rw [← germ_res hVW hxV s]
    refine IsUnit.map _ ?_
    have hπ := hp V hV hηV
    have hq := primeIdealOf_eq_span hη hp hV hηV
    have hYle : X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t) ≤ W ⊓ X.basicOpen t := by
      rw [Scheme.basicOpen_res]
      exact fun y hy => ⟨hVW hy.1, hy.2⟩
    have hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t) := by
      rw [Scheme.basicOpen_res]
      exact genericPoint_mem_inf hp hηV
    have hres : X.presheaf.map (homOfLE hYle).op (X.presheaf.map (homOfLE inf_le_left).op s) =
        X.presheaf.map (homOfLE (X.basicOpen_le _)).op (X.presheaf.map (homOfLE hVW).op s) := by
      rw [res_res, res_res]
    have hz : IsUnit (X.presheaf.germ V η hηV (X.presheaf.map (homOfLE hVW).op s)) := by
      rw [germ_res]
      exact (X.mem_basicOpen s η hηW).mp (hsη hηW)
    obtain ⟨r, hr, hru⟩ := exists_section_restrict_eq_of_germ_eq hV hηV hπ hq hY
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op (X.presheaf.map (homOfLE hVW).op s))
      (X.presheaf.germ V η hηV (X.presheaf.map (homOfLE hVW).op s))
      (by rw [algebraMap_germ, germ_res, germ_res])
    have hinj : r = X.presheaf.map (homOfLE hVW).op s := by
      have : Nonempty V := ⟨⟨η, hηV⟩⟩
      refine eq_of_germ_eq fun hgV => ?_
      rw [← germ_res (X.basicOpen_le _) hY r, hr, germ_res]
    rw [← hinj]
    refine hru ?_ hz
    rw [← hres]
    exact hs.map _

section Cocycle

variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}

theorem germ_eq_mul_germ {D : X.Opens} {r : ∀ a, Γ(X, U a ⊓ D)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ D ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_right)).op (r b))
    {a b : ι} {x : X} (ha : x ∈ U a ⊓ D) (hb : x ∈ U b ⊓ D) :
    X.presheaf.germ _ x ha (r a) =
      X.presheaf.germ _ x (show x ∈ U a ⊓ U b from ⟨ha.1, hb.1⟩) (g a b) *
        X.presheaf.germ _ x hb (r b) := by
  have hx : x ∈ U a ⊓ U b ⊓ D := ⟨⟨ha.1, hb.1⟩, ha.2⟩
  have h := congrArg (X.presheaf.germ _ x hx) (hr a b)
  rw [map_mul, germ_res, germ_res, germ_res] at h
  exact h

theorem compatible_of_res_eq {D : X.Opens} (hD : genericPoint X ∈ D) {r : ∀ a, Γ(X, U a ⊓ D)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ D ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right D inf_le_right)).op (r b))
    (c : Γ(X, D)) {s : ∀ a, Γ(X, U a)}
    (hs : ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      X.presheaf.map (homOfLE inf_le_right).op c * r a) (a b : ι) :
    X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b) := by
  refine eq_of_germ_eq fun hab => ?_
  have hga : genericPoint X ∈ U a ⊓ D := ⟨hab.1, hD⟩
  have hgb : genericPoint X ∈ U b ⊓ D := ⟨hab.2, hD⟩
  rw [map_mul, germ_res, germ_res]
  rw [← germ_res (inf_le_left : U a ⊓ D ≤ U a) hga (s a), hs a,
    ← germ_res (inf_le_left : U b ⊓ D ≤ U b) hgb (s b), hs b]
  rw [map_mul, map_mul, germ_res, germ_res, germ_eq_mul_germ hr hga hgb]
  ring


omit [IsIntegral X] in
theorem mem_basicOpen_of_compatible (hg : ∀ a b, IsUnit (g a b)) {s : ∀ a, Γ(X, U a)}
    (hs : ∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
      g a b * X.presheaf.map (homOfLE inf_le_right).op (s b))
    {a b : ι} {x : X} (ha : x ∈ U a) (hb : x ∈ X.basicOpen (s b)) : x ∈ X.basicOpen (s a) := by
  have hxb : x ∈ U b := X.basicOpen_le (s b) hb
  have hab : x ∈ U a ⊓ U b := ⟨ha, hxb⟩
  have h := congrArg (X.presheaf.germ _ x hab) (hs a b)
  rw [map_mul, germ_res, germ_res] at h
  rw [X.mem_basicOpen (s a) x ha, h]
  exact (IsUnit.mul (IsUnit.map (X.presheaf.germ _ x hab).hom (hg a b)) ((X.mem_basicOpen (s b) x hxb).mp hb))

variable [IsLocallyNoetherian X]


include hη hp in
theorem existsUnique_zpow_mul (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(X, U a),
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a) ∧
      ∃ a, ∃ x, x ∉ X.basicOpen t ∧ x ∈ X.basicOpen (s a) := by
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hηD : η ∉ X.basicOpen t := (hη η).mpr (specializes_refl η)
  obtain ⟨a₀, ha₀⟩ := hU η
  have hga₀ : genericPoint X ∈ U a₀ := genericPoint_mem ha₀

  have hf : X.presheaf.germ _ (genericPoint X) (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (r a₀) ≠ 0 := by
    intro hf0
    obtain ⟨b, hb⟩ := hr0
    apply hb
    refine eq_of_germ_eq fun hgb => ?_
    rw [map_zero, germ_eq_mul_germ hr hgb ⟨hga₀, hgD⟩, hf0, mul_zero]

  obtain ⟨hdvr, hirr⟩ := isDiscreteValuationRing_stalk hη hp
  have := hdvr

  have hφ : ∀ n : ℤ, X.presheaf.germ _ (genericPoint X) hgD (↑(τ ^ n) : Γ(X, X.basicOpen t)) =
      (algebraMap (X.presheaf.stalk η) X.functionField (X.presheaf.germ ⊤ η trivial t)) ^ n := by
    intro n
    have h1 : X.presheaf.germ _ (genericPoint X) hgD (τ : Γ(X, X.basicOpen t)) =
        algebraMap _ X.functionField (X.presheaf.germ ⊤ η trivial t) := by
      rw [hτ, germ_res, algebraMap_germ]
    rw [← h1]
    change ((Units.map (X.presheaf.germ _ (genericPoint X) hgD).hom.toMonoidHom (τ ^ n) : X.functionField)) = _
    rw [map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨n, ⟨u, hu, hun⟩, huniq⟩ :=
    GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit (K := X.functionField) hirr hf

  have hext : ∀ a, ∃ sa : Γ(X, U a), X.presheaf.map (homOfLE inf_le_left).op sa =
      X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
    intro a
    refine exists_res_eq hη hp _ fun hηa => ?_
    refine ⟨X.presheaf.germ _ η (⟨hηa, ha₀⟩ : η ∈ U a ⊓ U a₀) (g a a₀) * u, ?_⟩
    rw [map_mul, map_mul, hun, algebraMap_germ, germ_res, hφ n,
      germ_eq_mul_germ hr (⟨genericPoint_mem hηa, hgD⟩ : genericPoint X ∈ U a ⊓ X.basicOpen t) ⟨hga₀, hgD⟩]
    ring
  choose s hs using hext
  have hcomp := compatible_of_res_eq hgD hr (↑(τ ^ n) : Γ(X, X.basicOpen t)) hs
  refine ⟨n, ⟨s, hcomp, hs, a₀, η, hηD, ?_⟩, ?_⟩
  · rw [X.mem_basicOpen (s a₀) η ha₀]
    have hsu : X.presheaf.germ (U a₀) η ha₀ (s a₀) = u := by
      apply IsFractionRing.injective (X.presheaf.stalk η) X.functionField
      rw [hun, algebraMap_germ, ← germ_res inf_le_left (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (s a₀),
        hs a₀, map_mul, germ_res, hφ n]
    exact hsu ▸ hu
  · rintro n' ⟨s', hs'c, hs', a', x', hx'D, hx's⟩
    apply huniq n'
    have hηs' : η ∈ X.basicOpen (s' a') := ((hη x').mp hx'D).mem_open (X.basicOpen (s' a')).isOpen hx's
    have hηs₀ : η ∈ X.basicOpen (s' a₀) := mem_basicOpen_of_compatible hg hs'c ha₀ hηs'
    refine ⟨X.presheaf.germ (U a₀) η ha₀ (s' a₀), (X.mem_basicOpen _ η ha₀).mp hηs₀, ?_⟩
    rw [algebraMap_germ, ← germ_res inf_le_left (⟨hga₀, hgD⟩ : genericPoint X ∈ U a₀ ⊓ X.basicOpen t) (s' a₀),
      hs' a₀, map_mul, germ_res, hφ n']


include hη hp in
theorem exists_zpow_mul_isUnit (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) :
    ∃ n : ℤ, ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
  obtain ⟨a₀, ha₀⟩ := hU η
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hr0 : ∃ a, r a ≠ 0 := by
    refine ⟨a₀, fun h0 => ?_⟩
    have : Nonempty ↥(U a₀ ⊓ X.basicOpen t) := ⟨⟨genericPoint X, genericPoint_mem ha₀, hgD⟩⟩
    exact (hru a₀).ne_zero h0
  obtain ⟨n, ⟨s, hsc, hs, a', x', hx'D, hx's⟩, -⟩ := existsUnique_zpow_mul hη hp hU hg τ hτ hr hr0
  refine ⟨n, s, fun a => ?_, hsc, hs⟩
  refine isUnit_of_isUnit_res hη hp ?_ fun hηa => ?_
  · rw [hs a]
    exact ((τ ^ n).isUnit.map _).mul (hru a)
  · have hηs' : η ∈ X.basicOpen (s a') := ((hη x').mp hx'D).mem_open (X.basicOpen (s a')).isOpen hx's
    exact mem_basicOpen_of_compatible hg hsc hηa hηs'

theorem zpow_eq_zero {A B : Type*} [CommRing A] [CommRing B] (ρ : A →+* B)
    (hρ : Function.Injective ρ) {σ u p : A} (hσ : IsUnit σ) (hu : IsUnit u) (hp : ¬ IsUnit p)
    (τ : Bˣ) (hτ : (τ : B) = ρ p) {n : ℤ} (h : ρ σ = (τ ^ n : Bˣ) * ρ u) : n = 0 := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · cases k with
    | zero => rfl
    | succ k =>
      exfalso
      have h' : ρ σ = ρ (p ^ (k + 1) * u) := by
        rw [h, map_mul, map_pow, ← hτ, zpow_natCast, Units.val_pow_eq_pow_val]
      have hσ' : IsUnit (p ^ (k + 1) * u) := hρ h' ▸ hσ
      exact hp ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp (isUnit_of_mul_isUnit_left hσ'))
  · cases k with
    | zero => simp
    | succ k =>
      exfalso
      have e : ((τ ^ (-((k + 1 : ℕ) : ℤ)) : Bˣ) : B) * ((τ ^ (k + 1) : Bˣ) : B) = 1 := by
        rw [← Units.val_mul, zpow_neg, zpow_natCast, inv_mul_cancel, Units.val_one]
      have h' : ρ (σ * p ^ (k + 1)) = ρ u := by
        rw [map_mul, map_pow, h, ← hτ, ← Units.val_pow_eq_pow_val, mul_right_comm, e, one_mul]
      have hu' : IsUnit (σ * p ^ (k + 1)) := (hρ h').symm ▸ hu
      exact hp ((isUnit_pow_iff (Nat.succ_ne_zero k)).mp (isUnit_of_mul_isUnit_right hu'))


end Cocycle

end GlobalTheory.PrimeSection
end

universe u v

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.PrimeSection

theorem res_appLE {X Y : Scheme.{u}} (j : Y ⟶ X) {U : X.Opens} {W W' : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U) (h' : W' ≤ W) (s : Γ(X, U)) :
    Y.presheaf.map (homOfLE h').op (j.appLE U W h s) = j.appLE U W' (h'.trans h) s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

theorem appLE_res {X Y : Scheme.{u}} (j : Y ⟶ X) {U U' : X.Opens} {W : Y.Opens}
    (h : W ≤ j ⁻¹ᵁ U') (h' : U' ≤ U) (s : Γ(X, U)) :
    j.appLE U' W h (X.presheaf.map (homOfLE h').op s) =
      j.appLE U W (h.trans (j.preimage_mono h')) s := by
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_appLE {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X) {k : Z ⟶ X} (hk : i ≫ j = k)
    {U : X.Opens} {W : Y.Opens} {A : Z.Opens} (h : W ≤ j ⁻¹ᵁ U) (h' : A ≤ i ⁻¹ᵁ W)
    (h'' : A ≤ k ⁻¹ᵁ U) (s : Γ(X, U)) :
    i.appLE W A h' (j.appLE U W h s) = k.appLE U A h'' s := by
  subst hk
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]

theorem appLE_bijective {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] {U : X.Opens}
    (hU : U ≤ j.opensRange) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Bijective (j.appLE U W h.le) := by
  subst h
  rw [Scheme.Hom.appLE_eq_app]
  have := j.isIso_app U hU
  exact ConcreteCategory.bijective_of_isIso _

theorem eq_preimage_inf {X Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] {D U : X.Opens}
    (hj : j.opensRange = D) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) : W = j ⁻¹ᵁ (U ⊓ D) := by
  subst h hj
  exact le_antisymm (fun y hy ↦ ⟨hy, y, rfl⟩) fun y hy ↦ hy.1

theorem appLE_injective {X Y : Scheme.{u}} [IsIntegral X] (j : Y ⟶ X) [IsOpenImmersion j]
    [Nonempty Y] {U : X.Opens} {W : Y.Opens} (h : W = j ⁻¹ᵁ U) :
    Function.Injective (j.appLE U W h.le) := by
  intro s s' H
  obtain ⟨y⟩ := ‹Nonempty Y›
  refine res_inf_injective (D := j.opensRange) (genericPoint_mem ⟨y, rfl⟩) U
    ((appLE_bijective j inf_le_right (eq_preimage_inf rfl h)).1 ?_)
  rw [appLE_res, appLE_res]
  exact H

section Immersion

variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
  [IsIntegral X] [IsLocallyNoetherian X]
  {Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] (hj : j.opensRange = X.basicOpen t)
  {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
  {W : ι → Y.Opens} (hW : ∀ a, W a = j ⁻¹ᵁ U a)

include hj

omit [IsIntegral X] [IsLocallyNoetherian X] in
include hj in
theorem exists_transport (r : ∀ a, Γ(Y, W a))
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) :
    ∃ (r' : ∀ a, Γ(X, U a ⊓ X.basicOpen t)) (τ' : Γ(X, X.basicOpen t)ˣ),
      (τ' : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t ∧
      (∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r' a) =
        X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op
          (g a b) * X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r' b)) ∧
      (∀ a, r' a = 0 → r a = 0) ∧ (∀ a, IsUnit (r a) → IsUnit (r' a)) ∧
      ∀ (n : ℤ) (a : ι) (s : Γ(X, U a)), X.presheaf.map (homOfLE inf_le_left).op s =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ' ^ n) : Γ(X, X.basicOpen t)) * r' a ↔
        j.appLE (U a) (W a) (hW a).le s =
          Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a := by
  have hb := fun a ↦ appLE_bijective j (inf_le_right.trans hj.ge) (eq_preimage_inf hj (hW a))
  choose r' hr' using fun a ↦ (hb a).2 (r a)
  obtain ⟨τ', hτ'⟩ := exists_unit_eq_res t
  have htop : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ X.basicOpen t := fun y _ ↦ hj.le ⟨y, rfl⟩
  have hττ : Units.map (j.appLE _ ⊤ htop).hom.toMonoidHom τ' = τ := by
    ext
    rw [Units.coe_map, hτ, hτ']
    exact (appLE_res j _ _ _).trans (congrArg (fun φ : Γ(X, ⊤) ⟶ Γ(Y, ⊤) ↦ φ t) j.appLE_eq_app)
  refine ⟨r', τ', hτ', fun a b ↦ ?_, fun a h ↦ by rw [← hr', h, map_zero], fun a h ↦ ?_,
    fun n a s ↦ ?_⟩
  · have hab : W a ⊓ W b = j ⁻¹ᵁ (U a ⊓ U b) := by rw [hW, hW]; rfl
    refine (appLE_bijective j (inf_le_right.trans hj.ge) (eq_preimage_inf hj hab)).1 ?_
    have := hr a b
    rw [← hr' a, ← hr' b, res_appLE, res_appLE] at this
    rw [map_mul, appLE_res, appLE_res, appLE_res]
    exact this
  · rw [← hr' a] at h
    exact (isUnit_map_iff (RingEquiv.ofBijective _ (hb a)) _).1 h
  · rw [← (hb a).1.eq_iff, map_mul, appLE_res, appLE_res, hr', ← hττ, ← map_zpow, Units.coe_map]
    exact iff_of_eq (congrArg (_ = · * _) (res_appLE j htop le_top _).symm)

include hη hp

include hη hp hj in
theorem existsUnique_zpow_mul_appLE (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    (τ : Γ(Y, ⊤)ˣ) (hτ : (τ : Γ(Y, ⊤)) = j.appTop t) {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hr0 : ∃ a, r a ≠ 0) :
    ∃! n : ℤ, ∃ s : ∀ a, Γ(X, U a),
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      (∀ a, j.appLE (U a) (W a) (hW a).le (s a) =
        Y.presheaf.map (homOfLE le_top).op (↑(τ ^ n) : Γ(Y, ⊤)) * r a) ∧
      ∃ a, ∃ x, x ∉ X.basicOpen t ∧ x ∈ X.basicOpen (s a) := by
  obtain ⟨r', τ', hτ', hr', h0, -, H⟩ := exists_transport hj hW r hr τ hτ
  simpa only [H] using existsUnique_zpow_mul hη hp hU hg τ' hτ' hr'
    (hr0.imp fun a ha h ↦ ha (h0 a h))


include hη hp hj in
theorem exists_isUnit_appLE_eq (hU : ∀ x : X, ∃ a, x ∈ U a) (hg : ∀ a b, IsUnit (g a b))
    {r : ∀ a, Γ(Y, W a)}
    (hr : ∀ a b, Y.presheaf.map (homOfLE inf_le_left).op (r a) =
      j.appLE (U a ⊓ U b) (W a ⊓ W b) (inf_le_inf (hW a).le (hW b).le) (g a b) *
        Y.presheaf.map (homOfLE inf_le_right).op (r b))
    (hru : ∀ a, IsUnit (r a)) {T T' : Scheme.{u}} [IsIntegral T] [Nonempty T'] (e : T ⟶ X)
    (k : T' ⟶ T) [IsOpenImmersion k] (e' : T' ⟶ Y) (he : e' ≫ j = k ≫ e)
    {y : T} (hy : e y ∉ X.basicOpen t) {a₀ : ι} {A : T.Opens} (hyA : y ∈ A)
    (hA : A ≤ e ⁻¹ᵁ U a₀) {A' : T'.Opens} (hA' : A' = k ⁻¹ᵁ A) (hA'' : A' ≤ e' ⁻¹ᵁ W a₀)
    {u : Γ(T, A)} (hu : IsUnit u) (hur : k.appLE A A' hA'.le u = e'.appLE (W a₀) A' hA'' (r a₀)) :
    ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      (∀ a b, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        g a b * X.presheaf.map (homOfLE inf_le_right).op (s b)) ∧
      ∀ a, j.appLE (U a) (W a) (hW a).le (s a) = r a := by
  obtain ⟨τ, hτ⟩ : IsUnit (j.appTop t) := by
    obtain ⟨τ', hτ'⟩ := exists_unit_eq_res t
    have htop : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ X.basicOpen t := fun y _ ↦ hj.le ⟨y, rfl⟩
    have := τ'.isUnit.map (j.appLE _ ⊤ htop).hom
    rw [hτ', appLE_res] at this
    rwa [← show j.appLE ⊤ ⊤ _ = j.appTop from j.appLE_eq_app]
  obtain ⟨r', τ', hτ', hr', -, hu', H⟩ := exists_transport hj hW r hr τ hτ
  obtain ⟨n, s, hsu, hc, hs⟩ :=
    exists_zpow_mul_isUnit hη hp hU hg τ' hτ' hr' fun a ↦ hu' a (hru a)
  simp only [H] at hs
  have hnat : ∀ z : Γ(X, U a₀), k.appLE A A' hA'.le (e.appLE _ A hA z) =
      e'.appLE (W a₀) A' hA'' (j.appLE _ _ (hW a₀).le z) := fun z ↦ by
    have h : A' ≤ (k ≫ e) ⁻¹ᵁ U a₀ := hA'.le.trans (k.preimage_mono hA)
    rw [appLE_appLE k e rfl _ _ h, appLE_appLE e' j he _ _ h]
  let φ : Γ(Y, ⊤) →+* Γ(T', A') :=
    (e'.appLE (W a₀) A' hA'').hom.comp (Y.presheaf.map (homOfLE le_top).op).hom
  obtain rfl : n = 0 := by
    refine zpow_eq_zero (k.appLE A A' hA'.le).hom (appLE_injective k hA')
      ((hsu a₀).map (e.appLE _ A hA).hom) hu
      (p := e.appLE _ A hA (X.presheaf.map (homOfLE (le_top : U a₀ ≤ ⊤)).op t)) (fun H ↦ hy ?_)
      (Units.map φ.toMonoidHom τ) ?_ ?_
    · have := T.basicOpen_of_isUnit H
      rw [Scheme.basicOpen_appLE, Scheme.basicOpen_res] at this
      exact (show y ∈ A ⊓ e ⁻¹ᵁ (U a₀ ⊓ X.basicOpen t) from this.ge hyA).2.2
    · rw [hnat, appLE_res, Units.coe_map, hτ,
        ← show j.appLE ⊤ ⊤ le_top = j.appTop from j.appLE_eq_app]
      exact congrArg (e'.appLE (W a₀) A' hA'') (res_appLE j _ _ _)
    · rw [hnat, hs, map_mul, hur, ← map_zpow, Units.coe_map]
      rfl
  exact ⟨s, hsu, hc, fun a ↦ by simpa using hs a⟩

end Immersion

theorem isIntegral_of_basicOpen {X Y : Scheme.{u}} {t : Γ(X, ⊤)}
    (ht : ∀ U : X.Opens, IsAffineOpen U →
      X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∈ nonZeroDivisors Γ(X, U))
    (j : Y ⟶ X) [IsOpenImmersion j] [IsIntegral Y] (hj : j.opensRange = X.basicOpen t) :
    IsIntegral X := by
  have hinj : ∀ U : X.Opens, IsAffineOpen U →
      Function.Injective (j.appLE U (j ⁻¹ᵁ U) le_rfl) := fun U hU s s' h ↦ by
    have := hU.isLocalization_basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
    refine IsLocalization.injective
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
      ((Submonoid.powers_le).2 (ht U hU)) ?_
    have he : X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t) =
      U ⊓ X.basicOpen t := X.basicOpen_res _ _
    refine (appLE_bijective j (W := j ⁻¹ᵁ U) (he.le.trans (inf_le_right.trans hj.ge))
      (he ▸ eq_preimage_inf hj rfl)).1 ?_
    exact (appLE_res j _ _ s).trans (h.trans (appLE_res j _ _ s').symm)
  have : IsReduced X := ⟨fun W ↦ ⟨fun s hs ↦ X.IsSheaf.section_ext fun x hx ↦ by
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨U, hUW, hxU, hinj U hU ?_⟩
    rw [map_zero, map_zero]
    exact ((hs.map _).map _).eq_zero⟩⟩
  have hdense : Dense (Set.range j) := by
    refine dense_iff_inter_open.2 fun W hW ⟨x, hx⟩ ↦ ?_
    obtain ⟨U, hU, hxU, hUW⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨W, hW⟩) hx
    by_contra hne
    have hbot : j ⁻¹ᵁ U = ⊥ := eq_bot_iff.2 fun y hy ↦ hne ⟨j y, hUW hy, y, rfl⟩
    have : Subsingleton Γ(Y, j ⁻¹ᵁ U) := by rw [hbot]; infer_instance
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    exact not_subsingleton Γ(X, U) (hinj U hU).subsingleton
  have : IrreducibleSpace X := by
    have h := (IrreducibleSpace.isIrreducible_univ Y).image j j.continuous.continuousOn
    rw [Set.image_univ] at h
    have h' := h.closure
    rw [hdense.closure_eq] at h'
    exact (irreducibleSpace_def X).2 h'
  exact isIntegral_of_irreducibleSpace_of_isReduced X

theorem ker_eq_map_of_isPushout {A B C P : CommRingCat.{u}} {α : A ⟶ B} {β : A ⟶ C} {γ : B ⟶ P}
    {δ : C ⟶ P} (h : IsPushout α β γ δ) (hβ : Function.Surjective β) :
    RingHom.ker γ.hom = (RingHom.ker β.hom).map α.hom := by
  refine le_antisymm (fun z hz ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_)
  · let J := (RingHom.ker β.hom).map α.hom
    have hJ : RingHom.ker β.hom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp α.hom) := fun a ha ↦
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    let ψ : C →+* B ⧸ J := RingHom.liftOfSurjective β.hom hβ ⟨_, hJ⟩
    have w : α ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) = β ≫ CommRingCat.ofHom ψ := by
      ext a
      exact (RingHom.liftOfSurjective_comp_apply β.hom hβ ⟨_, hJ⟩ a).symm
    have := congrArg (fun φ : B ⟶ CommRingCat.of (B ⧸ J) ↦ φ z) (h.inl_desc _ _ w)
    rw [CommRingCat.comp_apply, show γ z = 0 from hz, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  · have := congrArg (fun φ : A ⟶ P ↦ φ a) h.w
    simp only [CommRingCat.comp_apply] at this
    rw [show β a = 0 from ha, map_zero] at this
    exact this

theorem ker_app_eq_span {X Z : Scheme.{u}} {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) {c : A} (hc : RingHom.ker β.hom = Ideal.span {c})
    {f : X ⟶ Spec A} {i : Z ⟶ X} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β))
    {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom = Ideal.span {(X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (f.appTop ((Scheme.ΓSpecIso A).inv c)))} := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  rw [ker_eq_map_of_isPushout hpo' hβ, hc, Ideal.map_span, Set.image_singleton]
  rfl

end GlobalTheory.PrimeSection
