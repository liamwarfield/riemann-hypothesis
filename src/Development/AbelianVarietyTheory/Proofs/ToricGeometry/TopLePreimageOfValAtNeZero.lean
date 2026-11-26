module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
public import ReciprocityTheory.ThetaQuasiPeriods.Transl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

variable {X Y : Scheme.{0}}

theorem top_le_preimage_iff_mem (x : Sp ℂ ⟶ X) (U : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U := by
  constructor
  · intro h
    exact h (Set.mem_univ (default : PrimeSpectrum ℂ))
  · intro h p _
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst this
    exact h

theorem top_le_preimage_mono (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ U :=
  fun _ hp => h (hV hp)

theorem top_le_preimage_inf (x : Sp ℂ ⟶ X) (U V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) ↔ ⊤ ≤ x ⁻¹ᵁ U ∧ ⊤ ≤ x ⁻¹ᵁ V := by
  simp only [top_le_preimage_iff_mem]
  exact Iff.rfl

theorem top_le_preimage_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) :
    ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := by
  rw [Scheme.Hom.comp_preimage]

def valAtHom (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* ℂ :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem valAt'_eq_valAt (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valAt x U h f := by
  rw [valAt', dite_eq_left h]

theorem valAt'_eq_valAtHom (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = valAtHom x U h f := valAt'_eq_valAt x h f

theorem valAt'_of_not_le (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ¬ ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = 0 := by
  rw [valAt', dite_eq_right h]

theorem top_le_preimage_of_valAt'_ne_zero (x : Sp ℂ ⟶ X) {U : X.Opens} {f : Γ(X, U)} (h : valAt' x U f ≠ 0) :
    ⊤ ≤ x ⁻¹ᵁ U := by
  by_contra hU
  exact h (valAt'_of_not_le x hU f)

theorem valAt'_ringHom (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f :=
  ⟨valAtHom x U h, valAt'_eq_valAtHom x h⟩

theorem valAt'_mul (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f * g) = valAt' x U f * valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_mul]
  · simp only [valAt'_of_not_le x h, mul_zero]

theorem valAt'_add (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f + g) = valAt' x U f + valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_add (f := _)]
  · simp only [valAt'_of_not_le x h, add_zero]

theorem valAt'_zero (x : Sp ℂ ⟶ X) (U : X.Opens) : valAt' x U 0 = 0 := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_zero]
  · simp only [valAt'_of_not_le x h]

theorem valAt'_neg (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) : valAt' x U (-f) = - valAt' x U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_neg]
  · simp only [valAt'_of_not_le x h, neg_zero]

theorem valAt'_sub (x : Sp ℂ ⟶ X) (U : X.Opens) (f g : Γ(X, U)) :
    valAt' x U (f - g) = valAt' x U f - valAt' x U g := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [valAt'_eq_valAtHom x h, map_sub]
  · simp only [valAt'_of_not_le x h, sub_zero]

theorem valAt'_sum {κ : Type*} (x : Sp ℂ ⟶ X) (U : X.Opens) (s : Finset κ) (f : κ → Γ(X, U)) :
    valAt' x U (∑ i ∈ s, f i) = ∑ i ∈ s, valAt' x U (f i) := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [valAt'_eq_valAtHom x h, map_sum]
  · simp only [valAt'_of_not_le x h, Finset.sum_const_zero]

theorem valAt'_one (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U 1 = 1 := by
  simp only [valAt'_eq_valAtHom x h, map_one]

theorem valAt'_prod {κ : Type*} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset κ) (f : κ → Γ(X, U)) :
    valAt' x U (∏ i ∈ s, f i) = ∏ i ∈ s, valAt' x U (f i) := by
  simp only [valAt'_eq_valAtHom x h, map_prod]

theorem valAt'_pow (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (n : ℕ) :
    valAt' x U (f ^ n) = valAt' x U f ^ n := by
  simp only [valAt'_eq_valAtHom x h, map_pow]

theorem valAt'_isUnit_ne_zero (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {f : Γ(X, U)} (hf : IsUnit f) :
    valAt' x U f ≠ 0 := by
  rw [valAt'_eq_valAtHom x h]
  exact (hf.map _).ne_zero

theorem valAt'_unit_ne_zero (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valAt' x U u.val ≠ 0 :=
  valAt'_isUnit_ne_zero x h u.isUnit

theorem valAt'_units_zpow (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valAt' x U (u ^ n).val = valAt' x U u.val ^ n := by
  simp only [valAt'_eq_valAtHom x h]
  have := congrArg Units.val (map_zpow (Units.map (valAtHom x U h : Γ(X, U) →* ℂ)) u n)
  rw [Units.val_zpow_eq_zpow_val] at this
  exact this

theorem valAt'_zpow (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (n : ℤ) :
    valAt' x U (u ^ n).val = valAt' x U u.val ^ n :=
  valAt'_units_zpow x h u n

theorem valAt'_units_inv (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (u : Γ(X, U)ˣ) :
    valAt' x U (u⁻¹).val = (valAt' x U u.val)⁻¹ := by
  simpa using valAt'_units_zpow x h u (-1)

theorem valAt'_units_prod {κ : Type*} (x : Sp ℂ ⟶ X) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Finset κ)
    (u : κ → Γ(X, U)ˣ) : valAt' x U (∏ i ∈ s, u i).val = ∏ i ∈ s, valAt' x U (u i).val := by
  rw [Units.coe_prod, valAt'_prod x h]

theorem valAt'_appLE (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U))
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((φ.appLE U V e).hom f) = valAt' (x ≫ φ) U f := by
  have hU : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := (top_le_preimage_comp x φ U).2 (top_le_preimage_mono x e hV)
  rw [valAt'_eq_valAt x hV, valAt'_eq_valAt _ hU, valAt, valAt, ← CommRingCat.comp_apply (φ.appLE U V e),
    Scheme.Hom.appLE_comp_appLE]

theorem valAt'_map (x : Sp ℂ ⟶ X) {U V : X.Opens} (i : Opposite.op U ⟶ Opposite.op V) (f : Γ(X, U))
    (hV : ⊤ ≤ x ⁻¹ᵁ V) : valAt' x V ((X.presheaf.map i).hom f) = valAt' x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := top_le_preimage_mono x i.unop.le hV
  rw [valAt'_eq_valAt x hV, valAt'_eq_valAt _ hU, valAt, valAt, ← CommRingCat.comp_apply (X.presheaf.map i),
    Scheme.Hom.map_appLE]

theorem valAt'_res (x : Sp ℂ ⟶ X) {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    valAt' x V (resG X h f) = valAt' x U f :=
  valAt'_map x (homOfLE h).op f hV

theorem valAt'_comp (x : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U)
  · rw [Scheme.Hom.app_eq_appLE]
    exact valAt'_appLE x φ U _ _ f h
  · rw [valAt'_of_not_le x h, valAt'_of_not_le _ (fun h' => h ((top_le_preimage_comp x φ U).1 h'))]

theorem top_le_preimage_basicOpen_iff (x : Sp ℂ ⟶ X) (U : X.Opens) (f : Γ(X, U)) :
    ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0 := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · have h1 : (Sp ℂ).basicOpen ((x.appLE U ⊤ h).hom f) = x ⁻¹ᵁ X.basicOpen f := by
      have := Scheme.basicOpen_appLE x ⊤ U h f
      rw [top_inf_eq] at this
      exact this
    rw [← h1, valAt'_eq_valAt x h, valAt, top_le_iff]
    generalize (x.appLE U ⊤ h).hom f = g
    rw [← isUnit_iff_ne_zero]
    constructor
    · intro hg
      have : IsUnit g := (Sp ℂ).toRingedSpace.isUnit_of_isUnit_germ ⊤ g fun p hp =>
        ((Sp ℂ).mem_basicOpen g p hp).1 (by rw [hg]; exact hp)
      exact this.map _
    · intro hg
      have : IsUnit g := by
        have h2 := hg.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
        simpa using h2
      exact (Sp ℂ).basicOpen_of_isUnit this
  · refine ⟨fun h' => (h (top_le_preimage_mono x (X.basicOpen_le f) h')).elim, fun h' => ?_⟩
    exact (h' (valAt'_of_not_le x h f)).elim

theorem valAt'_id_top (a : ℂ) :
    valAt' (𝟙 (Sp ℂ)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a) = a := by
  rw [valAt'_eq_valAt (𝟙 (Sp ℂ)) (U := ⊤) le_top]
  unfold valAt
  simp [Scheme.Hom.appLE]

theorem valAt'_constFn (x : Sp ℂ ⟶ X) (p : X ⟶ Sp ℂ) (hp : x ≫ p = 𝟙 _) (U : X.Opens) (a : ℂ)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : valAt' x U (constFn p U a) = a := by
  refine (valAt'_appLE x p ⊤ U le_top _ h).trans ?_
  rw [hp, valAt'_id_top]

theorem valAt'_rules : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) :=
  fun _ x => ⟨top_le_preimage_iff_mem x, fun _ h => valAt'_ringHom x h, fun _ _ h f hV => valAt'_res x h f hV,
    fun _ φ U f => valAt'_comp x φ U f, top_le_preimage_basicOpen_iff x, fun p hp U a h => valAt'_constFn x p hp U a h⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsUniquePointOfRingHom
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory.AffinePointValues

lemma appLE_specMap_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (f : Γ(Y, V) ⟶ R) (e) :
    (Spec.map f ≫ hV.fromSpec).appLE V ⊤ e ≫ (Scheme.ΓSpecIso R).hom = f := by

  apply Spec.map_injective
  rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec _ hV (isAffineOpen_top _) e,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

lemma specMap_appLE_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (x : Spec R ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    Spec.map (x.appLE V ⊤ hx ≫ (Scheme.ΓSpecIso R).hom) ≫ hV.fromSpec = x := by
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top _) hx,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

lemma fromSpec_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : CommRingCat.{0}}
    (s : Y ⟶ Spec R) (h) :
    hV.fromSpec ≫ s = Spec.map ((Scheme.ΓSpecIso R).inv ≫ s.appLE ⊤ V h) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV h,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, Spec.map_comp]

end GlobalTheory.AffinePointValues

namespace GlobalTheory


open AffinePointValues in
theorem existsUnique_point_of_ringHom :
    (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) := by
  intro X U hU e he
  let φ : Γ(X.left, U) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom e

  have hconst : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U (fun _ _ => trivial) ≫ φ =
      𝟙 _ := by
    ext a
    exact he a
  have hw : (Spec.map φ ≫ hU.fromSpec) ≫ X.hom = (𝟙_ (Over (Sp ℂ))).hom := by
    rw [Category.assoc, fromSpec_comp hU X.hom (fun _ _ => trivial), ← Spec.map_comp,
      Category.assoc, hconst, Spec.map_id]
    rfl
  have hpre : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U := by
    intro p _
    show hU.fromSpec.base ((Spec.map φ).base p) ∈ U
    have h : (Spec.map φ).base p ∈ hU.fromSpec ⁻¹ᵁ U := by
      rw [IsAffineOpen.fromSpec_preimage_self]; trivial
    exact h
  refine ⟨Over.homMk (Spec.map φ ≫ hU.fromSpec) hw, ⟨hpre, fun f => ?_⟩, ?_⟩
  · show valAt' (Spec.map φ ≫ hU.fromSpec) U f = e f
    rw [valAt', dite_eq_left hpre]
    exact congrArg (fun g => g.hom f) (appLE_specMap_fromSpec hU φ hpre)
  · rintro y ⟨hy, hv⟩
    apply Over.OverMorphism.ext
    have h1 : y.left.appLE U ⊤ hy ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = φ := by
      ext f
      have := hv f
      rw [valAt', dite_eq_left hy] at this
      exact this
    rw [← specMap_appLE_fromSpec hU y.left hy, h1]
    rfl

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem holFamily_of_affine
    (hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (Z : Scheme.{0}) (c : E → (Sp ℂ ⟶ Z))
    (hc : ∀ w ∈ W, ∃ V : Z.Opens, IsAffineOpen V ∧ ⊤ ≤ c w ⁻¹ᵁ V ∧ IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∧
      ∀ g : Γ(Z, V), DifferentiableOn ℂ (fun w => valAt' (c w) V g) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V})
    (U : Z.Opens) (f : Γ(Z, U)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w) U f) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} := by
  have hpt : ∀ (Y : Scheme.{0}) (x : Sp ℂ ⟶ Y) (O : Y.Opens),
      ⊤ ≤ x ⁻¹ᵁ O ↔ x (default : PrimeSpectrum ℂ) ∈ O := fun Y x O => (hv Y x).1 O

  have key : ∀ w₀ ∈ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U}, ∃ N : Set E, IsOpen N ∧ w₀ ∈ N ∧
      N ⊆ {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (c w) U f) N := by
    rintro w₀ ⟨hw₀, hU₀⟩
    obtain ⟨V, hVa, hV₀, hVo, hVd⟩ := hc w₀ hw₀
    obtain ⟨g, hgU, hg₀⟩ := hVa.exists_basicOpen_le (V := U)
      ⟨c w₀ (default : PrimeSpectrum ℂ), (hpt _ _ _).1 hU₀⟩ ((hpt _ _ _).1 hV₀)
    have hDV : Z.basicOpen g ≤ V := Z.basicOpen_le g
    let := hVa.isLocalization_basicOpen g
    obtain ⟨⟨h, ⟨_, n, rfl⟩⟩, hh⟩ := IsLocalization.surj (Submonoid.powers g) (resG Z hgU f)
    have hh' : resG Z hgU f * resG Z hDV g ^ n = resG Z hDV h := by
      rw [← map_pow]
      exact hh
    refine ⟨{w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∩ (fun w => valAt' (c w) V g) ⁻¹' {0}ᶜ,
      (hVd g).continuousOn.isOpen_inter_preimage hVo isOpen_compl_singleton, ?_, ?_, ?_⟩
    · refine ⟨⟨hw₀, hV₀⟩, ?_⟩
      exact ((hv Z (c w₀)).2.2.2.2.1 V g).1 ((hpt _ _ _).2 hg₀)
    · rintro w ⟨⟨hw, -⟩, hg⟩
      have hD : ⊤ ≤ c w ⁻¹ᵁ Z.basicOpen g := ((hv Z (c w)).2.2.2.2.1 V g).2 hg
      exact ⟨hw, (hpt _ _ _).2 (hgU ((hpt _ _ _).1 hD))⟩
    · have hq : DifferentiableOn ℂ (fun w => valAt' (c w) V h * (valAt' (c w) V g ^ n)⁻¹)
          ({w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ V} ∩ (fun w => valAt' (c w) V g) ⁻¹' {0}ᶜ) :=
        by
        apply DifferentiableOn.fun_mul
        · exact (hVd h).mono Set.inter_subset_left
        · apply DifferentiableOn.fun_inv
          · exact ((hVd g).mono Set.inter_subset_left).fun_pow n
          · intro w hw
            exact pow_ne_zero _ hw.2
      refine hq.congr fun w ⟨⟨hw, hwV⟩, hg⟩ => ?_
      have hg' : valAt' (c w) V g ≠ 0 := hg
      have hD : ⊤ ≤ c w ⁻¹ᵁ Z.basicOpen g := ((hv Z (c w)).2.2.2.2.1 V g).2 hg'
      obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hD
      have h1 := (hv Z (c w)).2.2.1 U _ hgU f hD
      have h2 := (hv Z (c w)).2.2.1 V _ hDV g hD
      have h3 := (hv Z (c w)).2.2.1 V _ hDV h hD
      rw [he] at h1 h2 h3
      have h4 := congrArg e hh'
      rw [map_mul, map_pow, h1, h2, h3] at h4
      rw [← div_eq_mul_inv]
      exact eq_div_of_mul_eq (pow_ne_zero _ hg') h4
  refine ⟨isOpen_iff_forall_mem_open.2 fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨N, hNo, hwN, hNs, -⟩ := key w hw
    exact ⟨N, hNs, hNo, hwN⟩
  · obtain ⟨N, hNo, hwN, -, hNd⟩ := key w hw
    exact (hNd.differentiableAt (hNo.mem_nhds hwN)).differentiableWithinAt

theorem holFamily_of_isPullback
    (hv : (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) {S X Y Z : Scheme.{0}} [IsAffine S]
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) (c : E → (Sp ℂ ⟶ Z))
    (ha : ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w ≫ p) U f) {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ U})
    (hb : ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w ≫ q) U f) {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ U})
    (U : Z.Opens) (f : Γ(Z, U)) :
    IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w => valAt' (c w) U f) {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ U} := by
  have hpt : ∀ (T : Scheme.{0}) (x : Sp ℂ ⟶ T) (O : T.Opens),
      ⊤ ≤ x ⁻¹ᵁ O ↔ x (default : PrimeSpectrum ℂ) ∈ O := fun T x O => (hv T x).1 O
  refine holFamily_of_affine hv W Z c (fun w hw => ?_) U f
  obtain ⟨VX, hVXa, hVX₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (p (c w (default : PrimeSpectrum ℂ))))
  obtain ⟨VY, hVYa, hVY₀, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (q (c w (default : PrimeSpectrum ℂ))))
  have hSX : VX ≤ s ⁻¹ᵁ (⊤ : S.Opens) := le_top
  have hST : VY ≤ t ⁻¹ᵁ (⊤ : S.Opens) := le_top

  have hmem : ∀ x : Sp ℂ ⟶ Z, ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) ↔
      ⊤ ≤ (x ≫ p) ⁻¹ᵁ VX ∧ ⊤ ≤ (x ≫ q) ⁻¹ᵁ VY := by
    intro x
    show ⊤ ≤ x ⁻¹ᵁ (p ⁻¹ᵁ VX) ⊓ x ⁻¹ᵁ (q ⁻¹ᵁ VY) ↔ _
    exact le_inf_iff
  have hPO := (isIso_pushoutSection_iff H hST hSX (UY := p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) rfl).1
    (isIso_pushoutSection_of_isAffineOpen H hST hSX rfl (isAffineOpen_top S) hVYa hVXa)
  have hVa : IsAffineOpen (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) := by
    have : IsAffine (⊤ : S.Opens) := isAffineOpen_top S
    have : IsAffine VY := hVYa
    have : IsAffine VX := hVXa
    exact .of_isIso (Scheme.Hom.isPullback_resLE H hST hSX rfl).isoPullback.hom

  have hNo : IsOpen {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)} := by
    convert (ha VX 0).1.inter (hb VY 0).1 using 1
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, hmem]
    tauto

  let T : Subring Γ(Z, p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) :=
    { carrier := {g | DifferentiableOn ℂ (fun w => valAt' (c w) (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) g)
        {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)}}
      mul_mem' := fun {a b} ha' hb' => (ha'.fun_mul hb').congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_mul]
      one_mem' := (differentiableOn_const (1 : ℂ)).congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_one]
      add_mem' := fun {a b} ha' hb' => (ha'.fun_add hb').congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_add (f := _)]
      zero_mem' := (differentiableOn_const (0 : ℂ)).congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_zero]
      neg_mem' := fun {a} ha' => ha'.fun_neg.congr fun w hw => by
        obtain ⟨e, he⟩ := (hv Z (c w)).2.1 _ hw.2
        simp only [he, map_neg] }

  have hXT : ∀ a : Γ(X, VX), (p.appLE VX (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_left).hom a ∈ T := by
    intro a
    change DifferentiableOn ℂ
      (fun w => valAt' (c w) (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)
        ((p.appLE VX (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_left).hom a)) _
    have hd : DifferentiableOn ℂ (fun w => valAt' (c w ≫ p) VX a)
        {w | w ∈ W ∧ ⊤ ≤ (c w ≫ p) ⁻¹ᵁ VX} := (ha VX a).2
    have hm : DifferentiableOn ℂ (fun w => valAt' (c w ≫ p) VX a)
        {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)} :=
      hd.mono fun w hw => ⟨hw.1, ((hmem _).1 hw.2).1⟩
    refine hm.congr fun w hw => by
      change w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) at hw
      have h1 := (hv Z (c w)).2.2.1 (p ⁻¹ᵁ VX) _ inf_le_left ((p.app VX).hom a) hw.2
      have h2 := (hv Z (c w)).2.2.2.1 X p VX a
      exact h1.trans h2
  have hYT : ∀ b : Γ(Y, VY), (q.appLE VY (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_right).hom b ∈ T := by
    intro b
    change DifferentiableOn ℂ
      (fun w => valAt' (c w) (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)
        ((q.appLE VY (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) inf_le_right).hom b)) _
    have hd : DifferentiableOn ℂ (fun w => valAt' (c w ≫ q) VY b)
        {w | w ∈ W ∧ ⊤ ≤ (c w ≫ q) ⁻¹ᵁ VY} := (hb VY b).2
    have hm : DifferentiableOn ℂ (fun w => valAt' (c w ≫ q) VY b)
        {w | w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)} :=
      hd.mono fun w hw => ⟨hw.1, ((hmem _).1 hw.2).2⟩
    refine hm.congr fun w hw => by
      change w ∈ W ∧ ⊤ ≤ c w ⁻¹ᵁ (p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY) at hw
      have h1 := (hv Z (c w)).2.2.1 (q ⁻¹ᵁ VY) _ inf_le_right ((q.app VY).hom b) hw.2
      have h2 := (hv Z (c w)).2.2.2.1 Y q VY b
      exact h1.trans h2

  let φX : Γ(X, VX) ⟶ CommRingCat.of T := CommRingCat.ofHom ((p.appLE VX _ inf_le_left).hom.codRestrict T hXT)
  let φY : Γ(Y, VY) ⟶ CommRingCat.of T := CommRingCat.ofHom ((q.appLE VY _ inf_le_right).hom.codRestrict T hYT)
  have hw' : s.appLE ⊤ VX hSX ≫ φX = t.appLE ⊤ VY hST ≫ φY := by
    ext x
    exact congrArg (fun k => k.hom x) hPO.w
  have hid : hPO.desc φX φY hw' ≫ CommRingCat.ofHom T.subtype = 𝟙 _ := by
    refine hPO.hom_ext ?_ ?_
    · rw [← Category.assoc, hPO.inl_desc, Category.comp_id]
      rfl
    · rw [← Category.assoc, hPO.inr_desc, Category.comp_id]
      rfl
  refine ⟨_, hVa, (hmem _).2 ⟨(hpt _ _ _).2 hVX₀, (hpt _ _ _).2 hVY₀⟩, hNo, fun g => ?_⟩
  have h1 := congrArg (fun k => k.hom g) hid
  have h2 : ((hPO.desc φX φY hw').hom g : Γ(Z, p ⁻¹ᵁ VX ⊓ q ⁻¹ᵁ VY)) = g := h1
  rw [← h2]
  exact ((hPO.desc φX φY hw').hom g).2

theorem holFamily_lift :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) := by
  intro hv E _ _ W X Y a b ha hb U f

  have H : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    IsPullback.of_hasPullback X.hom Y.hom
  have hfa : ∀ w, (lift (a w) (b w)).left ≫ (fst X Y).left = (a w).left := fun w => by
    rw [← Over.comp_left, lift_fst]
  have hfb : ∀ w, (lift (a w) (b w)).left ≫ (snd X Y).left = (b w).left := fun w => by
    rw [← Over.comp_left, lift_snd]
  exact holFamily_of_isPullback hv W H (fun w => (lift (a w) (b w)).left)
    (fun U' f' => by simpa only [hfa] using ha U' f')
    (fun U' f' => by simpa only [hfb] using hb U' f') U f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem isReduced_scheme_of_smooth_of_isIntegrallyClosed (T : Type) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f] :
    AlgebraicGeometry.IsReduced X := by
  have hT : GlobalTheory.IsNormalScheme (Sp T) := inferInstance
  have hX : GlobalTheory.IsNormalScheme X := (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff _).mp hT))
  infer_instance

theorem isReduced_of_smooth_complex :
    (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) :=
  fun _ p _ ↦ isReduced_scheme_of_smooth_of_isIntegrallyClosed ℂ p

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.CubeTrivialisationOnUniformisingSpace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.CubeValues

def ValueRules : Prop :=
  ∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)

section Values

variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

lemma le_preimage_inf (U V : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) ↔ ⊤ ≤ x ⁻¹ᵁ U ∧ ⊤ ≤ x ⁻¹ᵁ V := by
  show ⊤ ≤ x ⁻¹ᵁ U ⊓ x ⁻¹ᵁ V ↔ _
  exact le_inf_iff

lemma val_unit_ne_zero (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    valAt' x U f.val ≠ 0 := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  rw [he]
  exact (Units.map (e : Γ(X, U) →* ℂ) f).ne_zero

lemma val_unit_mul (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f f' : Γ(X, U)ˣ) :
    valAt' x U (f * f').val = valAt' x U f.val * valAt' x U f'.val := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  rw [he, he, he, Units.val_mul, map_mul]

lemma val_unit_prod_zpow (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {K : Type} [Fintype K]
    (f : K → Γ(X, U)ˣ) (ε : K → ℤ) :
    valAt' x U (∏ k, f k ^ ε k).val = ∏ k, valAt' x U (f k).val ^ ε k := by
  obtain ⟨e, he⟩ := (hv X x).2.1 U h
  have hm : ∀ w : Γ(X, U)ˣ, valAt' x U w.val = ((Units.map (e : Γ(X, U) →* ℂ) w : ℂˣ) : ℂ) :=
    fun w => he w.val
  calc valAt' x U (∏ k, f k ^ ε k).val = ((Units.map (e : Γ(X, U) →* ℂ) (∏ k, f k ^ ε k) : ℂˣ) : ℂ) := hm _
    _ = ∏ k, ((Units.map (e : Γ(X, U) →* ℂ) (f k) : ℂˣ) : ℂ) ^ ε k := by
      rw [map_prod, Units.coe_prod]
      simp only [map_zpow, Units.val_zpow_eq_zpow_val]
    _ = ∏ k, valAt' x U (f k).val ^ ε k := by simp only [hm]

lemma val_res (hv : ValueRules) {U V : X.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)ˣ) :
    valAt' x V (res hVU f).val = valAt' x U f.val :=
  (hv X x).2.2.1 U V hVU f.val h

lemma val_pullU (hv : ValueRules) {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)ˣ) :
    valAt' x (φ ⁻¹ᵁ U) (pullU φ U f).val = valAt' (x ≫ φ) U f.val :=
  (hv X x).2.2.2.1 Y φ U f.val

lemma le_preimage_wchart {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K] (φ : K → (X ⟶ Y))
    (j : K → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ L.wchart φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  have key : ∀ q : Sp ℂ, q ∈ x ⁻¹ᵁ L.wchart φ j ↔ ∀ k, q ∈ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
    intro q
    show x q ∈ L.wchart φ j ↔ ∀ k, φ k (x q) ∈ L.U (j k)
    simp [LB.wchart]
  constructor
  · intro h k q _
    exact (key q).1 (h trivial) k
  · intro h q _
    exact (key q).2 (fun k => h k trivial)

lemma val_gen (hv : ValueRules) {L : LB X} (t : L.Gen) (ht : t.IsGen) (i j : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valAt' x (L.U i) (t.s i).val =
      valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j) (t.s j).val := by
  have hij : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  have e := congrArg (fun w : Γ(X, L.U i ⊓ L.U j)ˣ => valAt' x (L.U i ⊓ L.U j) w.val) (ht i j)
  rw [val_unit_mul x hv hij, val_res x hv _ hij, val_res x hv _ hij] at e
  exact e

lemma val_linComb (hv : ValueRules) {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K]
    (φ : K → (X ⟶ Y)) (ε : K → ℤ) (j j' : K → L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j) (hj' : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j') :
    valAt' x (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by
  have h2 : ⊤ ≤ x ⁻¹ᵁ (L.wchart φ j ⊓ L.wchart φ j') := (le_preimage_inf x _ _).2 ⟨hj, hj'⟩
  simp only [LB.LinComb]
  rw [val_unit_prod_zpow x hv h2]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  congr 1
  refine (val_res x hv _ h2 _).trans ?_
  exact val_pullU x hv (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k))

lemma val_cocycle (hv : ValueRules) {L : LB X} (hL : L.IsLB) (i j k : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j ⊓ L.U k) (L.g j k).val =
      valAt' x (L.U i ⊓ L.U k) (L.g i k).val := by
  obtain ⟨-, -, hc⟩ := hL
  have hij : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) := (le_preimage_inf x _ _).2 ⟨hi, hj⟩
  have hijk : ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j ⊓ L.U k) := (le_preimage_inf x _ _).2 ⟨hij, hk⟩
  have e := congrArg (fun w : Γ(X, L.U i ⊓ L.U j ⊓ L.U k)ˣ => valAt' x _ w.val) (hc i j k)
  rw [val_unit_mul x hv hijk, val_res x hv _ hijk, val_res x hv _ hijk, val_res x hv _ hijk] at e
  exact e

end Values

section Points

variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)

lemma ex_zero : u.ex 0 = 1 := (u.ker 0).2 (zero_mem _)

lemma ex_add_period (z l : Fin g → ℂ) (hl : l ∈ u.Λ) : u.ex (z + l) = u.ex z := by
  rw [u.ex_add, (u.ker l).2 hl, _root_.mul_one]

lemma comp_foldr {T T' : Over (Sp ℂ)} (p : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A)) (l : List (Fin n)) :
    p ≫ l.foldr (fun k acc => padd A (y k) acc) (pzero A T) = (l.map fun k => p ≫ y k).prod := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.prod_nil, pzero, Hom.one_def, comp_toUnit_assoc]
  | cons k l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons, ← ih, padd, Hom.mul_def, comp_lift_assoc]

lemma ex_list_sum {κ : Type} (w : κ → Fin g → ℂ) (l : List κ) :
    u.ex (l.map w).sum = (l.map fun k => u.ex (w k)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, List.prod_nil, ex_zero]
  | cons k l ih => simp only [List.map_cons, List.sum_cons, List.prod_cons, u.ex_add, ih]

lemma comp_psum {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (w : Fin n → Fin g → ℂ) (h : ∀ k, p ≫ y k = u.ex (w k)) (I : Finset (Fin n)) :
    p ≫ psum A y I = u.ex (∑ a ∈ I, w a) := by
  have hs : ∑ a ∈ I, w a = (((List.finRange n).filter (fun a => decide (a ∈ I))).map w).sum := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _)]
    congr 1
    ext a
    simp
  rw [psum, comp_foldr, hs, ex_list_sum]
  exact congrArg List.prod (List.map_congr_left (fun k _ => h k))

def pt3 (x : Fin 3 → Fin g → ℂ) : 𝟙_ (Over (Sp ℂ)) ⟶ G3 A :=
  lift (u.ex (x 0)) (lift (u.ex (x 1)) (u.ex (x 2)))

lemma tripleProductPoint_comp_partialSum (x : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)) :
    (pt3 u x).left ≫ (psum A (x3 A) I).left = (u.ex (∑ a ∈ I, x a)).left := by
  rw [← Over.comp_left, comp_psum u (pt3 u x) (x3 A) x _ I]
  intro k
  fin_cases k <;> simp [pt3, x3]

lemma tripleProductPoint_add_period (x l : Fin 3 → Fin g → ℂ) (hl : ∀ a, l a ∈ u.Λ) :
    pt3 u (x + l) = pt3 u x := by
  simp only [pt3, Pi.add_apply, ex_add_period u _ _ (hl _)]

lemma hol_coord (a : Fin 3) (U : A.left.Opens) (f : Γ(A.left, U)) :
    IsOpen {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun w : Fin 3 → Fin g → ℂ => valAt' (u.ex (w a)).left U f)
        {w | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} := by
  obtain ⟨ho, hd⟩ := u.hol U f
  have hset : {w : Fin 3 → Fin g → ℂ | w ∈ (Set.univ : Set _) ∧ ⊤ ≤ (u.ex (w a)).left ⁻¹ᵁ U} =
      (fun w : Fin 3 → Fin g → ℂ => w a) ⁻¹' {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} := by
    ext w; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact ho.preimage (continuous_apply a)
  · exact hd.comp (differentiable_apply a).differentiableOn (fun w hw => hw.2)

private theorem pt3_preimage_theta_whole_iff {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ}
    (u : HolUnif A L₀ g) (L : LB A.left) (j : Finset (Fin 3) → L.ι) (x : Fin 3 → Fin g → ℂ) :
    ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j I.down) ↔
      ∀ I : Finset (Fin 3), ⊤ ≤ (u.ex (∑ a ∈ I, x a)).left ⁻¹ᵁ L.U (j I) := by
  show ⊤ ≤ (pt3 u x).left ⁻¹ᵁ
      L.wchart (fun I : ULift (Finset (Fin 3)) => (psum A (x3 A) I.down).left) (fun I => j I.down) ↔ _
  rw [le_preimage_wchart]
  simp only [tripleProductPoint_comp_partialSum]
  exact ⟨fun h I => h ⟨I⟩, fun h I => h I.down⟩

private theorem valAt_theta_transition_eq_prod_zpow (hv : ValueRules) {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left}
    {g : ℕ} (u : HolUnif A L₀ g) (L : LB A.left) (j j' : Finset (Fin 3) → L.ι) (x : Fin 3 → Fin g → ℂ)
    (hj : ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j I.down))
    (hj' : ⊤ ≤ (pt3 u x).left ⁻¹ᵁ (Theta A L).U (fun I => j' I.down)) :
    valAt' (pt3 u x).left ((Theta A L).U (fun I => j I.down) ⊓ (Theta A L).U (fun I => j' I.down))
        ((Theta A L).g (fun I => j I.down) (fun I => j' I.down)).val =
      ∏ I : Finset (Fin 3), valAt' (u.ex (∑ a ∈ I, x a)).left (L.U (j I) ⊓ L.U (j' I))
        (L.g (j I) (j' I)).val ^ ((-1 : ℤ) ^ (3 - I.card)) := by
  have e := val_linComb (pt3 u x).left hv L
    (fun I : ULift (Finset (Fin 3)) => (psum A (x3 A) I.down).left)
    (fun I : ULift (Finset (Fin 3)) => (-1 : ℤ) ^ (3 - I.down.card)) (fun I => j I.down) (fun I => j' I.down) hj hj'
  simp only [tripleProductPoint_comp_partialSum] at e
  refine e.trans ?_
  exact Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)

end Points

end GlobalTheory.CubeValues


open GlobalTheory.CubeValues in
theorem GlobalTheory.cube_trivialisation_on_uniformising_space :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) → (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Set E) (X Y : Over (Sp ℂ)) (a : E → (𝟙_ (Over (Sp ℂ)) ⟶ X)) (b : E → (𝟙_ (Over (Sp ℂ)) ⟶ Y)), (∀ (U : (X).left.Opens) (f : Γ((X).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (a w).left U f) {w | w ∈ W ∧ ⊤ ≤ (a w).left ⁻¹ᵁ U}) → (∀ (U : (Y).left.Opens) (f : Γ((Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' (b w).left U f) {w | w ∈ W ∧ ⊤ ≤ (b w).left ⁻¹ᵁ U}) → (∀ (U : (X ⊗ Y).left.Opens) (f : Γ((X ⊗ Y).left, U)), IsOpen {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun w => valAt' ((fun w => lift (a w) (b w)) w).left U f) {w | w ∈ W ∧ ⊤ ≤ ((fun w => lift (a w) (b w)) w).left ⁻¹ᵁ U})) → (∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (L₀ L : LB A.left) (g : ℕ) (u : HolUnif A L₀ g), L.IsLB → ∀ t : LB.Gen (Theta A L), t.IsGen → ∀ (W : L.ι → Set (Fin g → ℂ)) (c : L.ι → L.ι → (Fin g → ℂ) → ℂ), W = (fun (i : L.ι) => {z : Fin g → ℂ | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i}) → c = (fun (i j : L.ι) (z : Fin g → ℂ) => valAt' (u.ex z).left (L.U i ⊓ L.U j) (L.g i j).val) → ((∀ i, IsOpen (W i)) ∧ (∀ z, ∃ i, z ∈ W i) ∧ (∀ i j, DifferentiableOn ℂ (c i j) (W i ∩ W j)) ∧ (∀ i j z, z ∈ W i → z ∈ W j → c i j z ≠ 0) ∧ (∀ i j k z, z ∈ W i → z ∈ W j → z ∈ W k → c i j z * c j k z = c i k z) ∧ (∀ i z, ∀ l ∈ u.Λ, z + l ∈ W i ↔ z ∈ W i) ∧ (∀ i j z, ∀ l ∈ u.Λ, c i j (z + l) = c i j z)) ∧ ∃ T : (Finset (Fin 3) → L.ι) → (Fin 3 → Fin g → ℂ) → ℂ, (∀ j, DifferentiableOn ℂ (T j) {x | (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I))}) ∧ (∀ j x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → T j x ≠ 0) ∧ (∀ j j' x, (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j I)) → (∀ I : Finset (Fin 3), ∑ a ∈ I, x a ∈ W (j' I)) → T j x = (∏ I : Finset (Fin 3), c (j I) (j' I) (∑ a ∈ I, x a) ^ ((-1 : ℤ) ^ (3 - I.card))) * T j' x) ∧ (∀ j x (l : Fin 3 → Fin g → ℂ), (∀ a, l a ∈ u.Λ) → T j (x + l) = T j x)) := by
  intro hv0 hlift A _ _ L₀ L g u hL t ht W c hW hc
  have hv : ValueRules := hv0
  subst hW hc
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact (u.hol (L.U i) 0).1
  · intro z
    have hq : (u.ex z).left (default : PrimeSpectrum ℂ) ∈ ⨆ i, L.U i := by
      rw [hL.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hq
    exact ⟨i, ((hv _ (u.ex z).left).1 (L.U i)).2 hi⟩
  · intro i j
    have hset : ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j}) =
        {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (L.U i ⊓ L.U j)} := by
      ext z
      exact (le_preimage_inf _ _ _).symm
    show DifferentiableOn ℂ (fun z => valAt' (u.ex z).left (L.U i ⊓ L.U j) (L.g i j).val)
      ({z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i} ∩ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U j})
    rw [hset]
    exact (u.hol _ _).2
  · intro i j z hi hj
    exact val_unit_ne_zero _ hv ((le_preimage_inf _ _ _).2 ⟨hi, hj⟩) _
  · intro i j k z hi hj hk
    exact val_cocycle _ hv hL i j k hi hj hk
  · intro i z l hl
    show ⊤ ≤ (u.ex (z + l)).left ⁻¹ᵁ L.U i ↔ ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i
    rw [ex_add_period u z l hl]
  · intro i j z l hl
    show valAt' (u.ex (z + l)).left _ _ = valAt' (u.ex z).left _ _
    rw [ex_add_period u z l hl]
  · have hH := hlift (Fin 3 → Fin g → ℂ) Set.univ A (A ⊗ A) (fun w => u.ex (w 0))
      (fun w => lift (u.ex (w 1)) (u.ex (w 2))) (fun U f => hol_coord u 0 U f)
      (hlift (Fin 3 → Fin g → ℂ) Set.univ A A (fun w => u.ex (w 1)) (fun w => u.ex (w 2))
        (fun U f => hol_coord u 1 U f) (fun U f => hol_coord u 2 U f))
    refine ⟨fun j x => valAt' (pt3 u x).left ((Theta A L).U (fun I => j I.down)) (t.s (fun I => j I.down)).val,
      ?_, ?_, ?_, ?_⟩
    · intro j
      refine ((hH ((Theta A L).U (fun I => j I.down)) (t.s (fun I => j I.down)).val).2).mono ?_
      intro x hx
      exact ⟨trivial, (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx⟩
    · intro j x hx
      exact val_unit_ne_zero _ hv ((GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx) _
    · intro j j' x hx hx'
      have hi := (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j x).2 hx
      have hi' := (GlobalTheory.CubeValues.pt3_preimage_theta_whole_iff u L j' x).2 hx'
      have e := val_gen (pt3 u x).left hv t ht _ _ hi hi'
      rw [GlobalTheory.CubeValues.valAt_theta_transition_eq_prod_zpow hv u L j j' x hi hi'] at e
      exact e
    · intro j x l hl
      show valAt' (pt3 u (x + l)).left _ _ = valAt' (pt3 u x).left _ _
      rw [tripleProductPoint_add_period u x l hl]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.EqZeroOfForallAlgHomComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem eq_zero_of_forall_algHom_complex {A : Type*} [CommRing A] [Algebra ℂ A] [_root_.IsReduced A]
    [Algebra.FiniteType ℂ A] (a : A) (h : ∀ e : A →ₐ[ℂ] ℂ, e a = 0) : a = 0 := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := ℂ)
  have hrad : (⊥ : Ideal A).IsRadical := by
    rw [Ideal.isRadical_bot_iff]; infer_instance
  have hj : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out inferInstance hrad
  rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨-, hm⟩
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  have hb : Function.Bijective (algebraMap ℂ (A ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let i : ℂ ≃ₐ[ℂ] (A ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId ℂ (A ⧸ m)) hb
  have := h ((i.symm : (A ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m))
  rw [AlgHom.comp_apply] at this
  have h2 : Ideal.Quotient.mkₐ ℂ m a = 0 := by
    apply i.symm.injective
    rw [map_zero]; exact this
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem eq_of_valAt'_eq :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) →
    (∀ (X : Over (Sp ℂ)) (U : X.left.Opens), IsAffineOpen U → ∀ e : Γ(X.left, U) →+* ℂ, (∀ a, e (constFn X.hom U a) = a) → ∃! x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U ∧ ∀ f, valAt' x.left U f = e f) →
    (∀ (X : Over (Sp ℂ)), IsReduced X.left → LocallyOfFiniteType X.hom → ∀ (U : X.left.Opens) (f f' : Γ(X.left, U)), (∀ x : (𝟙_ (Over (Sp ℂ)) ⟶ X), ⊤ ≤ (x).left ⁻¹ᵁ U → valAt' x.left U f = valAt' x.left U f') → f = f') := by
  intro hval haff X hred hft U f f' h
  refine TopCat.Sheaf.eq_of_locally_eq' X.left.sheaf
    (fun V : {V : X.left.Opens // IsAffineOpen V ∧ V ≤ U} => V.1) U (fun V => homOfLE V.2.2) ?_ f f' ?_
  · intro p hp
    obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hVU⟩ :=
      X.left.isBasis_affineOpens.exists_subset_of_mem_open hp U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hpV⟩
  · rintro ⟨V, hV, hVU⟩
    change resG X.left hVU f = resG X.left hVU f'
    let c : ℂ →+* Γ(X.left, V) :=
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ V (fun _ _ => trivial)).hom
    have hc : c.FiniteType := by
      have h1 : (X.hom.appLE ⊤ V (fun _ _ => trivial)).hom.FiniteType :=
        HasRingHomProperty.appLE @LocallyOfFiniteType X.hom hft ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
      exact h1.comp (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
    letI : Algebra ℂ Γ(X.left, V) := c.toAlgebra
    haveI : Algebra.FiniteType ℂ Γ(X.left, V) := hc
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_algHom_complex
    intro e
    obtain ⟨x, ⟨hxV, hx⟩, -⟩ := haff X V hV e.toRingHom (fun a => e.commutes a)
    have hres := (hval X.left x.left).2.2.1 U V hVU
    have hxU : ⊤ ≤ x.left ⁻¹ᵁ U := fun p hp => hVU (hxV hp)
    have e1 : e (resG X.left hVU f) = valAt' x.left U f := (hx _).symm.trans (hres f hxV)
    have e2 : e (resG X.left hVU f') = valAt' x.left U f' := (hx _).symm.trans (hres f' hxV)
    rw [map_sub, e1, e2, h x hxU, sub_self]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedTensorObjComplex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem isReduced_tensorObj_complex :
    (∀ (X Y : Over (Sp ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X ⊗ Y).left) := by
  intro X Y hX hY hfX hfY

  have : GeometricallyReduced X.hom :=
    ReducedSubgroup.geometricallyReduced_of_perfectField (k := ℂ) X.hom
  have : Flat X.hom := inferInstance
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  change IsReduced (Limits.pullback X.hom Y.hom)
  infer_instance

end GlobalTheory
end
