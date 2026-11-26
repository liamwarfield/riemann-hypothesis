module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.CrdCalc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def valHom (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valR_eq (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = valHom x U h f := by
  unfold valR
  rw [dite_eq_left h]
  rfl

theorem valR_mul (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

theorem valR_res (x : Sp R ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_eq x V h, valR_eq x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]
  rfl

theorem valR_spMap {R' : Type} [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U ∧ ∀ f, valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun y _ => h (Set.mem_univ ((spMap φ) y))
  refine ⟨h', fun f => ?_⟩
  rw [valR_eq _ U h', valR_eq x U h]
  have e : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom).hom f =
    (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ).hom f
  rw [e, Category.assoc, n]

theorem isUnit_valR_iff (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    IsUnit (valR x U f) ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen f := by
  rw [valR_eq x U h]
  have e : IsUnit (valHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f) :=
    isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv _
  rw [e]
  have b := Scheme.basicOpen_appLE x ⊤ U h f
  constructor
  · intro hu
    rw [Scheme.basicOpen_of_isUnit _ hu] at b
    exact b.le.trans inf_le_right
  · intro hu
    rw [inf_eq_left.2 hu] at b
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => ?_
    exact (Scheme.mem_basicOpen _ _ y hy).1 (b.ge hy)

theorem top_le_iff [IsLocalRing R] (x : Sp R ⟶ X) (U : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint R) ∈ U :=
  ⟨fun h => h (Set.mem_univ _), fun h =>
    ((IsLocalRing.closed_point_mem_iff (R := R) (U := x ⁻¹ᵁ U)).1 h).ge⟩

theorem exists_unit_charts (H : LB X) (x : Sp R ⟶ X) (l l' : H.ι) (h : ⊤ ≤ x ⁻¹ᵁ H.U l)
    (h' : ⊤ ≤ x ⁻¹ᵁ H.U l') :
    ∃ c : Rˣ, ∀ s : H.Sec, valR x (H.U l) (s.f l) = c * valR x (H.U l') (s.f l') := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (H.U l ⊓ H.U l') := fun y hy => ⟨h hy, h' hy⟩
  refine ⟨Units.map (valHom x _ hh).toMonoidHom (H.g l l'), fun s => ?_⟩
  rw [← valR_res x (inf_le_left : H.U l ⊓ H.U l' ≤ H.U l) hh,
    ← valR_res x (inf_le_right : H.U l ⊓ H.U l' ≤ H.U l') hh]
  have := s.compat l l'
  change valR x _ ((X.presheaf.map _).hom _) = _
  rw [this, valR_mul x _ hh, valR_eq x _ hh]
  rfl

variable {H : LB X} {J : Type} {s : J → H.Sec}

theorem crd_exists [IsLocalRing R] (hH : H.IsLB) (s : J → H.Sec) (x : Sp R ⟶ X) : ∃ v, Crd H s x v := by
  have : x (IsLocalRing.closedPoint R) ∈ ⨆ i, H.U i := by rw [hH.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨_, l, 1, (top_le_iff x _).2 hl, fun _ => rfl⟩

theorem crd_unique {x : Sp R ⟶ X} {v v' : J → R} (h : Crd H s x v) (h' : Crd H s x v') :
    ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨l', c', hl', hv'⟩ := h'
  obtain ⟨u, hu⟩ := exists_unit_charts H x l' l hl' hl
  refine ⟨c' * u * c⁻¹, fun j => ?_⟩
  rw [hv, hv', hu, Units.val_mul, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]

theorem crd_isUnit_iff [IsLocalRing R] {x : Sp R ⟶ X} {v : J → R} (j : J) (h : Crd H s x v) :
    IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j) := by
  obtain ⟨l, c, hl, hv⟩ := h
  rw [hv, Units.isUnit_units_mul]
  constructor
  · intro hu
    exact ((isUnit_valR_iff x _ hl _).1 hu).trans
      (x.preimage_mono (le_iSup (fun k => X.basicOpen ((s j).f k)) l))
  · intro hu
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_iff x _).1 hu)
    have hk' := (top_le_iff x _).2 hk
    have hU : ⊤ ≤ x ⁻¹ᵁ H.U k := hk'.trans (x.preimage_mono (X.basicOpen_le _))
    obtain ⟨u, hu⟩ := exists_unit_charts H x l k hl hU
    rw [hu, Units.isUnit_units_mul]
    exact (isUnit_valR_iff x _ hU _).2 hk'

theorem crd_map {R' : Type} [CommRing R'] (φ : R →+* R') {x : Sp R ⟶ X} {v : J → R} (h : Crd H s x v) :
    Crd H s (spMap φ ≫ x) (fun j => φ (v j)) := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨h₁, h₂⟩ := valR_spMap φ x _ hl
  refine ⟨l, Units.map φ.toMonoidHom c, h₁, fun j => ?_⟩
  beta_reduce
  rw [h₂, hv, map_mul]
  rfl

theorem crd_smul {x : Sp R ⟶ X} {v : J → R} (c : Rˣ) (h : Crd H s x v) :
    Crd H s x (fun j => (c : R) * v j) := by
  obtain ⟨l, c', hl, hv⟩ := h
  exact ⟨l, c * c', hl, fun j => by beta_reduce; rw [hv, Units.val_mul, _root_.mul_assoc]⟩

theorem crd_ratio {x : Sp R ⟶ X} {v : J → R} {i j : J} {W : X.Opens} {r : Γ(X, W)} (h : Crd H s x v)
    (hr : IsRatio (s j) (s i) W r) (hW : ⊤ ≤ x ⁻¹ᵁ W) : v j = valR x W r * v i := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ H.U l) := fun y hy => ⟨hW hy, hl hy⟩
  have := congrArg (valR x (W ⊓ H.U l)) (hr l)
  rw [valR_mul x _ hh, valR_res x _ hh, valR_res x _ hh, valR_res x _ hh] at this
  rw [hv, hv, this, mul_left_comm]

theorem crd_calculus : (∀ (X : Scheme.{0}) (H : LB X) (J : Type) (s : J → H.Sec), H.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), (∃ v, Crd H s x v) ∧ (∀ v v', Crd H s x v → Crd H s x v' → ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j) ∧ ∀ v j, Crd H s x v → (IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j))) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (v : J → R), Crd H s x v → Crd H s (spMap φ ≫ x) (fun j => φ (v j))) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (c : Rˣ), Crd H s x v → Crd H s x (fun j => (c : R) * v j)) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (i j : J) (W : X.Opens) (r : Γ(X, W)), Crd H s x v → IsRatio (s j) (s i) W r → ⊤ ≤ x ⁻¹ᵁ W → v j = valR x W r * v i) :=
  fun _ _ _ s hH =>
    ⟨fun _ _ _ x => ⟨crd_exists hH s x, fun _ _ => crd_unique, fun _ j => crd_isUnit_iff j⟩,
      fun _ _ _ _ φ _ _ => crd_map φ, fun _ _ _ _ c => crd_smul c, fun _ _ _ _ _ _ _ _ => crd_ratio⟩

end GlobalTheory.ZH.CrdCalc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.SecRatio

private theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    resG X h₂ (resG X h₁ s) = resG X (h₂.trans h₁) s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

private theorem res_const {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {U V : X.Opens}
    (e : U ≤ V) (a : R) : resG X e (constFn p V a) = constFn p U a := by
  unfold constFn
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
  erw [Scheme.Hom.appLE_map]

variable {X : Scheme.{0}} {H : LB X}

theorem compat_res (s : H.Sec) (i j : H.ι) {V : X.Opens} (hi : V ≤ H.U i) (hj : V ≤ H.U j) :
    resG X hi (s.f i) = resG X (le_inf hi hj) (H.g i j : Γ(X, H.U i ⊓ H.U j)) * resG X hj (s.f j) := by
  have := congrArg (resG X (le_inf hi hj)) (s.compat i j)
  rw [map_mul] at this
  erw [rr, rr] at this
  exact this

theorem isUnit_res (t : H.Sec) (l : H.ι) {V : X.Opens} (hV : V ≤ Out.nonzeroLocus t)
    (hl : V ≤ H.U l) : IsUnit (resG X hl (t.f l)) := by
  have hle : V ≤ X.basicOpen (t.f l) := by
    intro x hx
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hV hx)
    have hk' : x ∈ H.U k := X.basicOpen_le _ hk
    have h1 : x ∈ X.basicOpen (resG X (inf_le_left : H.U k ⊓ H.U l ≤ H.U k) (t.f k)) := by
      erw [Scheme.basicOpen_res]
      exact ⟨⟨hk', hl hx⟩, hk⟩
    rw [compat_res t k l inf_le_left inf_le_right, Scheme.basicOpen_mul] at h1
    have h2 := h1.2
    erw [Scheme.basicOpen_res] at h2
    exact h2.2
  have hu : IsUnit (resG X (X.basicOpen_le (t.f l)) (t.f l)) :=
    X.toRingedSpace.isUnit_res_basicOpen (t.f l)
  have := hu.map (resG X hle)
  rwa [rr] at this

theorem existsUnique_isRatio (hH : H.IsLB) (s t : H.Sec) (W : X.Opens)
    (hW : W ≤ Out.nonzeroLocus t) : ∃! r : Γ(X, W), IsRatio s t W r := by
  have hu : ∀ l, IsUnit (resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l)) :=
    fun l => isUnit_res t l (inf_le_left.trans hW) _
  have hq : ∀ l, ∃ q : Γ(X, W ⊓ H.U l), resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) =
      q * resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (t.f l) := fun l =>
    ⟨resG X (inf_le_right : W ⊓ H.U l ≤ H.U l) (s.f l) * ↑(hu l).unit⁻¹, by
      rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]⟩
  choose q hq using hq
  have hcov : W ≤ ⨆ l, W ⊓ H.U l := by
    rw [← inf_iSup_eq, hH.cover, inf_top_eq]
  have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun l => W ⊓ H.U l) q := by
    intro i j
    change resG X (inf_le_left : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U i) (q i) =
      resG X (inf_le_right : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U j) (q j)
    have hi : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ H.U i := inf_le_left.trans inf_le_right
    have hj : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ H.U j := inf_le_right.trans inf_le_right
    have e1 := congrArg (resG X (inf_le_left : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U i)) (hq i)
    have e2 := congrArg (resG X (inf_le_right : W ⊓ H.U i ⊓ (W ⊓ H.U j) ≤ W ⊓ H.U j)) (hq j)
    rw [map_mul, rr, rr] at e1 e2
    have u := isUnit_res t i ((inf_le_left.trans inf_le_left).trans hW) hi
    apply u.mul_right_cancel
    rw [← e1, compat_res s i j hi hj, compat_res t i j hi hj, e2]
    ring
  obtain ⟨r, hr, hr'⟩ := X.sheaf.existsUnique_gluing' (fun l => W ⊓ H.U l) W
    (fun l => homOfLE inf_le_left) hcov q hcomp
  refine ⟨r, fun l => ?_, fun r' h' => hr' r' fun l => ?_⟩
  · have : resG X (inf_le_left : W ⊓ H.U l ≤ W) r = q l := hr l
    rw [this]; exact hq l
  · change resG X (inf_le_left : W ⊓ H.U l ≤ W) r' = q l
    apply (hu l).mul_right_cancel
    rw [← hq l]; exact (h' l).symm

theorem existsUnique_isLin {k : Type} [CommRing k] (p : X ⟶ Sp k) {J : Type} [Fintype J]
    (s : J → H.Sec) (a : J → k) : ∃! φ : H.Sec, IsLin p s a φ := by
  refine ⟨⟨fun l => ∑ j, constFn p (H.U l) (a j) * (s j).f l, fun i j => ?_⟩, fun l => rfl, ?_⟩
  · change resG X inf_le_left _ = _ * resG X inf_le_right _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_mul, res_const, res_const]
    have : resG X inf_le_left _ = _ * resG X inf_le_right _ := (s n).compat i j
    rw [this]; ring
  · rintro ⟨f, hf⟩ h
    have : f = _ := funext h
    subst this
    rfl

theorem ratio_and_lin : (∀ (X : Scheme.{0}) (H : LB X), H.IsLB → (∀ (s t : H.Sec) (W : X.Opens), W ≤ Out.nonzeroLocus t → ∃! r : Γ(X, W), IsRatio s t W r) ∧ ∀ (k : Type) [CommRing k] (p : X ⟶ Sp k) (J : Type) [Fintype J] (s : J → H.Sec) (a : J → k), ∃! φ : H.Sec, IsLin p s a φ) :=
  fun _ _ hH => ⟨existsUnique_isRatio hH, fun _ _ p _ _ s a => existsUnique_isLin p s a⟩

end GlobalTheory.SecRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace SemiAbTorsion

theorem finite_pow_eq_one_of_extension {T G B : Type*} [Group T] [CommGroup G] [Group B]
    (i : T →* G) (q : G →* B) (hi : Function.Injective i) (hk : ∀ x, q x = 1 → ∃ t, i t = x)
    (n : ℕ) (hT : Finite {t : T // t ^ n = 1}) (hB : Finite {b : B // b ^ n = 1}) :
    Finite {x : G // x ^ n = 1} := by
  let f : {x : G // x ^ n = 1} → {b : B // b ^ n = 1} :=
    fun x => ⟨q x.1, by rw [← map_pow, x.2, map_one]⟩
  refine Set.finite_univ_iff.mp (Set.Finite.of_finite_fibers f (Set.toFinite _) fun b hb => ?_)
  obtain ⟨x₀, -, rfl⟩ := hb
  rw [Set.univ_inter, ← Set.finite_coe_iff]
  have key : ∀ x : f ⁻¹' {f x₀}, ∃ t : {t : T // t ^ n = 1}, i t.1 = x.1.1 / x₀.1 := by
    intro x
    have hx : q x.1.1 = q x₀.1 := congrArg Subtype.val x.2
    obtain ⟨t, ht⟩ := hk (x.1.1 / x₀.1) (by rw [map_div, hx, div_self'])
    refine ⟨⟨t, hi ?_⟩, ht⟩
    rw [map_pow, ht, div_pow, x.1.2, x₀.2, map_one, div_one]
  choose g hg using key
  refine Finite.of_injective g fun x y h => Subtype.ext (Subtype.ext ?_)
  have := hg x
  rw [h, hg y] at this
  exact (div_left_inj.mp this).symm

theorem finite_chars_pow_eq_one (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (R : Type)
    [CommRing R] [IsDomain R] {n : ℕ} (hn : 1 ≤ n) :
    Finite {t : Multiplicative X →* Rˣ // t ^ n = 1} := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  obtain ⟨S, hS, hfin⟩ := (Group.fg_iff.mp (inferInstance : Group.FG (Multiplicative X)))
  haveI : Finite S := hfin.to_subtype
  let g : {t : Multiplicative X →* Rˣ // t ^ n = 1} → (S → rootsOfUnity n R) := fun t s =>
    ⟨t.1 s.1, (mem_rootsOfUnity _ _).2 (by simpa using DFunLike.congr_fun t.2 s.1)⟩
  refine Finite.of_injective g fun a b h => Subtype.ext ?_
  refine MonoidHom.eq_of_eqOn_dense hS fun s hs => ?_
  exact congrArg Subtype.val (congrFun h ⟨s, hs⟩)

theorem finite_ringHom (A F : Type) [CommRing A] [CommRing F] [Finite F]
    [Algebra.FiniteType ℤ A] : Finite (A →+* F) := by
  obtain ⟨S, hS⟩ := (inferInstance : Algebra.FiniteType ℤ A).out
  refine Finite.of_injective (fun (φ : A →+* F) (s : S) => φ s.1) fun a b h => ?_
  have : a.toIntAlgHom = b.toIntAlgHom :=
    AlgHom.ext_of_adjoin_eq_top hS fun s hs => congrFun h ⟨s, hs⟩
  ext x
  exact DFunLike.congr_fun this x

theorem finite_hom_range_subset {X : Scheme.{0}} (π : X ⟶ Sp ℤ) [LocallyOfFiniteType π]
    (F : CommRingCat.{0}) [Finite F] (V : X.Opens) (hV : IsAffineOpen V) :
    {f : Spec F ⟶ X | Set.range f ⊆ V}.Finite := by
  have h : LocallyOfFiniteType (hV.fromSpec ≫ π) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV.fromSpec ≫ π)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have e : φ.hom = algebraMap ℤ Γ(X, V) := RingHom.ext_int _ _
  have h' : (algebraMap ℤ Γ(X, V)).FiniteType := e ▸ h
  have : Algebra.FiniteType ℤ Γ(X, V) := RingHom.finiteType_algebraMap.mp h'
  haveI := finite_ringHom Γ(X, V) F
  refine (Set.finite_range fun ψ : Γ(X, V) →+* F =>
    Spec.map (CommRingCat.ofHom ψ) ≫ hV.fromSpec).subset fun f hf => ?_
  have hf' : Set.range f ⊆ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hf
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec f hf')
  refine ⟨ψ.hom, ?_⟩
  change Spec.map ψ ≫ _ = _
  rw [hψ, IsOpenImmersion.lift_fac]

theorem finite_points_over {Z : Scheme.{0}} (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z)
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (F : Type) [Field F] [Finite F]
    (t : Sp F ⟶ Z) : Finite (Over.mk t ⟶ G) := by
  let pt : Sp F := default
  have hpt : ∀ y : Sp F, y = pt := fun y => Subsingleton.elim _ _
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (t pt)) isOpen_univ
  have hc : IsCompact (G.hom ⁻¹ᵁ U : Set G.left) :=
    QuasiCompact.isCompact_preimage (f := G.hom) _ U.isOpen hU.isCompact
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens).mp hc
  have hfin : (⋃ V ∈ s, {f : Sp F ⟶ G.left | Set.range f ⊆ V.1}).Finite :=
    hs.biUnion fun V _ => finite_hom_range_subset (G.hom ≫ π) (CommRingCat.of F) V.1 V.2
  haveI := hfin.to_subtype
  have hm : ∀ x : Over.mk t ⟶ G,
      x.left ∈ ⋃ V ∈ s, {f : Sp F ⟶ G.left | Set.range f ⊆ V.1} := by
    intro x
    have h1 : x.left pt ∈ G.hom ⁻¹ᵁ U := by
      change (x.left ≫ G.hom) pt ∈ U
      rw [Over.w x]
      exact hxU
    rw [hsU] at h1
    simp only [TopologicalSpace.Opens.mem_iSup] at h1
    obtain ⟨V, hV, hx⟩ := h1
    refine Set.mem_biUnion hV ?_
    rintro _ ⟨y, rfl⟩
    rw [hpt y]
    exact hx
  exact Finite.of_injective (fun x => (⟨x.left, hm x⟩ : (⋃ V ∈ s,
    {f : Sp F ⟶ G.left | Set.range f ⊆ V.1} : Set _)))
    fun a b h => Over.OverMorphism.ext (congrArg Subtype.val h)

theorem comp_pow_points {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (g : T ⟶ A)
    (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

end SemiAbTorsion

open SemiAbTorsion

theorem semiAbelian_torsion_finite_and_closedPoint_finiteOrder : (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → (∀ (K : Type) [Field K] [IsAlgClosed K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension G) → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ G // x ^ n = 1}) ∧ (∀ (Z : Scheme.{0}) (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (G : Over Z) [GrpObj G] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom] (w : G.left), IsClosed ({w} : Set G.left) → ∃ n : ℕ, 1 ≤ n ∧ ∀ (K : Type) [Field K] (t : Sp K ⟶ Z) (x : Over.mk t ⟶ G), Set.range x.left = {w} → x ^ n = 1) := by
  intro hB
  refine ⟨?_, ?_⟩
  · rintro K _ _ G _ _ ⟨E⟩ n hn
    letI := E.addCommGroup
    letI := E.finite
    letI := E.grpB
    haveI := E.q_hom
    haveI := E.i_hom
    have hk := E.isKernel
    refine finite_pow_eq_one_of_extension (IsMonHom.monoidHom E.i (𝟙_ (Over (Sp K))))
      (IsMonHom.monoidHom E.q (𝟙_ (Over (Sp K)))) ?_ ?_ n ?_ (hB K E.B E.isAbelian n hn)
    · intro a b h
      exact hk.hom_ext h (toUnit_unique _ _)
    · intro x hx
      have hx' : x ≫ E.q = 1 := hx
      exact ⟨hk.lift x (toUnit _) (by rw [hx', Hom.one_def]), hk.lift_fst _ _ _⟩
    · haveI : IsDomain Γ((𝟙_ (Over (Sp K))).left, ⊤) :=
        inferInstanceAs (IsDomain Γ(Sp K, ⊤))
      haveI := finite_chars_pow_eq_one E.X Γ((𝟙_ (Over (Sp K))).left, ⊤) hn
      let e := splitTorusPointsEquiv (Sp K) E.X (𝟙_ (Over (Sp K)))
      refine Finite.of_injective (fun t => (⟨e t.1, by rw [← map_pow, t.2, map_one]⟩ :
        {t : Multiplicative E.X →* Γ((𝟙_ (Over (Sp K))).left, ⊤)ˣ // t ^ n = 1})) ?_
      intro a b h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
  · intro Z π _ G _ _ _ w hw
    haveI : Finite (G.left.residueField w) :=
      (jacobson_closedPoints_tools_int G.left (G.hom ≫ π)).2.1 w hw
    let t₀ : Sp (G.left.residueField w) ⟶ Z := G.left.fromSpecResidueField w ≫ G.hom
    haveI := finite_points_over π G (G.left.residueField w) t₀
    let x₀ : Over.mk t₀ ⟶ G := Over.homMk (G.left.fromSpecResidueField w) rfl
    refine ⟨Nat.card (Over.mk t₀ ⟶ G), Nat.card_pos, fun K _ t x hx => ?_⟩
    obtain ⟨⟨z, φ⟩, hz⟩ := (Scheme.SpecToEquivOfField K G.left).symm.surjective x.left
    simp only [Scheme.SpecToEquivOfField_symm_apply] at hz
    obtain rfl : z = w := by
      have : x.left (default : Sp K) ∈ ({w} : Set G.left) := hx ▸ Set.mem_range_self _
      rw [← hz] at this
      have h2 : (Spec.map φ ≫ G.left.fromSpecResidueField z) (default : Sp K) ∈
          Set.range (G.left.fromSpecResidueField z) := ⟨_, rfl⟩
      rw [Scheme.range_fromSpecResidueField] at h2
      exact h2.symm.trans this
    let u : Over.mk t ⟶ Over.mk t₀ := Over.homMk (Spec.map φ) (by
      change Spec.map φ ≫ G.left.fromSpecResidueField z ≫ G.hom = t
      rw [← Category.assoc, hz]
      exact Over.w x)
    have hu : x = u ≫ x₀ := Over.OverMorphism.ext hz.symm
    rw [hu, ← comp_pow_points, pow_card_eq_one', MonObj.comp_one]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPartPartSec
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.WtPart

section Alg
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))

def cf (χ : X) (s : R) : A := ((Equiv.ofBijective _ hb).symm s).coeff χ

theorem cf_apply (χ : X) (a : AddMonoidAlgebra A X) :
    cf hb χ (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _) a) = a.coeff χ :=
  congrArg (fun a : AddMonoidAlgebra A X => a.coeff χ) ((Equiv.ofBijective _ hb).symm_apply_apply a)

theorem cf_zero (χ : X) : cf hb χ 0 = 0 := by
  have := cf_apply hb χ 0
  rwa [map_zero] at this

theorem cf_add (χ : X) (s t : R) : cf hb χ (s + t) = cf hb χ s + cf hb χ t := by
  obtain ⟨a, rfl⟩ := hb.2 s
  obtain ⟨b, rfl⟩ := hb.2 t
  rw [← map_add (f := _), cf_apply, cf_apply, cf_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem cf_sum {K : Type} (χ : X) (T : Finset K) (s : K → R) :
    cf hb χ (∑ i ∈ T, s i) = ∑ i ∈ T, cf hb χ (s i) :=
  map_sum (AddMonoidHom.mk' (cf hb χ) (cf_add hb χ)) s T

open Classical in
theorem cf_mono (χ ψ : X) (b : A) :
    cf hb χ (f b * m (Multiplicative.ofAdd ψ)) = if ψ = χ then b else 0 := by
  rw [← AddMonoidAlgebra.liftNCRingHom_single f m (fun _ _ => Commute.all _ _), cf_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem cf_ext {s t : R} (h : ∀ χ, cf hb χ s = cf hb χ t) : s = t :=
  (Equiv.ofBijective _ hb).symm.injective (AddMonoidAlgebra.ext (Finsupp.ext h))

theorem cf_finite (s : R) : {χ | cf hb χ s ≠ 0}.Finite :=
  ((Equiv.ofBijective _ hb).symm s).coeff.support.finite_toSet.subset
    fun _ h => Finsupp.mem_support_iff.2 h

def part (χ : X) (s : R) : R := f (cf hb χ s) * m (Multiplicative.ofAdd χ)

theorem part_eq_zero {χ : X} {s : R} (h : cf hb χ s = 0) : part hb χ s = 0 := by
  rw [part, h, map_zero, zero_mul]

open Classical in
theorem part_mono (χ ψ : X) (b : A) :
    part hb χ (f b * m (Multiplicative.ofAdd ψ)) =
      if ψ = χ then f b * m (Multiplicative.ofAdd ψ) else 0 := by
  rw [part, cf_mono]
  split_ifs with h
  · rw [h]
  · rw [map_zero, zero_mul]

theorem part_map {A' R' : Type} [CommRing A'] [CommRing R'] {f' : A' →+* R'}
    {m' : Multiplicative X →* R'}
    (hb' : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f' m' (fun _ _ => Commute.all _ _)))
    (σ : R →+ R')
    (hσ : ∀ b ψ, ∃ b', σ (f b * m (Multiplicative.ofAdd ψ)) = f' b' * m' (Multiplicative.ofAdd ψ))
    (χ : X) (s : R) : σ (part hb χ s) = part hb' χ (σ s) := by
  obtain ⟨a, rfl⟩ := hb.2 s
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp only [map_zero, part, cf_zero, zero_mul]
  | add x y hx hy =>
    simp only [part] at hx hy
    simp only [map_add (f := _), part, cf_add, add_mul, hx, hy]
  | single ψ b =>
    obtain ⟨b', e⟩ := hσ b ψ
    rw [AddMonoidAlgebra.liftNCRingHom_single, e, part_mono, part_mono]
    split_ifs
    · exact e
    · exact map_zero σ

theorem constr_rel {K M M' N : Type} [CommGroup M] [CommGroup M'] [CommGroup N]
    (b : Module.Basis K ℤ X) (u : K → M) (u' : K → M') (c : K → N) (σ : M →* M') (τ : N →* M')
    (h : ∀ k, σ (u k) = τ (c k) * u' k) (ψ : X) :
    σ (Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (u k)) ψ)) =
      τ (Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (c k)) ψ)) *
        Additive.toMul (b.constr ℤ (fun k => Additive.ofMul (u' k)) ψ) := by
  simp only [Module.Basis.constr_apply, Finsupp.sum, toMul_sum, toMul_zsmul, toMul_ofMul, map_prod,
    map_zpow, h, mul_zpow, Finset.prod_mul_distrib]

end Alg

theorem rr {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem rapp {X Y : Scheme.{0}} (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    resG Y (q.preimage_mono h) ((q.app U).hom a) = (q.app V).hom (resG X h a) := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    q.naturality]
  rfl

section Datum
variable {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G] (D : E.GtDatum G)

abbrev mono (j : E.ChartIdx) (V : E.B.left.Opens) (h : V ≤ E.chart j) :
    Multiplicative E.X →* Γ(G.left, D.q.left ⁻¹ᵁ V) :=
  (Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
    (E.basis.constr ℤ (fun k => Additive.ofMul
      (res (Scheme.Hom.preimage_mono D.q.left h) (D.u j k)))).toAddMonoidHom)

theorem res_mono {j j' : E.ChartIdx} {V W : E.B.left.Opens} (hV : V ≤ E.chart j')
    (hW : W ≤ E.chart j) (h : W ≤ V) (ψ : E.X) :
    ∃ c : Γ(E.B.left, W), resG _ (D.q.left.preimage_mono h) (mono D j' V hV (Multiplicative.ofAdd ψ)) =
      (D.q.left.app W).hom c * mono D j W hW (Multiplicative.ofAdd ψ) := by
  have hW' : W ≤ E.chart j ⊓ E.chart j' := le_inf hW (h.trans hV)
  refine ⟨_, congrArg Units.val (constr_rel E.basis
    (fun k => res (Scheme.Hom.preimage_mono D.q.left hV) (D.u j' k))
    (fun k => res (Scheme.Hom.preimage_mono D.q.left hW) (D.u j k))
    (fun k => res hW' (res (le_inf (inf_le_left.trans (E.chart_le j k))
      (inf_le_right.trans (E.chart_le j' k))) ((E.O (E.basis k)).L.g (j k) (j' k))))
    (res (D.q.left.preimage_mono h)) (pullU D.q.left W) (fun k => Units.ext ?_) ψ)⟩
  have e := congrArg (resG _ (D.q.left.preimage_mono hW')) (congrArg Units.val (D.trans j j' k))
  rw [Units.val_mul, map_mul] at e
  exact (rr _ _ _).trans ((rr _ _ _).symm.trans (e.trans (congrArg₂ (· * ·) (rapp _ _ _) (rr _ _ _))))

end Datum

variable {k : Type} [Field k] (Φ : FibPre k) {d : ℕ}

def partSec (φ : (Φ.H d).Sec) (α : Φ.E.X) : (Φ.H d).Sec where
  f l := part (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l)
  compat l l' := by
    let q := Φ.D.q.left
    let I := {W : Φ.E.B.left.affineOpens // W.1 ≤ Φ.N₀.U l ⊓ Φ.N₀.U l'}
    refine Φ.G.left.sheaf.eq_of_locally_eq' (fun W : I => q ⁻¹ᵁ W.1.1) _
      (fun W => homOfLE (q.preimage_mono W.2)) (fun x hx => ?_) _ _ fun W => ?_
    · obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (X := Φ.E.B.left) (x := q x)
        (U := Φ.N₀.U l ⊓ Φ.N₀.U l') hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hle⟩, hxW⟩
    have h₁ : W.1.1 ≤ Φ.N₀.U l := W.2.trans inf_le_left
    have h₂ : W.1.1 ≤ Φ.N₀.U l' := W.2.trans inf_le_right
    have hW : W.1.1 ≤ Φ.E.chart (Φ.ch l) := h₁.trans (Φ.le l)
    let w : Γ(Φ.E.B.left, W.1.1) := resG _ W.2 (Φ.N₀.g l l').1 ^ d
    have hw : resG _ (q.preimage_mono W.2) ((Φ.H d).g l l').1 = (q.app W.1.1).hom w := by
      change resG _ (q.preimage_mono W.2) (((pullU q _ (Φ.N₀.g l l')) ^ d).1) = _
      rw [Units.val_pow_eq_pow_val, map_pow, map_pow]
      exact congrArg (· ^ d) (rapp _ _ _)
    have e₁ := part_map (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l))
      (Φ.D.coord (Φ.ch l) W.1.1 W.1.2 hW) (resG _ (q.preimage_mono h₁)).toAddMonoidHom
      (fun b ψ => by
        obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l) hW h₁ ψ
        refine ⟨resG _ h₁ b * c, (map_mul (resG _ (q.preimage_mono h₁)) _ _).trans ?_⟩
        rw [hc, rapp, map_mul, _root_.mul_assoc]) α (φ.f l)
    have e₂ := part_map (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l'))
      (Φ.D.coord (Φ.ch l) W.1.1 W.1.2 hW)
      ((AddMonoidHom.mulLeft ((q.app W.1.1).hom w)).comp (resG _ (q.preimage_mono h₂)).toAddMonoidHom)
      (fun b ψ => by
        obtain ⟨c, hc⟩ := res_mono Φ.D (Φ.le l') hW h₂ ψ
        refine ⟨w * (resG _ h₂ b * c), (congrArg (_ * ·)
          (map_mul (resG _ (q.preimage_mono h₂)) _ _)).trans ?_⟩
        rw [hc, rapp, map_mul, map_mul, _root_.mul_assoc, _root_.mul_assoc]) α (φ.f l')
    have e₃ := congrArg (resG _ (q.preimage_mono W.2)) (φ.compat l l')
    have e₄ : resG _ (q.preimage_mono h₁) (φ.f l) =
        (q.app W.1.1).hom w * resG _ (q.preimage_mono h₂) (φ.f l') :=
      (rr _ _ _).symm.trans (e₃.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) hw (rr _ _ _))))
    refine (rr _ _ _).trans (e₁.trans ((congrArg _ e₄).trans (e₂.symm.trans ?_)))
    exact ((map_mul (resG _ (q.preimage_mono W.2)) _ _).trans (congrArg₂ (· * ·) hw (rr _ _ _))).symm

open Classical in
theorem wt_partSec (φ : (Φ.H d).Sec) (α β : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.wt (partSec Φ φ α) β l = if α = β then Φ.wt φ α l else 0 :=
  cf_mono (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β α _

theorem isPart_partSec (φ : (Φ.H d).Sec) (α : Φ.E.X) : Φ.IsPart α φ (partSec Φ φ α) := by
  refine ⟨?_, fun l => by rw [wt_partSec, if_pos rfl]⟩
  rintro β ⟨l, hl⟩
  by_contra h
  exact hl (by rw [wt_partSec, if_neg (fun e => h e.symm)])

theorem supp_finite (φ : (Φ.H d).Sec) : (Φ.supp φ).Finite := by
  have := Φ.E.isAbelian.proper
  have : CompactSpace Φ.E.B.left := QuasiCompact.compactSpace_of_compactSpace Φ.E.B.hom
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun l => (Φ.N₀.U l : Set Φ.E.B.left))
    (fun l => (Φ.N₀.U l).isOpen) (fun x _ => Set.mem_iUnion.2
      (TopologicalSpace.Opens.mem_iSup.1 (Φ.isLB.cover.ge (show x ∈ ⊤ from trivial))))
  refine (T.finite_toSet.biUnion fun l _ =>
    cf_finite (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (φ.f l)).subset ?_
  rintro α ⟨l', hl'⟩
  by_contra hn
  have h0 : ∀ l ∈ T, (partSec Φ φ α).f l = 0 := fun l hl => by
    have : cf (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) α (φ.f l) = 0 := by
      by_contra h
      exact hn (Set.mem_biUnion hl h)
    exact part_eq_zero _ this
  have h1 : (partSec Φ φ α).f l' = 0 := by
    refine Φ.G.left.sheaf.eq_of_locally_eq' (fun l : T => (Φ.H d).U l' ⊓ (Φ.H d).U l.1) _
      (fun l => homOfLE inf_le_left) (fun x hx => ?_) _ _ fun l => ?_
    · obtain ⟨l, hl, hx'⟩ := Set.mem_iUnion₂.1 (hT (Set.mem_univ (Φ.D.q.left x)))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨l, hl⟩, hx, hx'⟩
    · refine ((partSec Φ φ α).compat l' l.1).trans ?_
      rw [h0 l.1 l.2, map_zero, mul_zero]
      exact (map_zero (resG _ _)).symm
  apply hl'
  rw [← (isPart_partSec Φ φ α).2 l', FibPre.wt, h1]
  exact cf_zero (Φ.D.coord (Φ.ch l') (Φ.N₀.U l') (Φ.aff l') (Φ.le l')) α

theorem sec_ext (φ ψ : (Φ.H d).Sec) (h : ∀ α l, Φ.wt φ α l = Φ.wt ψ α l) : φ = ψ := by
  have : φ.f = ψ.f := funext fun l =>
    cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun α => h α l
  cases φ
  cases ψ
  congr

theorem eq_sum_parts (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec)
    (hA : Φ.supp φ ⊆ A) (hψ : ∀ α ∈ A, Φ.IsPart α φ (ψ α)) (l : Φ.N₀.ι) :
    φ.f l = ∑ α ∈ A, (ψ α).f l := by
  refine cf_ext (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) fun β => Eq.symm ?_
  refine (cf_sum (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) β A _).trans ?_
  change ∑ α ∈ A, Φ.wt (ψ α) β l = Φ.wt φ β l
  have h0 : ∀ α ∈ A, α ≠ β → Φ.wt (ψ α) β l = 0 := fun α hα hne => by
    by_contra h
    exact hne ((hψ α hα).1 ⟨l, h⟩).symm
  by_cases hβ : β ∈ A
  · rw [Finset.sum_eq_single_of_mem β hβ h0, (hψ β hβ).2 l]
  · rw [Finset.sum_eq_zero fun α hα => h0 α hα fun e => hβ (e ▸ hα)]
    by_contra h
    exact hβ (hA ⟨l, fun e => h e.symm⟩)

theorem weight_parts : (∀ (k : Type) [Field k] (Φ : FibPre k) (d : ℕ), (∀ (φ : (Φ.H d).Sec) (α : Φ.E.X), ∃ ψ, Φ.IsPart α φ ψ) ∧ (∀ φ : (Φ.H d).Sec, (Φ.supp φ).Finite) ∧ (∀ φ ψ : (Φ.H d).Sec, (∀ α l, Φ.wt φ α l = Φ.wt ψ α l) → φ = ψ) ∧ ∀ (φ : (Φ.H d).Sec) (A : Finset Φ.E.X) (ψ : Φ.E.X → (Φ.H d).Sec), Φ.supp φ ⊆ A → (∀ α ∈ A, Φ.IsPart α φ (ψ α)) → ∀ l, φ.f l = ∑ α ∈ A, (ψ α).f l) :=
  fun _ _ Φ _ => ⟨fun φ α => ⟨_, isPart_partSec Φ φ α⟩, supp_finite Φ, sec_ext Φ, eq_sum_parts Φ⟩

end GlobalTheory.ZH.WtPart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffSymmSum
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.WtLin

theorem coeff_symm_sum {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) {J : Type} [Fintype J]
    (c : J → A) (s : J → B) (χ : X) :
    ((Equiv.ofBijective _ hb).symm (∑ i, f (c i) * s i)).coeff χ =
      ∑ i, c i * ((Equiv.ofBijective _ hb).symm (s i)).coeff χ := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm _).coeff χ = ∑ i, c i * (e.symm (s i)).coeff χ
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, h1]

theorem app_constFn {R : Type} [CommRing R] {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X)
    (hf : f ≫ q = q') (U : X.Opens) (a : R) :
    (f.app U).hom (constFn q U a) = constFn q' (f ⁻¹ᵁ U) a := by
  subst hf
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U _ (fun _ _ => trivial) le_rfl)

theorem weight_sum {k : Type} [Field k] (Φ : FibPre k) {d : ℕ} {J : Type} [Fintype J]
    (F : J → (Φ.H d).Sec) (a : J → k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α
        (∑ i, constFn Φ.G.hom ((Φ.H d).U l) (a i) * (F i).f l : Γ(Φ.G.left, (Φ.H d).U l)) =
      ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  refine Eq.trans ?_ (coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l))
    (fun i => constFn Φ.E.B.hom _ (a i)) (fun i => (F i).f l) α)
  simp only [app_constFn _ _ _ (Over.w Φ.D.q)]
  rfl

theorem weight_zero {k : Type} [Field k] (Φ : FibPre k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α 0 = 0 := by
  have := coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) (J := Empty)
    Empty.elim Empty.elim α
  simpa [SplitExt.GtDatum.weight] using this

theorem linIndep : (∀ (k : Type) [Field k] (Φ : FibPre k) (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec), Φ.Good N q cls F → ∀ a : J → k, (∀ l, ∑ i, constFn Φ.G.hom ((Φ.H 1).U l) (a i) * (F i).f l = 0) → a = 0) := by
  intro k _ Φ N q J _ cls F hG a ha
  classical
  funext i₀
  have key := hG.inj (cls i₀) (hG.short i₀)
    (fun i => if ∃ m, cls i₀ = cls i + N • m then a i else 0)
    (fun i hi => by
      by_contra h
      exact hi (if_neg h))
    (fun l => by
      have h := weight_sum Φ F a (cls i₀) l
      rw [ha l] at h
      refine Eq.trans ?_ (h.symm.trans (weight_zero Φ _ l))
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · have h0 : Φ.wt (F i) (cls i₀) l = 0 := by
          by_contra hne
          exact hi (hG.supp i _ ⟨l, hne⟩).2
        rw [h0, mul_zero, mul_zero])
  have := congrFun key i₀
  rwa [if_pos ⟨0, by simp⟩] at this

end GlobalTheory.ZH.WtLin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfWeightEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem weight_app {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) (χ : E.X) (a : Γ(E.B.left, V)) :
    D.weight j V hV h χ ((D.q.left.app V).hom a) = (Finsupp.single (0 : E.X) a) χ := by
  have e : (Equiv.ofBijective _ (D.coord j V hV h)).symm ((D.q.left.app V).hom a) =
      AddMonoidAlgebra.single 0 a := by
    rw [Equiv.symm_apply_eq, Equiv.ofBijective_apply]
    simp [AddMonoidAlgebra.liftNCRingHom]
  unfold SplitExt.GtDatum.weight
  rw [e, AddMonoidAlgebra.coeff_single]

theorem eq_of_weight_eq {S : Scheme.{0}} {E : SplitExt S} {G : Over S} [GrpObj G]
    (D : E.GtDatum G) (j : E.ChartIdx) (V : E.B.left.Opens) (hV : IsAffineOpen V)
    (h : V ≤ E.chart j) {s s' : Γ(G.left, D.q.left ⁻¹ᵁ V)}
    (e : ∀ χ, D.weight j V hV h χ s = D.weight j V hV h χ s') : s = s' := by
  apply (Equiv.ofBijective _ (D.coord j V hV h)).symm.injective
  apply AddMonoidAlgebra.ext
  ext χ
  exact e χ

theorem app_res {X Y : Scheme.{0}} (q : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : q ⁻¹ᵁ V ≤ q ⁻¹ᵁ U)
    (a : Γ(X, U)) :
    (q.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (Y.presheaf.map (homOfLE h').op).hom ((q.app U).hom a) := by
  have := q.naturality (homOfLE h).op
  exact congrArg (fun f => f.hom a) this

theorem FibPre.compat_iff {k : Type} [Field k] (Φ : FibPre k) (t : ∀ l, Γ(Φ.E.B.left, Φ.N₀.U l))
    (i j : Φ.N₀.ι) :
    ((Φ.G.left.presheaf.map (homOfLE (inf_le_left : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U i)).op).hom
        ((Φ.D.q.left.app (Φ.N₀.U i)).hom (t i)) =
      ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) *
        (Φ.G.left.presheaf.map (homOfLE (inf_le_right : (Φ.H 1).U i ⊓ (Φ.H 1).U j ≤ (Φ.H 1).U j)).op).hom
          ((Φ.D.q.left.app (Φ.N₀.U j)).hom (t j))) ↔
    (Φ.E.B.left.presheaf.map (homOfLE (inf_le_left : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U i)).op).hom (t i) =
      (Φ.N₀.g i j : Γ(Φ.E.B.left, Φ.N₀.U i ⊓ Φ.N₀.U j)) *
        (Φ.E.B.left.presheaf.map (homOfLE (inf_le_right : Φ.N₀.U i ⊓ Φ.N₀.U j ≤ Φ.N₀.U j)).op).hom (t j) := by
  have := Φ.D.q_flat
  have := Φ.D.q_surjective
  rw [← (GlobalTheory.FunDescent.app_injective Φ.D.q.left (Φ.N₀.U i ⊓ Φ.N₀.U j)).eq_iff, map_mul,
    app_res _ _ (Φ.D.q.left.preimage_mono inf_le_left), app_res _ _ (Φ.D.q.left.preimage_mono inf_le_right)]
  have hg : ((Φ.H 1).g i j : Γ(Φ.G.left, (Φ.H 1).U i ⊓ (Φ.H 1).U j)) =
      (Φ.D.q.left.app (Φ.N₀.U i ⊓ Φ.N₀.U j)).hom (Φ.N₀.g i j) :=
    congrArg Units.val (pow_one (pullU Φ.D.q.left (Φ.N₀.U i ⊓ Φ.N₀.U j) (Φ.N₀.g i j)))
  rw [hg]
  exact Iff.rfl

theorem FibPre.pure_zero : (∀ (k : Type) [Field k] (Φ : FibPre k), (∀ t : Φ.N₀.Sec, ∃ φ : (Φ.H 1).Sec, Φ.Pure 0 φ ∧ ∀ l, Φ.wt φ 0 l = t.f l) ∧ ∀ φ : (Φ.H 1).Sec, Φ.Pure 0 φ → ∃ t : Φ.N₀.Sec, (∀ l, Φ.wt φ 0 l = t.f l) ∧ (∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l)) ∧ Out.nonzeroLocus φ = Φ.D.q.left ⁻¹ᵁ Out.nonzeroLocus t) := by
  intro k _ Φ
  refine ⟨fun t => ?_, fun φ hφ => ?_⟩
  · refine ⟨⟨fun l => (Φ.D.q.left.app (Φ.N₀.U l)).hom (t.f l),
      fun i j => (Φ.compat_iff t.f i j).2 (t.compat i j)⟩, ?_, fun l => ?_⟩
    · rintro α ⟨l, hl⟩
      by_contra hα
      exact hl ((weight_app Φ.D _ _ _ _ α (t.f l)).trans (Finsupp.single_eq_of_ne hα))
    · exact (weight_app Φ.D _ _ _ _ 0 (t.f l)).trans Finsupp.single_eq_same
  · have hf : ∀ l, φ.f l = (Φ.D.q.left.app (Φ.N₀.U l)).hom (Φ.wt φ 0 l) := fun l => by
      refine eq_of_weight_eq Φ.D (Φ.ch l) _ (Φ.aff l) (Φ.le l) fun χ => ?_
      rw [weight_app]
      by_cases hχ : χ = 0
      · subst hχ
        exact Finsupp.single_eq_same.symm
      · rw [Finsupp.single_eq_of_ne hχ]
        by_contra hne
        exact hχ (hφ ⟨l, hne⟩)
    refine ⟨⟨fun l => Φ.wt φ 0 l, fun i j => (Φ.compat_iff _ i j).1 ?_⟩, fun _ => rfl, hf, ?_⟩
    · have c := φ.compat i j
      rw [hf i, hf j] at c
      exact c
    · unfold Out.nonzeroLocus
      rw [Scheme.Hom.preimage_iSup]
      refine iSup_congr fun l => ?_
      rw [Scheme.preimage_basicOpen, hf]
      rfl

end GlobalTheory.ZH
end
