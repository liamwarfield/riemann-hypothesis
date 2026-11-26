module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAppTopEqOfEffectiveEpi
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory

namespace FlatDescent

universe u

variable {X Y Z : Scheme.{u}}

theorem injective_appTop_of_epi (p : Y ⟶ X) [Epi p] : Function.Injective p.appTop := by
  have : Epi (Scheme.Γ.rightOp.map p) :=
    have := ΓSpec.adjunction.isLeftAdjoint
    inferInstance
  have : Mono p.appTop := inferInstanceAs (Mono (Scheme.Γ.rightOp.map p).unop)
  exact ConcreteCategory.injective_of_mono_of_preservesPullback p.appTop

theorem exists_appTop_eq_of_effectiveEpi (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) (hs : f.appTop s = g.appTop s) :
    ∃ a : Γ(X, ⊤), p.appTop a = s := by
  let E := RingHom.eqLocus f.appTop.hom g.appTop.hom
  let ι : CommRingCat.of E ⟶ Γ(Y, ⊤) := CommRingCat.ofHom E.subtype
  have hι : ι ≫ f.appTop = ι ≫ g.appTop := by
    ext x
    exact x.2
  have : HasPullback p p := inferInstance
  obtain ⟨u, hu⟩ := IsRegularEpi.exists_of_isKernelPair p h (Y.toSpecΓ ≫ Spec.map ι) (by
    rw [Scheme.toSpecΓ_naturality_assoc, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp,
      ← Spec.map_comp, hι])
  refine ⟨u.appTop ((Scheme.ΓSpecIso (.of E)).inv ⟨s, hs⟩), ?_⟩
  have h1 : (Scheme.ΓSpecIso (.of E)).inv ≫ u.appTop ≫ p.appTop = ι := by
    rw [← Scheme.Hom.comp_appTop, hu, Scheme.Hom.comp_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  exact congr($h1 ⟨s, hs⟩)

theorem appTop_appTop_eq {p : Y ⟶ X} {f g : Z ⟶ Y} (h : f ≫ p = g ≫ p) (a : Γ(X, ⊤)) :
    f.appTop (p.appTop a) = g.appTop (p.appTop a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Scheme.Hom.comp_appTop, h]

theorem existsUnique_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)) :
    (∃! a : Γ(X, ⊤), p.appTop a = s) ↔ f.appTop s = g.appTop s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact appTop_appTop_eq h.w a
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s hs
    exact ⟨a, ha, fun b hb => injective_appTop_of_epi p (hb.trans ha.symm)⟩

theorem isUnit_appTop_iff (p : Y ⟶ X) [EffectiveEpi p] (a : Γ(X, ⊤)) :
    IsUnit (p.appTop a) ↔ IsUnit a := by
  refine ⟨fun ha => ?_, fun ha => ha.map p.appTop.hom⟩
  obtain ⟨t, ht⟩ := ha.exists_right_inv
  have h := IsPullback.of_hasPullback p p
  obtain ⟨b, rfl⟩ := exists_appTop_eq_of_effectiveEpi p h t (by
    have h1 := congrArg (pullback.fst p p).appTop.hom ht
    have h2 := congrArg (pullback.snd p p).appTop.hom ht
    rw [map_mul, map_one] at h1 h2
    rw [appTop_appTop_eq h.w a] at h1
    exact left_inv_eq_right_inv ((mul_comm _ _).trans h1) h2)
  exact IsUnit.of_mul_eq_one b (injective_appTop_of_epi p (by rw [map_mul, ht, map_one]))

theorem existsUnique_units_appTop_eq_iff (p : Y ⟶ X) [EffectiveEpi p] {f g : Z ⟶ Y}
    (h : IsPullback f g p p) (s : Γ(Y, ⊤)ˣ) :
    (∃! a : Γ(X, ⊤)ˣ, Units.map p.appTop.hom.toMonoidHom a = s) ↔
      Units.map f.appTop.hom.toMonoidHom s = Units.map g.appTop.hom.toMonoidHom s := by
  refine ⟨?_, fun hs => ?_⟩
  · rintro ⟨a, rfl, -⟩
    exact Units.ext (appTop_appTop_eq h.w a)
  · obtain ⟨a, ha⟩ := exists_appTop_eq_of_effectiveEpi p h s (congrArg Units.val hs)
    obtain ⟨a, rfl⟩ := (isUnit_appTop_iff p a).1 (ha ▸ s.isUnit)
    exact ⟨a, Units.ext ha, fun b hb => Units.ext <|
      injective_appTop_of_epi p ((congrArg Units.val hb).trans ha.symm)⟩

section Opens

theorem isPullback_resLE {p : Y ⟶ X} {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens)
    (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) :
    IsPullback (f.resLE _ W hf) (g.resLE _ W hg) (p ∣_ U) (p ∣_ U) := by
  subst hW
  have hc : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      (s.fst ≫ (p ⁻¹ᵁ U).ι) ≫ p = (s.snd ≫ (p ⁻¹ᵁ U).ι) ≫ p := fun s => by
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, s.condition_assoc]
  have hr : ∀ s : PullbackCone (p ∣_ U) (p ∣_ U),
      Set.range (h.lift _ _ (hc s)) ⊆ Set.range (f ⁻¹ᵁ p ⁻¹ᵁ U).ι := fun s => by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change f (h.lift _ _ _ x) ∈ p ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_apply, h.lift_fst, Scheme.Hom.comp_apply]
    exact (s.fst x).2
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => IsOpenImmersion.lift (f ⁻¹ᵁ p ⁻¹ᵁ U).ι
    (h.lift _ _ (hc s)) (hr s)) (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono U.ι]
    simp [morphismRestrict_ι, Scheme.Hom.resLE_comp_ι_assoc, h.w]
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (p ⁻¹ᵁ U).ι]
    simp
  · rw [← cancel_mono (f ⁻¹ᵁ p ⁻¹ᵁ U).ι, IsOpenImmersion.lift_fac]
    refine h.hom_ext ?_ ?_
    · simp [← h₁]
    · simp [← h₂]

theorem appTop_resLE_apply (f : Z ⟶ Y) (V : Y.Opens) (W : Z.Opens) (e : W ≤ f ⁻¹ᵁ V)
    (s : Γ(Y, V)) : (f.resLE V W e).appTop (V.topIso.inv s) = W.topIso.inv (f.appLE V W e s) := by
  have : V.topIso.inv ≫ (f.resLE V W e).appTop = f.appLE V W e ≫ W.topIso.inv := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Iso.inv_hom_id_assoc]
  exact congr($this s)

theorem appTop_morphismRestrict_apply (p : Y ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    (p ∣_ U).appTop (U.topIso.inv a) = (p ⁻¹ᵁ U).topIso.inv (p.app U a) := by
  rw [← Scheme.Hom.resLE_eq_morphismRestrict, appTop_resLE_apply, Scheme.Hom.appLE_eq_app]

theorem effectiveEpi_morphismRestrict (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    (U : X.Opens) : EffectiveEpi (p ∣_ U) := by
  have : Flat (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : Surjective (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  have : QuasiCompact (p ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p U).flip ‹_›
  infer_instance

theorem existsUnique_app_eq_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p]
    {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens) (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U)
    (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) (s : Γ(Y, p ⁻¹ᵁ U)) :
    (∃! a : Γ(X, U), p.app U a = s) ↔ f.appLE _ W hf s = g.appLE _ W hg s := by
  have := effectiveEpi_morphismRestrict p U
  have hb : ∀ {T : Scheme.{u}} (V : T.Opens), Function.Bijective V.topIso.inv := fun V =>
    ConcreteCategory.bijective_of_isIso _
  rw [← (hb W).1.eq_iff, ← appTop_resLE_apply, ← appTop_resLE_apply,
    ← existsUnique_appTop_eq_iff (p ∣_ U) (isPullback_resLE h U W hW hf hg),
    ← (Equiv.ofBijective _ (hb U)).existsUnique_congr_right]
  simp only [Equiv.ofBijective_apply, appTop_morphismRestrict_apply, (hb _).1.eq_iff]

theorem isUnit_app_iff (p : Y ⟶ X) [Flat p] [Surjective p] [QuasiCompact p] (U : X.Opens)
    (a : Γ(X, U)) : IsUnit (p.app U a) ↔ IsUnit a := by
  have := effectiveEpi_morphismRestrict p U
  rw [← isUnit_map_iff (p ⁻¹ᵁ U).topIso.inv.hom, ← appTop_morphismRestrict_apply,
    isUnit_appTop_iff, isUnit_map_iff]

end Opens

end FlatDescent

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsLineOfAddAddEqZero
namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine

theorem map_add_of_triples {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A → B)
    (h0 : f 0 = 0) (hneg : ∀ P, f (-P) = -f P)
    (h3 : ∀ P Q R, P ≠ 0 → Q ≠ 0 → R ≠ 0 → P + Q + R = 0 → f P + f Q + f R = 0) (P Q : A) :
    f (P + Q) = f P + f Q := by
  by_cases hP : P = 0
  · simp [hP, h0]
  by_cases hQ : Q = 0
  · simp [hQ, h0]
  by_cases hR : P + Q = 0
  · have : P = -Q := eq_neg_of_add_eq_zero_left hR
    rw [hR, h0, this, hneg, neg_add_cancel]
  have := h3 P Q (-(P + Q)) hP hQ (neg_ne_zero.mpr hR) (add_neg_cancel _)
  rw [hneg] at this
  exact (add_neg_eq_zero.mp this).symm

variable {k : Type*} [Field k] [DecidableEq k] {W : Affine k}

theorem add_add_eq_zero_of_line {x₁ y₁ x₂ y₂ x₃ y₃ : k} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (h₃ : W.Nonsingular x₃ y₃) (l n : k)
    (e₁ : y₁ = l * x₁ + n) (e₂ : y₂ = l * x₂ + n) (e₃ : y₃ = l * x₃ + n)
    (s₁ : x₁ + x₂ + x₃ = l ^ 2 + W.a₁ * l - W.a₂)
    (s₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * l * n - W.a₁ * n - W.a₃ * l) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0 := by
  have key : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) ∧ W.slope x₁ x₂ y₁ y₂ = l := by
    by_cases hx : x₁ = x₂
    · subst hx
      have hy : y₁ = y₂ := e₁.trans e₂.symm
      subst hy
      have ht : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ = l * (y₁ - W.negY x₁ y₁) := by
        rw [negY]
        linear_combination (2 * x₁) * s₁ - s₂ - (W.a₁ + 2 * l) * e₁
      have hne : y₁ ≠ W.negY x₁ y₁ := by
        intro h
        rw [nonsingular_iff] at h₁
        rcases h₁.2 with h' | h'
        · apply h'
          rw [← h, sub_self, mul_zero] at ht
          linear_combination -ht
        · exact h' h
      refine ⟨fun h => hne h.2, ?_⟩
      rw [slope_of_Y_ne rfl hne, ht, mul_div_assoc, div_self (sub_ne_zero.mpr hne), mul_one]
    · refine ⟨fun h => hx h.1, ?_⟩
      rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
      linear_combination e₁ - e₂
  rw [Point.add_some key.1]
  apply Point.add_of_Y_eq
  · rw [key.2, addX]
    linear_combination -s₁
  · have hx : W.addX x₁ x₂ l = x₃ := by
      rw [addX]
      linear_combination -s₁
    rw [key.2, addY, negAddY, hx]
    congr 1
    linear_combination e₁ - e₃

theorem exists_line_of_add_add_eq_zero {x₁ y₁ x₂ y₂ x₃ y₃ : k} {h₁ : W.Nonsingular x₁ y₁}
    {h₂ : W.Nonsingular x₂ y₂} {h₃ : W.Nonsingular x₃ y₃}
    (h : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0) :
    ∃ l n : k, y₁ = l * x₁ + n ∧ y₂ = l * x₂ + n ∧ y₃ = l * x₃ + n ∧
      x₁ + x₂ + x₃ = l ^ 2 + W.a₁ * l - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * l * n - W.a₁ * n - W.a₃ * l ∧
      x₁ * x₂ * x₃ = n ^ 2 + W.a₃ * n - W.a₆ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
    rintro ⟨hx, hy⟩
    rw [Point.add_of_Y_eq hx hy, zero_add] at h
    exact Point.some_ne_zero _ h
  rw [Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at h
  obtain ⟨hx, hy⟩ := h
  have hp := addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, hx] at hp
  have hl : W.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    by_cases hx' : x₁ = x₂
    · have := Y_eq_of_Y_ne h₁.1 h₂.1 hx' (fun h => hxy ⟨hx', h⟩)
      rw [hx', this, sub_self, sub_self, mul_zero]
    · rw [slope_of_X_ne hx', div_mul_cancel₀ _ (sub_ne_zero.mpr hx')]
  rw [addY, negAddY, hx, negY, negY] at hy
  set l := W.slope x₁ x₂ y₁ y₂
  simp only [Cubic.mk.injEq, true_and] at hp
  obtain ⟨p₁, p₂, p₃⟩ := hp
  refine ⟨l, y₁ - l * x₁, by ring, by linear_combination hl, by linear_combination hy,
    by linear_combination p₁, by linear_combination -p₂, by linear_combination p₃⟩

section VariableChange


omit [DecidableEq k] in
theorem nonsingular_variableChange_iff (W : WeierstrassCurve k) (C : VariableChange k) (x y : k) :
    W.toAffine.Nonsingular ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t) ↔ (C • W).toAffine.Nonsingular x y := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  simp only [nonsingular_iff', equation_iff', variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  obtain ⟨u, r, s, t⟩ := C
  dsimp only at hu ⊢
  generalize (u : k) = v at hu ⊢
  obtain ⟨a₁, a₂, a₃, a₄, a₆⟩ := W
  dsimp only [toAffine]
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ ?_
  · field_simp
    linear_combination h
  · field_simp at h
    linear_combination h
  · rw [← not_iff_not]
    simp only [not_or, not_not]
    refine ⟨fun ⟨h, h'⟩ => ⟨?_, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
    · field_simp
      linear_combination h + s * h'
    · field_simp
      linear_combination h'
    · field_simp at h h'
      exact ⟨by linear_combination h - s * h', by linear_combination h'⟩

def variableChangePointFun {W W' : WeierstrassCurve k} (C : VariableChange k) (h : C • W = W') :
    W'.toAffine.Point → W.toAffine.Point
  | .zero => 0
  | .some x y hP => .some ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
      ((nonsingular_variableChange_iff W C x y).mpr (h ▸ hP))

def variableChangePoint {W W' : WeierstrassCurve k} (C : VariableChange k) (h : C • W = W') :
    W'.toAffine.Point →+ W.toAffine.Point :=
  AddMonoidHom.mk' (variableChangePointFun C h) <| by
    subst h
    have hu : (C.u : k) ≠ 0 := C.u.ne_zero
    refine map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, variableChangePointFun, Point.some.injEq, true_and, negY,
          variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
        field_simp
        ring
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := exists_line_of_add_add_eq_zero h
      simp only [variableChange_a₁, variableChange_a₂,
        variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val] at s₁ s₂
      field_simp at s₁ s₂
      refine add_add_eq_zero_of_line _ _ _ ((C.u : k) * l + C.s)
        ((C.u : k) ^ 3 * n + C.t - C.r * ((C.u : k) * l + C.s)) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; ring
      · rw [e₂]; ring
      · rw [e₃]; ring
      · linear_combination s₁
      · linear_combination s₂ + 2 * C.r * s₁

@[simp]
theorem variableChangePoint_some {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') {x y : k} (hP : W'.toAffine.Nonsingular x y) :
    variableChangePoint C h (.some x y hP) = .some ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
      ((nonsingular_variableChange_iff W C x y).mpr (h ▸ hP)) :=
  rfl

theorem variableChangePoint_bijective {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') : Function.Bijective (variableChangePoint C h) := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro (_ | ⟨x, y, hP⟩) h0
    · rfl
    · exact absurd h0 (Point.some_ne_zero _)
  · rintro (_ | ⟨x, y, hP⟩)
    · exact ⟨0, map_zero _⟩
    · have hx : x = (C.u : k) ^ 2 * ((x - C.r) / (C.u : k) ^ 2) + C.r := by field_simp; ring
      have hy : y = (C.u : k) ^ 3 * ((y - C.s * (x - C.r) - C.t) / (C.u : k) ^ 3)
          + (C.u : k) ^ 2 * C.s * ((x - C.r) / (C.u : k) ^ 2) + C.t := by field_simp; ring
      have hP' := hP
      rw [hx, hy, ← hx] at hP'
      nth_rw 1 [hx] at hP'
      rw [nonsingular_variableChange_iff, h] at hP'
      refine ⟨.some _ _ hP', ?_⟩
      rw [variableChangePoint_some, Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩

noncomputable def variableChangePointEquiv {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') : W'.toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.ofBijective (variableChangePoint C h) (variableChangePoint_bijective C h)

end VariableChange

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsHomDivMulRefine
namespace GlobalTheory

namespace QuadRefinement

section Additive

variable {O Y M : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y]
  [AddCommGroup M]

variable {τ : Y →+ Y →+ M} {w : O}

end Additive

section Multiplicative

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]

def mulRefine (τ : Y →+ Y →+ Additive A) (w : O) (y : Y) : A := (τ y (w • y)).toMul

variable {τ : Y →+ Y →+ Additive A} {w : O}

end Multiplicative

section HalfElement

variable {K : Type*} [Field K] [CharZero K] [StarRing K] {d : ℤ} {s : K}


end HalfElement

section Example

open QuadraticAlgebra

end Example

end QuadRefinement

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_smul_add_apply_smul_eq_of_add_star_eq_one (hsymm : ∀ y y', τ y y' = τ y' y)
    (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) (hw : w + star w = 1) (y y' : Y) :
    τ y (w • y') + τ y' (w • y) = τ y y' := by
  rw [hsymm y' (w • y), hadj, ← map_add (τ y), ← add_smul, hw, one_smul]

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_add_smul_add_eq_add_add (hsymm : ∀ y y', τ y y' = τ y' y)
    (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) (hw : w + star w = 1) (y y' : Y) :
    τ (y + y') (w • (y + y')) = τ y (w • y) + τ y' (w • y') + τ y y' := by
  rw [← apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw y y']
  simp only [smul_add, map_add (f := _), AddMonoidHom.add_apply]
  abel

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_neg_smul_neg_eq (y : Y) : τ (-y) (w • -y) = τ y (w • y) := by
  simp

variable {O Y A : Type*} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A] in
variable {τ : Y →+ Y →+ Additive A} {w : O} in
private theorem apply_smul_smul_smul_eq_zsmul_of_mul_star_eq (hadj : ∀ (a : O) y y', τ (a • y) y' = τ y (star a • y'))
    (a : O) (n : ℤ) (h : a * star a = n) (y : Y) :
    τ (a • y) (w • a • y) = n • τ y (w • y) := by
  have e : star a * w * a = (n : O) * w := by rw [← h]; ring
  rw [hadj, smul_smul, smul_smul, e, mul_smul, Int.cast_smul_eq_zsmul, map_zsmul]

theorem _root_.GlobalTheory.quadratic_refinement :
    (∀ {O Y A : Type} [CommRing O] [StarRing O] [AddCommGroup Y] [Module O Y] [CommGroup A]
      (τ : Y →+ Y →+ Additive A) (w : O), (∀ y y', τ y y' = τ y' y) →
      (∀ (a : O) y y', τ (a • y) y' = τ y (star a • y')) → w + star w = 1 →
      (∀ y y', _root_.GlobalTheory.QuadRefinement.mulRefine τ w (y + y') =
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w y *
          _root_.GlobalTheory.QuadRefinement.mulRefine τ w y' * (τ y y').toMul) ∧
      (∀ y, _root_.GlobalTheory.QuadRefinement.mulRefine τ w (-y) =
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w y) ∧
      (∀ y, _root_.GlobalTheory.QuadRefinement.mulRefine τ w y ^ 2 = (τ y y).toMul) ∧
      (∀ (a : O) (n : ℤ), a * star a = n → ∀ y,
        _root_.GlobalTheory.QuadRefinement.mulRefine τ w (a • y) =
          _root_.GlobalTheory.QuadRefinement.mulRefine τ w y ^ n) ∧
      (∀ ψ : Y → A, (∀ y y', ψ (y + y') = ψ y * ψ y' * (τ y y').toMul) → (∀ y, ψ (-y) = ψ y) →
        (∃ α : Multiplicative Y →* A,
          (∀ y, α (Multiplicative.ofAdd y) = ψ y / _root_.GlobalTheory.QuadRefinement.mulRefine τ w y)
            ∧ α ^ 2 = 1) ∧
        ∀ n : ℤ, w * star w = n → (∀ y, ψ (w • y) = ψ y ^ n) →
          (∀ y, ψ (star w • y) = ψ y ^ n) → ψ = _root_.GlobalTheory.QuadRefinement.mulRefine τ w) ∧
      (∀ (v : Additive A →+ ℚ) y,
        2 * v (Additive.ofMul (_root_.GlobalTheory.QuadRefinement.mulRefine τ w y)) =
          τ.compr₂ v y y)) ∧
    (∀ {K : Type} [Field K] [CharZero K] [StarRing K] (d : ℤ) (s : K), d % 8 = 7 →
      s ^ 2 = -(d : K) → star s = -s →
      IsIntegral ℤ ((1 + s) / 2) ∧ (1 + s) / 2 + star ((1 + s) / 2) = 1 ∧
      (1 + s) / 2 * star ((1 + s) / 2) = (((1 + d) / 4 : ℤ) : K) ∧
      4 * ((1 + d) / 4) = 1 + d ∧ Even ((1 + d) / 4)) := by
  refine ⟨?_, ?_⟩
  · intro O Y A _ _ _ _ _ τ w hsymm hadj hw
    set m := _root_.GlobalTheory.QuadRefinement.mulRefine τ w with hmdef
    have hm : ∀ y, m y = (τ y (w • y)).toMul := fun _ => rfl
    have hadd : ∀ y y', m (y + y') = m y * m y' * (τ y y').toMul := by
      intro y y'
      simp only [hm, apply_add_smul_add_eq_add_add hsymm hadj hw, toMul_add]
    have hneg : ∀ y, m (-y) = m y := by
      intro y
      simp only [hm, apply_neg_smul_neg_eq]
    have hsq : ∀ y, m y ^ 2 = (τ y y).toMul := by
      intro y
      rw [hm, ← toMul_nsmul, two_nsmul, apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw]
    have hpow : ∀ (a : O) (n : ℤ), a * star a = n → ∀ y, m (a • y) = m y ^ n := by
      intro a n h y
      rw [hm, hm, apply_smul_smul_smul_eq_zsmul_of_mul_star_eq hadj a n h, toMul_zsmul]
    refine ⟨hadd, hneg, hsq, hpow, ?_, ?_⟩
    · intro ψ hψ heven
      have h0 : ψ 0 = 1 := by
        have := hψ 0 0
        simpa using this
      have hψsq : ∀ y, ψ y ^ 2 = (τ y y).toMul := by
        intro y
        have h := hψ y (-y)
        rw [add_neg_cancel, h0, heven, map_neg, toMul_neg, eq_comm, mul_inv_eq_one] at h
        rw [sq, h]
      have hb : ∀ y y', ψ (y + y') / m (y + y') = ψ y / m y * (ψ y' / m y') := by
        intro y y'
        rw [hψ, hadd, mul_div_mul_right_eq_div, div_mul_div_comm]
      have hbsq : ∀ y, (ψ y / m y) ^ 2 = 1 := by
        intro y
        rw [div_pow, hψsq, hsq, div_self']
      let β : Multiplicative Y →* A :=
        MonoidHom.mk' (fun y => ψ y.toAdd / m y.toAdd) (fun y y' => by
          simp only [toAdd_mul]
          exact hb _ _)
      refine ⟨⟨β, fun y => rfl, ?_⟩, ?_⟩
      · ext y
        show β y ^ 2 = 1
        exact hbsq (Multiplicative.toAdd y)
      · intro n hn h1 h2
        funext y
        have hw1 : ψ (w • y) / m (w • y) = (ψ y / m y) ^ n := by
          rw [h1, hpow w n hn, div_zpow]
        have hw2 : ψ (star w • y) / m (star w • y) = (ψ y / m y) ^ n := by
          rw [h2, hpow (star w) n (by rw [star_star, mul_comm, hn]), div_zpow]
        have e : w • y + star w • y = y := by rw [← add_smul, hw, one_smul]
        have key : ψ y / m y = 1 := by
          calc ψ y / m y = ψ (w • y + star w • y) / m (w • y + star w • y) := by rw [e]
            _ = ((ψ y / m y) ^ 2) ^ n := by rw [hb, hw1, hw2, ← mul_zpow, ← sq]
            _ = 1 := by rw [hbsq, one_zpow]
        exact div_eq_one.mp key
    · intro v y
      rw [hm, ofMul_toMul, AddMonoidHom.compr₂_apply, ← apply_smul_add_apply_smul_eq_of_add_star_eq_one hsymm hadj hw y y,
        map_add, two_mul]
  · intro K _ _ _ d s hd hs hstar
    obtain ⟨k, rfl⟩ : ∃ k, d = 8 * k + 7 := ⟨d / 8, by omega⟩
    have hq : (1 + (8 * k + 7)) / 4 = 2 * k + 2 := by omega
    rw [hq]
    push_cast at hs
    have hst : star ((1 + s) / 2) = (1 - s) / 2 := by
      rw [div_eq_mul_inv, star_mul', star_inv₀, star_add, star_one, hstar, star_ofNat]
      ring
    refine ⟨?_, ?_, ?_, by omega, ⟨k + 1, by ring⟩⟩
    · refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((2 * k + 2 : ℤ)), ?_, ?_⟩
      · monicity!
      · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C]
        rw [algebraMap_int_eq, eq_intCast]
        push_cast
        linear_combination (1 / 4 : K) * hs
    · rw [hst]; ring
    · rw [hst]; push_cast; linear_combination (-1 / 4 : K) * hs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinitePresentationOfInjective
noncomputable section

open AddMonoidAlgebra

namespace GlobalTheory.GroupAlg

variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)

abbrev mapAlgebra : Algebra R[Y] R[X] := (mapDomainRingHom R u).toAlgebra

theorem mapAlgebra_tower : letI := mapAlgebra R u; IsScalarTower R R[Y] R[X] :=
  letI := mapAlgebra R u
  IsScalarTower.of_algebraMap_eq fun a => ((mapDomainAlgHom R R u).commutes a).symm

def cosetComb : letI := mapAlgebra R u; ((X ⧸ u.range) →₀ R[Y]) →ₗ[R[Y]] R[X] :=
  letI := mapAlgebra R u
  Finsupp.linearCombination R[Y] (fun c : X ⧸ u.range => (single c.out 1 : R[X]))

theorem cosetComb_single (c : X ⧸ u.range) (y : Y) (r : R) :
    cosetComb R u (Finsupp.single c (single y r)) = single (u y + c.out) r := by
  letI := mapAlgebra R u
  rw [cosetComb, Finsupp.linearCombination_single, Algebra.smul_def]
  change mapDomain u (single y r) * _ = _
  rw [mapDomain_single, single_mul_single, mul_one]

theorem exists_add_out (x : X) :
    ∃ y, u y + (QuotientAddGroup.mk x : X ⧸ u.range).out = x := by
  obtain ⟨⟨_, y, rfl⟩, h⟩ := QuotientAddGroup.mk_out_eq_mul u.range x
  exact ⟨-y, by rw [h]; simp⟩

theorem cosetComb_surjective : Function.Surjective (cosetComb R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨_, (cosetComb_single R u _ y r).trans (by rw [hy])⟩

theorem coset_bijective (hu : Function.Injective u) :
    Function.Bijective (fun p : (Σ _ : X ⧸ u.range, Y) => u p.2 + p.1.out) := by
  refine ⟨?_, fun x => ?_⟩
  · rintro ⟨c, y⟩ ⟨d, z⟩ h
    dsimp only at h
    have h1 : ∀ (c : X ⧸ u.range) y, (QuotientAddGroup.mk (u y + c.out) : X ⧸ u.range) = c := by
      intro c y
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff (N := u.range) (u y)).2 ⟨y, rfl⟩, zero_add,
        QuotientAddGroup.out_eq']
    obtain rfl : c = d := by rw [← h1 c y, h, h1]
    obtain rfl : y = z := hu (add_right_cancel h)
    rfl
  · obtain ⟨y, hy⟩ := exists_add_out u x
    exact ⟨⟨_, y⟩, hy⟩

theorem cosetComb_injective (hu : Function.Injective u) : Function.Injective (cosetComb R u) := by
  letI := mapAlgebra R u
  haveI := mapAlgebra_tower R u
  let b : Module.Basis (Σ _ : X ⧸ u.range, Y) R ((X ⧸ u.range) →₀ R[Y]) :=
    Finsupp.basis fun _ => AddMonoidAlgebra.basis Y R
  let e := b.equiv (AddMonoidAlgebra.basis X R) (Equiv.ofBijective _ (coset_bijective u hu))
  have : (cosetComb R u).restrictScalars R = e.toLinearMap := by
    refine b.ext fun p => ?_
    obtain ⟨c, y⟩ := p
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
    simp [b, cosetComb_single]
  have h2 : ⇑(cosetComb R u) = e := congrArg DFunLike.coe this
  rw [h2]
  exact e.injective

def cosetBasis (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Basis (X ⧸ u.range) R[Y] R[X] :=
  letI := mapAlgebra R u
  .ofRepr (LinearEquiv.ofBijective (cosetComb R u)
    ⟨cosetComb_injective R u hu, cosetComb_surjective R u⟩).symm

theorem free_of_injective (hu : Function.Injective u) :
    letI := mapAlgebra R u; Module.Free R[Y] R[X] :=
  letI := mapAlgebra R u
  .of_basis (cosetBasis R u hu)

theorem faithfullyFlat_of_injective (hu : Function.Injective u) :
    (mapDomainRingHom R u).FaithfullyFlat := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  change Module.FaithfullyFlat R[Y] R[X]
  rcases subsingleton_or_nontrivial R with h | h
  · have : Subsingleton R[Y] := Module.subsingleton R _
    exact ⟨fun m hm => (hm.ne_top (Subsingleton.elim _ _)).elim⟩
  · infer_instance

theorem finite_of_finiteIndex [u.range.FiniteIndex] : (mapDomainRingHom R u).Finite := by
  letI := mapAlgebra R u
  exact Module.Finite.of_surjective (cosetComb R u) (cosetComb_surjective R u)

theorem finitePresentation_of_injective (hu : Function.Injective u) [u.range.FiniteIndex] :
    (mapDomainRingHom R u).FinitePresentation := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Module.FinitePresentation R[Y] R[X] := Module.finitePresentation_of_projective _ _
  exact (inferInstance : Algebra.FinitePresentation R[Y] R[X])

theorem finrank_of_injective (hu : Function.Injective u) [u.range.FiniteIndex]
    (p : PrimeSpectrum R[Y]) : (mapDomainRingHom R u).finrank p = u.range.index := by
  letI := mapAlgebra R u
  have := free_of_injective R u hu
  have : Module.Finite R[Y] R[X] := finite_of_finiteIndex R u
  have : Nontrivial R[Y] := p.nontrivial
  change Module.rankAtStalk (R := R[Y]) R[X] p = _
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_nat_card_basis (cosetBasis R u hu)]
  rfl

theorem surjective_of_surjective (hu : Function.Surjective u) :
    Function.Surjective (mapDomainRingHom R u) := by
  intro p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add s t hs ht =>
    obtain ⟨a, rfl⟩ := hs
    obtain ⟨b, rfl⟩ := ht
    exact ⟨a + b, map_add _ _ _⟩
  | single x r =>
    obtain ⟨y, rfl⟩ := hu x
    exact ⟨single y r, mapDomain_single⟩

theorem formallyUnramified_of_isUnit (n : ℕ) (hn : IsUnit (n : R)) (hX : ∀ x : X, n • x = 0) :
    Algebra.FormallyUnramified R R[X] := by
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI f g h
  ext x
  have hB : IsUnit (n : B) := by simpa using hn.map (algebraMap R B)
  have hfg : f (single x 1) - g (single x 1) ∈ I := by
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun h (single x 1)
  have hp : ∀ k : R[X] →ₐ[R] B, k (single x 1) ^ n = 1 := fun k => by
    rw [← map_pow, single_pow, hX, one_pow, ← one_def, map_one]
  set a := f (single x 1)
  set b := g (single x 1)
  have hi : (a - b) * (a - b) = 0 := by
    have := Ideal.mul_mem_mul hfg hfg
    rwa [← pow_two, hI, Ideal.mem_bot] at this
  have key : ∀ m : ℕ, b * a ^ m = b ^ (m + 1) + m * b ^ m * (a - b) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ a, ← mul_assoc, ih]
      push_cast
      linear_combination (m * b ^ m) * hi
  have h3 := key n
  rw [pow_succ b, hp f, hp g] at h3
  have h4 : (n : B) * (a - b) = 0 := by linear_combination -h3
  have h5 : a - b = 0 := (hB.mul_right_eq_zero).1 h4
  exact sub_eq_zero.1 h5

theorem etale_of_isUnit_card [Finite X] (hn : IsUnit (Nat.card X : R)) : Algebra.Etale R R[X] := by
  have := formallyUnramified_of_isUnit R (X := X) _ hn fun x => card_nsmul_eq_zero'
  have : Module.FinitePresentation R R[X] := Module.finitePresentation_of_projective _ _
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory.GroupAlg
end
end
