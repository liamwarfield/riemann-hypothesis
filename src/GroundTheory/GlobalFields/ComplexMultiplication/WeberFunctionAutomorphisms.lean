module

public import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions

@[expose] public section

section -- merged from GroundTheory.GlobalFields.ComplexMultiplication.WeberFunction
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve OnePoint

variable {F : Type*} [Field F]

structure IsShortForm (W : WeierstrassCurve F) : Prop where
  a₁_eq : W.a₁ = 0
  a₂_eq : W.a₂ = 0
  a₃_eq : W.a₃ = 0

namespace ShortWeierstrass

def g₂ (W : WeierstrassCurve F) : F := -4 * W.a₄

def g₃ (W : WeierstrassCurve F) : F := -4 * W.a₆

end ShortWeierstrass

open ShortWeierstrass

theorem IsShortForm.Δ_eq {W : WeierstrassCurve F} (hW : IsShortForm W) :
    W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  simp only [WeierstrassCurve.Δ, b₂, b₄, b₆, b₈, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq]
  ring

theorem IsShortForm.a₄_ne_zero_or_a₆_ne_zero {W : WeierstrassCurve F} [W.IsElliptic]
    (hW : IsShortForm W) : W.a₄ ≠ 0 ∨ W.a₆ ≠ 0 := by
  by_contra h
  push Not at h
  have := W.isUnit_Δ.ne_zero
  rw [hW.Δ_eq, h.1, h.2] at this
  simp at this


open Classical in
open scoped Classical in
noncomputable def weberValue (W : WeierstrassCurve F) (x : F) : F :=
  if W.a₆ = 0 then g₂ W ^ 2 / W.Δ * x ^ 2
  else if W.a₄ = 0 then g₃ W / W.Δ * x ^ 3
  else g₂ W * g₃ W / W.Δ * x

noncomputable def weberFunction (W : WeierstrassCurve F) : W.toAffine.Point → OnePoint F
  | .zero => ∞
  | .some x _ _ => OnePoint.some (weberValue W x)

@[simp]
theorem weberFunction_some (W : WeierstrassCurve F) {x y : F} (h : W.toAffine.Nonsingular x y) :
    weberFunction W (.some x y h) = OnePoint.some (weberValue W x) := rfl

theorem weberValue_of_a₆_eq_zero {W : WeierstrassCurve F} (hb : W.a₆ = 0) (x : F) :
    weberValue W x = g₂ W ^ 2 / W.Δ * x ^ 2 := by
  simp [weberValue, hb]

theorem weberValue_of_a₄_eq_zero {W : WeierstrassCurve F} (ha : W.a₄ = 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₃ W / W.Δ * x ^ 3 := by
  simp [weberValue, ha, hb]

theorem weberValue_of_ne_zero {W : WeierstrassCurve F} (ha : W.a₄ ≠ 0) (hb : W.a₆ ≠ 0)
    (x : F) : weberValue W x = g₂ W * g₃ W / W.Δ * x := by
  simp [weberValue, ha, hb]

section Isomorphism

variable [CharZero F]

theorem variableChange_rst_eq_zero {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
  have h1 := hCW.a₁_eq
  have h2 := hCW.a₂_eq
  have h3 := hCW.a₃_eq
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, hW.a₁_eq, hW.a₂_eq,
    hW.a₃_eq] at h1 h2 h3
  have hs : C.s = 0 := by simpa [hv] using h1
  have ht : C.t = 0 := by simpa [hv] using h3
  have hr : C.r = 0 := by simpa [hv, hs] using h2
  exact ⟨hr, hs, ht⟩

theorem variableChange_a₄_of_isShortForm {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₄ = ↑C.u⁻¹ ^ 4 * W.a₄ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₄, hr, hs, ht]

theorem variableChange_a₆_of_isShortForm {C : VariableChange F} {W : WeierstrassCurve F}
    (hW : IsShortForm W) (hCW : IsShortForm (C • W)) : (C • W).a₆ = ↑C.u⁻¹ ^ 6 * W.a₆ := by
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hCW
  simp [variableChange_a₆, hr, ht]

theorem weberFunction_variableChangePoint (C : VariableChange F) {W W' : WeierstrassCurve F}
    [W.IsElliptic] (hC : C • W = W') (hW : IsShortForm W) (hW' : IsShortForm W')
    (P : W.toAffine.Point) :
    weberFunction W' (variableChangePoint C hC P) = weberFunction W P := by
  subst hC
  obtain ⟨hr, hs, ht⟩ := variableChange_rst_eq_zero hW hW'
  cases P with
  | zero => rfl
  | some x y h =>
    rw [variableChangePoint_some, weberFunction_some, weberFunction_some]
    congr 1
    have hv : (↑C.u⁻¹ : F) ≠ 0 := Units.ne_zero _
    have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
    have ha := variableChange_a₄_of_isShortForm hW hW'
    have hb := variableChange_a₆_of_isShortForm hW hW'
    have hb0 : (C • W).a₆ = 0 ↔ W.a₆ = 0 := by rw [hb]; simp
    have ha0 : (C • W).a₄ = 0 ↔ W.a₄ = 0 := by rw [ha]; simp
    by_cases h6 : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (hb0.mpr h6), weberValue_of_a₆_eq_zero h6]
      simp only [g₂, ha, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    by_cases h4 : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (ha0.mpr h4) (mt hb0.mp h6), weberValue_of_a₄_eq_zero h4 h6]
      simp only [g₃, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp
    · rw [weberValue_of_ne_zero (mt ha0.mp h4) (mt hb0.mp h6), weberValue_of_ne_zero h4 h6]
      simp only [g₂, g₃, ha, hb, variableChange_Δ, hr, sub_zero, Units.val_inv_eq_inv_val]
      field_simp

end Isomorphism

section FieldOfDefinition

variable {L : Type*} [Field L]

def pointMapOfRingHom (φ : F →+* L) {W : WeierstrassCurve F} :
    W.toAffine.Point → (W.map φ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (φ x) (φ y) ((W.toAffine.map_nonsingular φ.injective x y).mpr h)

theorem weberFunction_pointMapOfRingHom (φ : F →+* L) (W : WeierstrassCurve F)
    (P : W.toAffine.Point) :
    weberFunction (W.map φ) (pointMapOfRingHom φ P) = OnePoint.map φ (weberFunction W P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    have h4 : (W.map φ).a₄ = φ W.a₄ := rfl
    have h6 : (W.map φ).a₆ = φ W.a₆ := rfl
    show OnePoint.some _ = OnePoint.some _
    congr 1
    by_cases hb : W.a₆ = 0
    · rw [weberValue_of_a₆_eq_zero (by rw [h6, hb, map_zero]), weberValue_of_a₆_eq_zero hb]
      simp [g₂, map_Δ, map_ofNat]
    have hb' : (W.map φ).a₆ ≠ 0 := by rw [h6]; exact (map_ne_zero φ).mpr hb
    by_cases ha : W.a₄ = 0
    · rw [weberValue_of_a₄_eq_zero (by rw [h4, ha, map_zero]) hb', weberValue_of_a₄_eq_zero ha hb]
      simp [g₃, map_Δ, map_ofNat]
    · have ha' : (W.map φ).a₄ ≠ 0 := by rw [h4]; exact (map_ne_zero φ).mpr ha
      rw [weberValue_of_ne_zero ha' hb', weberValue_of_ne_zero ha hb]
      simp [g₂, g₃, map_Δ, map_ofNat]

end FieldOfDefinition

end GroundTheory.Global
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open WeierstrassCurve OnePoint ShortWeierstrass

variable {F : Type*} [Field F]


open scoped Classical in
noncomputable def automorphismOrder (W : WeierstrassCurve F) : ℕ := by
  classical
  exact if W.a₆ = 0 then 4 else if W.a₄ = 0 then 6 else 2

def automorphismScale (W : WeierstrassCurve F) :
    MulAction.stabilizer (VariableChange F) W →* Fˣ where
  toFun ξ := ξ.1.u
  map_one' := rfl
  map_mul' _ _ := rfl

def automorphismPoint {W : WeierstrassCurve F} (ξ : MulAction.stabilizer (VariableChange F) W) :
    W.toAffine.Point → W.toAffine.Point :=
  variableChangePoint ξ.1 (MulAction.mem_stabilizer_iff.mp ξ.2)

section CharZero

variable [CharZero F] {W : WeierstrassCurve F}

theorem automorphism_rst_eq_zero (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) : ξ.1.r = 0 ∧ ξ.1.s = 0 ∧ ξ.1.t = 0 :=
  variableChange_rst_eq_zero hW ((MulAction.mem_stabilizer_iff.mp ξ.2).symm ▸ hW)

theorem mem_range_automorphismScale (hW : IsShortForm W) (u : Fˣ) :
    u ∈ (automorphismScale W).range ↔
      (↑u⁻¹ : F) ^ 4 * W.a₄ = W.a₄ ∧ (↑u⁻¹ : F) ^ 6 * W.a₆ = W.a₆ := by
  constructor
  · rintro ⟨ξ, rfl⟩
    have hξ : ξ.1 • W = W := MulAction.mem_stabilizer_iff.mp ξ.2
    have hCW : IsShortForm (ξ.1 • W) := hξ.symm ▸ hW
    have h4 := variableChange_a₄_of_isShortForm hW hCW
    have h6 := variableChange_a₆_of_isShortForm hW hCW
    rw [hξ] at h4 h6
    exact ⟨h4.symm, h6.symm⟩
  · rintro ⟨h4, h6⟩
    have hC : (⟨u, 0, 0, 0⟩ : VariableChange F) • W = W := by
      ext
      · simp [variableChange_a₁, hW.a₁_eq]
      · simp [variableChange_a₂, hW.a₂_eq, hW.a₁_eq]
      · simp [variableChange_a₃, hW.a₃_eq, hW.a₁_eq]
      · simpa [variableChange_a₄, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h4
      · simpa [variableChange_a₆, hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using h6
    exact ⟨⟨_, MulAction.mem_stabilizer_iff.mpr hC⟩, rfl⟩

variable [W.IsElliptic]


omit [CharZero F] in
theorem scale_conditions_iff (hW : IsShortForm W) (w : F) :
    (w⁻¹ ^ 4 * W.a₄ = W.a₄ ∧ w⁻¹ ^ 6 * W.a₆ = W.a₆) ↔ w ^ automorphismOrder W = 1 := by
  have key : ∀ (k : ℕ) (c : F), c ≠ 0 → (w⁻¹ ^ k * c = c ↔ w ^ k = 1) := by
    intro k c hc
    rw [inv_pow]
    constructor
    · intro h
      exact inv_eq_one.mp (mul_right_cancel₀ hc (h.trans (one_mul c).symm))
    · intro h
      rw [h, inv_one, one_mul]
  unfold automorphismOrder
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    simp only [h6, mul_zero, and_true, if_true]
    exact key 4 _ h4
  by_cases h4 : W.a₄ = 0
  · simp only [h4, h6, mul_zero, true_and, if_false, if_true]
    exact key 6 _ h6
  · simp only [h4, h6, if_false, key 4 _ h4, key 6 _ h6]
    constructor
    · rintro ⟨a, b⟩
      have : w ^ 6 = w ^ 4 * w ^ 2 := by ring
      rw [this, a, one_mul] at b
      exact b
    · intro h
      refine ⟨?_, ?_⟩
      · rw [show w ^ 4 = (w ^ 2) ^ 2 by ring, h, one_pow]
      · rw [show w ^ 6 = (w ^ 2) ^ 3 by ring, h, one_pow]

theorem weberFunction_automorphismPoint (hW : IsShortForm W)
    (ξ : MulAction.stabilizer (VariableChange F) W) (P : W.toAffine.Point) :
    weberFunction W (automorphismPoint ξ P) = weberFunction W P :=
  weberFunction_variableChangePoint ξ.1 _ hW hW P

end CharZero

section Fibres

variable [CharZero F] {W : WeierstrassCurve F} [W.IsElliptic]


omit [CharZero F] [W.IsElliptic] in
theorem IsShortForm.sq_eq (hW : IsShortForm W) {x y : F} (h : W.toAffine.Nonsingular x y) :
    y ^ 2 = x ^ 3 + W.a₄ * x + W.a₆ := by
  have := h.1
  rw [Affine.equation_iff] at this
  simpa [hW.a₁_eq, hW.a₂_eq, hW.a₃_eq] using this

theorem exists_scale_of_weberValue_eq [IsAlgClosed F] (hW : IsShortForm W) {x₁ x₂ : F}
    (hx : weberValue W x₁ = weberValue W x₂) :
    ∃ v : F, v ≠ 0 ∧ v ^ 4 * W.a₄ = W.a₄ ∧ v ^ 6 * W.a₆ = W.a₆ ∧ v ^ 2 * x₁ = x₂ := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  by_cases h6 : W.a₆ = 0
  · have h4 : W.a₄ ≠ 0 := by
      rcases hW.a₄_ne_zero_or_a₆_ne_zero with h | h
      · exact h
      · exact absurd h6 h
    rw [weberValue_of_a₆_eq_zero h6, weberValue_of_a₆_eq_zero h6] at hx
    have hc : g₂ W ^ 2 / W.Δ ≠ 0 := by simp [g₂, h4, hΔ]
    have hsq : x₁ ^ 2 = x₂ ^ 2 := mul_left_cancel₀ hc hx
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩
    · obtain ⟨i, hi⟩ := IsAlgClosed.exists_eq_mul_self (-1 : F)
      have hi4 : i ^ 4 = 1 := by linear_combination (1 - i * i) * hi
      refine ⟨i, ?_, by rw [hi4, one_mul], by rw [h6, mul_zero], ?_⟩
      · rintro rfl
        simp at hi
      · linear_combination (-x₁) * hi - h
  by_cases h4 : W.a₄ = 0
  · rw [weberValue_of_a₄_eq_zero h4 h6, weberValue_of_a₄_eq_zero h4 h6] at hx
    have hc : g₃ W / W.Δ ≠ 0 := by simp [g₃, h6, hΔ]
    have hcube : x₁ ^ 3 = x₂ ^ 3 := mul_left_cancel₀ hc hx
    by_cases hx1 : x₁ = 0
    · have hx2 : x₂ = 0 := by
        rw [hx1, zero_pow (by norm_num)] at hcube
        exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hcube.symm
      exact ⟨1, one_ne_zero, by simp, by simp, by simp [hx1, hx2]⟩
    · obtain ⟨w, hw⟩ : ∃ w, w = x₂ / x₁ := ⟨_, rfl⟩
      have hw3 : w ^ 3 = 1 := by
        rw [hw, div_pow, ← hcube, div_self (pow_ne_zero 3 hx1)]
      have hw0 : w ≠ 0 := by
        rintro rfl
        simp at hw3
      refine ⟨w ^ 2, pow_ne_zero 2 hw0, by simp [h4], ?_, ?_⟩
      · rw [show (w ^ 2) ^ 6 = (w ^ 3) ^ 4 by ring, hw3, one_pow, one_mul]
      · rw [show (w ^ 2) ^ 2 = w ^ 3 * w by ring, hw3, one_mul, hw, div_mul_cancel₀ _ hx1]
  · rw [weberValue_of_ne_zero h4 h6, weberValue_of_ne_zero h4 h6] at hx
    have hc : g₂ W * g₃ W / W.Δ ≠ 0 := by simp [g₂, g₃, h4, h6, hΔ]
    have h : x₁ = x₂ := mul_left_cancel₀ hc hx
    exact ⟨1, one_ne_zero, by simp, by simp, by simp [h]⟩


omit [W.IsElliptic] in
theorem exists_automorphismPoint_of_scale (hW : IsShortForm W) {v x₁ y₁ x₂ y₂ : F} (hv : v ≠ 0)
    (h4 : v ^ 4 * W.a₄ = W.a₄) (h6 : v ^ 6 * W.a₆ = W.a₆) (hx : v ^ 2 * x₁ = x₂)
    (hy : v ^ 3 * y₁ = y₂) (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) :
    ∃ ξ : MulAction.stabilizer (VariableChange F) W,
      automorphismPoint ξ (.some x₁ y₁ h₁) = .some x₂ y₂ h₂ := by
  obtain ⟨ξ, hξ⟩ := (mem_range_automorphismScale hW ((Units.mk0 v hv)⁻¹)).mpr
    ⟨by simpa using h4, by simpa using h6⟩
  refine ⟨ξ, ?_⟩
  obtain ⟨hr, hs, ht⟩ := automorphism_rst_eq_zero hW ξ
  have hu : (↑ξ.1.u⁻¹ : F) = v := by
    have : ξ.1.u = (Units.mk0 v hv)⁻¹ := hξ
    rw [this, inv_inv, Units.val_mk0]
  simp only [automorphismPoint, variableChangePoint_some, hr, hs, ht, hu, sub_zero, zero_mul,
    Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

theorem weberFunction_eq_iff [IsAlgClosed F] (hW : IsShortForm W) (P Q : W.toAffine.Point) :
    weberFunction W P = weberFunction W Q ↔
      ∃ ξ : MulAction.stabilizer (VariableChange F) W, automorphismPoint ξ P = Q := by
  constructor
  · intro hPQ
    cases P with
    | zero =>
      cases Q with
      | zero => exact ⟨1, rfl⟩
      | some x y h => simp [weberFunction] at hPQ
    | some x₁ y₁ h₁ =>
      cases Q with
      | zero => simp [weberFunction] at hPQ
      | some x₂ y₂ h₂ =>
        simp only [weberFunction_some] at hPQ
        have hx : weberValue W x₁ = weberValue W x₂ := Option.some_injective _ hPQ
        obtain ⟨v, hv, h4, h6, hx2⟩ := exists_scale_of_weberValue_eq hW hx
        have hy : y₂ ^ 2 = (v ^ 3 * y₁) ^ 2 := by
          rw [hW.sq_eq h₂, ← hx2]
          linear_combination (-(v ^ 6)) * hW.sq_eq h₁ - v ^ 2 * x₁ * h4 - h6
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with hy | hy
        · exact exists_automorphismPoint_of_scale hW hv h4 h6 hx2 hy.symm h₁ h₂
        · refine exists_automorphismPoint_of_scale (v := -v) hW (neg_ne_zero.mpr hv) ?_ ?_ ?_ ?_
            h₁ h₂
          · rw [show (-v) ^ 4 = v ^ 4 by ring, h4]
          · rw [show (-v) ^ 6 = v ^ 6 by ring, h6]
          · rw [show (-v) ^ 2 = v ^ 2 by ring, hx2]
          · rw [hy]
            ring
  · rintro ⟨ξ, rfl⟩
    exact (weberFunction_automorphismPoint hW ξ P).symm

end Fibres

end GroundTheory.Global
