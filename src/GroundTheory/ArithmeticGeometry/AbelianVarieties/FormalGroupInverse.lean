module

public import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroup

@[expose] public section

section -- merged from GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupLaw
namespace GroundTheory.Arith.Abelian

noncomputable section

section Field

variable {K : Type*} [Field K] (V : WeierstrassCurve K)

open WeierstrassCurve.Affine

theorem equation_of_zwPoly {z w : K} (h : zwPoly V z w = 0) (hw : w ≠ 0) :
    V.toAffine.Equation (z / w) (-1 / w) := by
  have key : (-1 / w) ^ 2 + V.a₁ * (z / w) * (-1 / w) + V.a₃ * (-1 / w) -
      ((z / w) ^ 3 + V.a₂ * (z / w) ^ 2 + V.a₄ * (z / w) + V.a₆) = -zwPoly V z w / w ^ 3 := by
    unfold zwPoly; field_simp; ring
  rw [WeierstrassCurve.Affine.equation_iff]
  rw [h, neg_zero, zero_div, sub_eq_zero] at key
  exact key

variable [V.IsElliptic]


open scoped Classical in
open Classical in
noncomputable def zwPoint (z w : K) : V.toAffine.Point :=
  if h : zwPoly V z w = 0 ∧ w ≠ 0 then Point.mk (equation_of_zwPoly V h.1 h.2) else 0

theorem zwPoint_of {z w : K} (h : zwPoly V z w = 0) (hw : w ≠ 0) :
    zwPoint V z w = Point.mk (equation_of_zwPoly V h hw) := by
  rw [zwPoint, dite_eq_left ⟨h, hw⟩]

theorem secant_spec [DecidableEq K] [Infinite K] {z₁ w₁ z₂ w₂ l n b z₃ w₃ : K}
    (h₁ : zwPoly V z₁ w₁ = 0) (h₂ : zwPoly V z₂ w₂ = 0) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0)
    (hl₁ : w₁ = l * z₁ + n) (hl₂ : w₂ = l * z₂ + n) (hb : secantB V l * b = 1)
    (hx : z₁ / w₁ ≠ z₂ / w₂) (hz₃ : z₃ = -z₁ - z₂ - secantA V l n * b)
    (hw₃def : w₃ = l * z₃ + n) :
    zwPoly V z₃ w₃ = 0 ∧ w₃ ≠ 0 ∧
      zwPoint V z₁ w₁ + zwPoint V z₂ w₂ = -zwPoint V z₃ w₃ := by
  subst hl₁ hl₂

  set B := secantB V l with hB
  set A := secantA V l n with hA
  set Cc := V.a₁ * n + 2 * V.a₃ * l * n + V.a₄ * n ^ 2 + 3 * V.a₆ * l * n ^ 2 - l with hCc
  set D := V.a₃ * n ^ 2 + V.a₆ * n ^ 3 - n with hD
  have hf : ∀ t, zwPoly V t (l * t + n) = B * t ^ 3 + A * t ^ 2 + Cc * t + D := by
    intro t; simp only [zwPoly, hB, hA, hCc, hD, secantB, secantA]; ring
  have hs : A + B * (z₁ + z₂ + z₃) = 0 := by
    rw [hz₃]; linear_combination (-A) * hb
  set α := Cc - B * (z₁ * z₂ + z₁ * z₃ + z₂ * z₃) with hα
  set β := D + B * z₁ * z₂ * z₃ with hβ
  have hg : ∀ t, zwPoly V t (l * t + n) = B * (t - z₁) * (t - z₂) * (t - z₃) + α * t + β := by
    intro t; rw [hf]; linear_combination t ^ 2 * hs
  have hz : z₁ ≠ z₂ := by
    rintro rfl; exact hx rfl
  have e₁ : α * z₁ + β = 0 := by
    have := hg z₁; rw [h₁] at this; linear_combination -this
  have e₂ : α * z₂ + β = 0 := by
    have := hg z₂; rw [h₂] at this; linear_combination -this
  have hα0 : α = 0 := by
    have : α * (z₁ - z₂) = 0 := by linear_combination e₁ - e₂
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hz)
  have hβ0 : β = 0 := by rw [hα0, zero_mul, zero_add] at e₁; exact e₁
  have hcub : ∀ t, zwPoly V t (l * t + n) = B * (t - z₁) * (t - z₂) * (t - z₃) := by
    intro t; rw [hg, hα0, hβ0]; ring
  have h₃ : zwPoly V z₃ w₃ = 0 := by rw [hw₃def, hcub]; ring

  have hn : n ≠ 0 := by
    intro hn
    have hz₁ : z₁ ≠ 0 := by rintro rfl; apply hw₁; rw [hn]; ring
    have hz₂ : z₂ ≠ 0 := by rintro rfl; apply hw₂; rw [hn]; ring
    have hl : l ≠ 0 := by rintro rfl; apply hw₁; rw [hn]; ring
    apply hx; rw [hn, add_zero, add_zero, div_eq_div_iff (mul_ne_zero hl hz₁)
      (mul_ne_zero hl hz₂)]; ring

  set x₁ := z₁ / (l * z₁ + n) with hx₁
  set x₂ := z₂ / (l * z₂ + n) with hx₂
  set y₁ := -1 / (l * z₁ + n) with hy₁
  set y₂ := -1 / (l * z₂ + n) with hy₂
  have E₁ : V.toAffine.Equation x₁ y₁ := equation_of_zwPoly V h₁ hw₁
  have E₂ : V.toAffine.Equation x₂ y₂ := equation_of_zwPoly V h₂ hw₂
  set ℓ := l / n with hℓ
  set m := -1 / n with hm
  have line₁ : y₁ = ℓ * x₁ + m := by
    simp only [hy₁, hx₁, hℓ, hm]; field_simp; ring
  have line₂ : y₂ = ℓ * x₂ + m := by
    simp only [hy₂, hx₂, hℓ, hm]; field_simp; ring
  have hslope : V.toAffine.slope x₁ x₂ y₁ y₂ = ℓ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hx, line₁, line₂,
      show ℓ * x₁ + m - (ℓ * x₂ + m) = ℓ * (x₁ - x₂) by ring, mul_div_assoc,
      div_self (sub_ne_zero.2 hx), mul_one]
  have hpoly := WeierstrassCurve.Affine.addPolynomial_slope E₁ E₂ (fun h => hx h.1)
  rw [hslope, WeierstrassCurve.Affine.addPolynomial_eq] at hpoly
  set X' := V.toAffine.addX x₁ x₂ ℓ with hX'
  have hev : ∀ x, x ^ 3 + (-ℓ ^ 2 - V.a₁ * ℓ + V.a₂) * x ^ 2 +
      (2 * x₁ * ℓ ^ 2 + (V.a₁ * x₁ - 2 * y₁ - V.a₃) * ℓ + (-V.a₁ * y₁ + V.a₄)) * x +
      (-x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + V.a₃ * x₁) * ℓ - (y₁ ^ 2 + V.a₃ * y₁ - V.a₆)) =
      (x - x₁) * (x - x₂) * (x - X') := by
    intro x
    have := congrArg (Polynomial.eval x) hpoly
    simp [Cubic.toPoly] at this
    first | linear_combination this | linear_combination -this
  have hft : ∀ t, l * t + n ≠ 0 → zwPoly V t (l * t + n) =
      (t - x₁ * (l * t + n)) * (t - x₂ * (l * t + n)) * (t - X' * (l * t + n)) := by
    intro t hs
    generalize hsd : l * t + n = s at hs ⊢
    have h0 := hev (t / s)
    have key : zwPoly V t s = s ^ 3 * ((t / s) ^ 3 +
        (-ℓ ^ 2 - V.a₁ * ℓ + V.a₂) * (t / s) ^ 2 +
        (2 * x₁ * ℓ ^ 2 + (V.a₁ * x₁ - 2 * y₁ - V.a₃) * ℓ + (-V.a₁ * y₁ + V.a₄)) * (t / s) +
        (-x₁ ^ 2 * ℓ ^ 2 + (2 * x₁ * y₁ + V.a₃ * x₁) * ℓ - (y₁ ^ 2 + V.a₃ * y₁ - V.a₆))) := by
      rw [line₁]; simp only [zwPoly, hℓ, hm]; field_simp; rw [← hsd]; ring
    rw [key, h0]; field_simp
  have fac₁ : ∀ t, t - x₁ * (l * t + n) = n / (l * z₁ + n) * (t - z₁) := by
    intro t
    have hx1 : x₁ * (l * z₁ + n) = z₁ := div_mul_cancel₀ _ hw₁
    have hd : n / (l * z₁ + n) * (l * z₁ + n) = n := div_mul_cancel₀ _ hw₁
    apply mul_right_cancel₀ hw₁
    linear_combination (-(l * t + n)) * hx1 + (-(t - z₁)) * hd
  have fac₂ : ∀ t, t - x₂ * (l * t + n) = n / (l * z₂ + n) * (t - z₂) := by
    intro t
    have hx2 : x₂ * (l * z₂ + n) = z₂ := div_mul_cancel₀ _ hw₂
    have hd : n / (l * z₂ + n) * (l * z₂ + n) = n := div_mul_cancel₀ _ hw₂
    apply mul_right_cancel₀ hw₂
    linear_combination (-(l * t + n)) * hx2 + (-(t - z₂)) * hd
  set c := n / (l * z₁ + n) * (n / (l * z₂ + n)) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (div_ne_zero hn hw₁) (div_ne_zero hn hw₂)
  have key : ∀ t, t ≠ z₁ → t ≠ z₂ → l * t + n ≠ 0 → B * (t - z₃) = c * (t - X' * (l * t + n)) := by
    intro t ht₁ ht₂ hs
    have e := (hcub t).symm.trans (hft t hs)
    rw [fac₁, fac₂] at e
    have : (t - z₁) * (t - z₂) * (B * (t - z₃) - c * (t - X' * (l * t + n))) = 0 := by
      simp only [hc]; linear_combination e
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact absurd (sub_eq_zero.1 h) ht₁
      · exact absurd (sub_eq_zero.1 h) ht₂
    · exact sub_eq_zero.1 h
  have good : ∀ t, t ≠ -n / l → l * t + n ≠ 0 := by
    intro t ht h
    by_cases hl : l = 0
    · rw [hl, zero_mul, zero_add] at h; exact hn h
    · apply ht; field_simp; linear_combination h
  obtain ⟨ta, hta⟩ := Infinite.exists_notMem_finset ({z₁, z₂, -n / l} : Finset K)
  obtain ⟨tb, htb⟩ := Infinite.exists_notMem_finset ({z₁, z₂, -n / l, ta} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hta htb
  have ka := key ta hta.1 hta.2.1 (good ta hta.2.2)
  have kb := key tb htb.1 htb.2.1 (good tb htb.2.2.1)
  have hB' : B = c * (1 - X' * l) := by
    have : (ta - tb) * (B - c * (1 - X' * l)) = 0 := by linear_combination ka - kb
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Ne.symm htb.2.2.2)))
  have hz₃c : c * ((1 - X' * l) * z₃ - X' * n) = 0 := by linear_combination -ka + (ta - z₃) * hB'
  have hz₃X : z₃ = X' * w₃ := by
    have := (mul_eq_zero.1 hz₃c).resolve_left hc0
    rw [hw₃def]; linear_combination this
  have hw₃ : w₃ ≠ 0 := by
    intro h0
    have hz0 : z₃ = 0 := by rw [hz₃X, h0, mul_zero]
    apply hn
    have : w₃ = n := by rw [hw₃def, hz0]; ring
    rw [← this, h0]
  refine ⟨h₃, hw₃, ?_⟩
  have E₃ : V.toAffine.Equation (z₃ / w₃) (-1 / w₃) := equation_of_zwPoly V h₃ hw₃
  have P₁ : zwPoint V z₁ (l * z₁ + n) = Point.mk E₁ := zwPoint_of V h₁ hw₁
  have P₂ : zwPoint V z₂ (l * z₂ + n) = Point.mk E₂ := zwPoint_of V h₂ hw₂
  have P₃ : zwPoint V z₃ w₃ = Point.mk E₃ := zwPoint_of V h₃ hw₃
  rw [P₁, P₂, P₃]
  simp only [WeierstrassCurve.Affine.Point.mk]
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne' hx]
  congr 1
  rw [WeierstrassCurve.Affine.Point.some.injEq, hslope]
  refine ⟨?_, ?_⟩
  · rw [eq_div_iff hw₃]; exact hz₃X.symm
  · simp only [WeierstrassCurve.Affine.negAddY]
    rw [← hX', line₁, eq_div_iff hw₃]
    have : (ℓ * (X' - x₁) + (ℓ * x₁ + m)) * w₃ = ℓ * (X' * w₃) + m * w₃ := by ring
    rw [this, ← hz₃X]
    have hw₃' := hw₃
    rw [hw₃def] at hw₃' ⊢
    simp only [hℓ, hm]
    field_simp
    ring

omit [V.IsElliptic] in
theorem zwPoly_neg {z w e : K} (he : (1 - V.a₁ * z - V.a₃ * w) * e = 1) :
    zwPoly V (-z * e) (-w * e) = -e ^ 3 * zwPoly V z w := by
  have hc : 1 - V.a₁ * z - V.a₃ * w ≠ 0 := left_ne_zero_of_mul_eq_one he
  have he' : e = (1 - V.a₁ * z - V.a₃ * w)⁻¹ := eq_inv_of_mul_eq_one_right he
  subst he'
  unfold zwPoly
  field_simp
  ring

theorem neg_zwPoint {z w e : K} (h : zwPoly V z w = 0) (hw : w ≠ 0)
    (he : (1 - V.a₁ * z - V.a₃ * w) * e = 1) :
    zwPoly V (-z * e) (-w * e) = 0 ∧ -w * e ≠ 0 ∧
      -zwPoint V z w = zwPoint V (-z * e) (-w * e) := by
  have he0 : e ≠ 0 := right_ne_zero_of_mul_eq_one he
  have h' : zwPoly V (-z * e) (-w * e) = 0 := by rw [zwPoly_neg V he, h, mul_zero]
  have hw' : -w * e ≠ 0 := mul_ne_zero (neg_ne_zero.2 hw) he0
  refine ⟨h', hw', ?_⟩
  rw [zwPoint_of V h hw, zwPoint_of V h' hw']
  simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.neg_some]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  refine ⟨?_, ?_⟩
  · field_simp
  · rw [WeierstrassCurve.Affine.negY]
    have hc : 1 - V.a₁ * z - V.a₃ * w ≠ 0 := left_ne_zero_of_mul_eq_one he
    have he' : e = (1 - V.a₁ * z - V.a₃ * w)⁻¹ := eq_inv_of_mul_eq_one_right he
    subst he'
    field_simp

end Field

section Points

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) (τ : Type*)

theorem isDomain_mvPowerSeries : IsDomain (MvPowerSeries τ R) := NoZeroDivisors.to_isDomain _

attribute [local instance] isDomain_mvPowerSeries

theorem infinite_mvPowerSeries [Nonempty τ] : Infinite (MvPowerSeries τ R) := by
  classical
  let i : τ := Classical.arbitrary τ
  refine Infinite.of_injective (fun n : ℕ => (MvPowerSeries.X i : MvPowerSeries τ R) ^ n) ?_
  intro m n h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single i m)) h
  simp only [MvPowerSeries.coeff_X_pow] at this
  by_contra hmn
  rw [if_neg (fun h' => hmn (Finsupp.single_injective i h'))] at this
  exact one_ne_zero this

noncomputable def toFrac : R →+* FractionRing (MvPowerSeries τ R) :=
  (algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R))).comp MvPowerSeries.C

omit [IsDomain R] in
theorem toFrac_injective : Function.Injective (toFrac (R := R) τ) :=
  (IsFractionRing.injective (MvPowerSeries τ R) _).comp MvPowerSeries.C_injective

noncomputable abbrev curveFrac : WeierstrassCurve (FractionRing (MvPowerSeries τ R)) :=
  W.map (toFrac τ)

theorem isElliptic_curveFrac (hΔ : W.Δ ≠ 0) : (curveFrac W τ).IsElliptic :=
  ⟨by rw [curveFrac, WeierstrassCurve.map_Δ]
      exact isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (toFrac_injective τ)).2 hΔ)⟩

variable [Fact (W.Δ ≠ 0)]

instance : (curveFrac W τ).IsElliptic := isElliptic_curveFrac W τ Fact.out

noncomputable def pointOf (u : MvPowerSeries τ R) : (curveFrac W τ).toAffine.Point :=
  zwPoint (curveFrac W τ) (algebraMap _ (FractionRing (MvPowerSeries τ R)) u)
    (algebraMap _ (FractionRing (MvPowerSeries τ R)) (wAt W u))

omit [IsDomain R] [Fact (W.Δ ≠ 0)] in
theorem map_C_map_algebraMap :
    (W.map (MvPowerSeries.C (σ := τ))).map
      (algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R))) = curveFrac W τ := by
  rw [WeierstrassCurve.map_map]; rfl

omit [IsDomain R] [Fact (W.Δ ≠ 0)] in
theorem zwPoly_curveFrac {u : MvPowerSeries τ R} (hu : MvPowerSeries.constantCoeff u = 0) :
    zwPoly (curveFrac W τ) (algebraMap _ (FractionRing (MvPowerSeries τ R)) u)
      (algebraMap _ (FractionRing (MvPowerSeries τ R)) (wAt W u)) = 0 := by
  have := congrArg (algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R)))
    (zwPoly_wAt W hu)
  rwa [map_zwPoly, map_zero, map_C_map_algebraMap] at this

theorem pointOf_injective {u u' : MvPowerSeries τ R} (hu : MvPowerSeries.constantCoeff u = 0)
    (hu' : MvPowerSeries.constantCoeff u' = 0) (h0 : u ≠ 0) (h0' : u' ≠ 0)
    (h : pointOf W τ u = pointOf W τ u') : u = u' := by
  set ι := algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R))
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have hw : ι (wAt W u) ≠ 0 := (map_ne_zero_iff ι hι).2 (wAt_ne_zero W hu h0)
  have hw' : ι (wAt W u') ≠ 0 := (map_ne_zero_iff ι hι).2 (wAt_ne_zero W hu' h0')
  rw [pointOf, pointOf, zwPoint_of _ (zwPoly_curveFrac W τ hu) hw,
    zwPoint_of _ (zwPoly_curveFrac W τ hu') hw'] at h
  simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e : wAt W u = wAt W u' := by
    have := congrArg (fun t => -t⁻¹) h2
    simpa [div_eq_mul_inv] using this
  rw [e, div_left_inj' hw'] at h1
  exact hι h1


open scoped Classical in
open Classical in
theorem pointOf_add [Nonempty τ] {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hx : u₁ * wAt W u₂ ≠ u₂ * wAt W u₁) :
    pointOf W τ u₁ + pointOf W τ u₂ =
      pointOf W τ (MvPowerSeries.subst ![u₁, u₂] (addSeries W)) := by
  classical
  have : Infinite (MvPowerSeries τ R) := infinite_mvPowerSeries τ
  have : Infinite (FractionRing (MvPowerSeries τ R)) :=
    Infinite.of_injective _ (IsFractionRing.injective (MvPowerSeries τ R) _)
  set ι := algebraMap (MvPowerSeries τ R) (FractionRing (MvPowerSeries τ R)) with hιdef
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂
  set ψ := MvPowerSeries.substAlgHom (R := R) hab with hψdef
  have hψ : ∀ f, MvPowerSeries.subst ![u₁, u₂] f = ψ f := fun f => by
    rw [hψdef, MvPowerSeries.coe_substAlgHom]
  have ψX0 : ψ (MvPowerSeries.X 0) = u₁ := by rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψX1 : ψ (MvPowerSeries.X 1) = u₂ := by rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψC : ∀ r, ψ (MvPowerSeries.C r) = MvPowerSeries.C r := fun r => by
    rw [← hψ, MvPowerSeries.subst_C]
  have ψw : ∀ i, ψ (wAt W (MvPowerSeries.X i)) = wAt W (![u₁, u₂] i) := fun i => by
    rw [← hψ, wAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst (PowerSeries.HasSubst.X i)
      hab, MvPowerSeries.subst_X hab, wAt]
  have hc0 : ∀ f : MvPowerSeries (Fin 2) R, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (ψ f) = 0 := fun f hf => by
    rw [← hψ]
    exact MvPowerSeries.constantCoeff_subst_eq_zero hab (fun i => by fin_cases i <;> simpa) hf

  set l := ψ (addSlope W) with hl
  set n := ψ (addIntercept W) with hn
  set b := ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) with hb
  set z₃ := ψ (thirdZ W) with hz₃
  set w₃ := ψ (thirdW W) with hw₃
  set e := ψ (MvPowerSeries.invOfUnit (negDen W) 1) with he
  have rl₁ : wAt W u₁ = l * u₁ + n := by
    have := congrArg ψ (wAt_X_zero_eq W)
    rwa [map_add, map_mul, ψw, ψX0] at this
  have rl₂ : wAt W u₂ = l * u₂ + n := by
    have := congrArg ψ (wAt_X_one_eq W)
    rwa [map_add, map_mul, ψw, ψX1] at this
  have rb : secantB (W.map MvPowerSeries.C) l * b = 1 := by
    rw [hl, hb]
    have := congrArg ψ (mul_invOfUnit_one (constantCoeff_secantB W))
    simpa only [secantB, map_add (f := _), map_mul, map_pow, map_one, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, ψC] using this
  have rz₃ : z₃ = -u₁ - u₂ - secantA (W.map MvPowerSeries.C) l n * b := by
    rw [hz₃, thirdZ, hl, hn, hb]
    simp only [secantA, map_sub, map_neg, map_mul, map_add (f := _), map_pow, map_ofNat, ψX0, ψX1, ψC,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  have rw₃ : w₃ = l * z₃ + n := by rw [hw₃, thirdW, map_add (f := _), map_mul]
  have re : (1 - MvPowerSeries.C W.a₁ * z₃ - MvPowerSeries.C W.a₃ * w₃) * e = 1 := by
    rw [hz₃, hw₃, he]
    have := congrArg ψ (mul_invOfUnit_one (constantCoeff_negDen W))
    simpa only [negDen, map_sub, map_mul, map_one, ψC] using this
  have rF : ψ (addSeries W) = -z₃ * e := by rw [addSeries, map_mul, map_neg]

  set V := curveFrac W τ with hV
  have hw₁ : ι (wAt W u₁) ≠ 0 := (map_ne_zero_iff ι hι).2 (wAt_ne_zero W h₁ hu₁)
  have hw₂ : ι (wAt W u₂) ≠ 0 := (map_ne_zero_iff ι hι).2 (wAt_ne_zero W h₂ hu₂)
  have hb' : secantB V (ι l) * ι b = 1 := by
    have := congrArg ι rb
    rwa [map_mul, map_secantB, map_one, map_C_map_algebraMap] at this
  have hx' : ι u₁ / ι (wAt W u₁) ≠ ι u₂ / ι (wAt W u₂) := by
    rw [Ne, div_eq_div_iff hw₁ hw₂]
    intro h
    apply hx
    apply hι
    rw [map_mul, map_mul]
    linear_combination h
  have hz₃' : ι z₃ = -ι u₁ - ι u₂ - secantA V (ι l) (ι n) * ι b := by
    rw [rz₃, map_sub, map_sub, map_neg, map_mul, map_secantA, map_C_map_algebraMap]
  have hw₃' : ι w₃ = ι l * ι z₃ + ι n := by rw [rw₃, map_add (f := _), map_mul]
  obtain ⟨h₃, hw₃0, hsum⟩ := secant_spec V (zwPoly_curveFrac W τ h₁) (zwPoly_curveFrac W τ h₂)
    hw₁ hw₂ (by rw [rl₁, map_add (f := _), map_mul]) (by rw [rl₂, map_add (f := _), map_mul]) hb' hx' hz₃' hw₃'
  have he' : (1 - V.a₁ * ι z₃ - V.a₃ * ι w₃) * ι e = 1 := by
    have := congrArg ι re
    rwa [map_mul, map_sub, map_sub, map_mul, map_mul, map_one] at this
  obtain ⟨h', hw', hneg⟩ := neg_zwPoint V h₃ hw₃0 he'

  have hF : MvPowerSeries.constantCoeff (ψ (addSeries W)) = 0 := hc0 _ (constantCoeff_addSeries W)
  have hS : zwPoly (W.map MvPowerSeries.C) (ψ (addSeries W)) (-w₃ * e) = 0 := by
    apply hι
    rw [map_zwPoly, map_C_map_algebraMap, map_zero, rF, map_mul, map_mul, map_neg, map_neg]
    exact h'
  have hwF : wAt W (ψ (addSeries W)) = -w₃ * e := by
    refine eq_of_zwPoly_eq_zero _ (zwPoly_wAt W hF) hS ?_
    refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
    have hw0 : MvPowerSeries.constantCoeff w₃ = 0 := hc0 _ (constantCoeff_thirdW W)
    simp [hF, constantCoeff_wAt W hF, hw0]
  unfold pointOf
  rw [hsum, hneg, hψ, hwF, rF, map_mul, map_mul, map_neg, map_neg]

end Points

section Lin

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {τ : Type*}

theorem coeff_single_X [DecidableEq τ] (i j : τ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.X j : MvPowerSeries τ R) =
      if i = j then 1 else 0 := by
  rw [MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg, if_neg h]
    intro h'
    exact h (Finsupp.single_left_injective one_ne_zero h')

theorem two_le_order_addSeries_sub' : (2 : ℕ∞) ≤ MvPowerSeries.order (addSeries W -
    (MvPowerSeries.C 1 * MvPowerSeries.X 0 + MvPowerSeries.C 1 * MvPowerSeries.X 1)) := by
  simpa using two_le_order_addSeries_sub W

theorem coeff_single_subst_addSeries [DecidableEq τ] {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0) (i : τ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (MvPowerSeries.subst ![u₁, u₂] (addSeries W)) =
      MvPowerSeries.coeff (Finsupp.single i 1) u₁ + MvPowerSeries.coeff (Finsupp.single i 1) u₂ := by
  rw [coeff_single_subst_pair (two_le_order_addSeries_sub' W) h₁ h₂, one_mul, one_mul]

theorem constantCoeff_subst_addSeries {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![u₁, u₂] (addSeries W)) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂)
    (fun i => by fin_cases i <;> simpa) (constantCoeff_addSeries W)

theorem subst_pair_gAt {u₁ u₂ : MvPowerSeries τ R} (h₁ : MvPowerSeries.constantCoeff u₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff u₂ = 0) (i : Fin 2) :
    MvPowerSeries.subst ![u₁, u₂] (gAt W (MvPowerSeries.X i)) = gAt W (![u₁, u₂] i) := by
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂
  rw [gAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst (PowerSeries.HasSubst.X i) hab,
    MvPowerSeries.subst_X hab, gAt]

theorem mul_wAt_ne [IsDomain R] {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (h12 : u₁ ≠ u₂)
    (hD : MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W)) ≠ 0) :
    u₁ * wAt W u₂ ≠ u₂ * wAt W u₁ := by
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair h₁ h₂
  have hg : gAt W u₂ - gAt W u₁ = (u₂ - u₁) * MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W)) := by
    have := congrArg (MvPowerSeries.subst ![u₁, u₂]) (gAt_X_one_sub_gAt_X_zero W)
    rwa [MvPowerSeries.subst_sub hab, MvPowerSeries.subst_mul hab, MvPowerSeries.subst_sub hab,
      MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab, subst_pair_gAt W h₁ h₂,
      subst_pair_gAt W h₁ h₂] at this
  rw [wAt_eq_mul_gAt W h₁, wAt_eq_mul_gAt W h₂]
  intro h
  have : u₁ * u₂ * ((u₂ - u₁) * MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W))) = 0 := by
    rw [← hg]; linear_combination h
  simp only [mul_eq_zero, hu₁, hu₂, hD, sub_eq_zero, false_or, or_false] at this
  exact h12 this.symm

theorem ne_zero_of_coeff_ne_zero {f : MvPowerSeries τ R} {d : τ →₀ ℕ}
    (h : MvPowerSeries.coeff d f ≠ 0) : f ≠ 0 := by
  rintro rfl; simp at h

end Lin

section Assoc

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R) [Fact (W.Δ ≠ 0)]

attribute [local instance] isDomain_mvPowerSeries


open scoped Classical in
open Classical in
theorem pointOf_add_of_coeff {τ : Type*} [Nonempty τ] {u₁ u₂ : MvPowerSeries τ R}
    (h₁ : MvPowerSeries.constantCoeff u₁ = 0) (h₂ : MvPowerSeries.constantCoeff u₂ = 0)
    {i₁ i₂ i₃ i₄ : τ} (hi₁ : MvPowerSeries.coeff (Finsupp.single i₁ 1) u₁ ≠ 0)
    (hi₂ : MvPowerSeries.coeff (Finsupp.single i₂ 1) u₂ ≠ 0)
    (hi₃ : MvPowerSeries.coeff (Finsupp.single i₃ 1) u₁ ≠
      MvPowerSeries.coeff (Finsupp.single i₃ 1) u₂)
    (hi₄ : MvPowerSeries.coeff (Finsupp.single i₄ 1) u₁ +
      MvPowerSeries.coeff (Finsupp.single i₄ 1) u₂ ≠ 0) :
    pointOf W τ u₁ + pointOf W τ u₂ =
      pointOf W τ (MvPowerSeries.subst ![u₁, u₂] (addSeries W)) := by
  have hu₁ := ne_zero_of_coeff_ne_zero hi₁
  have hu₂ := ne_zero_of_coeff_ne_zero hi₂
  have h12 : u₁ ≠ u₂ := fun h => hi₃ (by rw [h])
  have hD : MvPowerSeries.subst ![u₁, u₂] (divDiff (formalG W)) ≠ 0 := by
    refine ne_zero_of_coeff_ne_zero (d := Finsupp.single i₄ 1) ?_
    rw [coeff_single_subst_pair (two_le_order_divDiff_formalG W) h₁ h₂, one_mul, one_mul]
    exact hi₄
  exact pointOf_add W τ h₁ h₂ hu₁ hu₂ (mul_wAt_ne W h₁ h₂ hu₁ hu₂ h12 hD)

theorem addSeries_assoc_of_isDomain :
    MvPowerSeries.subst ![MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1] (addSeries W), MvPowerSeries.X 2] (addSeries W) =
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 2] (addSeries W)]
      (addSeries W) := by
  classical
  set Y : Fin 3 → MvPowerSeries (Fin 3) R := MvPowerSeries.X with hY
  have hc : ∀ i, MvPowerSeries.constantCoeff (Y i) = 0 := fun i => by simp [hY]
  have hA := constantCoeff_subst_addSeries W (hc 0) (hc 1)
  have hB := constantCoeff_subst_addSeries W (hc 1) (hc 2)
  have lA : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1)
      (MvPowerSeries.subst ![Y 0, Y 1] (addSeries W)) = (if i = 0 then 1 else 0) +
        (if i = 1 then 1 else 0) := fun i => by
    rw [coeff_single_subst_addSeries W (hc 0) (hc 1), hY, coeff_single_X, coeff_single_X]
  have lB : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1)
      (MvPowerSeries.subst ![Y 1, Y 2] (addSeries W)) = (if i = 1 then 1 else 0) +
        (if i = 2 then 1 else 0) := fun i => by
    rw [coeff_single_subst_addSeries W (hc 1) (hc 2), hY, coeff_single_X, coeff_single_X]
  have lY : ∀ i j, MvPowerSeries.coeff (Finsupp.single i 1) (Y j) = if i = j then 1 else 0 :=
    fun i j => by rw [hY, coeff_single_X]
  have e01 := pointOf_add_of_coeff W (hc 0) (hc 1) (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0)
    (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])
  have e12 := pointOf_add_of_coeff W (hc 1) (hc 2) (i₁ := 1) (i₂ := 2) (i₃ := 1) (i₄ := 1)
    (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])
  have eL := pointOf_add_of_coeff W hA (hc 2) (i₁ := 0) (i₂ := 2) (i₃ := 0) (i₄ := 0)
    (by simp [lA]) (by simp [lY]) (by simp [lA, lY]) (by simp [lA, lY])
  have eR := pointOf_add_of_coeff W (hc 0) hB (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0)
    (by simp [lY]) (by simp [lB]) (by simp [lB, lY]) (by simp [lB, lY])
  have hL := constantCoeff_subst_addSeries W hA (hc 2)
  have hR := constantCoeff_subst_addSeries W (hc 0) hB
  refine pointOf_injective W (Fin 3) hL hR ?_ ?_ ?_
  · refine ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_
    rw [coeff_single_subst_addSeries W hA (hc 2), lA, lY]; simp
  · refine ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_
    rw [coeff_single_subst_addSeries W (hc 0) hB, lB, lY]; simp
  · rw [← eL, ← eR, ← e01, ← e12, add_assoc]

theorem addSeries_comm_of_isDomain :
    addSeries W = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (addSeries W) := by
  classical
  have hc : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) = 0 :=
    fun i => by simp
  have lY : ∀ i j : Fin 2, MvPowerSeries.coeff (Finsupp.single i 1)
      (MvPowerSeries.X j : MvPowerSeries (Fin 2) R) = if i = j then 1 else 0 :=
    fun i j => coeff_single_X i j
  have e01 := pointOf_add_of_coeff W (hc 0) (hc 1) (i₁ := 0) (i₂ := 1) (i₃ := 0) (i₄ := 0)
    (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])
  have e10 := pointOf_add_of_coeff W (hc 1) (hc 0) (i₁ := 1) (i₂ := 0) (i₃ := 0) (i₄ := 0)
    (by simp [lY]) (by simp [lY]) (by simp [lY]) (by simp [lY])
  rw [GroundTheory.LocalField.FormalGroup.subst_X_X] at e01
  have h01 := constantCoeff_addSeries W
  have h10 := constantCoeff_subst_addSeries W (hc 1) (hc 0)
  refine pointOf_injective W (Fin 2) h01 h10 ?_ ?_ ?_
  · refine ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_
    have := coeff_single_subst_addSeries W (hc 0) (hc 1) 0
    rw [GroundTheory.LocalField.FormalGroup.subst_X_X] at this
    rw [this, lY, lY]; simp
  · refine ne_zero_of_coeff_ne_zero (d := Finsupp.single 0 1) ?_
    rw [coeff_single_subst_addSeries W (hc 1) (hc 0), lY, lY]; simp
  · rw [← e01, ← e10, add_comm]

end Assoc

section FormalGroupLaw

def univCurve : WeierstrassCurve (MvPolynomial (Fin 5) ℤ) :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

theorem univCurve_Δ_ne_zero : univCurve.Δ ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.eval ![(0 : ℤ), 0, 1, 0, 0]) h
  rw [← WeierstrassCurve.map_Δ, map_zero] at h'
  have e : univCurve.map (MvPolynomial.eval ![(0 : ℤ), 0, 1, 0, 0]) = ⟨0, 0, 1, 0, 0⟩ := by
    ext <;> simp [univCurve]
  rw [e] at h'
  norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at h'

instance : Fact (univCurve.Δ ≠ 0) := ⟨univCurve_Δ_ne_zero⟩

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def univMap : MvPolynomial (Fin 5) ℤ →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem univCurve_map : univCurve.map (univMap W) = W := by
  ext <;> simp [univCurve, univMap]

theorem addSeries_eq_map : addSeries W = MvPowerSeries.map (univMap W) (addSeries univCurve) := by
  rw [map_addSeries, univCurve_map]

theorem coeff_single_addSeries (i : Fin 2) :
    MvPowerSeries.coeff (Finsupp.single i 1) (addSeries W) = 1 := by
  classical
  have h := MvPowerSeries.coeff_of_lt_order (d := Finsupp.single i 1)
    (lt_of_lt_of_le (by simp) (two_le_order_addSeries_sub W))
  rw [map_sub, sub_eq_zero] at h
  rw [h, map_add (f := _), coeff_single_X, coeff_single_X]
  fin_cases i <;> simp

def univFormalGroup : FormalGroup (MvPolynomial (Fin 5) ℤ) where
  toPowerSeries := addSeries univCurve
  zero_constantCoeff := constantCoeff_addSeries _
  lin_coeff_X := coeff_single_addSeries _ 0
  lin_coeff_Y := coeff_single_addSeries _ 1
  assoc := addSeries_assoc_of_isDomain univCurve

def formalGroup : FormalGroup R where
  toPowerSeries := addSeries W
  zero_constantCoeff := constantCoeff_addSeries W
  lin_coeff_X := coeff_single_addSeries W 0
  lin_coeff_Y := coeff_single_addSeries W 1
  assoc := by
    have := (univFormalGroup.map (univMap W)).assoc
    rwa [FormalGroup.map_toPowerSeries, univFormalGroup, ← addSeries_eq_map] at this

@[simp]
theorem formalGroup_toPowerSeries : (formalGroup W).toPowerSeries = addSeries W := rfl

instance : (formalGroup W).IsComm where
  comm := by
    change addSeries W = MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] (addSeries W)
    have hs : MvPowerSeries.HasSubst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) (MvPolynomial (Fin 5) ℤ)), MvPowerSeries.X 0] :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by fin_cases i <;> simp
    conv_lhs => rw [addSeries_eq_map, addSeries_comm_of_isDomain univCurve]
    rw [MvPowerSeries.map_subst hs, ← addSeries_eq_map]
    congr 1
    funext i
    fin_cases i <;> simp

end FormalGroupLaw

end

end GroundTheory.Arith.Abelian
end

namespace GroundTheory.Arith.Abelian

noncomputable section

section Neg

variable {A : Type*} [CommRing A] (V : WeierstrassCurve A)

theorem zwPoly_neg_mul {z w e : A} (he : (1 - V.a₁ * z - V.a₃ * w) * e = 1) :
    zwPoly V (-z * e) (-w * e) = -e ^ 3 * zwPoly V z w := by
  unfold zwPoly
  linear_combination (-e * w * (e + 1)) * he

end Neg

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

section Apply

variable {T : Type*} [CommRing T] [Algebra R T] (ψ : MvPowerSeries (Fin 2) R →ₐ[R] T)

theorem algHom_C (r : R) : ψ (MvPowerSeries.C r) = algebraMap R T r := by
  have : MvPowerSeries.C r = algebraMap R (MvPowerSeries (Fin 2) R) r := by
    rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [this, ψ.commutes]

theorem map_C_algHom :
    (W.map (MvPowerSeries.C (σ := Fin 2))).map (ψ : MvPowerSeries (Fin 2) R →+* T) =
      W.map (algebraMap R T) := by
  rw [WeierstrassCurve.map_map]
  congr 1
  ext r
  exact algHom_C ψ r

theorem apply_wAt_X_zero :
    ψ (wAt W (MvPowerSeries.X 0)) = ψ (addSlope W) * ψ (MvPowerSeries.X 0) + ψ (addIntercept W) := by
  rw [wAt_X_zero_eq, map_add (f := _), map_mul]

theorem apply_wAt_X_one :
    ψ (wAt W (MvPowerSeries.X 1)) = ψ (addSlope W) * ψ (MvPowerSeries.X 1) + ψ (addIntercept W) := by
  rw [wAt_X_one_eq, map_add (f := _), map_mul]

theorem zwPoly_apply_wAt_X (i : Fin 2) :
    zwPoly (W.map (algebraMap R T)) (ψ (MvPowerSeries.X i)) (ψ (wAt W (MvPowerSeries.X i))) = 0 := by
  have := congrArg (ψ : MvPowerSeries (Fin 2) R →+* T)
    (zwPoly_wAt W (MvPowerSeries.constantCoeff_X (R := R) i))
  rwa [map_zwPoly, map_zero, map_C_algHom] at this

theorem secantB_apply_mul :
    secantB (W.map (algebraMap R T)) (ψ (addSlope W)) *
      ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) = 1 := by
  have := congrArg (ψ : MvPowerSeries (Fin 2) R →+* T) (mul_invOfUnit_one (constantCoeff_secantB W))
  rwa [map_mul, map_one, map_secantB, map_C_algHom] at this

theorem apply_thirdZ :
    ψ (thirdZ W) = -ψ (MvPowerSeries.X 0) - ψ (MvPowerSeries.X 1) -
      secantA (W.map (algebraMap R T)) (ψ (addSlope W)) (ψ (addIntercept W)) *
        ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) := by
  have h := map_secantA (W.map (MvPowerSeries.C (σ := Fin 2))) (ψ : MvPowerSeries (Fin 2) R →+* T)
    (addSlope W) (addIntercept W)
  rw [map_C_algHom] at h
  have h' : ψ (secantA (W.map MvPowerSeries.C) (addSlope W) (addIntercept W)) =
      secantA (W.map (algebraMap R T)) (ψ (addSlope W)) (ψ (addIntercept W)) := h
  rw [thirdZ, map_sub, map_sub, map_neg, map_mul, h']

theorem apply_thirdW : ψ (thirdW W) = ψ (addSlope W) * ψ (thirdZ W) + ψ (addIntercept W) := by
  rw [thirdW, map_add (f := _), map_mul]

theorem negDen_apply_mul :
    (1 - algebraMap R T W.a₁ * ψ (thirdZ W) - algebraMap R T W.a₃ * ψ (thirdW W)) *
      ψ (MvPowerSeries.invOfUnit (negDen W) 1) = 1 := by
  have := congrArg ψ (mul_invOfUnit_one (constantCoeff_negDen W))
  rwa [map_mul, map_one, negDen, map_sub, map_sub, map_one, map_mul, map_mul, algHom_C,
    algHom_C] at this

theorem apply_addSeries :
    ψ (addSeries W) = -ψ (thirdZ W) * ψ (MvPowerSeries.invOfUnit (negDen W) 1) := by
  rw [addSeries, map_mul, map_neg]

end Apply

section Inverse

def invDen : PowerSeries R :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * formalW W

theorem constantCoeff_invDen : MvPowerSeries.constantCoeff (invDen W) = 1 := by
  have h : MvPowerSeries.constantCoeff (formalW W) = 0 := constantCoeff_formalW W
  simp [invDen, PowerSeries.C_apply, h, PowerSeries.X]

def invSeries : PowerSeries R :=
  -PowerSeries.X * MvPowerSeries.invOfUnit (invDen W) 1

theorem constantCoeff_invSeries : MvPowerSeries.constantCoeff (invSeries W) = 0 := by
  simp [invSeries, PowerSeries.X]

theorem wAt_X_unit : wAt W (PowerSeries.X : PowerSeries R) = formalW W :=
  PowerSeries.X_subst _

theorem wAt_invSeries :
    wAt W (invSeries W) = -formalW W * MvPowerSeries.invOfUnit (invDen W) 1 := by
  set e := MvPowerSeries.invOfUnit (invDen W) 1 with he_def
  have he : (1 - (W.map MvPowerSeries.C).a₁ * (PowerSeries.X : PowerSeries R) -
      (W.map MvPowerSeries.C).a₃ * formalW W) * e = 1 :=
    mul_invOfUnit_one (constantCoeff_invDen W)
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
    PowerSeries.constantCoeff_X
  have h0 : zwPoly (W.map MvPowerSeries.C) PowerSeries.X (formalW W) = 0 := by
    have := zwPoly_wAt W hX
    rwa [wAt_X_unit] at this
  have hneg := zwPoly_neg_mul (W.map MvPowerSeries.C) he
  rw [h0, mul_zero] at hneg
  have hi := constantCoeff_invSeries W
  refine eq_of_zwPoly_eq_zero _ (zwPoly_wAt W hi) hneg ?_
  refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
  have hw : MvPowerSeries.constantCoeff (formalW W) = 0 := constantCoeff_formalW W
  simp [hi, constantCoeff_wAt W hi, hw]

theorem map_invDen {S : Type*} [CommRing S] (f : R →+* S) :
    MvPowerSeries.map f (invDen W) = invDen (W.map f) := by
  have h : MvPowerSeries.map f (formalW W) = formalW (W.map f) := map_formalW W f
  simp only [invDen, map_sub, map_one, map_mul, h, PowerSeries.C_apply, MvPowerSeries.map_C,
    PowerSeries.X, MvPowerSeries.map_X, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]

theorem map_invSeries {S : Type*} [CommRing S] (f : R →+* S) :
    MvPowerSeries.map f (invSeries W) = invSeries (W.map f) := by
  rw [invSeries, map_mul, map_neg, map_invOfUnit_one f (constantCoeff_invDen W), map_invDen,
    invSeries, PowerSeries.X, MvPowerSeries.map_X]
  rfl

theorem subst_X_invSeries_of_isDomain [IsDomain R] (h2 : (2 : R) ≠ 0) :
    MvPowerSeries.subst ![PowerSeries.X, invSeries W] (addSeries W) = (0 : PowerSeries R) := by
  have hX : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries R) = 0 :=
    PowerSeries.constantCoeff_X
  have hi := constantCoeff_invSeries W
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair hX hi
  set ψ := MvPowerSeries.substAlgHom (R := R) hab with hψdef
  have hψ : ∀ f, MvPowerSeries.subst ![PowerSeries.X, invSeries W] f = ψ f := fun f => by
    rw [hψdef, MvPowerSeries.coe_substAlgHom]
  have ψX0 : ψ (MvPowerSeries.X 0) = PowerSeries.X := by
    rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψX1 : ψ (MvPowerSeries.X 1) = invSeries W := by
    rw [← hψ, MvPowerSeries.subst_X hab]; rfl
  have ψw : ∀ i, ψ (wAt W (MvPowerSeries.X i)) = wAt W (![PowerSeries.X, invSeries W] i) :=
    fun i => by
      rw [← hψ, wAt, GroundTheory.LocalField.FormalGroup.subst_powerSeries_subst
        (PowerSeries.HasSubst.X i) hab, MvPowerSeries.subst_X hab, wAt]
  set V := W.map (algebraMap R (PowerSeries R)) with hV
  set u : PowerSeries R := PowerSeries.X with hu
  set e := MvPowerSeries.invOfUnit (invDen W) 1 with he
  set w := formalW W with hw
  set l := ψ (addSlope W) with hl
  set n := ψ (addIntercept W) with hn
  set b := ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1) with hb
  have hu' : invSeries W = -u * e := rfl
  have r₁ : w = l * u + n := by
    have := apply_wAt_X_zero W ψ
    rwa [ψw, ψX0, Matrix.cons_val_zero, wAt_X_unit] at this
  have r₂ : -w * e = l * invSeries W + n := by
    have := apply_wAt_X_one W ψ
    rwa [ψw, ψX1, Matrix.cons_val_one, Matrix.cons_val_fin_one, wAt_invSeries] at this
  have he1 : e + 1 ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    simp [he, MvPowerSeries.constantCoeff_invOfUnit] at this
    exact h2 (by linear_combination this)
  have hlu : l * u = w := by
    have h : (e + 1) * (l * u - w) = 0 := by rw [hu'] at r₂; linear_combination r₂ - r₁
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left he1)
  have hn0 : n = 0 := by linear_combination -r₁ - hlu
  have z₁ : zwPoly V u w = 0 := by
    have := zwPoly_apply_wAt_X W ψ 0
    rwa [ψw, ψX0, Matrix.cons_val_zero, wAt_X_unit] at this
  have z₂ : zwPoly V (invSeries W) (-w * e) = 0 := by
    have := zwPoly_apply_wAt_X W ψ 1
    rwa [ψw, ψX1, Matrix.cons_val_one, Matrix.cons_val_fin_one, wAt_invSeries] at this
  have hcub : ∀ t, zwPoly V t (l * t) =
      t * (secantB V l * t ^ 2 + secantA V l n * t - l) := by
    intro t; simp only [zwPoly, secantB, secantA, hn0]; ring
  have q₁ : u * (secantB V l * u ^ 2 + secantA V l n * u - l) = 0 := by
    rw [← hcub, hlu, z₁]
  have q₂ : invSeries W * (secantB V l * invSeries W ^ 2 + secantA V l n * invSeries W - l) = 0 := by
    rw [← hcub, ← z₂]; congr 1; linear_combination -r₂ - hn0
  have hu0 : u ≠ 0 := PowerSeries.X_ne_zero
  have heu : IsUnit e := by
    refine MvPowerSeries.isUnit_iff_constantCoeff.2 ?_
    simp [he, MvPowerSeries.constantCoeff_invOfUnit]
  have hu'0 : invSeries W ≠ 0 := by
    rw [hu']; exact mul_ne_zero (neg_ne_zero.2 hu0) heu.ne_zero
  have p₁ := (mul_eq_zero.1 q₁).resolve_left hu0
  have p₂ := (mul_eq_zero.1 q₂).resolve_left hu'0
  have hd : u - invSeries W ≠ 0 := by
    rw [hu', show u - -u * e = u * (e + 1) by ring]
    exact mul_ne_zero hu0 he1
  have hs : secantB V l * (u + invSeries W) + secantA V l n = 0 := by
    have : (u - invSeries W) * (secantB V l * (u + invSeries W) + secantA V l n) = 0 := by
      linear_combination p₁ - p₂
    exact (mul_eq_zero.1 this).resolve_left hd
  have rb := secantB_apply_mul W ψ
  have hz : ψ (thirdZ W) = 0 := by
    rw [apply_thirdZ, ψX0, ψX1]
    linear_combination (u + invSeries W) * rb - b * hs
  rw [hψ, apply_addSeries, hz, neg_zero, zero_mul]

theorem two_ne_zero_univ : (2 : MvPolynomial (Fin 5) ℤ) ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (0 : Fin 5 → ℤ)) h
  rw [map_ofNat, map_zero] at this
  norm_num at this

theorem subst_X_invSeries :
    MvPowerSeries.subst ![PowerSeries.X, invSeries W] (addSeries W) = (0 : PowerSeries R) := by
  have h := congrArg (MvPowerSeries.map (univMap W))
    (subst_X_invSeries_of_isDomain univCurve two_ne_zero_univ)
  have hX : MvPowerSeries.constantCoeff
      (PowerSeries.X : PowerSeries (MvPolynomial (Fin 5) ℤ)) = 0 := PowerSeries.constantCoeff_X
  have hab := GroundTheory.LocalField.FormalGroup.hasSubst_pair hX (constantCoeff_invSeries univCurve)
  rw [MvPowerSeries.map_subst hab, map_zero] at h
  rw [← h, addSeries_eq_map]
  congr 1
  funext i
  fin_cases i
  · simp [PowerSeries.X, MvPowerSeries.map_X]
  · simp [map_invSeries, univCurve_map]

theorem inv_formalGroup : GroundTheory.LocalField.FormalGroup.inv (formalGroup W) = invSeries W :=
  (GroundTheory.LocalField.FormalGroup.eq_inv_of_subst_eq_zero _ (constantCoeff_invSeries W)
    (subst_X_invSeries W)).symm

end Inverse

end

end GroundTheory.Arith.Abelian
