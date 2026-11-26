module

public import Formalism.EllipticTorsion.EllipticTorsionProofs.IntegralPSBserSubOne
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CoefficientWeightsLemmaTwo
public import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsSumPowPrimePow
public import Formalism.EllipticTorsion.EllipticTorsionProofs.VeluUSeries
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeTwo
public import Formalism.EllipticTorsion.EllipticTorsionProofs.CubeThree

@[expose] public section

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.UnitCancel
universe u

noncomputable section

namespace Formalism.ELL

open Formalism.G

theorem unit_cancellation : Formalism.ELL.UnitCancel.{u} := by
  intro p _ K _ _ _ _ σ G b hb h
  obtain ⟨u, rfl⟩ := hb
  have := Formalism.ELL.N_padic_integer_smul p K σ _ h ((u⁻¹ : (ℤ_[p])ˣ) : ℤ_[p])
  convert this using 1
  rw [smul_smul, ← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, inv_mul_cancel]
  simp

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsSubgroupHolds
noncomputable section

universe u

namespace Formalism.ELL.FormalGroupPointsSubgroup

open WeierstrassCurve Polynomial

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma add_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c := by
  exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma sub_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact add_le ha (by rwa [norm_neg])

lemma le_sub_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a‖ ≤ ‖a - b‖ := by
  have h1 : ‖a‖ ≤ max ‖a - b‖ ‖b‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (a - b) b
  rcases le_max_iff.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 (not_le.mpr h)

lemma mul_le {a b : K} {c d : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ d) : ‖a * b‖ ≤ c * d := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

lemma y_int (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) : ‖y‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    refine add_le (add_le (add_le hx3 ?_) ?_) h6
    · simpa using mul_le h2 hx2
    · simpa using mul_le h4 hx
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 hx) (le_refl ‖y‖)
    · simpa using mul_le h3 (le_refl ‖y‖)
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  nlinarith

lemma y_sq_le (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖y‖ ^ 2 ≤ ‖x‖ ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hx0 : (0 : ℝ) < ‖x‖ := by linarith
  have hx2 : ‖x‖ ^ 2 < ‖x‖ ^ 3 := by
    nlinarith [mul_pos (mul_pos hx0 hx0) (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hx1 : ‖x‖ ≤ ‖x‖ ^ 3 := by
    nlinarith [mul_pos hx0 (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hxy : ‖x‖ < ‖y‖ := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul hc hc (norm_nonneg y) hx0.le
    nlinarith
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 3 := by
    refine add_le (add_le (add_le (le_of_eq (norm_pow _ _)) ?_) ?_) ?_
    · exact (mul_le h2 (le_of_eq (norm_pow x 2))).trans (by linarith)
    · exact (mul_le h4 (le_refl ‖x‖)).trans (by linarith)
    · exact h6.trans (one_le_pow₀ hx.le)
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖x‖ * ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 (le_refl ‖x‖)) (le_refl ‖y‖)
    · exact (mul_le h3 (le_refl ‖y‖)).trans (by nlinarith [norm_nonneg y])
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg y]
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  linarith

lemma addX_norm [DecidableEq K] (W : WeierstrassCurve K) (hW : IntegralModel W)
    {x₁ x₂ y₁ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) (hx₁ : 1 < ‖x₁‖) (hx₂ : 1 < ‖x₂‖) :
    1 < ‖W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)‖ := by
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  set x₃ := W.toAffine.addX x₁ x₂ ℓ with hx₃
  set y₃ := W.toAffine.negAddY x₁ x₂ y₁ ℓ with hy₃
  by_contra hC
  push Not at hC
  have h₃ : W.toAffine.Equation x₃ y₃ := Affine.equation_negAdd h₁ h₂ hxy
  have hy3 : ‖y₃‖ ≤ 1 := y_int W hW h₃ hC
  have hpoly := Affine.addPolynomial_slope h₁ h₂ hxy
  rw [← hℓ] at hpoly
  have hev := congrArg (Polynomial.eval (x₃ + 1)) hpoly
  simp only [Affine.addPolynomial, Affine.linePolynomial, Affine.polynomial] at hev
  simp at hev
  have hx3def : x₃ = ℓ ^ 2 + W.toAffine.a₁ * ℓ - W.toAffine.a₂ - x₁ - x₂ := by simp [hx₃]
  rw [← hx3def] at hev
  obtain ⟨a1, a2, a3, a4, a6⟩ := hW

  have hy3def : y₃ = ℓ * (x₃ - x₁) + y₁ := by simp [hy₃, hx₃]
  have hx0 : 0 ≤ ‖x₁‖ := norm_nonneg _
  have hℓ0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hsq := y_sq_le W ⟨a1, a2, a3, a4, a6⟩ h₁ hx₁
  have hd : ‖x₁‖ ≤ ‖x₁ - x₃‖ := le_sub_of_lt (by linarith)
  have hlin : ‖ℓ‖ * ‖x₁‖ ≤ max ‖y₁‖ 1 := by
    have e : ℓ * (x₁ - x₃) = y₁ - y₃ := by rw [hy3def]; ring
    have : ‖ℓ * (x₁ - x₃)‖ ≤ max ‖y₁‖ 1 := by
      rw [e]; exact sub_le (le_max_left _ _) (hy3.trans (le_max_right _ _))
    rw [norm_mul] at this
    nlinarith
  have hℓsq : ‖ℓ‖ ^ 2 ≤ ‖x₁‖ := by
    have hm : (max ‖y₁‖ 1) ^ 2 ≤ ‖x₁‖ ^ 3 := by
      rcases le_total ‖y₁‖ 1 with h | h
      · rw [max_eq_right h, one_pow]; exact one_le_pow₀ hx₁.le
      · rw [max_eq_left h]; exact hsq
    have : (‖ℓ‖ * ‖x₁‖) ^ 2 ≤ ‖x₁‖ ^ 3 :=
      (pow_le_pow_left₀ (by positivity) hlin 2).trans hm
    have hx1p : 0 < ‖x₁‖ ^ 2 := by positivity
    nlinarith

  set M := max 1 ‖ℓ‖ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMℓ : ‖ℓ‖ ≤ M := le_max_right _ _
  have hMsq : M ^ 2 ≤ ‖x₁‖ := by
    rcases le_total 1 ‖ℓ‖ with h | h
    · rw [hM, max_eq_right h]; exact hℓsq
    · rw [hM, max_eq_left h]; nlinarith
  have ht : ‖x₃ + 1‖ ≤ 1 := add_le hC (by simp)
  have hu : ‖ℓ * (x₃ + 1 - x₁) + y₁‖ ≤ M := by
    have e : ℓ * (x₃ + 1 - x₁) + y₁ = y₃ + ℓ := by rw [hy3def]; ring
    rw [e]; exact add_le (hy3.trans hM1) hMℓ
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hLHS : ‖(ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆)‖ ≤ ‖x₁‖ := by
    have ht2 : ‖(x₃ + 1) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have ht3 : ‖(x₃ + 1) ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have hc : ‖(x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆‖ ≤ 1 := by
      refine add_le (add_le (add_le ht3 ?_) ?_) a6
      · simpa using mul_le a2 ht2
      · simpa using mul_le a4 ht
    refine sub_le (add_le (add_le ?_ ?_) ?_) (hc.trans (by nlinarith))
    · rw [norm_pow]; exact (pow_le_pow_left₀ (norm_nonneg _) hu 2).trans hMsq
    · have := mul_le (mul_le a1 ht) hu
      linarith
    · have := mul_le a3 hu
      linarith

  have hRHS : ‖x₁‖ * ‖x₂‖ ≤ ‖(x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)‖ := by
    have e1 : ‖x₁‖ ≤ ‖x₃ + 1 - x₁‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e2 : ‖x₂‖ ≤ ‖x₃ + 1 - x₂‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e3 : x₃ + 1 - x₃ = 1 := by ring
    rw [e3, mul_one, norm_mul]
    exact mul_le_mul e1 e2 (norm_nonneg _) (norm_nonneg _)
  have heq : (ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆) =
      -((x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)) := by
    linear_combination hev
  rw [heq, norm_neg] at hLHS
  have := hRHS.trans hLHS
  nlinarith

end Formalism.ELL.FormalGroupPointsSubgroup

namespace Formalism.ELL

open WeierstrassCurve

open Classical in
theorem formal_group_points_subgroup_holds : Formalism.ELL.FormalGroupPointsSubgroup' := by
  intro K _ _ W hW _ P Q hP hQ
  refine ⟨?_, ?_⟩
  · rcases P with _ | @⟨x₁, y₁, h₁⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, zero_add]; exact hQ
    rcases Q with _ | @⟨x₂, y₂, h₂⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, add_zero]; exact hP
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
      trivial
    · rw [Affine.Point.add_some hxy]
      exact FormalGroupPointsSubgroup.addX_norm W hW h₁.1 h₂.1 hxy hP hQ
  · rcases P with _ | @⟨x, y, h⟩
    · trivial
    · simpa [InFormalGroupPoints] using hP

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.VeluInt
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace VeluIntegrality

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def ball : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rwa [norm_neg]

theorem veluGx_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGx W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGx
  refine sub_mem (add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx 2))
    (mul_mem (mul_mem (ofNat_mem _ 2) h2) hx)) h4) (mul_mem h1 hy)

theorem veluGy_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGy W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGy
  exact sub_mem (sub_mem (mul_mem (neg_mem (ofNat_mem _ 2)) hy) (mul_mem h1 hx)) h3

theorem veluV_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluV W x y ∈ (ball : Subring K) := by
  have gx := veluGx_mem W hW hx hy
  have gy := veluGy_mem W hW hx hy
  unfold veluV
  split_ifs
  · exact gx
  · exact sub_mem (mul_mem (ofNat_mem _ 2) gx) (mul_mem hW.1 gy)

theorem veluU_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluU W x y ∈ (ball : Subring K) := by
  unfold veluU
  exact pow_mem (veluGy_mem W hW hx hy) 2

end VeluIntegrality

open VeluIntegrality in
theorem velu_integral_model : VeluIntegralModel := by
  intro K _ _ W k S hW hS
  have hx : ∀ i, (S i).1 ∈ (ball : Subring K) := fun i => (hS i).1
  have hy : ∀ i, (S i).2 ∈ (ball : Subring K) := fun i => (hS i).2
  have hv : (∑ i, veluV W (S i).1 (S i).2) ∈ (ball : Subring K) :=
    sum_mem fun i _ => veluV_mem W hW (hx i) (hy i)
  have hw : (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2))
      ∈ (ball : Subring K) :=
    sum_mem fun i _ => add_mem (veluU_mem W hW (hx i) (hy i))
      (mul_mem (hx i) (veluV_mem W hW (hx i) (hy i)))
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · show W.a₄ - 5 * (∑ i, veluV W (S i).1 (S i).2) ∈ (ball : Subring K)
    exact sub_mem h4 (mul_mem (ofNat_mem _ 5) hv)
  · show W.a₆ - (W.a₁ ^ 2 + 4 * W.a₂) * (∑ i, veluV W (S i).1 (S i).2)
      - 7 * (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2)) ∈ (ball : Subring K)
    exact sub_mem (sub_mem h6 (mul_mem (add_mem (pow_mem h1 2) (mul_mem (ofNat_mem _ 4) h2)) hv))
      (mul_mem (ofNat_mem _ 7) hw)

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.ModelUnitOf
universe u

namespace Formalism.ELL.unitAtAlt

open Formalism.ELL

lemma two_or_three {K : Type u} [NormedField K] [IsUltrametricDist K] :
    ‖(2 : K)‖ = 1 ∨ ‖(3 : K)‖ = 1 := by
  have h2 : ‖(2 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 2
  have h3 : ‖(3 : K)‖ ≤ 1 := by
    simpa using IsUltrametricDist.norm_natCast_le_one K 3
  have h1 : ‖(1 : K)‖ ≤ max ‖(3 : K)‖ ‖(2 : K)‖ := by
    have : (1 : K) = 3 + -2 := by norm_num
    rw [this]
    simpa [norm_neg] using IsUltrametricDist.norm_add_le_max (3 : K) (-2)
  rw [norm_one] at h1
  by_cases h : ‖(2 : K)‖ = 1
  · exact Or.inl h
  · right
    have hlt : ‖(2 : K)‖ < 1 := lt_of_le_of_ne h2 h
    rcases le_max_iff.mp h1 with h' | h'
    · exact le_antisymm h3 h'
    · exact absurd h' (not_le.mpr hlt)

lemma of_model {K : Type u} [NormedField K] (W : WeierstrassCurve K) (j : K)
    (hI : IntegralModel W) (hc : W.c₄ ^ 3 = j * W.Δ) (hΔ : ‖W.Δ‖ = 1) :
    ∃ (W : WeierstrassCurve K) (_ : W.IsElliptic),
      IntegralModel W ∧ ‖W.Δ‖ = 1 ∧ W.j = j := by
  have hne : W.Δ ≠ 0 := by
    intro h; rw [h, norm_zero] at hΔ; exact zero_ne_one hΔ
  have : W.IsElliptic := ⟨hne.isUnit⟩
  refine ⟨W, inferInstance, hI, hΔ, ?_⟩
  rw [WeierstrassCurve.j, hc, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  field_simp

end Formalism.ELL.unitAtAlt

namespace Formalism.ELL

open Formalism.ELL.unitAtAlt

theorem modelUnit_of (hL : Formalism.ELL.ModelLegendre.{u}) (hD : Formalism.ELL.ModelDeuring.{u}) :
    Formalism.ELL.ModelUnit.{u} := by
  intro K _ _ _ j hj
  rcases two_or_three (K := K) with h2 | h3
  · obtain ⟨l, hl, _hl1, hc, hΔ⟩ := hL K h2 j hj
    refine of_model (legendre l) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [legendre]
    · simp
    · rw [norm_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      simp [hl]
    · simp
    · exact hl.le
    · simp
  · obtain ⟨a, ha, hc, hΔ⟩ := hD K h3 j hj
    refine of_model (deuring a) j ?_ hc hΔ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [deuring]
    · exact ha
    all_goals simp

end Formalism.ELL
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.ConstantCoeffLogOnePlus
noncomputable section

namespace Formalism.ELL.EulerSeries

open Formalism.G Formalism.ELL

variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]

def eulFun (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun d => (d.degree : K) * MvPowerSeries.coeff d F

theorem coeff_eulFun (F : MvPowerSeries σ K) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (eulFun F) = (d.degree : K) * MvPowerSeries.coeff d F := rfl

def eulLin : MvPowerSeries σ K →ₗ[K] MvPowerSeries σ K where
  toFun := eulFun
  map_add' F G := by
    ext d
    simp only [coeff_eulFun, map_add (f := _), mul_add]
  map_smul' c F := by
    ext d
    simp only [coeff_eulFun, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

theorem eulFun_mul (F G : MvPowerSeries σ K) :
    eulFun (F * G) = F • eulFun G + G • eulFun F := by
  ext d
  rw [smul_eq_mul, smul_eq_mul, mul_comm G, map_add (f := _), coeff_eulFun, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [coeff_eulFun, coeff_eulFun, ← hp, map_add (f := _), Nat.cast_add]
  ring

def eul : Derivation K (MvPowerSeries σ K) (MvPowerSeries σ K) :=
  Derivation.mk' eulLin fun a b => eulFun_mul a b

theorem eul_apply (F : MvPowerSeries σ K) : eul F = eulFun F := rfl

theorem eq_zero_of_eulFun (F : MvPowerSeries σ K) (h0 : MvPowerSeries.constantCoeff F = 0)
    (h : eulFun F = 0) : F = 0 := by
  ext d
  rw [map_zero]
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact h0
  · have h1 := congrArg (MvPowerSeries.coeff d) h
    rw [coeff_eulFun, map_zero] at h1
    have hdeg : ((d.degree : ℕ) : K) ≠ 0 := by
      rw [Nat.cast_ne_zero]
      exact fun h' => hd ((Finsupp.degree_eq_zero_iff d).mp h')
    exact (mul_eq_zero.mp h1).resolve_left hdeg

def Agree (N : ℕ) (F G : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < N → MvPowerSeries.coeff d F = MvPowerSeries.coeff d G

theorem Agree.mul_right {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G)
    (H : MvPowerSeries σ K) : Agree N (F * H) (G * H) := by
  intro d hd
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have hdeg := congrArg Finsupp.degree hp
  rw [map_add (f := _)] at hdeg
  rw [h p.1 (by omega)]

theorem Agree.eulFun {N : ℕ} {F G : MvPowerSeries σ K} (h : Agree N F G) :
    Agree N (eulFun F) (eulFun G) := by
  intro d hd
  rw [coeff_eulFun, coeff_eulFun, h d hd]

theorem coeff_pow_eq_zero {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    ∀ (n : ℕ) (d : σ →₀ ℕ), d.degree < n → MvPowerSeries.coeff d (f ^ n) = 0
  | 0, d, hd => absurd hd (Nat.not_lt_zero _)
  | n + 1, d, hd => by
    rw [pow_succ', MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hdeg := congrArg Finsupp.degree hp
    rw [map_add (f := _)] at hdeg
    by_cases h1 : p.1 = 0
    · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
    · have : 0 < p.1.degree :=
        Nat.pos_of_ne_zero (fun h => h1 ((Finsupp.degree_eq_zero_iff _).mp h))
      rw [coeff_pow_eq_zero hf n p.2 (by omega), mul_zero]

def truncLog (N : ℕ) (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  ∑ n ∈ Finset.range N, PowerSeries.coeff n (PowerSeries.log K) • f ^ n

theorem agree_truncLog {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (N : ℕ) : Agree N (logOnePlus f) (truncLog N f) := by
  intro d hd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [logOnePlus, PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    truncLog, map_sum]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N) ?_]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul]
  · intro n hn
    rw [Function.mem_support] at hn
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hn
    rw [coeff_pow_eq_zero hf n d (by omega), smul_zero]

theorem coeff_log_succ_mul (k : ℕ) :
    PowerSeries.coeff (k + 1) (PowerSeries.log K) * ((k + 1 : ℕ) : K) = (-1) ^ k := by
  rw [PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero k)]
  simp only [map_div₀, map_pow, map_neg, map_one, map_natCast]
  have : ((k + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  field_simp
  ring

theorem eul_truncLog (f : MvPowerSeries σ K) (M : ℕ) :
    eulFun (truncLog (M + 1) f) = (∑ k ∈ Finset.range M, (-f) ^ k) * eulFun f := by
  have h0 : PowerSeries.coeff 0 (PowerSeries.log K) = 0 := by simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← eul_apply, truncLog, map_sum, Finset.sum_range_succ', h0, zero_smul, map_zero,
    add_zero, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.map_smul, Derivation.leibniz_pow, Nat.add_sub_cancel, Algebra.smul_def,
    nsmul_eq_mul, smul_eq_mul, eul_apply, neg_pow]
  have h1 : algebraMap K (MvPowerSeries σ K) (PowerSeries.coeff (k + 1) (PowerSeries.log K)) *
      ((k + 1 : ℕ) : MvPowerSeries σ K) = (-1) ^ k := by
    rw [← map_natCast (algebraMap K (MvPowerSeries σ K)), ← map_mul, coeff_log_succ_mul,
      map_pow, map_neg, map_one]
  linear_combination (f ^ k * eulFun f) * h1

theorem eul_log_mul {f : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    eulFun (logOnePlus f) * (1 + f) = eulFun f := by
  ext d
  have hA := ((agree_truncLog hf (d.degree + 2)).eulFun).mul_right (1 + f) d (by omega)
  rw [hA, show d.degree + 2 = (d.degree + 1) + 1 from rfl, eul_truncLog]
  have hg := geom_sum_mul (-f) (d.degree + 1)
  have hE : (∑ k ∈ Finset.range (d.degree + 1), (-f) ^ k) * eulFun f * (1 + f) =
      eulFun f - (-f) ^ (d.degree + 1) * eulFun f := by
    linear_combination (-(eulFun f)) * hg
  rw [hE, map_sub]
  have hz : Agree (d.degree + 1) ((-f) ^ (d.degree + 1)) 0 := by
    intro e he
    rw [map_zero]
    exact coeff_pow_eq_zero (by rw [map_neg, hf, neg_zero]) _ e he
  have := hz.mul_right (eulFun f) d (by omega)
  rw [this, zero_mul, map_zero, sub_zero]

theorem constantCoeff_logOnePlus {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (logOnePlus f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hf _ PowerSeries.constantCoeff_log

theorem log_zero : logOnePlus (0 : MvPowerSeries σ K) = 0 := by
  apply eq_zero_of_eulFun _ (constantCoeff_logOnePlus (map_zero _))
  have := eul_log_mul (map_zero (MvPowerSeries.constantCoeff (σ := σ) (R := K)))
  rwa [add_zero, mul_one, ← eul_apply 0, map_zero] at this

theorem log_add {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    logOnePlus f + logOnePlus g = logOnePlus (f + g + f * g) := by
  have hh : MvPowerSeries.constantCoeff (f + g + f * g) = 0 := by
    simp only [map_add (f := _), map_mul, hf, hg, add_zero, mul_zero]
  have hu : IsUnit (1 + (f + g + f * g)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add (f := _), hh, map_one, add_zero]
    exact isUnit_one
  have e1 := eul_log_mul hf
  have e2 := eul_log_mul hg
  have e3 := eul_log_mul hh
  have hD : eulFun (f + g + f * g) = eulFun f + eulFun g + (f * eulFun g + g * eulFun f) := by
    show eul (f + g + f * g) = eul f + eul g + (f * eul g + g * eul f)
    rw [map_add (f := _), map_add (f := _), Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have key : eulFun (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) = 0 := by
    rw [← hu.mul_left_inj, zero_mul]
    show eul (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) * _ = 0
    rw [map_sub, map_add (f := _), eul_apply, eul_apply, eul_apply]
    linear_combination (1 + g) * e1 + (1 + f) * e2 - e3 - hD
  have := eq_zero_of_eulFun _ (by
    rw [map_sub, map_add (f := _), constantCoeff_logOnePlus hf, constantCoeff_logOnePlus hg,
      constantCoeff_logOnePlus hh, add_zero, sub_zero]) key
  exact sub_eq_zero.mp this

variable [IsUltrametricDist K]

theorem integral_map (F : MvPowerSeries σ (unitBall K)) :
    IntegralMv (MvPowerSeries.map (unitBall K).subtype F) := fun d => by
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff d F).2

theorem integral_add_mul {f g : MvPowerSeries σ K} (hf : IntegralMv f) (hg : IntegralMv g) :
    IntegralMv (f + g + f * g) := by
  have hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K := fun n => hf n
  have hg' : ∀ n, MvPowerSeries.coeff n g ∈ unitBall K := fun n => hg n
  have := integral_map (f.toSubring _ hf' + g.toSubring _ hg' +
    f.toSubring _ hf' * g.toSubring _ hg')
  simpa only [map_add (f := _), map_mul, MvPowerSeries.map_toSubring] using this

theorem exists_inv {f : MvPowerSeries σ K} (hf0 : MvPowerSeries.constantCoeff f = 0)
    (hf : IntegralMv f) :
    ∃ h : MvPowerSeries σ K, MvPowerSeries.constantCoeff h = 0 ∧ IntegralMv h ∧
      f + h + f * h = 0 := by
  have hf' : ∀ n, MvPowerSeries.coeff n f ∈ unitBall K := fun n => hf n
  set f' := f.toSubring _ hf' with hf'def
  have hc : MvPowerSeries.constantCoeff f' = 0 := by
    apply Subtype.ext
    rw [hf'def, MvPowerSeries.constantCoeff_toSubring, hf0]
    rfl
  have hu : IsUnit (1 + f') := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add (f := _), hc, map_one, add_zero]
    exact isUnit_one
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨MvPowerSeries.map (unitBall K).subtype (v - 1), ?_, integral_map _, ?_⟩
  · have hprod := congrArg (MvPowerSeries.map (unitBall K).subtype) hv
    rw [map_mul, map_add (f := _), map_one, MvPowerSeries.map_toSubring] at hprod
    have h2 := congrArg MvPowerSeries.constantCoeff hprod
    simp only [map_mul, map_add (f := _), map_one, hf0, add_zero, one_mul] at h2
    simp only [map_sub, h2, map_one, sub_self]
  · have hprod := congrArg (MvPowerSeries.map (unitBall K).subtype) hv
    rw [map_mul, map_add (f := _), map_one, MvPowerSeries.map_toSubring] at hprod
    rw [map_sub, map_one]
    linear_combination hprod

end Formalism.ELL.EulerSeries

namespace Formalism.ELL

theorem N_additive_subgroup : Formalism.ELL.NAddSubgroup := by
  intro K _ _ _ σ
  classical
  refine ⟨⟨0, map_zero _, fun d => by simp, EulerSeries.log_zero.symm⟩, ?_, ?_⟩
  · rintro G H ⟨f, hf0, hfi, rfl⟩ ⟨g, hg0, hgi, rfl⟩
    exact ⟨f + g + f * g, by simp only [map_add (f := _), map_mul, hf0, hg0, add_zero, mul_zero],
      EulerSeries.integral_add_mul hfi hgi, EulerSeries.log_add hf0 hg0⟩
  · rintro G ⟨f, hf0, hfi, rfl⟩
    obtain ⟨h, hh0, hhi, hfh⟩ := EulerSeries.exists_inv hf0 hfi
    refine ⟨h, hh0, hhi, ?_⟩
    have := EulerSeries.log_add hf0 hh0
    rw [hfh, EulerSeries.log_zero] at this
    linear_combination -this

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.IntVal
noncomputable section

namespace Formalism.ELL.IntegerValuedContinuity

theorem continuous_eval {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] (P : Polynomial K) :
    Continuous fun b : ℤ_[p] => P.eval (algebraMap ℚ_[p] K (b : ℚ_[p])) := by
  have h1 : Continuous (algebraMap ℚ_[p] K) := by
    have : (⇑(algebraMap ℚ_[p] K)) = fun c => c • (1 : K) := by
      funext c; exact Algebra.algebraMap_eq_smul_one c
    rw [this]; exact continuous_id.smul continuous_const
  have h2 : Continuous (fun b : ℤ_[p] => (b : ℚ_[p])) := continuous_subtype_val
  exact (P.continuous).comp (h1.comp h2)

end Formalism.ELL.IntegerValuedContinuity

namespace Formalism.ELL

theorem integer_valued_padic_integers : IntValuedZp := by
  intro p _ K _ _ P hP b
  have hc := Formalism.ELL.IntegerValuedContinuity.continuous_eval (p := p) (K := K) P
  have hclosed : IsClosed {b : ℤ_[p] | ‖P.eval (algebraMap ℚ_[p] K (b : ℚ_[p]))‖ ≤ 1} :=
    isClosed_le (continuous_norm.comp hc) continuous_const
  refine PadicInt.denseRange_natCast.induction_on b hclosed ?_
  intro n
  show ‖P.eval (algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]))‖ ≤ 1
  have : algebraMap ℚ_[p] K (((n : ℤ_[p])) : ℚ_[p]) = (n : K) := by
    simp
  rw [this]; exact hP n

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.IsogenyExpansion
section -- merged from Formalism.EllipticTorsion.IsoExpand
universe u

namespace Formalism.ELL

def quadDiff {M T : Type u} [AddCommGroup M] [AddCommGroup T] (φ : M → T) (a b : M) : T :=
  φ (a + b) - φ a - φ b

def QuadHyp {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T) : Prop :=
  (∀ a a' b : M, quadDiff φ (a + a') b - quadDiff φ a b - quadDiff φ a' b ∈ N) ∧
  φ 0 ∈ N ∧
  (∀ (α : O) (t : M), φ (α • t) - nrm α • φ t ∈ N) ∧
  (∀ (α : O) (a b : M), quadDiff φ (α • a) b - quadDiff φ a (bar α • b) ∈ N)

def IsoExpand : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∑ i, φ (∑ e, y e i • t e))
        - ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
            + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
                quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) ∈ N

def IsoVanish : Prop :=
  ∀ (O S M T : Type u) [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T] (N : AddSubgroup T) (bar : O → O) (nrm : O → S) (φ : M → T), QuadHyp N bar nrm φ →
    ∀ (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M),
      (∀ e e', ∑ i, bar (y e i) * y e' i = 0) → (∀ e, ∑ i, nrm (y e i) = 0) →
        (∑ i, φ (∑ e, y e i • t e)) ∈ N

end Formalism.ELL
end

open Finset

namespace Formalism.ELL.QuadraticDifferenceHypotheses

universe u

section Exact
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]

structure BiHyp (bar : O → O) (ψ : M → Q) : Prop where
  add1 : ∀ a a' b : M, quadDiff ψ (a + a') b = quadDiff ψ a b + quadDiff ψ a' b
  zero : ψ 0 = 0
  adj : ∀ (α : O) (a b : M), quadDiff ψ (α • a) b = quadDiff ψ a (bar α • b)

theorem qd_comm (ψ : M → Q) (a b : M) : quadDiff ψ a b = quadDiff ψ b a := by
  unfold quadDiff; rw [add_comm]; abel

theorem sum1 {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (b : M) :
    quadDiff ψ (∑ e ∈ s, x e) b = ∑ e ∈ s, quadDiff ψ (x e) b :=
  map_sum (AddMonoidHom.mk' (fun a => quadDiff ψ a b) (fun a a' => H.add1 a a' b)) x s

theorem sum2 {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    (s : Finset ι) (x : ι → M) (a : M) :
    quadDiff ψ a (∑ e ∈ s, x e) = ∑ e ∈ s, quadDiff ψ a (x e) := by
  rw [qd_comm, sum1 H]
  exact Finset.sum_congr rfl fun e _ => qd_comm _ _ _

theorem expand {bar : O → O} {ψ : M → Q} (H : BiHyp bar ψ) {ι : Type*}
    [LinearOrder ι] (s : Finset ι) (x : ι → M) :
    ψ (∑ e ∈ s, x e) = ∑ e ∈ s, ψ (x e) +
      ∑ e ∈ s, ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by
  refine Finset.induction_on_max s ?_ ?_
  · simp [H.zero]
  · intro a s hlt ih
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hdef : ∀ p q : M, ψ (p + q) = quadDiff ψ p q + ψ p + ψ q := by
      intro p q; unfold quadDiff; abel
    have hfa : (insert a s).filter (fun e' => a < e') = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact lt_irrefl _
      · exact not_lt.mpr (hlt z hz).le
    have hse : ∀ e ∈ s, ∑ e' ∈ (insert a s).filter (fun e' => e < e'), quadDiff ψ (x e) (x e') =
        quadDiff ψ (x e) (x a) + ∑ e' ∈ s.filter (fun e' => e < e'), quadDiff ψ (x e) (x e') := by
      intro e he
      rw [Finset.filter_insert, if_pos (hlt e he),
        Finset.sum_insert (fun h => ha (Finset.mem_filter.mp h).1)]
    rw [Finset.sum_insert ha, hdef, ih, Finset.sum_insert ha, Finset.sum_insert ha, hfa,
      Finset.sum_empty, Finset.sum_congr rfl hse, Finset.sum_add_distrib, qd_comm, sum1 H]
    abel

end Exact

section Quot
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]

theorem mk_quadDiff (N : AddSubgroup T) (φ : M → T) (a b : M) :
    QuotientAddGroup.mk' N (quadDiff φ a b) =
      quadDiff (fun a => QuotientAddGroup.mk' N (φ a)) a b := by
  simp [quadDiff, map_sub]

theorem biHyp_of {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) : BiHyp bar (fun a => QuotientAddGroup.mk' N (φ a)) := by
  have key : ∀ x : T, x ∈ N → QuotientAddGroup.mk' N x = 0 :=
    fun x hx => (QuotientAddGroup.eq_zero_iff x).mpr hx
  refine ⟨?_, key _ h.2.1, ?_⟩
  · intro a a' b
    have := key _ (h.1 a a' b)
    simp only [map_sub, mk_quadDiff] at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · intro α a b
    have := key _ (h.2.2.2 α a b)
    simp only [map_sub, mk_quadDiff] at this
    exact sub_eq_zero.mp this

theorem mk_nrm {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) (α : O) (s : M) :
    QuotientAddGroup.mk' N (φ (α • s)) = QuotientAddGroup.mk' N (nrm α • φ s) :=
  sub_eq_zero.mp (by rw [← map_sub]; exact (QuotientAddGroup.eq_zero_iff _).mpr (h.2.2.1 α s))

theorem expand_mk {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) (n m : ℕ) (y : Fin m → Fin n → O) (t : Fin m → M) :
    QuotientAddGroup.mk' N (∑ i, φ (∑ e, y e i • t e)) =
      QuotientAddGroup.mk' N ((∑ e, (∑ i, nrm (y e i)) • φ (t e))
        + (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
            quadDiff φ (t e) ((∑ i, bar (y e i) * y e' i) • t e'))) := by
  set f := QuotientAddGroup.mk' N
  have H := biHyp_of h
  have e1 : ∀ i, f (φ (∑ e, y e i • t e)) = ∑ e, f (nrm (y e i) • φ (t e)) +
      ∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'),
        quadDiff (fun a => f (φ a)) (t e) ((bar (y e i) * y e' i) • t e') := by
    intro i
    rw [expand H]
    congr 1
    · exact Finset.sum_congr rfl fun e _ => mk_nrm h _ _
    · refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun e' _ => ?_
      rw [H.adj, smul_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib, map_add (f := _), map_sum,
    map_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Finset.sum_smul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_comm, map_sum]
    refine Finset.sum_congr rfl fun e' _ => ?_
    rw [mk_quadDiff, Finset.sum_smul, sum2 H]

end Quot

end Formalism.ELL.QuadraticDifferenceHypotheses

namespace Formalism.ELL

open Formalism.ELL.QuadraticDifferenceHypotheses

universe u

theorem isogeny_expansion : IsoExpand.{u} := by
  intro O S M T _ _ _ _ _ _ N bar nrm φ h n m y t
  have E := expand_mk h n m y t
  rw [← sub_eq_zero, ← map_sub] at E
  exact (QuotientAddGroup.eq_zero_iff _).mp E

theorem isogeny_vanishing : IsoVanish.{u} := by
  intro O S M T _ _ _ _ _ _ N bar nrm φ h n m y t hiso hnrm
  have E := isogeny_expansion O S M T N bar nrm φ h n m y t
  have hz : ∀ a : M, quadDiff φ a 0 ∈ N := fun a => by
    simpa [quadDiff] using neg_mem h.2.1
  simp only [hiso, hnrm, zero_smul, Finset.sum_const_zero, zero_add] at E
  have hS : (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'), quadDiff φ (t e) 0) ∈ N :=
    sum_mem fun e _ => sum_mem fun e' _ => hz _
  have := add_mem E hS
  rwa [sub_add_cancel] at this

end Formalism.ELL
end

universe u

namespace Formalism.ELL

theorem legendreInv : LegendreInv.{u} := legendre_invariant
theorem deuringInv : DeuringInv.{u} := deuring_invariant
theorem modelLegendre : ModelLegendre.{u} := legendre_model
theorem modelDeuring : ModelDeuring.{u} := deuring_model
theorem modelUnit : ModelUnit.{u} := by
  apply modelUnit_of <;> first | exact modelLegendre | exact modelDeuring | exact legendreInv | exact deuringInv
theorem intValuedZp : IntValuedZp.{u} := integer_valued_padic_integers
theorem nAddSubgroup : NAddSubgroup.{u} := N_additive_subgroup
theorem nZpSmul : NZpSmul.{u} := N_padic_integer_smul
theorem nPderiv : NPderiv.{u} := N_partial_derivative

theorem formal_group_points_subgroup : FormalGroupPointsSubgroup'.{u} := formal_group_points_subgroup_holds
theorem formal_group_points_no_torsion : FormalGroupPointsTorsionFree.{u} := formal_group_points_no_prime_to_p_torsion
theorem torsionIntegral : TorsionIntegral.{u} := torsionIntegral_of formal_group_points_no_torsion

theorem isoExpand : IsoExpand.{u} := isogeny_expansion
theorem isoVanish : IsoVanish.{u} := isogeny_vanishing

theorem changeIntegral : ChangeIntegral.{u} := change_of_variables_integral

theorem lwP₂ : LogWeight.{u} := logarithm_coeff_weight
theorem unitCancel : UnitCancel.{u} := unit_cancellation

theorem compExpWeight : CompExpWeight.{u} := comp_exp_coeff_weight

theorem lemma2Weights : EllipticTorsionWeights.{u} := coefficient_weights_lemma_two
theorem frobExpand : FrobExpand.{u} := frobenius_expansion

theorem wSeriesUnique : WSeriesUnique.{u} := wSeriesExistsUnique_holds
theorem wSeriesLead : WSeriesLead.{u} := wSeriesLeadingTerm_holds
theorem wSubstUnique : WSubstUnique.{u} := wSeriesSubstUnique_holds
theorem wPoint : WPoint.{u} := wSeriesNonsingularPoint_holds
theorem wChordSeries : WChordSeries.{u} := wChordSeries_of wSubstUnique
theorem wChordSubst : WChordSubst.{u} := wChordSubst_of wSeriesSubstUnique_holds
theorem wFormalGroup : WFormalGroup.{u} := by
  apply wFormalGroup_of <;> first | exact wChordSeries | exact wChordSubst | exact wPoint | exact wSubstUnique | exact wSeriesUnique | exact wSeriesLead

theorem formal_group_points_param : FormalGroupPointsParametrisation.{u} := by
  apply formal_group_points_param_of <;> first | exact intValuedZp | exact nAddSubgroup | exact nZpSmul | exact nPderiv | exact lwP₂ | exact unitCancel | exact compExpWeight | exact lemma2Weights | exact frobExpand | exact wFormalGroup | exact formal_group_points_subgroup | exact formal_group_points_no_torsion | exact isoExpand | exact isoVanish | exact changeIntegral | exact wPoint | exact wSubstUnique | exact wChordSubst | exact wChordSeries | exact veluIntegralModel | exact veluUSeries | exact modelUnit
theorem formal_group_points_hom : FormalGroupPointsHomomorphism.{u} := by
  apply formal_group_points_hom_of <;> first | exact wSubstUnique | exact wChordSubst | exact formal_group_points_param | exact wFormalGroup | exact wChordSeries | exact wPoint

theorem veluIntegralModel : VeluIntegralModel.{u} := velu_integral_model
theorem veluUSeries : VeluUSeries.{u} := velu_u_series

theorem cubeTwo : CubeTwo.{u} := cube_two
theorem cubeThree : CubeThree.{u} := chordDeterminantFactor_holds

end Formalism.ELL
