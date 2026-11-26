module

public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscFieldEqTorsionField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.DiscRoot

open Polynomial _root_.WeierstrassCurve

theorem exists_vieta_two (p q : ℂ) : ∃ x y : ℂ, x + y = p ∧ x * y = q := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (p ^ 2 - 4 * q) (show 0 < 2 by norm_num)
  exact ⟨(p + s) / 2, (p - s) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hs⟩

theorem exists_vieta_three (p q r : ℂ) :
    ∃ x y z : ℂ, x + y + z = p ∧ x * y + x * z + y * z = q ∧ x * y * z = r := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 3 - C p * X ^ 2 + C q * X - C r : ℂ[X]) (by
    have : (X ^ 3 - C p * X ^ 2 + C q * X - C r : ℂ[X]).degree = 3 := by compute_degree!
    rw [this]; decide)
  simp only [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
  obtain ⟨y, z, h1, h2⟩ := exists_vieta_two (p - x) (q - x * (p - x))
  exact ⟨x, y, z, by linear_combination h1, by linear_combination x * h1 + h2, by linear_combination x * h2 + hx⟩

theorem exists_vieta_four (p q r t : ℂ) :
    ∃ x y z w : ℂ, x + y + z + w = p ∧ x * y + x * z + x * w + y * z + y * w + z * w = q ∧
      x * y * z + x * y * w + x * z * w + y * z * w = r ∧ x * y * z * w = t := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (X ^ 4 - C p * X ^ 3 + C q * X ^ 2 - C r * X + C t : ℂ[X]) (by
    have : (X ^ 4 - C p * X ^ 3 + C q * X ^ 2 - C r * X + C t : ℂ[X]).degree = 4 := by compute_degree!
    rw [this]; decide)
  simp only [IsRoot.def, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hx
  obtain ⟨y, z, w, h1, h2, h3⟩ := exists_vieta_three (p - x) (q - x * (p - x)) (r - x * (q - x * (p - x)))
  exact ⟨x, y, z, w, by linear_combination h1, by linear_combination x * h1 + h2, by linear_combination x * h2 + h3,
    by linear_combination x * h3 - hx⟩

variable {W : WeierstrassCurve ℂ}

theorem four_torsion (hΔ : W.Δ ≠ 0) {e s t : ℂ} (h2 : W.b₂ = -4 * (3 * e - s ^ 2 - t ^ 2))
    (h4 : W.b₄ = 2 * (e * (e - s ^ 2) + e * (e - t ^ 2) + (e - s ^ 2) * (e - t ^ 2)))
    (h6 : W.b₆ = -4 * (e * (e - s ^ 2) * (e - t ^ 2))) (hs : s ≠ 0) (ht : t ≠ 0) (hst : s + t ≠ 0) :
    e + s * t ∈ torsionCoords W 4 ∧
      s * t * (s + t) - (W.a₁ * (e + s * t) + W.a₃) / 2 ∈ torsionCoords W 4 := by
  simp only [b₂, b₄, b₆] at h2 h4 h6
  set x := e + s * t with hx
  set y := s * t * (s + t) - (W.a₁ * x + W.a₃) / 2 with hy
  have heq : W.toAffine.Equation x y := by
    rw [Affine.equation_iff]
    simp only [toAffine]
    rw [hy, hx]
    linear_combination (-(e + s * t) ^ 2 / 4) * h2 - (e + s * t) / 2 * h4 - 1 / 4 * h6
  have hns : W.toAffine.Nonsingular x y := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 heq
  have hd : y - W.toAffine.negY x y = 2 * (s * t * (s + t)) := by
    simp only [Affine.negY, toAffine]
    rw [hy]; ring
  have hd0 : y - W.toAffine.negY x y ≠ 0 := by
    rw [hd]; exact mul_ne_zero two_ne_zero (mul_ne_zero (mul_ne_zero hs ht) hst)
  have hne : y ≠ W.toAffine.negY x y := sub_ne_zero.1 hd0
  have hl : W.toAffine.slope x x y y = s + t - W.a₁ / 2 := by
    rw [Affine.slope_of_Y_ne rfl hne, div_eq_iff hd0, hd]
    simp only [toAffine]
    rw [hy, hx]
    linear_combination (e + s * t) / 2 * h2 + 1 / 2 * h4
  have h0 : 4 • Affine.Point.some x y hns = 0 := by
    rw [show 4 = 2 * 2 from rfl, mul_smul, two_smul, two_smul, Affine.Point.add_self_of_Y_ne hne]
    apply Affine.Point.add_self_of_Y_eq
    simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, hl, toAffine]
    rw [hy, hx]
    linear_combination (s + t) / 2 * h2
  exact ⟨⟨x, y, hns, h0, Or.inl rfl⟩, ⟨x, y, hns, h0, Or.inr rfl⟩⟩

theorem three_torsion (hΔ : W.Δ ≠ 0) {x : ℂ}
    (h : 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ = 0) : x ∈ torsionCoords W 3 := by
  simp only [b₂, b₄, b₆, b₈] at h
  obtain ⟨y, y', h1, h2⟩ := exists_vieta_two (-(W.a₁ * x + W.a₃)) (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    linear_combination y * h1 - h2
  have hns : W.toAffine.Nonsingular x y :=
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 ((Affine.equation_iff _ _).2 heq)
  have key : (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) ^ 2 +
      W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) * (2 * y + W.a₁ * x + W.a₃) =
      (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    linear_combination -h - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * heq
  have hd : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    simp only [Affine.negY, toAffine]; ring
  have hd0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    intro h0
    rw [h0] at key
    have h3 : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y = 0 := by
      apply pow_eq_zero_iff (n := 2) two_ne_zero |>.1
      linear_combination key
    rcases ((Affine.nonsingular_iff _ _).1 hns).2 with h4 | h4
    · exact h4 (by simp only [toAffine]; linear_combination -h3)
    · exact h4 (by simp only [toAffine]; linear_combination h0)
  have hne : y ≠ W.toAffine.negY x y := sub_ne_zero.1 (hd ▸ hd0)
  have hX : W.toAffine.addX x x (W.toAffine.slope x x y y) = x := by
    have hl : W.toAffine.slope x x y y * (2 * y + W.a₁ * x + W.a₃) =
        3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
      rw [Affine.slope_of_Y_ne rfl hne, hd, div_mul_cancel₀ _ hd0]
    rw [← hl] at key
    simp only [Affine.addX, toAffine] at key ⊢
    apply mul_right_cancel₀ (pow_ne_zero 2 hd0)
    linear_combination key
  refine ⟨x, y, hns, ?_, Or.inl rfl⟩
  rw [show 3 = 2 + 1 from rfl, add_smul, two_smul, one_smul, Affine.Point.add_self_of_Y_ne hne]
  apply Affine.Point.add_of_Y_eq hX
  simp only [Affine.addY, Affine.negAddY, hX, sub_self, mul_zero, zero_add]

variable {M : IntermediateField ℚ ℂ}

theorem sqrt_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 4 ⊆ M) {e₁ e₂ e₃ s : ℂ}
    (h2 : W.b₂ = -4 * (e₁ + e₂ + e₃)) (h4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃)) (h6 : W.b₆ = -4 * (e₁ * e₂ * e₃))
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) (hs : s ^ 2 = e₁ - e₂) : s ∈ M := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₃) (show 0 < 2 by norm_num)
  have key : ∀ t : ℂ, t ^ 2 = e₁ - e₃ → s * t ≠ 0 ∧ e₁ + s * t ∈ M ∧ s * t * (s + t) ∈ M := by
    intro t ht
    have hs0 : s ≠ 0 := fun h => h12 (by rw [h] at hs; linear_combination -hs)
    have ht0 : t ≠ 0 := fun h => h13 (by rw [h] at ht; linear_combination -ht)
    have hst : s + t ≠ 0 := fun h => h23 (by linear_combination hs - ht - (s - t) * h)
    obtain ⟨k1, k2⟩ := four_torsion (e := e₁) hΔ (by rw [hs, ht, h2]; ring) (by rw [hs, ht, h4]; ring)
      (by rw [hs, ht, h6]; ring) hs0 ht0 hst
    have k1 : e₁ + s * t ∈ M := hM k1
    have k2 : _ ∈ M := hM k2
    refine ⟨mul_ne_zero hs0 ht0, k1, ?_⟩
    have := add_mem k2 (div_mem (add_mem (mul_mem ha₁ k1) ha₃) (ofNat_mem M 2))
    rwa [sub_add_cancel] at this
  obtain ⟨h0, k1, k2⟩ := key t ht
  obtain ⟨-, k3, k4⟩ := key (-t) (by rw [neg_sq, ht])
  have hs0 : s ≠ 0 := left_ne_zero_of_mul h0
  have ht0 : t ≠ 0 := right_ne_zero_of_mul h0
  have : s = (s * t * (s + t) - s * -t * (s + -t)) / ((e₁ + s * t) - (e₁ + s * -t)) := by
    rw [eq_div_iff (by
      rw [show (e₁ + s * t) - (e₁ + s * -t) = 2 * (s * t) by ring]
      exact mul_ne_zero two_ne_zero h0)]
    ring
  rw [this]
  exact div_mem (sub_mem k2 k4) (sub_mem k1 k3)

theorem fourth_root_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 4 ⊆ M) {c : ℂ}
    (hc : c ^ 4 = W.Δ) : c ∈ M := by
  obtain ⟨e₁, e₂, e₃, k2, k4, k6⟩ := exists_vieta_three (-W.b₂ / 4) (W.b₄ / 2) (-W.b₆ / 4)
  have h2 : W.b₂ = -4 * (e₁ + e₂ + e₃) := by linear_combination 4 * k2
  have h4 : W.b₄ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by linear_combination -2 * k4
  have h6 : W.b₆ = -4 * (e₁ * e₂ * e₃) := by linear_combination 4 * k6
  have h8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by linear_combination W.b_relation / 4
  have hD : W.Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
    rw [Δ, h8, h2, h4, h6]; ring
  have h12 : e₁ ≠ e₂ := fun h => hΔ (by rw [hD, h]; ring)
  have h13 : e₁ ≠ e₃ := fun h => hΔ (by rw [hD, h]; ring)
  have h23 : e₂ ≠ e₃ := fun h => hΔ (by rw [hD, h]; ring)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₂) (show 0 < 2 by norm_num)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (e₁ - e₃) (show 0 < 2 by norm_num)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (e₂ - e₃) (show 0 < 2 by norm_num)
  have ms : s ∈ M := sqrt_mem hΔ ha₁ ha₃ hM h2 h4 h6 h12 h13 h23 hs
  have mt : t ∈ M := sqrt_mem (e₁ := e₁) (e₂ := e₃) (e₃ := e₂) hΔ ha₁ ha₃ hM (by rw [h2]; ring) (by rw [h4]; ring)
    (by rw [h6]; ring) h13 h12 h23.symm ht
  have mu : u ∈ M := sqrt_mem (e₁ := e₂) (e₂ := e₃) (e₃ := e₁) hΔ ha₁ ha₃ hM (by rw [h2]; ring) (by rw [h4]; ring)
    (by rw [h6]; ring) h23 h12.symm h13.symm hu
  have mi : Complex.I * s ∈ M := sqrt_mem (e₁ := e₂) (e₂ := e₁) (e₃ := e₃) hΔ ha₁ ha₃ hM (by rw [h2]; ring)
    (by rw [h4]; ring) (by rw [h6]; ring) h12.symm h23 h13 (by rw [mul_pow, Complex.I_sq, hs]; ring)
  have mb : 2 * (s * t * u) ∈ M := mul_mem (ofNat_mem M 2) (mul_mem (mul_mem ms mt) mu)
  have mb' : Complex.I * (2 * (s * t * u)) ∈ M := by
    rw [show Complex.I * (2 * (s * t * u)) = 2 * (Complex.I * s * t * u) by ring]
    exact mul_mem (ofNat_mem M 2) (mul_mem (mul_mem mi mt) mu)
  have hb : (2 * (s * t * u)) ^ 4 = c ^ 4 := by
    rw [hc, hD, ← hs, ← ht, ← hu]; ring
  generalize 2 * (s * t * u) = b at mb mb' hb
  have hf : (c - b) * (c + b) * ((c - Complex.I * b) * (c + Complex.I * b)) = 0 := by
    linear_combination -hb - (c ^ 2 - b ^ 2) * b ^ 2 * Complex.I_sq
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hf
  rcases hf with (h | h) | h | h <;> rw [h]
  exacts [mb, neg_mem mb, mb', neg_mem mb']

theorem cube_root_mem (hΔ : W.Δ ≠ 0) (hM : torsionCoords W 3 ⊆ M) {c : ℂ} (hc : c ^ 3 = W.Δ) : c ∈ M := by
  obtain ⟨x, y, z, w, k2, k4, k6, k8⟩ := exists_vieta_four (-W.b₂ / 3) W.b₄ (-W.b₆) (W.b₈ / 3)
  have h2 : W.b₂ = -3 * (x + y + z + w) := by linear_combination 3 * k2
  have h4 := k4.symm
  have h6 : W.b₆ = -(x * y * z + x * y * w + x * z * w + y * z * w) := by linear_combination k6
  have h8 : W.b₈ = 3 * (x * y * z * w) := by linear_combination -3 * k8
  have mx : x ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have my : y ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have mz : z ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have mw : w ∈ M := hM (three_torsion hΔ (by rw [h2, h4, h6, h8]; ring))
  have m4 : W.b₄ ∈ M := by
    rw [h4]
    exact add_mem (add_mem (add_mem (add_mem (add_mem (mul_mem mx my) (mul_mem mx mz)) (mul_mem mx mw))
      (mul_mem my mz)) (mul_mem my mw)) (mul_mem mz mw)
  have hr := W.b_relation
  have res : ∀ u : ℂ, u ^ 3 - W.b₄ * u ^ 2 + (W.b₂ * W.b₆ - 4 * W.b₈) / 3 * u -
      (W.b₂ ^ 2 * W.b₈ / 27 + W.b₆ ^ 2 - 4 * W.b₄ * W.b₈ / 3) = 0 → (W.b₄ - 3 * u) ^ 3 = W.Δ := by
    intro u hu
    rw [Δ]
    linear_combination -27 * hu + (9 * W.b₄ - 9 * u) * hr
  have a1 := res (x * y + z * w) (by rw [h2, h4, h6, h8]; ring)
  have a2 := res (x * z + y * w) (by rw [h2, h4, h6, h8]; ring)
  have a3 := res (x * w + y * z) (by rw [h2, h4, h6, h8]; ring)
  have m1 : W.b₄ - 3 * (x * y + z * w) ∈ M :=
    sub_mem m4 (mul_mem (ofNat_mem M 3) (add_mem (mul_mem mx my) (mul_mem mz mw)))
  have m2 : W.b₄ - 3 * (x * z + y * w) ∈ M :=
    sub_mem m4 (mul_mem (ofNat_mem M 3) (add_mem (mul_mem mx mz) (mul_mem my mw)))
  rw [show W.b₄ - 3 * (x * w + y * z) = -((W.b₄ - 3 * (x * y + z * w)) + (W.b₄ - 3 * (x * z + y * w))) by
    linear_combination 3 * h4] at a3
  generalize W.b₄ - 3 * (x * y + z * w) = a at a1 a3 m1
  generalize W.b₄ - 3 * (x * z + y * w) = b at a2 a3 m2
  have hab : b - a ≠ 0 := fun h => hΔ (by
    rw [sub_eq_zero.1 h] at a3
    linear_combination (-8 / 9 : ℂ) * a1 - 1 / 9 * a3)
  have hq : b ^ 2 + b * a + a ^ 2 = 0 := mul_left_cancel₀ hab (by linear_combination a2 - a1)
  have hf : (c - a) * (c - b) * (c + (a + b)) = 0 := by
    linear_combination hc - a1 + (a - c) * hq
  simp only [mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at hf
  rcases hf with (h | h) | h <;> rw [h]
  exacts [m1, m2, neg_mem (add_mem m1 m2)]

theorem twelfth_root_mem (hΔ : W.Δ ≠ 0) (ha₁ : W.a₁ ∈ M) (ha₃ : W.a₃ ∈ M) (hM : torsionCoords W 12 ⊆ M) {z : ℂ}
    (hz : z ^ 12 = W.Δ) : z ∈ M := by
  have h0 : z ≠ 0 := fun h => hΔ (by rw [← hz, h]; norm_num)
  have h3 : z ^ 3 ∈ M := fourth_root_mem hΔ ha₁ ha₃ ((torsionCoords_mono W (by norm_num)).trans hM)
    (by rw [← hz]; ring)
  have h4 : z ^ 4 ∈ M := cube_root_mem hΔ ((torsionCoords_mono W (by norm_num)).trans hM) (by rw [← hz]; ring)
  rw [show z = z ^ 4 / z ^ 3 by field_simp]
  exact div_mem h4 h3

theorem discField_eq_torsionField (d : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F) [A.IsElliptic] :
    discField d A = torsionField d A := by
  refine le_antisymm (sup_le le_rfl ?_) (torsionField_le_discField d A)
  rw [IntermediateField.adjoin_le_iff]
  intro z (hz : z ^ 12 = _)
  have hF : F ≤ torsionField d A := le_sup_right.trans (hilbertField_le_torsionField d A)
  have hD : (A.baseChange ℂ).Δ = (A.Δ : ℂ) := by rw [baseChange, map_Δ]; rfl
  refine twelfth_root_mem (W := A.baseChange ℂ) ?_ (hF A.a₁.2) (hF A.a₃.2) ?_ (hD ▸ hz)
  · rw [hD]
    exact fun h => A.isUnit_Δ.ne_zero (Subtype.ext h)
  · exact fun w hw => (le_sup_right : _ ≤ torsionField d A) (IntermediateField.subset_adjoin ℚ _ hw)

end GlobalTheory.Mem.DiscRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionStepZeroTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionStepZeroTypePrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.ZeroGrp

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

def autOf (A : GL (Fin n) (𝓞 E)) : Sp E n ≃ₗ[E] Sp E n :=
  LinearEquiv.ofLinear (Matrix.toLin' (A.1.map (algebraMap (𝓞 E) E))) (Matrix.toLin' ((A⁻¹).1.map (algebraMap (𝓞 E) E)))
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one])

omit [StarRing E] in
theorem autOf_apply (A : GL (Fin n) (𝓞 E)) (x : Sp E n) (i : Fin n) :
    autOf A x i = ∑ j, algebraMap (𝓞 E) E (A.1 i j) * x j := rfl

omit [StarRing E] in
theorem autOf_inv (A : GL (Fin n) (𝓞 E)) : (autOf A)⁻¹ = autOf A⁻¹ := LinearEquiv.ext fun _ => rfl

omit [StarRing E] in
theorem extE_lt (c : ℕ) (g : Sp E n ≃ₗ[E] Sp E n) (v : Sp E (n + c)) (l : Fin (n + c)) :
    CongLevel.extE c g v l = if h : l.1 < n then g (CongLevel.resX c v) ⟨l.1, h⟩ else v l := by
  rw [CongLevel.extE_apply, Pi.add_apply, CongLevel.inX_apply]
  split_ifs with h
  · have : CongLevel.resX c v ⟨l.1, h⟩ = v l := rfl
    rw [Pi.sub_apply, this]
    ring
  · rw [add_zero]

theorem extE_maps_scl {q c : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (he : ∀ i j, i ≤ j → j < n → e i ≤ e j)
    (A : GL (Fin n) (𝓞 E)) (hA : ∀ i j : Fin n, j.1 < i.1 → A.1 i j = 0) (v : Sp E (n + c))
    (hv : v ∈ LocE.sclLat P q (n + c) e) : CongLevel.extE c (autOf A) v ∈ LocE.sclLat P q (n + c) e := by
  rw [CongLevel.mem_sclLat] at hv ⊢
  intro l
  rw [extE_lt]
  split_ifs with h
  · rw [autOf_apply, Finset.mul_sum]
    refine TopStep.intAt_sum _ fun j _ => ?_
    by_cases hj : j.1 < l.1
    · rw [hA ⟨l.1, h⟩ j hj]
      simpa using TopStep.intAt_zero
    · obtain ⟨d, hd⟩ := Int.le.dest (he l.1 j.1 (by omega) j.2)
      have h1 := ((IntAt.coe P (A.1 ⟨l.1, h⟩ j)).mul (TopStep.intAt_pow (TopStep.intAt_nat q) d)).mul
        (hv (Fin.castAdd c j))
      convert h1 using 1
      have : CongLevel.resX c v j = v (Fin.castAdd c j) := rfl
      rw [this, Fin.val_castAdd, ← hd, zpow_add₀ hq, zpow_natCast]
      have := zpow_ne_zero (e l.1) hq
      field_simp
  · exact hv l

theorem uni_iff {κ : Type} [CommRing κ] {a : ℕ} (ha : n = a) {M : GL (Fin n) κ} :
    M ∈ uniUT n κ a [] ↔ (∀ i j : Fin n, j.1 < i.1 → M.1 i j = 0) ∧ ∀ i, M.1 i i = 1 := by
  subst ha
  rw [mem_uniUT]
  refine ⟨fun h => ⟨fun i j => h.2.1 i j i.2, fun i => h.2.2 i i.2⟩, fun h => ⟨fun i j hij => ?_, fun i j _ => h.1 i j,
    fun i _ => h.2 i⟩⟩
  have : coarse n [] j.1 < coarse n [] i.1 := hij
  rw [coarse_of_lt i.2] at this
  omega

theorem extE_stab_scl {q c : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (he : ∀ i j, i ≤ j → j < n → e i ≤ e j)
    (A : GL (Fin n) (𝓞 E)) (hA : A ∈ uniUT n (𝓞 E) n []) :
    CongLevel.extE c (autOf A) ∈ stabL E (n + c) (LocE.sclLat P q (n + c) e) := by
  intro v
  refine ⟨fun hv => ?_, extE_maps_scl hq e he A ((uni_iff rfl).1 hA).1 v⟩
  have h := extE_maps_scl hq e he A⁻¹ ((uni_iff rfl).1 (inv_mem hA)).1 _ hv
  rw [← autOf_inv, ← CongLevel.extE_inv] at h
  rwa [show (CongLevel.extE c (autOf A))⁻¹ (CongLevel.extE c (autOf A) v) = v from LinearEquiv.symm_apply_apply _ v] at h

omit [NumberField E] [StarRing E] in
theorem bvecS_eq (q rS c : ℕ) (f : Fin n) :
    LocE.bvecS E q n rS n c (f.1 + rS) = Loc.inX E n c (Pi.single f 1) := by
  have h1 : LocE.fIdx n c n (symIdxInv n rS (f.1 + rS)) = f.1 := by
    have := f.2
    unfold LocE.fIdx symIdxInv
    split_ifs <;> omega
  unfold LocE.bvecS LocE.bvecG
  rw [h1]
  unfold LocE.scE
  rw [if_pos f.2, zpow_zero, one_smul]
  funext l
  rw [CongLevel.inX_apply]
  unfold Loc.eN
  have := f.2
  by_cases h : l.1 < n
  · rw [dite_eq_left h, Pi.single_apply]
    simp [Fin.ext_iff]
  · rw [dite_eq_right h, if_neg (by omega)]

theorem inX_mem_flagS (q rS c : ℕ) (f : Fin n) (x : Sp E n) :
    Loc.inX E n c x ∈ LocE.flagS P q n rS n c (f.1 + rS) ↔
      ∀ l : Fin n, IntAt P (((q : E) ^ (if f.1 ≤ l.1 then (1 : ℤ) else 0))⁻¹ * x l) := by
  unfold LocE.flagS
  rw [CongLevel.mem_sclLat]
  have key : ∀ l, l < n → (LocE.scE n (fun i => i + 1) l +
      if LocE.bd5 n rS (f.1 + rS) ≤ symIdx n rS (LocE.fPos n c n l) then (1 : ℤ) else 0) = if f.1 ≤ l then 1 else 0 := by
    intro l hl
    have := f.2
    unfold LocE.scE LocE.bd5 LocE.fPos symIdx
    rw [if_pos hl, if_pos hl, if_pos hl, if_neg (by omega : ¬ f.1 + rS = rS + n), zero_add]
    simp
  constructor
  · intro h l
    have h1 := h (Fin.castAdd c l)
    rw [key _ (by simp), CongLevel.inX_apply, dite_eq_left (by simp)] at h1
    exact h1
  · intro h l
    rw [CongLevel.inX_apply]
    by_cases hl : l.1 < n
    · rw [dite_eq_left hl, key _ hl]
      exact h ⟨l.1, hl⟩
    · rw [dite_eq_right hl, mul_zero]
      exact TopStep.intAt_zero

theorem extE_mem_JGsym {q : ℕ} (hq : (q : E) ≠ 0) (rS r t c : ℕ) (A : GL (Fin n) (𝓞 E)) (hA : A ∈ uniUT n (𝓞 E) n []) :
    CongLevel.extE c (autOf A) ∈ LocE.JGsym P q n rS r t n c := by
  have hs : ∀ s, CongLevel.extE c (autOf A) ∈ stabL E (n + c) (LocE.flagS P q n rS n c s) := by
    intro s
    refine extE_stab_scl hq _ (fun i j hij hj => ?_) A hA
    have hi : i < n := by omega
    unfold LocE.scE LocE.fPos symIdx
    simp only [if_pos hi, if_pos hj]
    split_ifs <;> omega
  refine ⟨extE_stab_scl hq _ (fun i j hij hj => ?_) A hA, fun s _ => hs s, fun s _ => ⟨hs s, ?_⟩⟩
  · unfold LocE.scE
    rw [if_pos hj, if_pos (by omega)]
  · by_cases h : rS ≤ s ∧ s < rS + n
    · obtain ⟨f, rfl⟩ : ∃ f : Fin n, s = f.1 + rS := ⟨⟨s - rS, by omega⟩, by simp only; omega⟩
      rw [bvecS_eq, CongLevel.extE_inX, ← map_sub, inX_mem_flagS]
      intro l
      obtain ⟨h1, h2⟩ := (uni_iff rfl).1 hA
      have e : (autOf A (Pi.single f 1) - (Pi.single f 1 : Sp E n)) l =
          algebraMap (𝓞 E) E (A.1 l f) - (Pi.single f 1 : Sp E n) l := by
        rw [Pi.sub_apply, autOf_apply]
        simp [Pi.single_apply]
      rw [e]
      split_ifs with hl
      · by_cases hlf : l = f
        · subst hlf
          simpa [h2] using TopStep.intAt_zero
        · have : f.1 < l.1 := lt_of_le_of_ne hl fun h => hlf (Fin.ext h.symm)
          simpa [h1 l f this, hlf] using TopStep.intAt_zero
      · have hlf : l ≠ f := fun h => hl (h ▸ le_rfl)
        simpa [hlf] using IntAt.coe P (A.1 l f)
    · obtain ⟨i, hi⟩ : ∃ i, LocE.fIdx n c n (symIdxInv n rS s) = n + i :=
        ⟨LocE.fIdx n c n (symIdxInv n rS s) - n, by unfold LocE.fIdx symIdxInv; split_ifs <;> omega⟩
      unfold LocE.bvecS LocE.bvecG
      rw [hi, map_smul, CongLevel.extE_apply, CongLevel.resX_eN]
      simp

omit [StarRing E] in
theorem exists_lift (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) (hM : M ∈ uniUT n _ n []) :
    ∃ A ∈ uniUT n (𝓞 E) n [], ∀ i j, Ideal.Quotient.mk P.asIdeal (A.1 i j) = M.1 i j := by
  obtain ⟨h1, h2⟩ := (uni_iff rfl).1 hM
  choose a ha using fun i j => Ideal.Quotient.mk_surjective (M.1 i j)
  let B : Matrix (Fin n) (Fin n) (𝓞 E) := Matrix.of fun i j => if j.1 < i.1 then 0 else if i = j then 1 else a i j
  have hB : B.det = 1 := by
    rw [Matrix.det_of_upperTriangular (M := B) (fun i j hij => if_pos (show j.1 < i.1 from hij))]
    simp [B]
  refine ⟨Matrix.GeneralLinearGroup.mk'' B (by rw [hB]; exact isUnit_one), (uni_iff rfl).2 ⟨fun i j hij => ?_, fun i => ?_⟩,
    fun i j => ?_⟩
  · exact if_pos hij
  · show B i i = 1
    simp [B]
  · show Ideal.Quotient.mk P.asIdeal (if j.1 < i.1 then 0 else if i = j then 1 else a i j) = _
    split_ifs with c1 c2
    · rw [h1 i j c1, map_zero]
    · rw [c2, h2, map_one]
    · exact ha i j

theorem uni_iff_prX {k : ℕ} (hn : n = k) (rS r t c : ℕ) (hr : k + rS ≤ r) (M : GL (Fin n) (𝓞 E ⧸ P.asIdeal)) :
    M ∈ uniUT n _ k [] ↔ ∃ g ∈ Loc.prX (Loc.Cbe (LocE.JGsym P (qOf P) k rS r t n c) 1),
      ∀ x ∈ stdAt E n P, redV P (g x) = M.1.mulVec (redV P x) := by
  subst hn
  have hq := TopStep.qOf_ne_zero (P := P)
  have hc : ∀ ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c), ρ ∈ Loc.Cbe (LocE.JGsym P (qOf P) n rS r t n c) 1 ↔
      ρ ∈ Loc.R1 E n c ∧ ρ ∈ LocE.JGsym P (qOf P) n rS r t n c := by
    intro ρ
    simp [Loc.Cbe]
  constructor
  · intro hM
    obtain ⟨A, hA, hAM⟩ := exists_lift M hM
    refine ⟨autOf A, ⟨CongLevel.extE c (autOf A), (hc _).2 ⟨CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ _, extE_mem_JGsym hq _ _ _ _ A hA⟩,
      CongLevel.extE_inX _ _⟩, fun x hx => ?_⟩
    funext i
    have hx' := TopStep.mem_stdAt.1 hx
    show redP P (autOf A x i) = ∑ j, M.1 i j * redP P (x j)
    rw [autOf_apply, TopStep.reduction_sum₂ _ fun j _ => (IntAt.coe P _).mul (hx' j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [reduction_mul (IntAt.coe P _) (hx' j), reduction_coe, hAM]
  · rintro ⟨g, ⟨ρ, hρ, hg⟩, hM⟩
    have key : ∀ f l : Fin n, f.1 ≤ l.1 → M.1 l f = (Pi.single f 1 : Fin n → 𝓞 E ⧸ P.asIdeal) l := by
      intro f l hl
      have h1 := (((hc ρ).1 hρ).2.2.2 (f.1 + rS) (by have := f.2; omega)).2
      rw [bvecS_eq, hg, ← map_sub, inX_mem_flagS] at h1
      have h2 := h1 l
      rw [if_pos hl, zpow_one, mul_comm, ← div_eq_mul_inv, Pi.sub_apply] at h2
      have h3 := TopStep.redP_eq_zero_of_div h2
      have h4 : IntAt P (g (Pi.single f 1) l - (Pi.single f 1 : Sp E n) l) := by
        have := (TopStep.intAt_nat (qOf P)).mul h2
        rwa [mul_div_cancel₀ _ hq] at this
      have h5 := reduction_add h4 (TopStep.mem_stdAt.1 (TopStep.single_mem_stdAt (P := P) f) l)
      rw [sub_add_cancel, h3, zero_add] at h5
      have h6 := congrFun (hM _ (TopStep.single_mem_stdAt f)) l
      rw [TopStep.redV_single, Matrix.mulVec_single_one] at h6
      rw [← TopStep.redV_single]
      exact h6.symm.trans h5
    refine (uni_iff rfl).2 ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [key j i hij.le, Pi.single_eq_of_ne fun h => by rw [h] at hij; omega]
    · rw [key i i le_rfl, Pi.single_eq_same]

theorem grpG_zero : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), cst.sharp = true → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → GrpG sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  intro X Pr R Ch sel S mu cst P hP hs _ M
  have hm := R.two_le_m
  have e1 : (colLev Ch 0 ⟨P.1, hP⟩).H = uniUT (R.N 0) _ R.k [] := by
    unfold colLev
    rw [if_pos (by omega)]
    rfl
  have e2 : Jat (Pr := Pr) cst.sharp 0 P.1 = LocE.JGsym P.1 (qOf P.1) R.k R.rS R.r R.t (R.N 0) (cOf R 0) := by
    unfold Jat
    rw [if_pos hP, if_pos hs]
  unfold prCat
  rw [e1, e2]
  exact uni_iff_prX (by simp [Ranks.N]) _ _ _ _ (by unfold Ranks.rS Ranks.r; omega) M

end GlobalTheory.Mem.ZeroGrp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelGroupReductionStepZeroTypePrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelGroupReduction_stepZero_typePrime : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), cst.sharp = true → GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → GrpG sel mu cst 0 P 1 (colLev Ch 0 ⟨P.1, hP⟩) := by
  first | exact @GlobalTheory.Mem.ZeroGrp.grpG_zero | exact GlobalTheory.Mem.ZeroGrp.grpG_zero | (intros; apply GlobalTheory.Mem.ZeroGrp.grpG_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineEigenvalueEqOneOfBoxSumNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineEigenvalueEqOneOfBoxSumNeZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero

def periods {V K : Type} [AddCommGroup V] (f : V → K) : AddSubgroup V where
  carrier := {u | ∀ t, f (t + u) = f t}
  zero_mem' := fun t => by simp
  add_mem' := fun {a b} ha hb t => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha t => by rw [← ha (t + -a)]; simp

theorem eigen_eq_one_of_reps {V K : Type} [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (L : AddSubgroup V)
    (S : Finset V) (hf : ∀ v, ∀ u ∈ L, f (v + u) = f v) (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ L → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ L) (T : V ≃+ V) (b : V) (χ : K) (hT : ∀ t, f (T t + b) = χ * f t)
    (hS : ∑ s ∈ S, f s ≠ 0) : χ = 1 := by
  classical
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hsurj : ∀ v, ∃ t, T t + b = v := fun v => ⟨T.symm (v - b), by simp⟩
  have hχ : χ ≠ 0 := by
    rintro rfl
    obtain ⟨t, rfl⟩ := hsurj t₀
    exact ht₀ (by rw [hT, zero_mul])
  set M := periods f with hM
  have hMf : ∀ v, ∀ u ∈ M, f (v + u) = f v := fun v u hu => hu v
  have hLM : L ≤ M := fun u hu t => hf t u hu
  have hTM : ∀ u, T u ∈ M ↔ u ∈ M := fun u => by
    have e : ∀ t, f (T t + b + T u) = χ * f (t + u) := fun t => by
      rw [← hT, map_add (f := _)]; congr 1; abel
    constructor
    · intro h t
      apply mul_left_cancel₀ hχ
      rw [← e, hMf _ _ h, hT]
    · intro h v
      obtain ⟨t, rfl⟩ := hsurj v
      rw [e, hMf _ _ h, hT]
  have hmap : M.map (T : V →+ V) = M := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hTM u).2 hu
    · intro hv
      exact ⟨T.symm v, (hTM _).1 (by simpa using hv), by simp⟩
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := fun v => by
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    simpa using hMf v _ h
  let S' : Finset V := S.image fun s => (QuotientAddGroup.mk s : V ⧸ M).out
  have hinj' : ∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ M → s = s' := fun s hs s' hs' h => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 hs'
    have := QuotientAddGroup.eq_iff_sub_mem.2 h
    simp only [QuotientAddGroup.out_eq'] at this
    rw [this]
  have hcov' : ∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ M := fun v hv => by
    obtain ⟨s, hs, e⟩ := hcov v hv
    refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', QuotientAddGroup.eq_iff_sub_mem]
    exact hLM e
  have i1 : M.relIndex L ≠ 0 := by rw [AddSubgroup.relIndex_eq_one.2 hLM]; exact one_ne_zero
  have i2 : L.relIndex M ≠ 0 :=
    boxSum_ne_zero_invariant_affineChange.relIndex_ne_zero_of_cover L M (S.image fun s => s - t₀) fun k hk => by
      obtain ⟨s, hs, e⟩ := hcov (t₀ + k) (by rwa [hMf _ _ hk])
      refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
      convert e using 1
      abel
  have h1 := (sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff V K f L M S S' i1 i2 hf hMf hinj hcov hinj' hcov').1 hS
  have h2 := sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq f M M S' le_rfl (by simp) hMf hinj' hcov'
  rw [AddSubgroup.relIndex_self, Nat.cast_one, one_mul] at h2
  rw [← h2] at h1
  let e : V ⧸ M ≃ V ⧸ M := (QuotientAddGroup.congr M M T hmap).toEquiv.trans (Equiv.addRight (QuotientAddGroup.mk b))
  have he : ∀ c : V ⧸ M, f (e c).out = χ * f c.out := fun c => by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective c
    have : e (QuotientAddGroup.mk v) = QuotientAddGroup.mk (T v + b) := rfl
    rw [this, hout, hout, hT]
  have h3 : ∑ᶠ c : V ⧸ M, f (e c).out = ∑ᶠ c : V ⧸ M, f c.out := finsum_comp_equiv (f := fun c : V ⧸ M => f c.out) e
  simp only [he] at h3
  rw [← mul_finsum] at h3
  exact mul_right_cancel₀ h1 (by rw [h3, one_mul])

theorem eigen_eq_one : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E) (χ : K), (∀ t, f (T t + b) = χ * f t) → boxSum P N N f ≠ 0 → χ = 1 := by
  intro E _ _ K _ _ P hP ι _ _ f N hf T b χ hT hS
  have hq := NormalFormAtPrime.qOf_ne_zero P
  have h3 := rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP N N
  refine eigen_eq_one_of_reps f (boxSum_ne_zero_invariant_affineChange.lat P ι ((qOf P : E) ^ N)⁻¹)
    (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) N N) (fun v u hu => ?_) (fun s hs s' hs' h => ?_)
    (fun v hv => ?_) T.toAddEquiv b χ hT (right_ne_zero_of_mul hS)
  · have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  · funext i
    exact h3.1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  · choose s hs hs' using fun i => h3.2 (v i) (hf.1 v hv i)
    exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩

end GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineEigenvalueEqOneOfBoxSumNeZeroStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_eigenvalue_eq_one_of_boxSum_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E) (χ : K), (∀ t, f (T t + b) = χ * f t) → boxSum P N N f ≠ 0 → χ = 1 := by
  first | exact @GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one | exact GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one | (intros; apply GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleRepresentativesFiniteLevelCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleRepresentativesFiniteLevelCosets
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxFin

open GlobalTheory.Mem.LevFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_classes {N q : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (j : ℕ) :
    ∃ (ι : Type) (_ : Finite ι) (f : (Sp E N ≃ₗ[E] Sp E N) → ι), ∀ h h' : Sp E N ≃ₗ[E] Sp E N,
      (∀ x ∈ LocE.sclLat P q N e, h⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h x ∈ LocE.sclLat P q N e) →
      (∀ x ∈ LocE.sclLat P q N e, h'⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h' x ∈ LocE.sclLat P q N e) →
      f h = f h' → ∀ x ∈ LocE.sclLat P q N e, (q : E)⁻¹ • ((h⁻¹ * h') x - x) ∈ LocE.sclLat P q N e := by
  classical
  have hc : ((q ^ (j + 1) : ℕ) : E) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hq
  have hq' : ((q ^ (j + 1) : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hc (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa only [Ne, Ideal.span_singleton_eq_bot] using hq')
  have hz : ∀ l : ℕ, (q : E) ^ e l ≠ 0 := fun l => zpow_ne_zero _ hq
  have he : ∀ i : Fin N, (Pi.single i ((q : E) ^ e i.1) : Sp E N) ∈ LocE.sclLat P q N e := by
    intro i
    rw [GlobalTheory.CongLevel.mem_sclLat]
    intro l
    rw [Pi.single_apply]
    split_ifs with hl
    · rw [hl, inv_mul_cancel₀ (hz _)]
      exact GlobalTheory.GO.ChRoot.intAt_one'
    · rw [mul_zero]
      exact GlobalTheory.GO.ChRoot.intAt_zero'
  let m : (Sp E N ≃ₗ[E] Sp E N) → Fin N → Fin N → E :=
    fun h i l => ((q : E) ^ e l.1)⁻¹ * ((q : E) ^ j * h (Pi.single i ((q : E) ^ e i.1)) l)
  have hex : ∀ a : E, ∃ r : 𝓞 E, IntAt P a → IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (a - algebraMap (𝓞 E) E r)) := by
    intro a
    by_cases ha : IntAt P a
    · obtain ⟨r, hr⟩ := exists_int_congr hc ha
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose r hr using hex
  refine ⟨Fin N → Fin N → 𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}, inferInstance,
    fun h i l => Ideal.Quotient.mk _ (r (m h i l)), fun a b ha hb hab x hx => ?_⟩
  have hma : ∀ i l, IntAt P (m a i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (ha _ (he i)).2 l
  have hmb : ∀ i l, IntAt P (m b i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (hb _ (he i)).2 l
  have h1 : ∀ i l, IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    intro i l
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun hab i) l))
    have ht' := congrArg (algebraMap (𝓞 E) E) ht
    simp only [map_mul, map_natCast, map_sub] at ht'
    have := ((hr _ (hmb i l)).add (intAt_neg (hr _ (hma i l)))).add (intAt_neg (IntAt.coe P t))
    convert this using 1
    generalize ((q ^ (j + 1) : ℕ) : E) = c at *
    field_simp
    linear_combination ht'
  have e1 : (q : E)⁻¹ • ((a⁻¹ * b) x - x) = a⁻¹ ((q : E)⁻¹ • (b x - a x)) := by
    rw [map_smul, map_sub, show a⁻¹ (a x) = x from LinearEquiv.symm_apply_apply _ x]
    rfl
  rw [e1]
  refine (ha _ ?_).1
  rw [GlobalTheory.CongLevel.mem_sclLat] at hx ⊢
  intro l
  have ex : x = ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) • (Pi.single i ((q : E) ^ e i.1) : Sp E N) := by
    funext l
    have := hz l.1
    simp [Finset.sum_apply, Pi.single_apply]
    field_simp
  have e2 : ((q : E) ^ e l.1)⁻¹ * ((q : E)⁻¹ • (b x - a x)) l =
      ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) * (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    conv_lhs => rw [ex]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      Finset.mul_sum, m]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hz l.1
    have := hz i.1
    push_cast
    field_simp
    ring
  rw [e2]
  exact Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) GlobalTheory.GO.ChRoot.intAt_zero' fun i _ =>
    (hx i).mul (h1 i l)

theorem exists_finite_index_of_adm_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  intro X Pr R sharp j P
  classical
  have hq := qOf_ne P
  have hb : ∀ h : AutY X R j, admitted Pr j P h → ∀ x ∈ lamYat (Pr := Pr) (R := R) j P,
      h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧ ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P := by
    intro h hh
    by_cases hP : P ∈ Pr.vGs
    · have hs := hh.1 hP
      intro x hx
      refine ⟨((inv_mem hs) x).2 hx, ?_⟩
      rw [← Nat.cast_pow]
      exact natCast_smul_mem _ _ ((hs x).2 hx)
    · exact (between_iff hP h).2 (hh.2 hP)
  obtain ⟨ι, hι, f, hf⟩ := exists_classes (P := P) (N := R.N j + cOf R j) hq
    (LocE.scE (R.N j) (if P ∈ Pr.vGs then fun i => i + 1 else 0)) j
  refine ⟨ι, hι, f, fun h h' hh hh' e => ?_⟩
  have h1 := hf h h' (hb h hh) (hb h' hh') e
  have h2 := hf h' h (hb h' hh') (hb h hh) e.symm
  refine mem_Jat _ _ _ _ (stab_of_cong hq _ _ h1 ?_) h1
  rw [mul_inv_rev, inv_inv]
  exact h2

end GlobalTheory.Mem.Col2.IdxFin

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleRepresentativesFiniteLevelCosetsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleRepresentatives_finite_level_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  first | exact @GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets | exact GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets | (intros; apply GlobalTheory.Mem.Col2.IdxFin.exists_finite_index_of_adm_cosets <;> assumption)
end
end
