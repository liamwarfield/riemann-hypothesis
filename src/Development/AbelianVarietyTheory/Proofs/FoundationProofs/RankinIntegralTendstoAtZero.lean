module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumModerateMeasurabl
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBound
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FirstDiff
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FirstDiff
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.TermDiff

lemma rpow_neg_sub_le {x y p : ℝ} (hx : 1/2 ≤ x) (hxy : x ≤ y) (hp0 : 0 ≤ p) (hp2 : p ≤ 2) :
    |x ^ (-p) - y ^ (-p)| ≤ 8 * (y - x) / y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  set r := x / y with hr
  have hr0 : 0 < r := div_pos hx0 hy0
  have hr1 : r ≤ 1 := (div_le_one hy0).2 hxy
  have hyr : y ^ (-p) = x ^ (-p) * r ^ p := by
    rw [hr, Real.div_rpow hx0.le hy0.le, Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
    have : 0 < x ^ p := Real.rpow_pos_of_pos hx0 p
    have : 0 < y ^ p := Real.rpow_pos_of_pos hy0 p
    field_simp
  have hrp1 : r ^ p ≤ 1 := Real.rpow_le_one hr0.le hr1 hp0
  have hrp2 : r ^ (2:ℝ) ≤ r ^ p := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 hp2
  have hr2 : r ^ (2:ℝ) = r ^ 2 := Real.rpow_two r
  have hxp : x ^ (-p) ≤ 4 := by
    rw [Real.rpow_neg hx0.le, ← Real.inv_rpow hx0.le]
    have h1 : x⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hx0 (by norm_num)]; linarith
    calc x⁻¹ ^ p ≤ (2:ℝ) ^ p := Real.rpow_le_rpow (inv_nonneg.2 hx0.le) h1 hp0
      _ ≤ (2:ℝ) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp2
      _ = 4 := by norm_num
  have hxp0 : 0 ≤ x ^ (-p) := Real.rpow_nonneg hx0.le _
  rw [hyr]
  have e : x ^ (-p) - x ^ (-p) * r ^ p = x ^ (-p) * (1 - r ^ p) := by ring
  rw [e, abs_of_nonneg (mul_nonneg hxp0 (by linarith))]
  have h1r : 1 - r ^ p ≤ 2 * (1 - r) := by
    have : 1 - r^2 ≤ 2 * (1 - r) := by nlinarith [mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hr1)]
    rw [hr2] at hrp2
    linarith
  have h1r' : 1 - r = (y - x) / y := by rw [hr]; field_simp
  calc x ^ (-p) * (1 - r ^ p) ≤ 4 * (2 * (1 - r)) :=
        mul_le_mul hxp h1r (by linarith) (by norm_num)
    _ = 8 * (y - x) / y := by rw [h1r']; ring

lemma norm_pow_sub_pow_le (z w : ℂ) (n : ℕ) (M : ℝ) (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖w ^ (n+1) - z ^ (n+1)‖ ≤ (n+1) * M ^ n * ‖w - z‖ := by
  rw [← geom_sum₂_mul, norm_mul]
  gcongr
  have hM : 0 ≤ M := (norm_nonneg z).trans hz
  calc ‖∑ i ∈ Finset.range (n+1), w ^ i * z ^ (n + 1 - 1 - i)‖
      ≤ ∑ i ∈ Finset.range (n+1), ‖w ^ i * z ^ (n + 1 - 1 - i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), M ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [norm_mul, norm_pow, norm_pow]
        calc ‖w‖ ^ i * ‖z‖ ^ (n + 1 - 1 - i) ≤ M ^ i * M ^ (n + 1 - 1 - i) := by gcongr
          _ = M ^ n := by rw [← pow_add]; congr 1; omega
    _ = (n+1) * M ^ n := by simp

lemma inv_pow_sub_le (j : ℕ) (z w : ℂ) (hz : 0 < ‖z‖) (hwz : ‖w - z‖ ≤ ‖z‖ / 2) :
    ‖(z ^ j)⁻¹ - (w ^ j)⁻¹‖ ≤ j * 4 ^ j * ‖w - z‖ / ‖z‖ ^ (j + 1) := by
  have hW1 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
    have := norm_sub_le w (w - z); simpa using this
  have hW2 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
    have := norm_add_le z (w - z); simpa using this
  have hWl : ‖z‖ / 2 ≤ ‖w‖ := by linarith
  have hW0 : 0 < ‖w‖ := by linarith
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz
  have hw0 : w ≠ 0 := norm_pos_iff.1 hW0
  cases j with
  | zero => simp
  | succ n =>
    rw [inv_sub_inv (pow_ne_zero _ hz0) (pow_ne_zero _ hw0), norm_div, norm_mul, norm_pow, norm_pow]
    have hM : ‖w‖ ≤ 2 * ‖z‖ := by linarith
    have hnum := norm_pow_sub_pow_le z w n (2 * ‖z‖) (by linarith) hM
    have hden : ‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1) ≤ ‖z‖ ^ (n+1) * ‖w‖ ^ (n+1) := by gcongr
    have hdpos : 0 < ‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1) := by positivity
    calc ‖w ^ (n+1) - z ^ (n+1)‖ / (‖z‖ ^ (n+1) * ‖w‖ ^ (n+1))
        ≤ ((n+1) * (2 * ‖z‖) ^ n * ‖w - z‖) / (‖z‖ ^ (n+1) * (‖z‖ / 2) ^ (n+1)) :=
          div_le_div₀ (by positivity) hnum hdpos hden
      _ = (n+1) * 2 ^ (2 * n + 1) * ‖w - z‖ / ‖z‖ ^ (n + 2) := by
          rw [div_pow, mul_pow]; field_simp; ring
      _ ≤ ((n+1 : ℕ) : ℝ) * 4 ^ (n+1) * ‖w - z‖ / ‖z‖ ^ (n + 1 + 1) := by
          push_cast
          gcongr
          calc (2:ℝ) ^ (2 * n + 1) ≤ 2 ^ (2 * n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 4 ^ (n+1) := by rw [show 2 * n + 2 = 2 * (n+1) by ring, pow_mul]; norm_num

theorem first_diff : ∀ j : ℕ, ∃ C : ℝ, ∀ (s : ℝ) (z a : ℂ), 0 ≤ s → s ≤ 1 → 1 ≤ ‖z‖ → 2 * ‖a‖ ≤ ‖z‖ → ‖trm j s z - trm j s (z + a)‖ ≤ C * ‖a‖ / ‖z‖ ^ (j + 1) := by
  intro j
  refine ⟨j * 4 ^ j + 8 * 2 ^ j, ?_⟩
  intro s z a hs0 hs1 hz ha
  have hZ : 0 < ‖z‖ := by linarith
  have hwz : (z + a) - z = a := by ring
  have hA : ‖(z + a) - z‖ ≤ ‖z‖ / 2 := by rw [hwz]; linarith
  have hW1 : ‖z‖ ≤ ‖z + a‖ + ‖a‖ := by
    have := norm_sub_le (z + a) a; simpa using this
  have hW2 : ‖z + a‖ ≤ ‖z‖ + ‖a‖ := norm_add_le z a
  have hWl : ‖z‖ / 2 ≤ ‖z + a‖ := by linarith
  have hW0 : 0 < ‖z + a‖ := by linarith
  have hv : ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
  have hdv : ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)‖ ≤ 8 * ‖a‖ / ‖z‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, neg_mul]
    rcases le_total ‖z‖ ‖z + a‖ with h | h
    · refine (rpow_neg_sub_le (by linarith) h (by linarith) (by linarith)).trans ?_
      rw [div_le_div_iff₀ hW0 hZ]
      nlinarith
    · rw [abs_sub_comm]
      refine (rpow_neg_sub_le (by linarith) h (by linarith) (by linarith)).trans ?_
      gcongr
      linarith
  have hu' : ‖((z + a) ^ j)⁻¹‖ ≤ 2 ^ j / ‖z‖ ^ j := by
    rw [norm_inv, norm_pow, ← one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 1 * ‖z‖ ^ j = 2 ^ j * (‖z‖ / 2) ^ j := by rw [div_pow]; field_simp
      _ ≤ 2 ^ j * ‖z + a‖ ^ j := by gcongr
  have hdu := inv_pow_sub_le j z (z + a) hZ hA
  rw [hwz] at hdu
  unfold trm
  have e : (z ^ j)⁻¹ * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((z + a) ^ j)⁻¹ * ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)
      = ((z ^ j)⁻¹ - ((z + a) ^ j)⁻¹) * ((‖z‖ ^ (-2 * s) : ℝ) : ℂ)
        + ((z + a) ^ j)⁻¹ * (((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)) := by ring
  rw [e]
  calc _ ≤ ‖(z ^ j)⁻¹ - ((z + a) ^ j)⁻¹‖ * ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ)‖
        + ‖((z + a) ^ j)⁻¹‖ * ‖((‖z‖ ^ (-2 * s) : ℝ) : ℂ) - ((‖z + a‖ ^ (-2 * s) : ℝ) : ℂ)‖ :=
          norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ (j * 4 ^ j * ‖a‖ / ‖z‖ ^ (j + 1)) * 1 + (2 ^ j / ‖z‖ ^ j) * (8 * ‖a‖ / ‖z‖) := by
          gcongr
    _ = (j * 4 ^ j + 8 * 2 ^ j) * ‖a‖ / ‖z‖ ^ (j + 1) := by
          field_simp; ring

end GlobalTheory.EisM.TermDiff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FirstDiffStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_trm_sub_trm_add_le : ∀ j : ℕ, ∃ C : ℝ, ∀ (s : ℝ) (z a : ℂ), 0 ≤ s → s ≤ 1 → 1 ≤ ‖z‖ → 2 * ‖a‖ ≤ ‖z‖ → ‖trm j s z - trm j s (z + a)‖ ≤ C * ‖a‖ / ‖z‖ ^ (j + 1) := by
  first | exact @GlobalTheory.EisM.TermDiff.first_diff | exact GlobalTheory.EisM.TermDiff.first_diff | (intros; apply GlobalTheory.EisM.TermDiff.first_diff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBound
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section
namespace GlobalTheory.RowBd

lemma summ3 : Summable (fun x : ℤ × ℤ => ‖x‖ ^ (-(3:ℝ))) := by
  have h := EisensteinSeries.summable_one_div_norm_rpow (k := 3) (by norm_num)
  rw [← (finTwoArrowEquiv ℤ).symm.summable_iff] at h
  refine h.congr fun p => ?_
  simp [EisensteinSeries.norm_eq_max_natAbs, Prod.norm_def, Int.norm_eq_abs]

def shear (n : ℤ) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun x := (x.1, x.2 + n * x.1)
  invFun x := (x.1, x.2 - n * x.1)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

lemma low (τ : ℍ) (c d : ℤ) :
    min 1 τ.im * ‖shear ⌊τ.re⌋ (c, d)‖ ≤ 2 * ‖(c : ℂ) * τ + d‖ := by
  set m := min 1 τ.im
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmy : m ≤ τ.im := min_le_right _ _
  have hm0 : 0 < m := lt_min one_pos τ.im_pos
  set z : ℂ := (c : ℂ) * τ + d
  have hre : z.re = c * τ.re + d := by simp [z]
  have him : z.im = c * τ.im := by simp [z]
  have h1 : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hfl0 : (0:ℝ) ≤ τ.re - ⌊τ.re⌋ := by have := Int.floor_le τ.re; linarith
  have hfl1 : τ.re - ⌊τ.re⌋ < 1 := by have := Int.lt_floor_add_one τ.re; linarith
  have hc : m * |(c:ℝ)| ≤ ‖z‖ := by
    rw [him, abs_mul, abs_of_pos τ.im_pos] at h2
    nlinarith [abs_nonneg (c:ℝ)]
  have he : |((d + ⌊τ.re⌋ * c : ℤ) : ℝ)| ≤ |z.re| + |(c:ℝ)| := by
    have : ((d + ⌊τ.re⌋ * c : ℤ) : ℝ) = z.re - c * (τ.re - ⌊τ.re⌋) := by rw [hre]; push_cast; ring
    rw [this]
    have ha := abs_sub z.re (c * (τ.re - ⌊τ.re⌋))
    have hb : |(c:ℝ) * (τ.re - ⌊τ.re⌋)| ≤ |(c:ℝ)| := by
      rw [abs_mul, abs_of_nonneg hfl0]
      nlinarith [abs_nonneg (c:ℝ)]
    linarith
  simp only [shear, Equiv.coe_fn_mk, Prod.norm_def, Int.norm_eq_abs]
  rw [mul_max_of_nonneg _ _ hm0.le, max_le_iff]
  constructor
  · nlinarith [norm_nonneg z]
  · nlinarith [abs_nonneg (c:ℝ), abs_nonneg z.re]

lemma trm_le {j : ℕ} (hj : 1 ≤ j) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {μ : ℝ} (hμ0 : 0 < μ)
    (hμ1 : μ ≤ 1) {z : ℂ} (hz : z = 0 ∨ μ ≤ ‖z‖) : ‖trm j s z‖ ≤ (μ ^ (j + 2))⁻¹ := by
  have hB : 1 ≤ (μ ^ (j + 2))⁻¹ := (one_le_inv₀ (pow_pos hμ0 _)).mpr (pow_le_one₀ hμ0.le hμ1)
  rcases hz with rfl | hz
  · simp [trm, zero_pow (by omega : j ≠ 0)]
    positivity
  set t := ‖z‖ with ht
  have ht0 : 0 < t := hμ0.trans_le hz
  have hn : ‖trm j s z‖ = (t ^ j)⁻¹ * t ^ (-2 * s) := by
    simp only [trm, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), ht]
  rw [hn]
  rcases le_or_gt 1 t with h1 | h1
  · have a1 : t ^ (-2 * s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    have a2 : (t ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
    have a3 : 0 ≤ t ^ (-2 * s) := Real.rpow_nonneg ht0.le _
    calc (t ^ j)⁻¹ * t ^ (-2 * s) ≤ 1 * 1 := mul_le_mul a2 a1 a3 zero_le_one
      _ ≤ _ := by linarith
  · have a1 : t ^ (-2 * s) ≤ t ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht0 h1.le (by linarith)
    have a3 : t ^ (-2:ℝ) = (t ^ 2)⁻¹ := by rw [Real.rpow_neg ht0.le]; norm_cast
    have a4 : 0 ≤ (t ^ j)⁻¹ := by positivity
    calc (t ^ j)⁻¹ * t ^ (-2 * s) ≤ (t ^ j)⁻¹ * (t ^ 2)⁻¹ := by
          rw [← a3]; exact mul_le_mul_of_nonneg_left a1 a4
      _ = (t ^ (j + 2))⁻¹ := by rw [pow_add, mul_inv]
      _ ≤ (μ ^ (j + 2))⁻¹ := inv_anti₀ (pow_pos hμ0 _) (pow_le_pow_left₀ hμ0.le hz _)

lemma dif_eq {L : ℕ} (hL : 0 < L) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (x : ℤ × ℤ) :
    dif L v F x = (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, (F x - F (x + (r:ℤ) • v)) := by
  simp only [dif]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub,
    ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hL.ne'), one_mul]

lemma dif_le {L : ℕ} (hL : 0 < L) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (x : ℤ × ℤ) (B : ℝ)
    (h : ∀ r ∈ Finset.range L, ‖F x - F (x + (r:ℤ) • v)‖ ≤ B) : ‖dif L v F x‖ ≤ B := by
  rw [dif_eq hL, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := norm_sum_le (Finset.range L) (fun r => F x - F (x + (r:ℤ) • v))
  have h2 : ∑ r ∈ Finset.range L, ‖F x - F (x + (r:ℤ) • v)‖ ≤ L * B := by
    simpa using Finset.sum_le_card_nsmul _ _ _ h
  rw [inv_mul_le_iff₀ (by exact_mod_cast hL)]
  linarith

lemma one_le_norm {x : ℤ × ℤ} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  rw [Prod.norm_def, Int.norm_eq_abs, Int.norm_eq_abs]
  by_cases h1 : x.1 = 0
  · have h2 : x.2 ≠ 0 := fun h => hx (Prod.ext h1 h)
    exact le_max_of_le_right (by exact_mod_cast Int.one_le_abs h2)
  · exact le_max_of_le_left (by exact_mod_cast Int.one_le_abs h1)

def g (x : ℤ × ℤ) : ℝ := ‖x‖ ^ (-(3:ℝ)) + if x = 0 then 1 else 0

lemma g_summ : Summable g := summ3.add (hasSum_ite_eq (0 : ℤ × ℤ) (1:ℝ)).summable

lemma g_nonneg (x : ℤ × ℤ) : 0 ≤ g x := by
  unfold g; have := Real.rpow_nonneg (norm_nonneg x) (-(3:ℝ)); split_ifs <;> linarith

lemma g_zero : g 0 = 1 := by simp [g, Real.zero_rpow (by norm_num : -(3:ℝ) ≠ 0)]

lemma g_ne {x : ℤ × ℤ} (hx : x ≠ 0) : g x = (‖x‖ ^ 3)⁻¹ := by
  simp only [g, if_neg hx, add_zero]
  rw [Real.rpow_neg (norm_nonneg x)]; norm_cast

theorem rowbd : ∀ j L : ℕ, 2 ≤ j → 0 < L → ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ∃ u : ℤ × ℤ → ℝ,
    Summable u ∧ ∑' x, u x ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧
    ∀ (s : ℝ) (x : ℤ × ℤ), 0 ≤ s → s ≤ 1 →
      ‖dif L (0, 1) (fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ u x := by
  intro j L hj hL
  obtain ⟨C1, hC1⟩ := GlobalTheory.T.norm_trm_sub_trm_add_le j
  set C1' := max C1 0 with hC1'
  have hC1'0 : 0 ≤ C1' := le_max_right _ _
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL
  set K : ℝ := 2 ^ (j + 3) * (4 * L) ^ 3 + 8 * C1' * L with hK
  have hK0 : 0 ≤ K := by positivity
  set S : ℝ := ∑' x : ℤ × ℤ, g x
  have hS : 0 ≤ S := tsum_nonneg g_nonneg
  refine ⟨K * S, j + 5, fun τ => ?_⟩
  set m := min 1 τ.im with hmdef
  have hm0 : 0 < m := lt_min one_pos τ.im_pos
  have hm1 : m ≤ 1 := min_le_left _ _
  set e := shear ⌊τ.re⌋ with he
  set M : ℝ := (m ^ (j + 5))⁻¹ with hM
  refine ⟨fun x => K * M * g (e x), ?_, ?_, ?_⟩
  · exact (e.summable_iff.mpr g_summ).mul_left _
  · rw [tsum_mul_left, e.tsum_eq g]
    have hMb : M ≤ τ.im ^ (j + 5) + (τ.im ^ (j + 5))⁻¹ := by
      rcases le_total 1 τ.im with h | h
      · have h' : m = 1 := min_eq_left h
        have := one_le_pow₀ h (n := j + 5)
        have : 0 ≤ (τ.im ^ (j + 5))⁻¹ := by positivity
        rw [hM, h', one_pow, inv_one]; linarith
      · have h' : m = τ.im := min_eq_right h
        have := pow_pos τ.im_pos (j + 5)
        rw [hM, h']; linarith
    calc K * M * S = K * S * M := by ring
      _ ≤ K * S * (τ.im ^ (j + 5) + (τ.im ^ (j + 5))⁻¹) :=
        mul_le_mul_of_nonneg_left hMb (mul_nonneg hK0 hS)
  · intro s x hs0 hs1
    set F : ℤ × ℤ → ℂ := fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2) with hF
    have hlow : ∀ y : ℤ × ℤ, m * ‖e y‖ ≤ 2 * ‖(y.1 : ℂ) * τ + y.2‖ := fun y => low τ y.1 y.2
    have hez : ∀ y : ℤ × ℤ, e y = 0 → y = 0 := fun y hy => by
      simp only [he, shear, Equiv.coe_fn_mk, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at hy ⊢
      obtain ⟨h1, h2⟩ := hy
      rw [h1, mul_zero, add_zero] at h2
      exact ⟨h1, h2⟩

    have hFb : ∀ y, ‖F y‖ ≤ ((m / 2) ^ (j + 2))⁻¹ := by
      intro y
      refine trm_le (by omega) hs0 hs1 (by positivity) (by linarith) ?_
      by_cases hy : y = 0
      · left; simp [hy]
      · right
        have h1 : 1 ≤ ‖e y‖ := one_le_norm (fun h => hy (hez y h))
        have := hlow y
        nlinarith
    have htr : ∀ r : ℕ, F (x + (r:ℤ) • ((0:ℤ), (1:ℤ))) =
        trm j s (((x.1 : ℂ) * τ + x.2) + (r:ℂ)) := by
      intro r; simp only [hF]; congr 1; simp; push_cast; ring
    have hM' : M = (m ^ (j + 2))⁻¹ * (m ^ 3)⁻¹ := by
      rw [hM, ← mul_inv, ← pow_add]
    have hm3 : 1 ≤ (m ^ 3)⁻¹ := (one_le_inv₀ (pow_pos hm0 _)).mpr (pow_le_one₀ hm0.le hm1)
    have ha0 : 0 < (m ^ (j + 2))⁻¹ := by positivity
    have hB0 : ((m / 2) ^ (j + 2))⁻¹ = 2 ^ (j + 2) * (m ^ (j + 2))⁻¹ := by
      rw [div_pow, inv_div, div_eq_mul_inv]
    set t := ‖(x.1 : ℂ) * τ + x.2‖ with ht
    set P := ‖e x‖ with hP
    have hxl : m * P ≤ 2 * t := hlow x
    have hP0 : 0 ≤ P := norm_nonneg _
    rcases le_or_gt (2 * (L:ℝ)) t with hA | hB
    ·
      have ht1 : 1 ≤ t := by linarith
      have ht0 : 0 < t := by linarith
      have hx0 : e x ≠ 0 := by
        intro h0
        have hx : x = 0 := hez x h0
        simp [ht, hx] at hA
        linarith
      have hP1 : 1 ≤ P := one_le_norm hx0
      have hstep : ∀ r ∈ Finset.range L, ‖F x - F (x + (r:ℤ) • ((0:ℤ), (1:ℤ)))‖ ≤
          C1' * L * (t ^ 3)⁻¹ := by
        intro r hr
        have hrL : (r:ℝ) ≤ L := by exact_mod_cast (Finset.mem_range.mp hr).le
        have hx' : F x = trm j s ((x.1 : ℂ) * τ + x.2) := rfl
        rw [htr, hx']
        have hra : ‖(r:ℂ)‖ = r := by simp
        have h := hC1 s ((x.1 : ℂ) * τ + x.2) (r:ℂ) hs0 hs1 ht1 (by rw [hra]; linarith)
        rw [hra, ← ht] at h
        have hpow : t ^ 3 ≤ t ^ (j + 1) := pow_le_pow_right₀ ht1 (by omega)
        have hr0 : (0:ℝ) ≤ r := by positivity
        calc _ ≤ C1 * r / t ^ (j + 1) := h
          _ ≤ C1' * r / t ^ (j + 1) := by gcongr; exact le_max_left _ _
          _ ≤ C1' * L / t ^ (j + 1) := by gcongr
          _ ≤ C1' * L / t ^ 3 := by gcongr
          _ = C1' * L * (t ^ 3)⁻¹ := by rw [div_eq_mul_inv]
      refine (dif_le hL _ F x _ hstep).trans ?_
      show C1' * L * (t ^ 3)⁻¹ ≤ K * M * g (e x)
      rw [g_ne hx0, hM']
      have hmP : 0 < m * P := by positivity
      have h8 : (t ^ 3)⁻¹ ≤ 8 * ((m * P) ^ 3)⁻¹ := by
        have h1 : (m * P) ^ 3 ≤ (2 * t) ^ 3 := pow_le_pow_left₀ hmP.le hxl 3
        have h2 : ((2 * t) ^ 3)⁻¹ ≤ ((m * P) ^ 3)⁻¹ := inv_anti₀ (by positivity) h1
        rw [mul_pow, mul_inv] at h2
        norm_num at h2
        linarith
      have hmp : ((m * P) ^ 3)⁻¹ = (m ^ 3)⁻¹ * (P ^ 3)⁻¹ := by rw [mul_pow, mul_inv]
      have hq0 : 0 ≤ (m ^ 3)⁻¹ * (P ^ 3)⁻¹ := by positivity
      have hK1 : 8 * C1' * L ≤ K := by
        have : (0:ℝ) ≤ 2 ^ (j + 3) * (4 * L) ^ 3 := by positivity
        rw [hK]; linarith
      calc C1' * L * (t ^ 3)⁻¹ ≤ C1' * L * (8 * ((m ^ 3)⁻¹ * (P ^ 3)⁻¹)) := by
            rw [← hmp]; exact mul_le_mul_of_nonneg_left h8 (by positivity)
        _ = (8 * C1' * L) * 1 * ((m ^ 3)⁻¹ * (P ^ 3)⁻¹) := by ring
        _ ≤ K * (m ^ (j + 2))⁻¹ * ((m ^ 3)⁻¹ * (P ^ 3)⁻¹) := by
            gcongr
            exact (one_le_inv₀ (pow_pos hm0 _)).mpr (pow_le_one₀ hm0.le hm1)
        _ = K * ((m ^ (j + 2))⁻¹ * (m ^ 3)⁻¹) * (P ^ 3)⁻¹ := by ring
    ·
      have hstep : ∀ r ∈ Finset.range L, ‖F x - F (x + (r:ℤ) • ((0:ℤ), (1:ℤ)))‖ ≤
          2 * ((m / 2) ^ (j + 2))⁻¹ := by
        intro r _
        have h1 := hFb x
        have h2 := hFb (x + (r:ℤ) • ((0:ℤ), (1:ℤ)))
        exact (norm_sub_le _ _).trans (by linarith)
      refine (dif_le hL _ F x _ hstep).trans ?_
      show 2 * ((m / 2) ^ (j + 2))⁻¹ ≤ K * M * g (e x)
      rw [hB0, hM']
      have hK2 : 2 ^ (j + 3) * (4 * L) ^ 3 ≤ K := by
        have : 0 ≤ 8 * C1' * L := by positivity
        rw [hK]; linarith
      have h2j : (2:ℝ) * 2 ^ (j + 2) = 2 ^ (j + 3) := by ring
      by_cases hx0 : e x = 0
      · rw [hx0, g_zero]
        have h4 : (1:ℝ) ≤ (4 * L) ^ 3 := one_le_pow₀ (by linarith)
        have hK3 : 2 ^ (j + 3) ≤ K := by
          have : (2:ℝ) ^ (j + 3) * 1 ≤ 2 ^ (j + 3) * (4 * L) ^ 3 := by gcongr
          linarith
        calc 2 * (2 ^ (j + 2) * (m ^ (j + 2))⁻¹) = 2 ^ (j + 3) * (m ^ (j + 2))⁻¹ * 1 := by
              rw [← h2j]; ring
          _ ≤ K * (m ^ (j + 2))⁻¹ * (m ^ 3)⁻¹ := by gcongr
          _ = _ := by ring
      · rw [g_ne hx0]
        have hP1 : 1 ≤ P := one_le_norm hx0
        have hmP : 0 < m * P := by positivity
        have hmPL : (m * P) ^ 3 ≤ (4 * L) ^ 3 := pow_le_pow_left₀ hmP.le (by linarith) 3
        have hinv : ((4 * (L:ℝ)) ^ 3)⁻¹ ≤ (m ^ 3)⁻¹ * (P ^ 3)⁻¹ := by
          rw [← mul_inv, ← mul_pow]; exact inv_anti₀ (by positivity) hmPL
        have h4 : (0:ℝ) < (4 * L) ^ 3 := by positivity
        calc 2 * (2 ^ (j + 2) * (m ^ (j + 2))⁻¹)
            = 2 ^ (j + 3) * (4 * L) ^ 3 * (m ^ (j + 2))⁻¹ * ((4 * (L:ℝ)) ^ 3)⁻¹ := by
              rw [← h2j]; field_simp
          _ ≤ K * (m ^ (j + 2))⁻¹ * ((m ^ 3)⁻¹ * (P ^ 3)⁻¹) := by gcongr
          _ = K * ((m ^ (j + 2))⁻¹ * (m ^ 3)⁻¹) * (P ^ 3)⁻¹ := by ring

end GlobalTheory.RowBd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeRowDifferenceSummableBoundStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound : ∀ j L : ℕ, 2 ≤ j → 0 < L → ∃ (C : ℝ) (A : ℕ), ∀ τ : ℍ, ∃ u : ℤ × ℤ → ℝ, Summable u ∧ ∑' x, u x ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧ ∀ (s : ℝ) (x : ℤ × ℤ), 0 ≤ s → s ≤ 1 → ‖dif L (0, 1) (fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ u x := by
  first | exact @GlobalTheory.RowBd.rowbd | exact GlobalTheory.RowBd.rowbd | (intros; apply GlobalTheory.RowBd.rowbd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumModerateMeasurabl
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.LatBd

theorem continuous_eisensteinLatticeTermWeightS_exponent {j : ℕ} (hj : 1 ≤ j) (z : ℂ) : Continuous fun s : ℝ => trm j s z := by
  by_cases hz : z = 0
  · subst hz
    have : ∀ s : ℝ, trm j s 0 = 0 := fun s => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · unfold trm
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact continuous_const.rpow (continuous_const.mul continuous_id) fun _ => Or.inl (norm_ne_zero_iff.2 hz)

theorem lin_ne_zero (x : ℤ × ℤ) (hx : x ≠ 0) (τ : ℍ) : (x.1 : ℂ) * (τ : ℂ) + x.2 ≠ 0 := by
  intro h
  have him : (x.1 : ℝ) * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa using this
  have h1 : x.1 = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' τ.im_pos.ne'
  have h2 : x.2 = 0 := by
    have := congrArg Complex.re h
    simp [h1] at this
    exact_mod_cast this
  exact hx (Prod.ext h1 h2)

theorem trm_cont_tau {j : ℕ} (hj : 1 ≤ j) (s : ℝ) (x : ℤ × ℤ) :
    Continuous fun τ : ℍ => trm j s ((x.1 : ℂ) * τ + x.2) := by
  by_cases hx : x = 0
  · subst hx
    have : ∀ τ : ℍ, trm j s (((0 : ℤ × ℤ).1 : ℂ) * τ + (0 : ℤ × ℤ).2) = 0 := fun τ => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · have hc : Continuous fun τ : ℍ => (x.1 : ℂ) * (τ : ℂ) + x.2 :=
      (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
    unfold trm
    refine ((hc.pow j).inv₀ fun τ => pow_ne_zero _ (lin_ne_zero x hx τ)).mul
      (Complex.continuous_ofReal.comp ((continuous_norm.comp hc).rpow_const fun τ => Or.inl ?_))
    exact norm_ne_zero_iff.2 (lin_ne_zero x hx τ)

theorem dif_cont {α : Type*} [TopologicalSpace α] (L : ℕ) (v : ℤ × ℤ) (F : α → ℤ × ℤ → ℂ)
    (h : ∀ x, Continuous fun a => F a x) (x : ℤ × ℤ) : Continuous fun a => dif L v (F a) x := by
  unfold dif
  exact (h x).sub (continuous_const.mul (continuous_finsetSum _ fun r _ => h _))

theorem difdif_le (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (u : ℤ × ℤ → ℝ) (h : ∀ x, ‖dif L v F x‖ ≤ u x)
    (x : ℤ × ℤ) : ‖dif L v (dif L v F) x‖ ≤ u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v) := by
  show ‖dif L v F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, dif L v F (x + (r : ℤ) • v)‖ ≤ _
  refine (norm_sub_le _ _).trans (add_le_add (h x) ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => h _))
    (inv_nonneg.2 (Nat.cast_nonneg L))

theorem hasSum_dom (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (u : ℤ × ℤ → ℝ) {S : ℝ} (hu : HasSum u S) :
    HasSum (fun x => u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v)) (2 * S) := by
  have h1 : ∀ r : ℕ, HasSum (fun x => u (x + (r : ℤ) • v)) S := fun r =>
    (Equiv.addRight ((r : ℤ) • v)).hasSum_iff.2 hu
  have h2 := hasSum_sum (s := Finset.range L) fun r _ => h1 r
  have h3 := hu.add (h2.mul_left ((L : ℝ)⁻¹))
  convert h3 using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp; ring

theorem measurable_tsum_any {X I : Type} [MeasurableSpace X] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (g : X → I → ℂ) (hg : ∀ i, Measurable fun x => g x i) :
    Measurable fun x => ∑' i, g x i := by
  have e : ∀ x, ∑' i, g x i = ∫ i, g x i ∂(Measure.count : Measure I) := fun x => by
    by_cases hf : Summable (g x)
    · have hi : Integrable (g x) (Measure.count : Measure I) := by
        rw [integrable_count_iff]; exact summable_norm_iff.mpr hf
      rw [integral_countable hi]; simp [measureReal_def]
    · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
      intro hi; rw [integrable_count_iff] at hi; exact hf (summable_norm_iff.mp hi)
  simp only [e]
  have hm : Measurable fun p : X × I => g p.1 p.2 := measurable_from_prod_countable_left hg
  exact (StronglyMeasurable.integral_prod_right' (ν := (Measure.count : Measure I))
    hm.stronglyMeasurable).measurable

end GlobalTheory.EisM.LatBd

namespace GlobalTheory.EisM.LatBd

theorem lat_mod_meas_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) →
    (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧
    (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧
    ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  intro j L Φ hj hL ⟨B, hB⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hj1 : 1 ≤ j := by omega
  obtain ⟨C, A, hrow⟩ := GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound j L hj hL

  have dom : ∀ τ : ℍ, ∃ U : ℤ × ℤ → ℝ, ∃ S : ℝ, HasSum U (2 * S) ∧ S ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x, ‖Φ x * dif L (0, 1) (dif L (0, 1)
        fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ B * U x := by
    intro τ
    obtain ⟨u, hus, hule, hu⟩ := hrow τ
    refine ⟨_, _, hasSum_dom L hL (0, 1) u hus.hasSum, hule, fun s hs0 hs1 x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hB x) (difdif_le L (0, 1) _ u (fun x => hu s x hs0 hs1) x) (norm_nonneg _) hB0
  refine ⟨⟨2 * B * C, A, fun s τ hs0 hs1 => ?_⟩, fun s => ?_, fun τ => ?_⟩
  · obtain ⟨U, S, hU, hS, hb⟩ := dom τ
    have h := tsum_of_norm_bounded (hU.mul_left B) (hb s hs0 hs1)
    have hpos : 0 ≤ B * 2 := by positivity
    calc ‖lat j s L (0, 1) Φ τ‖ ≤ B * (2 * S) := h
      _ = (B * 2) * S := by ring
      _ ≤ (B * 2) * (C * (τ.im ^ A + (τ.im ^ A)⁻¹)) := mul_le_mul_of_nonneg_left hS hpos
      _ = 2 * B * C * (τ.im ^ A + (τ.im ^ A)⁻¹) := by ring
  · unfold lat
    refine measurable_tsum_any (fun (τ : ℍ) x => Φ x * dif L (0, 1) (dif L (0, 1)
      fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x) fun x => ?_
    exact (continuous_const.mul (dif_cont L (0, 1) _
      (dif_cont L (0, 1) _ (fun y => trm_cont_tau hj1 s y)) x)).measurable
  · obtain ⟨U, S, hU, -, hb⟩ := dom τ
    unfold lat
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => B * U x) (hU.mul_left B).summable
      (fun x => ?_) ?_
    · have hc : Continuous fun s : ℝ => Φ x * dif L (0, 1) (dif L (0, 1)
          fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x :=
        continuous_const.mul (dif_cont L (0, 1) _ (dif_cont L (0, 1) _ (fun y => continuous_eisensteinLatticeTermWeightS_exponent hj1 _)) x)
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
      exact hb s hs.1.le hs.2.le

end GlobalTheory.EisM.LatBd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumModerateMeasurablStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_moderate_measurable_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧ (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧ ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  first | exact @GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto | exact GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto | (intros; apply GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinIntegralTendstoAtZero
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma rpow_le_add_inv_of_mem_Icc {y s : ℝ} (hy : 0 < y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    y ^ s ≤ y + y⁻¹ := by
  rcases le_or_gt 1 y with h | h
  · have : y ^ s ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h hs1
    rw [Real.rpow_one] at this
    have : 0 ≤ y⁻¹ := inv_nonneg.mpr hy.le
    linarith
  · have h1 : y ^ s ≤ 1 := Real.rpow_le_one hy.le h.le hs0
    have h2 : 1 ≤ y⁻¹ := by rw [le_inv_comm₀ one_pos hy]; simpa using h.le
    linarith

lemma mod_ofReal_norm {F : ℍ → ℂ} (hF : Mod F) : Mod (fun τ => ((‖F τ‖ : ℝ) : ℂ)) := by
  obtain ⟨C, A, h⟩ := hF
  exact ⟨C, A, fun τ => by simpa using h τ⟩

lemma mod_im_pow (A : ℕ) : Mod (fun τ : ℍ => (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, A, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im ^ A + (τ.im ^ A)⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul]

lemma mod_im_add_inv : Mod (fun τ : ℍ => (((τ.im + τ.im⁻¹ : ℝ)) : ℂ)) := by
  refine ⟨1, 1, fun τ => ?_⟩
  have h0 : 0 ≤ τ.im + τ.im⁻¹ := by
    have := τ.im_pos; positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0, one_mul, pow_one]

theorem rankin_tendsto : ∀ (k j L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Φ : ℤ × ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ), 1 ≤ k → 2 ≤ j → 0 < L → 0 < L' → N ∣ L' → Wt L' ρ → CF k L' (ch ε) h → PolyB b → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Tendsto (fun s : ℝ => pet k ρ (qs h) (fun τ => qs b τ * lat j s L (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (pet k ρ (qs h) (fun τ => qs b τ * lat j 0 L (0, 1) Φ τ))) := by
  intro k j L L' N ε Φ ρ h b hk hj hL hL' hN hρ hh hb hΦ
  obtain ⟨⟨C, A, hC⟩, hmeas, hlim⟩ := GlobalTheory.T.regularizedEisensteinLatticeSum_moderate_measurable_tendsto j L Φ hj hL hΦ
  have hbc : Continuous (qs b) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2
  have hhc : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hh.1.1).2
  have him : Continuous (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im
  set G : ℍ → ℂ := fun τ => ((‖qs b τ‖ : ℝ) : ℂ) * ((C : ℂ) * (((τ.im ^ A + (τ.im ^ A)⁻¹ : ℝ)) : ℂ)) *
    (((τ.im + τ.im⁻¹ : ℝ)) : ℂ) with hG
  have hGc : Continuous G := by
    have h1 : Continuous (fun τ : ℍ => (τ.im ^ A)⁻¹) :=
      (him.pow A).inv₀ (fun τ => (pow_pos τ.im_pos A).ne')
    have h2 : Continuous (fun τ : ℍ => τ.im⁻¹) := him.inv₀ (fun τ => τ.im_pos.ne')
    simp only [hG]
    fun_prop
  have hGmod : Mod G := by
    have M := GlobalTheory.T.hasModerateGrowth_algebra_slash_stable
    exact (M.1 _ _ ((M.1 _ _ (mod_ofReal_norm (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth b hb))
      ((M.1 _ _ (M.2.1 (C : ℂ)) (mod_im_pow A)).2)).2) mod_im_add_inv).2
  have hint := GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L' L' N ε h ρ G hk hL' hN hρ hh hGc.aestronglyMeasurable hGmod
  have hρm : Measurable (fun τ => (ρ τ : ℂ)) := Complex.measurable_ofReal.comp hρ.meas
  simp only [pet]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun τ => ‖(ρ τ : ℂ) * (conj (qs h τ) * G τ * (τ.im : ℂ) ^ k)‖) ?_ ?_ hint.norm ?_
  · refine Filter.Eventually.of_forall (fun s => ?_)
    have hs : Measurable (fun τ : ℍ => (((τ.im ^ s : ℝ)) : ℂ)) :=
      Complex.measurable_ofReal.comp ((him.measurable).pow_const s)
    exact (hρm.mul ((((Complex.continuous_conj.comp hhc).measurable).mul ((hbc.measurable.mul (hmeas s)).mul hs)).mul
      ((Complex.measurable_ofReal.comp him.measurable).pow_const k))).aestronglyMeasurable
  · have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
    filter_upwards [hev] with s hs
    refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have hρ0 := hρ.nonneg τ
    have hl := hC s τ hs.1.le hs.2.le
    have hys := rpow_le_add_inv_of_mem_Icc hy hs.1.le hs.2.le
    have hX : 0 ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) := le_trans (norm_nonneg _) hl
    have hys0 : 0 ≤ τ.im ^ s := Real.rpow_nonneg hy.le s
    have key : ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s ≤
        |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹) :=
      mul_le_mul (hl.trans (le_abs_self _)) hys hys0 (abs_nonneg _)
    simp only [hG, norm_mul, Complex.norm_real, Complex.norm_conj, norm_pow, Real.norm_eq_abs,
      norm_norm, abs_norm, Complex.ofReal_mul]
    rw [abs_of_nonneg hy.le, abs_of_nonneg (Real.rpow_nonneg hy.le s),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ τ.im + τ.im⁻¹)]
    have hcomb : |C| * |τ.im ^ A + (τ.im ^ A)⁻¹| = |C * (τ.im ^ A + (τ.im ^ A)⁻¹)| := (abs_mul _ _).symm
    have hP : 0 ≤ |ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k := by positivity
    calc |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * ‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) * τ.im ^ k)
        = (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (‖lat j s L (0, 1) Φ τ‖ * τ.im ^ s) := by ring
      _ ≤ (|ρ τ| * ‖qs h τ‖ * ‖qs b τ‖ * τ.im ^ k) * (|C * (τ.im ^ A + (τ.im ^ A)⁻¹)| * (τ.im + τ.im⁻¹)) :=
        mul_le_mul_of_nonneg_left key hP
      _ = |ρ τ| * (‖qs h τ‖ * (‖qs b τ‖ * (|C| * |τ.im ^ A + (τ.im ^ A)⁻¹|) * (τ.im + τ.im⁻¹)) * τ.im ^ k) := by
        rw [hcomb]; ring
  · refine Filter.Eventually.of_forall (fun τ => ?_)
    have hy := τ.im_pos
    have h1 : Tendsto (fun s : ℝ => (((τ.im ^ s : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 (((τ.im ^ (0:ℝ) : ℝ)) : ℂ)) := by
      have : ContinuousAt (fun s : ℝ => τ.im ^ s) 0 :=
        Real.continuousAt_const_rpow hy.ne'
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp this.tendsto).mono_left nhdsWithin_le_nhds
    have h2 := ((tendsto_const_nhds (x := (ρ τ : ℂ))).mul
      (((tendsto_const_nhds (x := conj (qs h τ))).mul (((tendsto_const_nhds (x := qs b τ)).mul (hlim τ)).mul h1)).mul
        (tendsto_const_nhds (x := (τ.im : ℂ) ^ k))))
    simpa only [Real.rpow_zero, Complex.ofReal_one, mul_one] using h2

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinIntegralTendstoAtZeroStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinIntegral_tendsto_at_zero : ∀ (k j L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Φ : ℤ × ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ), 1 ≤ k → 2 ≤ j → 0 < L → 0 < L' → N ∣ L' → Wt L' ρ → CF k L' (ch ε) h → PolyB b → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Tendsto (fun s : ℝ => pet k ρ (qs h) (fun τ => qs b τ * lat j s L (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (pet k ρ (qs h) (fun τ => qs b τ * lat j 0 L (0, 1) Φ τ))) := by
  first | exact @GlobalTheory.EisM.rankin_tendsto | exact GlobalTheory.EisM.rankin_tendsto | (intros; apply GlobalTheory.EisM.rankin_tendsto <;> assumption)
end
