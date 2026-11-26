module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthAlgebraSlashStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPositivityEulerFactorPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoStepRecursionLocalEulerFactors
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoStepRecursionLocalEulerFactors
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocSer

theorem step (x y : ℂ) (c : ℕ → ℂ) (h1 : c 1 = x + y) (h0 : c 0 = 1)
    (hr : ∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) :
    ∀ r, c (r + 1) = y * c r + x ^ (r + 1) := by
  intro r
  induction r with
  | zero => rw [h1, h0]; ring
  | succ n ih => rw [hr n, ih]; ring

theorem bound (x y z : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1)) :
    ∀ r : ℕ, ‖c r * z ^ r‖ ≤ ((r : ℝ) + 1) * (max ‖x * z‖ ‖y * z‖) ^ r := by
  intro r
  induction r with
  | zero => simp [h0]
  | succ n ih =>
    have e : c (n + 1) * z ^ (n + 1) = (y * z) * (c n * z ^ n) + (x * z) ^ (n + 1) := by
      rw [hs n]; ring
    rw [e]
    set ρ := max ‖x * z‖ ‖y * z‖
    have hx : ‖x * z‖ ≤ ρ := le_max_left _ _
    have hy : ‖y * z‖ ≤ ρ := le_max_right _ _
    have hρ : 0 ≤ ρ := le_trans (norm_nonneg _) hx
    calc ‖(y * z) * (c n * z ^ n) + (x * z) ^ (n + 1)‖
        ≤ ‖y * z‖ * ‖c n * z ^ n‖ + ‖x * z‖ ^ (n + 1) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_pow]
      _ ≤ ρ * (((n : ℝ) + 1) * ρ ^ n) + ρ ^ (n + 1) := by
          gcongr
      _ = (((n + 1 : ℕ) : ℝ) + 1) * ρ ^ (n + 1) := by push_cast; ring

theorem summ1 (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) * ρ ^ r) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have a := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have b := summable_geometric_of_lt_one h0 h1
  exact (a.add b).congr (fun r => by ring)

theorem summ2 (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) ^ 2 * ρ ^ r) := by
  have hn : ‖ρ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  have a := summable_pow_mul_geometric_of_norm_lt_one 2 hn
  have a1 := summable_pow_mul_geometric_of_norm_lt_one 1 hn
  have b := summable_geometric_of_lt_one h0 h1
  exact ((a.add (a1.mul_left 2)).add b).congr (fun r => by ring)

theorem part1 (x y z : ℂ) (c : ℕ → ℂ) (h0 : c 0 = 1)
    (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1))
    (hx : ‖x * z‖ < 1) (hy : ‖y * z‖ < 1) :
    Summable (fun r => c r * z ^ r) ∧ (∑' r, c r * z ^ r) * ((1 - x * z) * (1 - y * z)) = 1 := by
  set ρ := max ‖x * z‖ ‖y * z‖
  have hρ1 : ρ < 1 := max_lt hx hy
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) (le_max_left _ _)
  have hS : Summable (fun r => c r * z ^ r) :=
    Summable.of_norm_bounded (summ1 ρ hρ0 hρ1) (bound x y z c h0 hs)
  refine ⟨hS, ?_⟩
  have hG := tsum_geometric_of_norm_lt_one hx
  have hGs := summable_geometric_of_norm_lt_one hx
  have hne : (1 : ℂ) - x * z ≠ 0 := by
    intro h
    have : x * z = 1 := by linear_combination -h
    rw [this, norm_one] at hx; exact lt_irrefl _ hx
  have hG' : (∑' n : ℕ, (x * z) ^ n) * (1 - x * z) = 1 := by
    rw [hG]; exact inv_mul_cancel₀ hne
  have e1 := hS.tsum_eq_zero_add
  have e2 : ∀ r : ℕ, c (r + 1) * z ^ (r + 1) = (y * z) * (c r * z ^ r) + (x * z) * (x * z) ^ r := by
    intro r; rw [hs r]; ring
  simp_rw [e2] at e1
  rw [Summable.tsum_add (hS.mul_left _) (hGs.mul_left _), tsum_mul_left, tsum_mul_left, h0] at e1
  simp only [pow_zero, mul_one] at e1
  linear_combination (1 - x * z) * e1 + (x * z) * hG'

theorem part2 (x y : ℂ) (c : ℕ → ℂ) (T : ℝ) (hT0 : 0 ≤ T) (hT1 : T < 1) (hx : ‖x‖ ^ 2 * T < 1)
    (hy : ‖y‖ ^ 2 * T < 1) (h0 : c 0 = 1) (hs : ∀ r, c (r + 1) = y * c r + x ^ (r + 1)) :
    (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)
      = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  have hnx : 0 ≤ ‖x‖ := norm_nonneg _
  have hny : 0 ≤ ‖y‖ := norm_nonneg _
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  have hxy : ‖y‖ * (‖x‖ * T) < 1 := by
    have hp := mul_lt_mul'' hx hy (by positivity) (by positivity)
    have e : (‖y‖ * (‖x‖ * T)) ^ 2 = (‖x‖ ^ 2 * T) * (‖y‖ ^ 2 * T) := by ring
    have : (‖y‖ * (‖x‖ * T)) ^ 2 < 1 := by rw [e]; linarith
    nlinarith [mul_nonneg hny (mul_nonneg hnx hT0)]

  set m := max ‖x‖ ‖y‖ with hm
  have hσ : m ^ 2 * T < 1 := by
    rcases max_choice ‖x‖ ‖y‖ with h | h <;> rw [hm, h] <;> assumption
  have hb : ∀ r : ℕ, ‖c r‖ ≤ ((r : ℝ) + 1) * m ^ r := by
    intro r; have := bound x y 1 c h0 hs r; simpa using this
  have hU : Summable (fun r : ℕ => ‖c r‖ ^ 2 * T ^ r) := by
    refine Summable.of_nonneg_of_le (fun r => by positivity) (fun r => ?_)
      (summ2 (m ^ 2 * T) (by positivity) hσ)
    calc ‖c r‖ ^ 2 * T ^ r ≤ (((r : ℝ) + 1) * m ^ r) ^ 2 * T ^ r := by
          gcongr; exact hb r
      _ = ((r : ℝ) + 1) ^ 2 * (m ^ 2 * T) ^ r := by ring
  have hf : ∀ r : ℕ, c r * conj (c r) * (T : ℂ) ^ r = ((‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) := by
    intro r; push_cast; rw [Complex.mul_conj']
  have hVs : Summable (fun r : ℕ => c r * conj (c r) * (T : ℂ) ^ r) := by
    have := (Complex.summable_ofReal).mpr hU
    exact this.congr (fun r => (hf r).symm)
  have hVdef : ((∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r : ℝ) : ℂ) = ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r := by
    rw [Complex.ofReal_tsum]; congr 1; funext r; exact (hf r).symm

  have hW : Summable (fun r => c r * (conj x * T) ^ r) ∧
      (∑' r, c r * (conj x * T) ^ r) * ((1 - x * (conj x * T)) * (1 - y * (conj x * T))) = 1 := by
    refine part1 x y (conj x * T) c h0 hs ?_ ?_
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; exact hxy
  have hW' : Summable (fun r => conj (c r) * (x * T) ^ r) ∧
      (∑' r, conj (c r) * (x * T) ^ r) * ((1 - conj x * (x * T)) * (1 - conj y * (x * T))) = 1 := by
    refine part1 (conj x) (conj y) (x * T) (fun r => conj (c r)) (by simp [h0]) ?_ ?_ ?_
    · intro r
      show conj (c (r + 1)) = conj y * conj (c r) + conj x ^ (r + 1)
      rw [hs r]; simp only [map_add (f := _), map_mul, map_pow]
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
    · rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; linarith [hxy]
  have hGn : ‖x * conj x * (T : ℂ)‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_conj, hnT]; nlinarith
  have hGs := summable_geometric_of_norm_lt_one hGn
  have hG : (∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n) * (1 - x * conj x * T) = 1 := by
    rw [tsum_geometric_of_norm_lt_one hGn]
    refine inv_mul_cancel₀ ?_
    intro h
    have : x * conj x * (T : ℂ) = 1 := by linear_combination -h
    rw [this, norm_one] at hGn; exact lt_irrefl _ hGn
  have e1 := hVs.tsum_eq_zero_add
  have e2 : ∀ r : ℕ, c (r + 1) * conj (c (r + 1)) * (T : ℂ) ^ (r + 1) =
      (T : ℂ) * (y * conj y * (c r * conj (c r) * (T : ℂ) ^ r) + y * conj x * (c r * (conj x * T) ^ r)
        + x * conj y * (conj (c r) * (x * T) ^ r) + x * conj x * (x * conj x * T) ^ r) := by
    intro r; rw [hs r]; simp only [map_add (f := _), map_mul, map_pow]; ring
  simp_rw [e2] at e1
  rw [tsum_mul_left, Summable.tsum_add (((hVs.mul_left _).add (hW.1.mul_left _)).add (hW'.1.mul_left _))
    (hGs.mul_left _), Summable.tsum_add ((hVs.mul_left _).add (hW.1.mul_left _)) (hW'.1.mul_left _),
    Summable.tsum_add (hVs.mul_left _) (hW.1.mul_left _)] at e1
  simp only [tsum_mul_left, h0, map_one, pow_zero, mul_one] at e1
  have hW2 := hW.2
  have hW'2 := hW'.2
  set V := ∑' r : ℕ, c r * conj (c r) * (T : ℂ) ^ r
  set W := ∑' r, c r * (conj x * T) ^ r
  set W' := ∑' r, conj (c r) * (x * T) ^ r
  set G := ∑' n : ℕ, (x * conj x * (T : ℂ)) ^ n
  have key : V * ((1 - x * conj x * T) * (1 - y * conj y * T) * ((1 - x * conj y * T) * (1 - conj x * y * T)))
      = 1 - x * conj x * (y * conj y) * T ^ 2 := by
    linear_combination ((1 - x * conj x * T) * (1 - x * conj y * T) * (1 - conj x * y * T)) * e1
      + (T * y * conj x * (1 - x * conj y * T)) * hW2 + (T * x * conj y * (1 - conj x * y * T)) * hW'2
      + (x * conj x * T * (1 - x * conj y * T) * (1 - conj x * y * T)) * hG
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, hVdef]
  push_cast
  have hx2 : ((‖x‖ : ℂ)) ^ 2 = x * conj x := (Complex.mul_conj' x).symm
  have hy2 : ((‖y‖ : ℂ)) ^ 2 = y * conj y := (Complex.mul_conj' y).symm
  have hxy2 : ((‖x * y‖ : ℂ)) ^ 2 = x * y * conj (x * y) := (Complex.mul_conj' _).symm
  have hn2 : ((‖1 - x * conj y * T‖ : ℂ)) ^ 2 = (1 - x * conj y * T) * conj (1 - x * conj y * T) :=
    (Complex.mul_conj' _).symm
  rw [hx2, hy2, hxy2, hn2]
  simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal]
  linear_combination key

theorem twoStep_eulerFactors : ∀ (x y : ℂ) (c : ℕ → ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∑' r : ℕ, c r * (T : ℂ) ^ r) * ((1 - x * T) * (1 - y * T)) = 1 ∧ (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2) = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  intro x y c T hT0 hT1 hx hy h0 h1 hr
  have hs := step x y c h1 h0 hr
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]
  have hsq : ∀ u : ℂ, ‖u‖ ^ 2 * T < 1 → ‖u * (T : ℂ)‖ < 1 := by
    intro u hu
    rw [norm_mul, hnT]
    have hn : 0 ≤ ‖u‖ * T := mul_nonneg (norm_nonneg _) hT0
    have : (‖u‖ * T) ^ 2 ≤ ‖u‖ ^ 2 * T := by
      have : (‖u‖ * T) ^ 2 = (‖u‖ ^ 2 * T) * T := by ring
      rw [this]
      exact mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) hT0) hT1.le
    nlinarith
  exact ⟨(part1 x y T c h0 hs (hsq x hx) (hsq y hy)).2, part2 x y c T hT0 hT1 hx hy h0 hs⟩

end GlobalTheory.LocSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoStepRecursionLocalEulerFactorsStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoStepRecursion_localEulerFactors : ∀ (x y : ℂ) (c : ℕ → ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 → c 0 = 1 → c 1 = x + y → (∀ r, c (r + 2) = (x + y) * c (r + 1) - x * y * c r) → (∑' r : ℕ, c r * (T : ℂ) ^ r) * ((1 - x * T) * (1 - y * T)) = 1 ∧ (∑' r : ℕ, ‖c r‖ ^ 2 * T ^ r) * ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2) = 1 - ‖x * y‖ ^ 2 * T ^ 2 := by
  first | exact @GlobalTheory.LocSer.twoStep_eulerFactors | exact GlobalTheory.LocSer.twoStep_eulerFactors | (intros; apply GlobalTheory.LocSer.twoStep_eulerFactors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpNormProductLeOne
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
namespace GlobalTheory.EisM

theorem locineq_log_sum {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    T * ‖∑ i, z i‖ ^ 2 ≤ - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
  have hs : ∀ i j, HasSum (fun n : ℕ => (z i * conj (z j) * T) ^ n / n)
      (-Complex.log (1 - z i * conj (z j) * T)) := fun i j =>
    Complex.hasSum_taylorSeries_neg_log (h i j)
  have H := hasSum_sum (s := Finset.univ) (fun i _ => hasSum_sum (s := Finset.univ) (fun j _ => hs i j))
  have H2 := ((Complex.hasSum_iff _ _).mp H).1
  have hterm : ∀ n : ℕ, (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ)).re
      = T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n := by
    intro n
    have e : (∑ i, ∑ j, (z i * conj (z j) * T) ^ n / (n : ℂ))
        = (((T ^ n * ‖∑ i, z i ^ n‖ ^ 2 / n : ℝ)) : ℂ) := by
      have e1 : ∀ i j, (z i * conj (z j) * T) ^ n / (n : ℂ)
          = z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n) := by
        intro i j; rw [map_pow]; ring
      simp_rw [e1]
      have e2 : ∑ i, ∑ j, z i ^ n * conj (z j ^ n) * ((T : ℂ) ^ n / n)
          = (∑ i, z i ^ n) * conj (∑ j, z j ^ n) * ((T : ℂ) ^ n / n) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
        simp_rw [Finset.sum_mul]
      rw [e2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [e, Complex.ofReal_re]
  have hre : (∑ i, ∑ j, -Complex.log (1 - z i * conj (z j) * T)).re
      = - ∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖ := by
    simp [Complex.re_sum, Complex.log_re]
  rw [hre] at H2
  simp_rw [hterm] at H2
  have := le_hasSum H2 1 (fun n _ => by positivity)
  simpa using this

theorem locineq_exp_prod {ι : Type*} [Fintype ι] (z : ι → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (h : ∀ i j, ‖z i * conj (z j) * T‖ < 1) :
    Real.exp (‖∑ i, z i‖ ^ 2 * T) * ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖ ≤ 1 := by
  have hpos : ∀ i j, 0 < ‖1 - z i * conj (z j) * T‖ := by
    intro i j
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun e => ?_)
    have := h i j
    rw [← e, norm_one] at this
    exact lt_irrefl _ this
  have hP : ∏ i, ∏ j, ‖1 - z i * conj (z j) * T‖
      = Real.exp (∑ i, ∑ j, Real.log ‖1 - z i * conj (z j) * T‖) := by
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Real.exp_log (hpos i j)).symm
  rw [hP, ← Real.exp_add, Real.exp_le_one_iff]
  have := locineq_log_sum z T hT h
  linarith

theorem locineq : ∀ (x y : ℂ) (T : ℝ), 0 ≤ T → T < 1 → ‖x‖ ^ 2 * T < 1 → ‖y‖ ^ 2 * T < 1 →
    Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖(1 - x * T) * (1 - y * T)‖ ^ 2 *
      ((1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2)) ≤ 1 := by
  intro x y T hT0 hT1 hx hy
  have hxT : ‖x‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg x, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg x) (norm_nonneg x))]
  have hyT : ‖y‖ * T < 1 := by
    by_contra hc; push_neg at hc
    nlinarith [norm_nonneg y, mul_le_mul_of_nonneg_left hT1.le (mul_nonneg (norm_nonneg y) (norm_nonneg y))]
  have hxy : ‖x‖ * ‖y‖ * T < 1 := by
    nlinarith [mul_nonneg (sq_nonneg (‖x‖ - ‖y‖)) hT0]
  let z : Fin 3 → ℂ := ![1, x, y]
  have hnT : ‖(T : ℂ)‖ = T := by rw [Complex.norm_real, Real.norm_of_nonneg hT0]
  have h : ∀ i j, ‖z i * conj (z j) * T‖ < 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [z, hnT, Complex.norm_conj, abs_of_nonneg hT0] <;> nlinarith
  have key := locineq_exp_prod z T hT0 h
  have c1 : ‖1 - conj x * T‖ = ‖1 - x * T‖ := by
    rw [← Complex.norm_conj (1 - x * T)]; simp
  have c2 : ‖1 - conj y * T‖ = ‖1 - y * T‖ := by
    rw [← Complex.norm_conj (1 - y * T)]; simp
  have c3 : ‖1 - y * conj x * T‖ = ‖1 - x * conj y * T‖ := by
    rw [← Complex.norm_conj (1 - x * conj y * T)]; simp; ring_nf
  have d0 : ‖1 - (T : ℂ)‖ = 1 - T := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dx : ‖1 - x * conj x * T‖ = 1 - ‖x‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have dy : ‖1 - y * conj y * T‖ = 1 - ‖y‖ ^ 2 * T := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  simp only [z, Fin.sum_univ_three, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_one, one_mul, mul_one] at key
  rw [c1, c2, c3, d0, dx, dy] at key
  rw [norm_mul]
  calc _ = Real.exp (‖1 + x + y‖ ^ 2 * T) * ((1 - T) * ‖1 - x * T‖ * ‖1 - y * T‖ *
        (‖1 - x * T‖ * (1 - ‖x‖ ^ 2 * T) * ‖1 - x * conj y * T‖) *
        (‖1 - y * T‖ * ‖1 - x * conj y * T‖ * (1 - ‖y‖ ^ 2 * T))) := by ring
    _ ≤ 1 := key

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPositivityEulerFactorPrime
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.LocIneq

theorem term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) = b (p ^ e) * ((1 / (p : ℝ) ^ (1 + s) : ℝ) : ℂ) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hne : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  rw [LSeries.term_of_ne_zero hne]
  have h1 : ((p ^ e : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ) = ((((p : ℝ) ^ (1 + s)) ^ e : ℝ) : ℂ) := by
    rw [show ((p ^ e : ℕ) : ℂ) = (((p ^ e : ℕ) : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg _)]
    congr 1
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0]
  rw [h1, div_eq_mul_inv]
  congr 1
  push_cast
  rw [one_div, inv_pow]

theorem real_term_prime_pow (b : ℕ → ℂ) (s : ℝ) (p : ℕ) (e : ℕ) :
    ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) = ‖b (p ^ e)‖ ^ 2 * (1 / (p : ℝ) ^ (1 + s)) ^ e := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp0, mul_comm, Real.rpow_mul_natCast hp0, div_eq_mul_inv,
    one_div, inv_pow]

theorem local_positivity_eulerFactor : ∀ (b ω : ℕ → ℂ) (s C : ℝ) (p : ℕ), 0 < s → p.Prime → b 1 = 1 → ‖ω p‖ = 1 → (∀ r : ℕ, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → Real.exp (‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ * ‖∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)‖ ^ 2 * (∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s)) * (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ := by
  intro b ω s C p hs hp hb1 hω hrec hbd
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hC : 0 ≤ C := by
    have := hbd 1
    rw [hb1] at this
    simp at this
    linarith
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self (b p ^ 2 - 4 * ω p)
  set x : ℂ := (b p + z) / 2 with hx
  set y : ℂ := (b p - z) / 2 with hy
  have hxy : x + y = b p := by rw [hx, hy]; ring
  have hxy' : x * y = ω p := by rw [hx, hy]; linear_combination (1 / 4 : ℂ) * hz
  have hc0 : b (p ^ 0) = 1 := by simpa using hb1
  have hc1 : b (p ^ 1) = x + y := by rw [pow_one, hxy]
  have hcr : ∀ r, b (p ^ (r + 2)) = (x + y) * b (p ^ (r + 1)) - x * y * b (p ^ r) := by
    intro r; rw [hxy, hxy']; exact hrec r
  have hroots := GlobalTheory.roots_norm_le_of_bounded_two_step_recursion x y (fun r => b (p ^ r))
    (Real.sqrt C) (Real.sqrt p) (Real.sqrt_nonneg _) hc0 hc1 hcr (by
      intro r
      have h := hbd (p ^ r)
      refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
      rw [mul_pow, ← pow_mul, mul_comm r 2, pow_mul, Real.sq_sqrt hC, Real.sq_sqrt hp0.le]
      simpa using h)
  have hP : (p : ℝ) < (p : ℝ) ^ (1 + s) := by
    conv_lhs => rw [← Real.rpow_one (p : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt hp1 (by linarith)
  have hP0 : 0 < (p : ℝ) ^ (1 + s) := by linarith
  have hsq : 1 / (p : ℝ) ^ (2 * (1 + s)) = (1 / (p : ℝ) ^ (1 + s)) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hp0.le, Real.rpow_two, div_pow, one_pow]
  simp only [term_prime_pow b s p hp, real_term_prime_pow b s p, hsq]
  rw [div_eq_mul_one_div (‖1 + b p‖ ^ 2)]
  have hT0 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
  have hpT : p * (1 / (p : ℝ) ^ (1 + s)) < 1 := by
    rw [mul_one_div, div_lt_one hP0]; exact hP
  generalize 1 / (p : ℝ) ^ (1 + s) = T at hT0 hpT ⊢
  have hT1 : T < 1 := by nlinarith
  have hb : ∀ w : ℂ, ‖w‖ ≤ Real.sqrt p → ‖w‖ ^ 2 * T < 1 := by
    intro w hw
    have : ‖w‖ ^ 2 ≤ p := by
      rw [← Real.sq_sqrt hp0.le]
      exact pow_le_pow_left₀ (norm_nonneg _) hw 2
    nlinarith
  have hxT := hb x hroots.1
  have hyT := hb y hroots.2
  obtain ⟨hL, hR⟩ := GlobalTheory.T.twoStepRecursion_localEulerFactors x y (fun r => b (p ^ r)) T hT0.le hT1 hxT hyT hc0 hc1 hcr
  have hI := GlobalTheory.EisM.locineq x y T hT0.le hT1 hxT hyT
  rw [add_assoc, hxy] at hI
  rw [hxy', hω] at hR
  have hR0 : 0 ≤ ∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r := tsum_nonneg fun r => by positivity
  have hLn := congrArg (fun w : ℂ => ‖w‖ ^ 2) hL
  simp only [norm_one, one_pow] at hLn
  rw [norm_mul, mul_pow] at hLn
  have hL0 : 0 ≤ ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 := by positivity
  generalize (∑' r : ℕ, ‖b (p ^ r)‖ ^ 2 * T ^ r) = R at hR hR0 ⊢
  generalize ‖∑' r : ℕ, b (p ^ r) * (T : ℂ) ^ r‖ ^ 2 = L at hLn hL0 ⊢
  generalize ‖(1 - x * T) * (1 - y * T)‖ ^ 2 = D at hLn hI
  generalize (1 - ‖x‖ ^ 2 * T) * (1 - ‖y‖ ^ 2 * T) * ‖1 - x * conj y * T‖ ^ 2 = E at hR hI
  generalize Real.exp (‖1 + b p‖ ^ 2 * T) = A at hI ⊢
  have h1 : 0 < 1 - T := by linarith
  have h2 : 0 < 1 - T ^ 2 := by nlinarith
  rw [one_pow, one_mul] at hR
  have hK : 0 ≤ (1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹ := by positivity
  have hone : ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹) = 1 := by
    calc ((1 - T) * D * E) * ((1 - T)⁻¹ * L * R * (1 - T ^ 2)⁻¹)
        = ((1 - T) * (1 - T)⁻¹) * (L * D) * ((R * E) * (1 - T ^ 2)⁻¹) := by ring
      _ = 1 := by rw [hLn, hR, mul_inv_cancel₀ h1.ne', mul_inv_cancel₀ h2.ne']; ring
  have h3 := mul_le_mul_of_nonneg_right hI hK
  rwa [mul_assoc, hone, mul_one, one_mul] at h3

end GlobalTheory.LocIneq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalPositivityEulerFactorPrimeStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_positivity_eulerFactor_prime : ∀ (b ω : ℕ → ℂ) (s C : ℝ) (p : ℕ), 0 < s → p.Prime → b 1 = 1 → ‖ω p‖ = 1 → (∀ r : ℕ, b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → Real.exp (‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ * ‖∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)‖ ^ 2 * (∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s)) * (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ := by
  first | exact @GlobalTheory.LocIneq.local_positivity_eulerFactor | exact GlobalTheory.LocIneq.local_positivity_eulerFactor | (intros; apply GlobalTheory.LocIneq.local_positivity_eulerFactor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLe
open Filter Topology

namespace GlobalTheory

theorem one_div_succ_rpow_one_add_le_telescope {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    1 / (x + 1) ^ (1 + s) ≤ (1 / x ^ s - 1 / (x + 1) ^ s) / s := by
  have hx1 : 0 < x + 1 := by linarith
  have hq : 0 < (x + 1) / x := div_pos hx1 hx
  have h1 : 1 - ((x + 1) / x)⁻¹ ≤ Real.log ((x + 1) / x) := Real.one_sub_inv_le_log_of_pos hq
  have h2 : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
  have h3 : 1 + s * (1 / (x + 1)) ≤ ((x + 1) / x) ^ s := by
    rw [Real.rpow_def_of_pos hq]
    have h4 := Real.add_one_le_exp (Real.log ((x + 1) / x) * s)
    have h5 : s * (1 / (x + 1)) ≤ Real.log ((x + 1) / x) * s := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (h2 ▸ h1) hs.le
    linarith
  rw [Real.div_rpow hx1.le hx.le] at h3
  rw [Real.rpow_add hx1, Real.rpow_one]
  have hA : 0 < x ^ s := Real.rpow_pos_of_pos hx _
  have hB : 0 < (x + 1) ^ s := Real.rpow_pos_of_pos hx1 _
  generalize x ^ s = A at *
  generalize (x + 1) ^ s = B at *
  rw [le_div_iff₀ hs]
  have h6 : (1 + s * (1 / (x + 1))) / B ≤ B / A / B := by gcongr
  have h7 : B / A / B = 1 / A := by field_simp
  have h8 : (1 + s * (1 / (x + 1))) / B = 1 / B + 1 / ((x + 1) * B) * s := by field_simp
  linarith

theorem sum_range_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 2), 1 / (n : ℝ) ^ (1 + s)
      ≤ 1 + (1 - 1 / ((k : ℝ) + 1) ^ s) / s := by
  induction k with
  | zero =>
    have : (1 + s) ≠ 0 := by linarith
    simp [Finset.sum_range_succ, Real.zero_rpow this]
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl, Finset.sum_range_succ]
    have h := one_div_succ_rpow_one_add_le_telescope (x := (k : ℝ) + 1) hs (by positivity)
    have e : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 1 + 1 := by push_cast; ring
    have e' : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [e, e']
    have : (1 - 1 / ((k : ℝ) + 1 + 1) ^ s) / s = (1 - 1 / ((k : ℝ) + 1) ^ s) / s
        + (1 / ((k : ℝ) + 1) ^ s - 1 / ((k : ℝ) + 1 + 1) ^ s) / s := by ring
    linarith

theorem tsum_one_div_rpow_one_add_le {s : ℝ} (hs : 0 < s) :
    ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + s) ≤ 1 + 1 / s := by
  refine Real.tsum_le_of_sum_range_le (fun n => by positivity) fun k => ?_
  calc ∑ n ∈ Finset.range k, 1 / (n : ℝ) ^ (1 + s)
      ≤ ∑ n ∈ Finset.range (k + 2), 1 / (n : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => by positivity)
    _ ≤ 1 + (1 - 1 / ((k : ℝ) + 1) ^ s) / s := sum_range_one_div_rpow_one_add_le hs k
    _ ≤ 1 + 1 / s := by
        have : 0 ≤ 1 / ((k : ℝ) + 1) ^ s := by positivity
        gcongr
        linarith

theorem prod_primesBelow_inv_one_sub_one_div_rpow_le :
    ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  intro s hs N
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ (1 + s) :=
    Real.summable_one_div_nat_rpow.2 (by linarith)
  have hE := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) (by simp)
    (fun {m n} _ => by
      simp only [Nat.cast_mul]
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), one_div_mul_one_div])
    hsum.norm N
  have hP : ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹
      = ∏ p ∈ N.primesBelow, ∑' e : ℕ, 1 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) := by
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hp0 : (0 : ℝ) ≤ p := by linarith
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) := Real.one_lt_rpow hp1 (by linarith)
    rw [← tsum_geometric_of_lt_one (by positivity) ((div_lt_one (by linarith)).2 h1)]
    refine tsum_congr fun e => ?_
    rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) e, ← Real.rpow_mul hp0, mul_comm,
      Real.rpow_mul hp0, Real.rpow_natCast, one_div_pow]
  rw [hP, hE]
  exact (Summable.tsum_subtype_le _ _ (fun n => by positivity) hsum).trans
    (tsum_one_div_rpow_one_add_le hs)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowInvOneSubOneDivRpowLeStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le : ∀ (s : ℝ), 0 < s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ ≤ 1 + 1 / s := by
  first | exact @GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | exact GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le | (intros; apply GlobalTheory.prod_primesBelow_inv_one_sub_one_div_rpow_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowZetaTwoAddLeTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowZetaTwoAddLeTwo
open Filter Topology

namespace GlobalTheory

theorem prod_Ico_inv_one_sub_inv_sq (M : ℕ) :
    ∏ n ∈ Finset.Ico 2 (M + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ = 2 * ((M : ℝ) + 1) / ((M : ℝ) + 2) := by
  induction M with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 by ring, Finset.prod_Ico_succ_top (by omega), ih]
    push_cast
    have h1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have h3 : (1 - 1 / ((k:ℝ) + 2) ^ 2) = ((k:ℝ)+1)*((k:ℝ)+3) / ((k:ℝ)+2)^2 := by
      field_simp; ring
    rw [h3]
    field_simp
    ring

theorem one_le_inv_one_sub_inv_sq {n : ℕ} (hn : 2 ≤ n) : 1 ≤ (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 1 / (n:ℝ)^2 := by positivity
  have hlt : 1 / (n:ℝ)^2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  exact one_le_inv₀ (by linarith) |>.mpr (by linarith)

theorem factor_le (s : ℝ) (hs : 0 ≤ s) {p : ℕ} (hp : 2 ≤ p) :
    (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  have hp' : (2:ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (1:ℝ) ≤ p := by linarith
  have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  rw [Real.rpow_two] at hle
  have hsq : (4:ℝ) ≤ (p:ℝ)^2 := by nlinarith
  have hlt : 1 / (p:ℝ)^2 < 1 := by rw [div_lt_one (by positivity)]; linarith
  apply inv_anti₀
  · linarith
  · have : 1 / (p:ℝ) ^ (2 * (1 + s)) ≤ 1 / (p:ℝ)^2 :=
      one_div_le_one_div_of_le (by positivity) hle
    linarith

theorem prod_primesBelow_zeta_two_add_le_two :
    ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  intro s hs N
  have hsub : N.primesBelow ⊆ Finset.Ico 2 (N + 2) := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [Finset.mem_Ico]
    exact ⟨hp.2.two_le, by omega⟩
  have hmem : ∀ p ∈ N.primesBelow, 2 ≤ p := fun p hp => (Nat.prime_of_mem_primesBelow hp).two_le
  calc ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹
      ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have := one_le_inv_one_sub_inv_sq (hmem p hp)
          have h2 := factor_le s hs (hmem p hp)

          have hp' : (2:ℝ) ≤ p := by exact_mod_cast hmem p hp
          have hle : (p:ℝ) ^ (2:ℝ) ≤ (p:ℝ) ^ (2 * (1 + s)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          have hpos : 0 < (p:ℝ) ^ (2 * (1 + s)) := by positivity
          have hlt : 1 / (p:ℝ) ^ (2 * (1 + s)) < 1 := by
            rw [div_lt_one hpos]; rw [Real.rpow_two] at hle; nlinarith
          exact inv_nonneg.mpr (by linarith)
        · intro p hp; exact factor_le s hs (hmem p hp)
    _ ≤ ∏ n ∈ Finset.Ico 2 (N + 2), (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
        rw [← Finset.prod_sdiff hsub]
        have h0 : 0 ≤ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹ :=
          Finset.prod_nonneg fun p hp => le_trans zero_le_one (one_le_inv_one_sub_inv_sq (hmem p hp))
        have h1 : 1 ≤ ∏ n ∈ Finset.Ico 2 (N + 2) \ N.primesBelow, (1 - 1 / (n : ℝ) ^ 2)⁻¹ := by
          apply Finset.one_le_prod₀
          intro n hn
          exact one_le_inv_one_sub_inv_sq (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hn).1).1
        nlinarith
    _ = 2 * ((N : ℝ) + 1) / ((N : ℝ) + 2) := prod_Ico_inv_one_sub_inv_sq N
    _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdPrimesBelowZetaTwoAddLeTwoStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le : ∀ (s : ℝ), 0 ≤ s → ∀ N : ℕ, ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ ≤ 2 := by
  first | exact @GlobalTheory.prod_primesBelow_zeta_two_add_le_two | exact GlobalTheory.prod_primesBelow_zeta_two_add_le_two | (intros; apply GlobalTheory.prod_primesBelow_zeta_two_add_le_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeff
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem tendsto_eulerProduct_LSeries_of_sq : ∀ (b : ℕ → ℂ) (s : ℝ), 0 < s → b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e)) atTop (𝓝 (LSeries b ((1 + s : ℝ) : ℂ))) := by
  intro b s hs hb1 hmul hsum
  have hn : Summable (fun n : ℕ => ‖LSeries.term b ((1 + s : ℝ) : ℂ) n‖) := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + s)) :=
      Real.summable_one_div_nat_rpow.2 (by linarith)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hsum.add h1)
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · positivity
    · rw [Complex.ofReal_re, ← add_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (‖b n‖ - 1), norm_nonneg (b n)]
  refine EulerProduct.eulerProduct (f := LSeries.term b ((1 + s : ℝ) : ℂ)) ?_ ?_ hn ?_
  · simp [LSeries.term, hb1]
  · intro m n hmn
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    rw [LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn0,
      LSeries.term_of_ne_zero (mul_ne_zero hm hn0), hmul m n hmn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, div_mul_div_comm]
  · simp

theorem prod_primesBelow_sq_le_tsum : ∀ (b : ℕ → ℂ) (s : ℝ), b 1 = 1 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) ≤ ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro b s hb1 hmul hsum N
  have h0 : ∀ n : ℕ, 0 ≤ ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := fun n => by positivity
  have key := EulerProduct.prod_primesBelow_tsum_eq_tsum_smoothNumbers
    (f := fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) (by simp [hb1])
    (fun {m n} hmn => by
      simp only [hmul m n hmn, norm_mul, mul_pow, Nat.cast_mul]
      rw [Real.mul_rpow (by positivity) (by positivity), div_mul_div_comm])
    (by simpa only [Real.norm_of_nonneg (h0 _)] using hsum) N
  rw [key]
  exact hsum.tsum_subtype_le _ _ h0

theorem global_positivity_ineq : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro M b ω s C hs hb1 hb0 hmul hbM hrec hC hsum X
  set f : ℕ → ℝ := fun n => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hf
  set Ssum := ∑' n : ℕ, f n
  set Lp : ℕ → ℂ := fun p => ∑' e : ℕ, LSeries.term b ((1 + s : ℝ) : ℂ) (p ^ e) with hLp
  set Rp : ℕ → ℝ := fun p => ∑' e : ℕ, ‖b (p ^ e)‖ ^ 2 / ((p ^ e : ℕ) : ℝ) ^ (1 + s) with hRp
  set α : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (1 + s))⁻¹ with hα
  set β : ℕ → ℝ := fun p => (1 - 1 / (p : ℝ) ^ (2 * (1 + s)))⁻¹ with hβ
  set A : ℕ → ℝ := fun p => if ¬ p ∣ M then ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) else 0 with hA
  have hA0 : ∀ p, 0 ≤ A p := fun p => by
    simp only [hA]; split_ifs <;> positivity

  have hα1 : ∀ p : ℕ, p.Prime → 1 ≤ α p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (1 + s) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (1 + s) := by positivity
    have h3 : 1 / (p : ℝ) ^ (1 + s) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hα]
    rw [one_le_inv₀ (by linarith)]; linarith
  have hβ1 : ∀ p : ℕ, p.Prime → 1 ≤ β p := by
    intro p hp
    have h1 : (1 : ℝ) < (p : ℝ) ^ (2 * (1 + s)) :=
      Real.one_lt_rpow (by exact_mod_cast hp.one_lt) (by linarith)
    have h2 : 0 < 1 / (p : ℝ) ^ (2 * (1 + s)) := by positivity
    have h3 : 1 / (p : ℝ) ^ (2 * (1 + s)) < 1 := by rw [div_lt_one (by linarith)]; exact h1
    simp only [hβ]
    rw [one_le_inv₀ (by linarith)]; linarith

  have hdiv : ∀ p : ℕ, p.Prime → p ∣ M → Lp p = 1 ∧ Rp p = 1 := by
    intro p hp hpM
    have hz : ∀ e : ℕ, e ≠ 0 → b (p ^ e) = 0 := by
      intro e he
      apply hbM
      intro hc
      have : p ∣ Nat.gcd (p ^ e) M := Nat.dvd_gcd (dvd_pow_self p he) hpM
      rw [hc] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    constructor
    · simp only [hLp]
      rw [tsum_eq_single 0]
      · simp [LSeries.term, hb1]
      · intro e he; simp [LSeries.term, hz e he]
    · simp only [hRp]
      rw [tsum_eq_single 0]
      · simp [hb1]
      · intro e he; simp [hz e he]
  have hRp0 : ∀ p, 0 ≤ Rp p := fun p => tsum_nonneg (fun e => by positivity)
  have hα0 : ∀ p : ℕ, p.Prime → 0 ≤ α p := fun p hp => le_trans zero_le_one (hα1 p hp)
  have hβ0 : ∀ p : ℕ, p.Prime → 0 ≤ β p := fun p hp => le_trans zero_le_one (hβ1 p hp)

  have hloc : ∀ p : ℕ, p.Prime → Real.exp (A p) ≤ α p * ‖Lp p‖ ^ 2 * Rp p * β p := by
    intro p hp
    by_cases hpM : p ∣ M
    · obtain ⟨h1, h2⟩ := hdiv p hp hpM
      simp only [hA, hpM, not_true_eq_false, if_false, Real.exp_zero, h1, h2, norm_one, one_pow, mul_one]
      nlinarith [hα1 p hp, hβ1 p hp]
    · have := GlobalTheory.T.local_positivity_eulerFactor_prime b ω s C p hs hp hb1 (hrec p 1 hp hpM).1 (fun r => (hrec p r hp hpM).2) hC
      simpa only [hA, hpM, not_false_eq_true, if_true] using this

  have hfin : ∀ N : ℕ, X ≤ N → Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by
    intro N hN
    have e1 : ∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) = ∑ p ∈ X.primesBelow, A p := by
      rw [Nat.primesBelow, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h1 : p.Prime <;> by_cases h2 : p ∣ M <;> simp [hA, h1, h2]
    have e2 : ∑ p ∈ X.primesBelow, A p ≤ ∑ p ∈ N.primesBelow, A p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesBelow_mono hN) (fun p _ _ => hA0 p)
    rw [e1]
    calc Real.exp (∑ p ∈ X.primesBelow, A p) ≤ Real.exp (∑ p ∈ N.primesBelow, A p) := Real.exp_le_exp.mpr e2
      _ = ∏ p ∈ N.primesBelow, Real.exp (A p) := Real.exp_sum _ _
      _ ≤ ∏ p ∈ N.primesBelow, (α p * ‖Lp p‖ ^ 2 * Rp p * β p) :=
          Finset.prod_le_prod₀ (fun p _ => (Real.exp_pos _).le) (fun p hp => hloc p (Nat.prime_of_mem_primesBelow hp))
      _ = (∏ p ∈ N.primesBelow, α p) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * (∏ p ∈ N.primesBelow, Rp p) * (∏ p ∈ N.primesBelow, β p) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib, norm_prod, Finset.prod_pow]
      _ ≤ (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum * 2 := by
          have a1 := GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_le s hs N
          have a2 := GlobalTheory.T.prod_primesBelow_inv_one_sub_rpow_two_mul_le s hs.le N
          have a3 := prod_primesBelow_sq_le_tsum b s hb1 hmul hsum N
          have p1 : 0 ≤ ∏ p ∈ N.primesBelow, α p := Finset.prod_nonneg (fun p hp => hα0 p (Nat.prime_of_mem_primesBelow hp))
          have p2 : 0 ≤ ∏ p ∈ N.primesBelow, Rp p := Finset.prod_nonneg (fun p _ => hRp0 p)
          have p3 : 0 ≤ ∏ p ∈ N.primesBelow, β p := Finset.prod_nonneg (fun p hp => hβ0 p (Nat.prime_of_mem_primesBelow hp))
          gcongr
      _ = 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum := by ring
  have hlim := tendsto_eulerProduct_LSeries_of_sq b s hs hb1 hmul hsum
  have hcont : Tendsto (fun N : ℕ => 2 * (1 + 1 / s) * ‖∏ p ∈ N.primesBelow, Lp p‖ ^ 2 * Ssum) atTop (𝓝 (2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * Ssum)) :=
    ((hlim.norm.pow 2).const_mul _).mul_const _
  exact ge_of_tendsto hcont (Filter.eventually_atTop.mpr ⟨X, hfin⟩)

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeffStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_positivity_ineq_multiplicative_coeff : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  first | exact @GlobalTheory.EisM.global_positivity_ineq | exact GlobalTheory.EisM.global_positivity_ineq | (intros; apply GlobalTheory.EisM.global_positivity_ineq <;> assumption)
end
