module

public import Formalism.LandauZeroFreeBounds.NoZeroComplexOf
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth

@[expose] public section

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LRight
open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma norm_term_twist_moebius_le {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (n : ℕ) :
    ‖term (↗χ * ↗μ) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  apply LSeries.norm_term_le
  simp only [Pi.mul_apply, Pi.one_apply, norm_one, norm_mul]
  have h1 := DirichletCharacter.norm_le_one χ (n : ZMod q)
  have h2 : ‖((μ n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact mul_le_one₀ h1 (norm_nonneg _) h2

open Formalism.ZF.MoebiusInverseZetaBounds in
theorem inverseBound : LInvBound := by
  intro q _ χ s hs
  have hσ1 : 0 < s.re - 1 := by linarith
  have hshift : ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) ≤ s.re / (s.re - 1) := by
    apply Real.tsum_le_of_sum_range_le
    · intro n
      positivity
    · intro m
      rcases m with _ | k
      · simp only [Finset.range_zero, Finset.sum_empty]
        positivity
      · rw [Finset.sum_range_succ']
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hanti : AntitoneOn (fun x : ℝ => x ^ (-s.re)) (Set.Icc (1 : ℝ) (1 + k)) := by
          intro x hx y _ hxy
          exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
        have hsum := hanti.sum_le_integral
        have hint : ∫ x in (1 : ℝ)..(1 + k), x ^ (-s.re) =
            ((1 + k : ℝ) ^ (-s.re + 1) - 1 ^ (-s.re + 1)) / (-s.re + 1) := by
          apply integral_rpow
          refine Or.inr ⟨by linarith, ?_⟩
          rw [Set.uIcc_of_le (by linarith)]
          intro h
          linarith [h.1]
        have hpos : 0 ≤ (1 + k : ℝ) ^ (-s.re + 1) := by positivity
        have hb : ((1 + k : ℝ) ^ (-s.re + 1) - 1 ^ (-s.re + 1)) / (-s.re + 1) ≤ 1 / (s.re - 1) := by
          rw [Real.one_rpow, show -s.re + 1 = -(s.re - 1) by ring, div_neg, ← neg_div]
          have hpos' : 0 ≤ (1 + k : ℝ) ^ (-(s.re - 1)) := by positivity
          gcongr
          linarith
        have e : ∑ i ∈ Finset.range k, (((i + 1 : ℕ) : ℝ) + 1) ^ (-(s.re - 1) - 1) =
            ∑ i ∈ Finset.range k, (fun x : ℝ => x ^ (-s.re)) (1 + ((i + 1 : ℕ) : ℝ)) :=
          Finset.sum_congr rfl fun i _ => by
            show (((i + 1 : ℕ) : ℝ) + 1) ^ (-(s.re - 1) - 1) = (1 + ((i + 1 : ℕ) : ℝ)) ^ (-s.re)
            congr 1 <;> ring
        rw [e]
        have e2 : s.re / (s.re - 1) = 1 / (s.re - 1) + 1 := by
          field_simp
          ring
        simp only [Nat.cast_zero, zero_add, Real.one_rpow]
        rw [hint] at hsum
        linarith
  have hp : -(s.re - 1) - 1 < -1 := by linarith
  have hfun : (fun n : ℕ => ‖term (1 : ℕ → ℂ) s (n + 1)‖) = fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) :=
    funext (norm_term_one_succ s)
  have hS1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ := by
    rw [← summable_nat_add_iff 1, hfun]
    exact summable_shift hp
  have hT1 : ∑' n, ‖term (1 : ℕ → ℂ) s n‖ ≤ s.re / (s.re - 1) := by
    rw [hS1.tsum_eq_zero_add, LSeries.term_zero, norm_zero, zero_add, hfun]
    exact hshift
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hinv : ‖LSeries ↗χ s‖⁻¹ = ‖LSeries (↗χ * ↗μ) s‖ := by
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hmul]
  rw [hinv]
  have hS2 : Summable fun n => ‖term (↗χ * ↗μ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_term_twist_moebius_le χ s n) hS1
  calc ‖LSeries (↗χ * ↗μ) s‖ = ‖∑' n, term (↗χ * ↗μ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗μ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ :=
      Summable.tsum_le_tsum (fun n => norm_term_twist_moebius_le χ s n) hS2 hS1
    _ ≤ s.re / (s.re - 1) := hT1

lemma negLD_eq_LSeries_mul_vonMangoldt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    negLD χ s = L (↗χ * ↗Λ) s := by
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 s] LSeries ↗χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  rw [negLD, hev.deriv_eq, DirichletCharacter.LFunction_eq_LSeries χ hs,
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, neg_div]

lemma norm_LSeries_twist_vonMangoldt_le {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ‖L (↗χ * ↗Λ) s‖ ≤ Formalism.ZF.lamF s.re := by
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  have hSΛ : Summable fun n => ‖term ↗Λ (s.re : ℂ) n‖ :=
    summable_norm_iff.2 (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  have hle : ∀ n, ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ (s.re : ℂ) n‖ := by
    intro n
    calc ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ s n‖ := by
          apply LSeries.norm_term_le
          simp only [Pi.mul_apply, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
      _ = ‖term ↗Λ (s.re : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re]
  have hS2 : Summable fun n => ‖term (↗χ * ↗Λ) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hSΛ
  calc ‖L (↗χ * ↗Λ) s‖ = ‖∑' n, term (↗χ * ↗Λ) s n‖ := rfl
    _ ≤ ∑' n, ‖term (↗χ * ↗Λ) s n‖ := norm_tsum_le_tsum_norm hS2
    _ ≤ ∑' n, ‖term ↗Λ (s.re : ℂ) n‖ := Summable.tsum_le_tsum hle hS2 hSΛ
    _ = Formalism.ZF.lamF s.re := rfl

theorem l_log_deriv_right : LLogDerivRight := by
  obtain ⟨C, hC0, hC⟩ := Formalism.ZF.logDerivBoundRightHalfPlane
  refine ⟨C, hC0, ?_⟩
  intro q _ χ s hs
  rw [negLD_eq_LSeries_mul_vonMangoldt χ hs]
  refine le_trans (norm_LSeries_twist_vonMangoldt_le χ hs) ?_
  have hre : 1 < (s.re : ℂ).re := by simpa using hs
  rw [Formalism.ZF.lamF_eq_norm hs, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre,
    neg_div, norm_neg]
  have h := hC (s.re : ℂ) hre
  simpa using h

end Formalism.ZeroFreeDirichlet
end
end

section -- merged from Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound
open Complex Filter Topology Metric

noncomputable section

namespace Formalism.ZeroFreeDirichlet

private theorem differentiable_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) :
    Differentiable ℂ (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) := by
  refine Finset.induction_on Z ?_ ?_
  · simp
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact ((differentiable_id.sub_const a).pow (m a)).mul ih

private theorem deriv_sub_mul_at_self {g : ℂ → ℂ} {ρ : ℂ} (hg : DifferentiableAt ℂ g ρ) :
    deriv (fun z => (z - ρ) * g z) ρ = g ρ := by
  have h : HasDerivAt (fun z => (z - ρ) * g z) (1 * g ρ + (ρ - ρ) * deriv g ρ) ρ :=
    ((hasDerivAt_id ρ).sub_const ρ).mul hg.hasDerivAt
  rw [h.deriv]
  ring

private theorem deriv_eq_zero_iff_mult_of_local_factor {f k : ℂ → ℂ} {ρ : ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hk : DifferentiableAt ℂ k ρ) (hk0 : k ρ ≠ 0)
    (hf : f =ᶠ[𝓝 ρ] fun w => (w - ρ) ^ n * k w) :
    (deriv f ρ = 0 → 2 ≤ n) ∧ (deriv f ρ ≠ 0 → n = 1) := by
  rw [hf.deriv_eq]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hfun : (fun w => (w - ρ) ^ (j + 1) * k w) = fun w => (w - ρ) * ((w - ρ) ^ j * k w) := by
    funext w
    ring
  have hg : DifferentiableAt ℂ (fun w => (w - ρ) ^ j * k w) ρ := by
    fun_prop
  rw [hfun, deriv_sub_mul_at_self hg]
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    simp only [pow_zero, one_mul]
    exact ⟨fun h => absurd h hk0, fun _ => by simp⟩
  · have h0 : (ρ - ρ) ^ j = 0 := by
      rw [sub_self]
      exact zero_pow hj.ne'
    rw [h0, zero_mul]
    exact ⟨fun _ => by omega, fun h => absurd rfl h⟩

theorem exists_localZeroExpansion_of_bound (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ) (hr : 0 < r) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ ≠ 0 → m ρ = 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r := by
  have hr3 : 0 < r / 3 := by linarith
  obtain ⟨Z, m, h, hZ, hm, hhd, hh0, hfac⟩ :=
    Formalism.ZF.zeroFactorization f z₀ r (r / 3) hr3 (by linarith) hf hfz₀
  have hsub : ∀ z ∈ closedBall z₀ (r / 3), z ∈ ball z₀ r := fun z hz => by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hloc : ∀ z ∈ ball z₀ r, f =ᶠ[𝓝 z] fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w := by
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hfac w (ball_subset_closedBall hw)
  have hhdiff : ∀ z ∈ ball z₀ r, DifferentiableAt ℂ h z := fun z hz =>
    hhd.differentiableAt (Filter.mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)
  have hZ0 : ∀ ρ ∈ Z, f ρ = 0 := fun ρ hρ => ((hZ ρ).1 hρ).2
  have hZb : ∀ ρ ∈ Z, ρ ∈ closedBall z₀ (r / 3) := fun ρ hρ => ((hZ ρ).1 hρ).1
  have horder : ∀ ρ ∈ Z, (deriv f ρ = 0 → 2 ≤ m ρ) ∧ (deriv f ρ ≠ 0 → m ρ = 1) := by
    intro ρ hρ
    have hρb := hsub ρ (hZb ρ hρ)
    refine deriv_eq_zero_iff_mult_of_local_factor (k := fun w => (∏ ρ' ∈ Z.erase ρ, (w - ρ') ^ m ρ') * h w)
      (hm ρ hρ) ((differentiable_prod_sub_pow (Z.erase ρ) m ρ).mul (hhdiff ρ hρb)) ?_ ?_
    · exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' =>
        pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) (hh0 ρ (hZb ρ hρ))
    · filter_upwards [hloc ρ hρb] with w hw
      rw [hw, ← mul_assoc, Finset.mul_prod_erase Z (fun ρ' => (w - ρ') ^ m ρ') hρ]
  have hlow : ∀ w ∈ sphere z₀ r,
      2 ^ (∑ ρ ∈ Z, m ρ) * (r / 3) ^ (∑ ρ ∈ Z, m ρ) ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ := by
    intro w hw
    rw [← mul_pow, norm_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => pow_nonneg (by linarith) _) fun ρ hρ => ?_
    rw [norm_pow]
    have h1 := hZb ρ hρ
    rw [mem_closedBall] at h1
    rw [mem_sphere] at hw
    have h2 : 2 * (r / 3) ≤ ‖w - ρ‖ := by
      rw [← dist_eq_norm]
      linarith [dist_triangle w ρ z₀]
    exact pow_le_pow_left₀ (by linarith) h2 _
  have hup : ‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ ≤ (r / 3) ^ (∑ ρ ∈ Z, m ρ) := by
    rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun ρ _ => norm_nonneg _) fun ρ hρ => ?_
    rw [norm_pow]
    have h1 := hZb ρ hρ
    rw [mem_closedBall, dist_eq_norm] at h1
    have h2 : ‖z₀ - ρ‖ ≤ r / 3 := by
      rw [norm_sub_rev]
      exact h1
    exact pow_le_pow_left₀ (norm_nonneg _) h2 _
  have hcl : closure (ball z₀ r) = closedBall z₀ r := by
    exact closure_ball z₀ hr.ne'
  have hfr : frontier (ball z₀ r) = sphere z₀ r := by
    exact frontier_ball z₀ hr.ne'
  have h2pos : (0 : ℝ) < 2 ^ (∑ ρ ∈ Z, m ρ) := by positivity
  have hmax : ∀ z ∈ closedBall z₀ r, ‖h z‖ * 2 ^ (∑ ρ ∈ Z, m ρ) ≤ M * ‖h z₀‖ := by
    have hd : DiffContOnCl ℂ h (ball z₀ r) := DifferentiableOn.diffContOnCl (by rw [hcl]; exact hhd)
    intro z hz
    have hc : ‖h z‖ ≤ M * ‖h z₀‖ / 2 ^ (∑ ρ ∈ Z, m ρ) := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ (by rw [hcl]; exact hz)
      intro w hw
      rw [hfr] at hw
      have hwc : w ∈ closedBall z₀ r := sphere_subset_closedBall hw
      have b1 := hbound w hwc
      rw [hfac w hwc, hfac z₀ (mem_closedBall_self hr.le), norm_mul, norm_mul] at b1
      have l1 := hlow w hw
      have hA : (0 : ℝ) < (r / 3) ^ (∑ ρ ∈ Z, m ρ) := pow_pos hr3 _
      have key : (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (‖h w‖ * 2 ^ (∑ ρ ∈ Z, m ρ)) ≤
          (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by
        calc (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (‖h w‖ * 2 ^ (∑ ρ ∈ Z, m ρ))
            = (2 ^ (∑ ρ ∈ Z, m ρ) * (r / 3) ^ (∑ ρ ∈ Z, m ρ)) * ‖h w‖ := by ring
          _ ≤ ‖∏ ρ ∈ Z, (w - ρ) ^ m ρ‖ * ‖h w‖ := mul_le_mul_of_nonneg_right l1 (norm_nonneg _)
          _ ≤ M * (‖∏ ρ ∈ Z, (z₀ - ρ) ^ m ρ‖ * ‖h z₀‖) := b1
          _ ≤ M * ((r / 3) ^ (∑ ρ ∈ Z, m ρ) * ‖h z₀‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hup (norm_nonneg _)) (by linarith)
          _ = (r / 3) ^ (∑ ρ ∈ Z, m ρ) * (M * ‖h z₀‖) := by ring
      have key2 := le_of_mul_le_mul_left key hA
      exact (le_div_iff₀ h2pos).mpr key2
    exact (le_div_iff₀ h2pos).mp hc
  have hh0z₀ : h z₀ ≠ 0 := hh0 z₀ (mem_closedBall_self hr3.le)
  have h2M : (2 : ℝ) ^ (∑ ρ ∈ Z, m ρ) ≤ M := by
    have h1 := hmax z₀ (mem_closedBall_self hr.le)
    have hpos : 0 < ‖h z₀‖ := norm_pos_iff.mpr hh0z₀
    exact le_of_mul_le_mul_left (by linarith) hpos
  have hsum : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * Real.log 2 ≤ Real.log M := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) h2M
    exact (le_div_iff₀ hl2).mpr h1
  have hone : (1 : ℝ) ≤ 2 ^ (∑ ρ ∈ Z, m ρ) := by
    exact one_le_pow₀ (by norm_num)
  have hbB : ∀ z ∈ closedBall z₀ (r / 3), ‖h z‖ ≤ M * ‖h z₀‖ := by
    intro z hz
    have hzr : z ∈ closedBall z₀ r := closedBall_subset_closedBall (by linarith) hz
    exact (le_mul_of_one_le_right (norm_nonneg _) hone).trans (hmax z hzr)
  have hB := Formalism.ZF.logDerivBoundOnBall h z₀ (r / 3) M hr3 hM
    (hhd.mono (closedBall_subset_closedBall (by linarith))) hh0 hbB
  refine ⟨Z, m, hZ, hm, fun ρ hρ => (horder ρ hρ).1, fun ρ hρ => (horder ρ hρ).2, hsum, ?_⟩
  intro z hz hfz
  have hz3 : z ∈ closedBall z₀ (r / 3 / 2) := by
    rw [mem_closedBall] at hz ⊢
    linarith
  have hzr : z ∈ closedBall z₀ r := closedBall_subset_closedBall (by linarith) hz
  have hzb : z ∈ ball z₀ r := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hzρ : ∀ ρ ∈ Z, z - ρ ≠ 0 := fun ρ hρ he =>
    hfz (by rw [sub_eq_zero.mp he]; exact hZ0 ρ hρ)
  have e1 := hfac z hzr
  have hPz : (∏ ρ ∈ Z, (z - ρ) ^ m ρ) ≠ 0 := fun h0 => hfz (by rw [e1, h0, zero_mul])
  have hhz : h z ≠ 0 := fun h0 => hfz (by rw [e1, h0, mul_zero])
  have hl : logDeriv (fun w => (∏ ρ ∈ Z, (w - ρ) ^ m ρ) * h w) z =
      logDeriv (fun w => ∏ ρ ∈ Z, (w - ρ) ^ m ρ) z + logDeriv h z := by
    exact logDeriv_mul z hPz hhz (differentiable_prod_sub_pow Z m z) (hhdiff z hzb)
  rw [Formalism.ZF.landauLocal_logDeriv_prod Z m z hzρ, logDeriv_apply, logDeriv_apply] at hl
  have hsplit : deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) = deriv h z / h z := by
    rw [(hloc z hzb).deriv_eq, e1, hl]
    ring
  rw [hsplit]
  calc ‖deriv h z / h z‖ ≤ 24 * Real.log M / (r / 3) := hB z hz3
    _ = 72 * Real.log M / r := by
      rw [div_div_eq_mul_div]
      ring

end Formalism.ZeroFreeDirichlet
end
end
