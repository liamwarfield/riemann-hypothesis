module

public import Formalism.ZeroFreeRegion.SmallHeightLogDeriv

@[expose] public section

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound
open Complex Filter Topology LSeries ArithmeticFunction

noncomputable section

namespace Formalism.ZF

namespace MoebiusInverseZetaBounds

lemma summable_shift {p : ℝ} (hp : p < -1) : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ p) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr hp)
  simpa only [Nat.cast_add, Nat.cast_one] using h

lemma rpow_le_integral {x σ : ℝ} (hx : 0 < x) (hσ : 0 < σ) :
    (x + 1) ^ (-σ - 1) ≤ (x ^ (-σ) - (x + 1) ^ (-σ)) / σ := by
  have ha : 0 < x + 1 := by linarith
  have hy : 0 < x / (x + 1) := div_pos hx ha
  have hlog : Real.log (x / (x + 1)) ≤ x / (x + 1) - 1 := Real.log_le_sub_one_of_pos hy
  have hexp : 1 + σ / (x + 1) ≤ (x / (x + 1)) ^ (-σ) := by
    rw [Real.rpow_def_of_pos hy]
    have h1 := Real.add_one_le_exp (Real.log (x / (x + 1)) * (-σ))
    have h2 : σ / (x + 1) ≤ Real.log (x / (x + 1)) * (-σ) := by
      have e : σ / (x + 1) = (x / (x + 1) - 1) * (-σ) := by
        field_simp
        ring
      rw [e]
      exact mul_le_mul_of_nonpos_right hlog (by linarith)
    linarith
  have hA := Real.rpow_pos_of_pos ha (-σ)
  have hsplit : x ^ (-σ) = (x + 1) ^ (-σ) * (x / (x + 1)) ^ (-σ) := by
    rw [Real.div_rpow hx.le ha.le]
    field_simp
  have hm1 : (x + 1) ^ (-σ - 1) = (x + 1) ^ (-σ) / (x + 1) := by
    rw [Real.rpow_sub ha, Real.rpow_one]
  rw [le_div_iff₀ hσ, hm1, hsplit]
  have hmul : (x + 1) ^ (-σ) * (σ / (x + 1)) ≤ (x + 1) ^ (-σ) * ((x / (x + 1)) ^ (-σ) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hA.le
  calc (x + 1) ^ (-σ) / (x + 1) * σ = (x + 1) ^ (-σ) * (σ / (x + 1)) := by ring
    _ ≤ (x + 1) ^ (-σ) * ((x / (x + 1)) ^ (-σ) - 1) := hmul
    _ = (x + 1) ^ (-σ) * (x / (x + 1)) ^ (-σ) - (x + 1) ^ (-σ) := by ring

lemma tsum_rpow_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' n : ℕ, ((n : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ := by
  have key : ∀ n : ℕ, ∑ i ∈ Finset.range (n + 1), ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + (1 - ((n : ℝ) + 1) ^ (-σ)) / σ := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have h := rpow_le_integral (x := (k : ℝ) + 1) (by positivity) hσ
      have e : (1 - ((k : ℝ) + 1) ^ (-σ)) / σ + (((k : ℝ) + 1) ^ (-σ) - ((k : ℝ) + 1 + 1) ^ (-σ)) / σ =
          (1 - ((k : ℝ) + 1 + 1) ^ (-σ)) / σ := by ring
      push_cast
      linarith
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro n
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have : 0 < 1 / σ := by positivity
    linarith
  | succ k =>
    have h1 := key k
    have h2 : 0 ≤ ((k : ℝ) + 1) ^ (-σ) := by positivity
    have h3 : (1 - ((k : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ := div_le_div_of_nonneg_right (by linarith) hσ.le
    linarith

lemma norm_term_one_succ (s : ℂ) (n : ℕ) :
    ‖term (1 : ℕ → ℂ) s (n + 1)‖ = ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := by
  rw [LSeries.norm_term_eq, if_neg (Nat.succ_ne_zero n)]
  simp only [Pi.one_apply, norm_one]
  push_cast
  rw [show -(s.re - 1) - 1 = -s.re by ring, Real.rpow_neg (by positivity), one_div]

lemma norm_term_moebius_le (s : ℂ) (n : ℕ) :
    ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ ≤ ‖term (1 : ℕ → ℂ) s n‖ := by
  refine LSeries.norm_term_le s ?_
  simp only [Pi.one_apply, norm_one]
  rw [Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

end MoebiusInverseZetaBounds

open MoebiusInverseZetaBounds in
theorem zetaInvBound_statement : ZetaInvBound := by
  intro s hs
  have hL := LSeries_one_mul_Lseries_moebius hs
  rw [LSeries_one_eq_riemannZeta hs] at hL
  have hinv := eq_inv_of_mul_eq_one_right hL
  rw [← norm_inv, ← hinv]
  have hσ : 0 < s.re - 1 := by linarith
  have hsum1 : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := summable_shift (by linarith)
  have hs1 : Summable fun n => ‖term (1 : ℕ → ℂ) s n‖ := by
    rw [← summable_nat_add_iff 1]
    simpa only [norm_term_one_succ] using hsum1
  have hsμ : Summable fun n => ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term_moebius_le s) hs1
  calc ‖LSeries (fun n => ((moebius n : ℤ) : ℂ)) s‖
      ≤ ∑' n, ‖term (fun n => ((moebius n : ℤ) : ℂ)) s n‖ := norm_tsum_le_tsum_norm hsμ
    _ ≤ ∑' n, ‖term (1 : ℕ → ℂ) s n‖ := Summable.tsum_le_tsum (norm_term_moebius_le s) hsμ hs1
    _ = ∑' n : ℕ, ((n : ℝ) + 1) ^ (-(s.re - 1) - 1) := by
      rw [hs1.tsum_eq_zero_add]
      simp only [LSeries.term_zero, norm_zero, zero_add, norm_term_one_succ]
    _ ≤ 1 + 1 / (s.re - 1) := tsum_rpow_le hσ
    _ = s.re / (s.re - 1) := by
      field_simp
      ring

end Formalism.ZF
end
end

section -- merged from Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivBound
open Complex Metric

noncomputable section

namespace Formalism.ZF

lemma zflb_exists_log {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by
  have hopen : IsOpen (ball z₀ R) := isOpen_ball
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball z₀ R) :=
    (hf.deriv hopen).div hf hne
  obtain ⟨G, hG⟩ := hd.isExactOn_ball
  refine ⟨fun z => G z - G z₀, by simp, fun z hz => (hG z hz).sub_const _, ?_⟩
  have hk : ∀ z ∈ ball z₀ R, HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀))) 0 z := by
    intro z hz
    have hfz : HasDerivAt f (deriv f z) z := (hf.differentiableAt (hopen.mem_nhds hz)).hasDerivAt
    have hgz : HasDerivAt (fun w => -(G w - G z₀)) (-(deriv f z / f z)) z := ((hG z hz).sub_const _).neg
    have h : HasDerivAt (fun w => f w * Complex.exp (-(G w - G z₀)))
        (deriv f z * Complex.exp (-(G z - G z₀)) +
          f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z))) z :=
      hfz.mul hgz.cexp
    have h0 : deriv f z * Complex.exp (-(G z - G z₀)) +
        f z * (Complex.exp (-(G z - G z₀)) * -(deriv f z / f z)) = 0 := by
      have h1 := hne z hz
      field_simp
      all_goals ring
    exact h0 ▸ h
  intro z hz
  have hz₀ : z₀ ∈ ball z₀ R := mem_ball_self (pos_of_mem_ball hz)
  have hconst := hopen.is_const_of_deriv_eq_zero (convex_ball z₀ R).isPreconnected
    (fun w hw => (hk w hw).differentiableAt.differentiableWithinAt) (fun w hw => (hk w hw).deriv) hz hz₀
  simp only [sub_self, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

theorem logDerivBoundOnBall : LogDerivBound := by
  intro f z₀ R M hR hM hf hne hbd z hz
  have hR0 : R ≠ 0 := hR.ne'
  have hfb : DifferentiableOn ℂ f (ball z₀ R) := hf.mono ball_subset_closedBall
  have hneb : ∀ w ∈ ball z₀ R, f w ≠ 0 := fun w hw => hne w (ball_subset_closedBall hw)
  obtain ⟨g, hg0, hgd, hgf⟩ := zflb_exists_log hfb hneb
  have hf0 : 0 < ‖f z₀‖ := norm_pos_iff.2 (hne z₀ (mem_closedBall_self hR.le))
  have hre : ∀ w ∈ ball z₀ R, (g w).re ≤ Real.log M := by
    intro w hw
    have h1 := hbd w (ball_subset_closedBall hw)
    rw [hgf w hw, norm_mul, Complex.norm_exp] at h1
    have h2 : Real.exp (g w).re ≤ M := by
      by_contra h
      have h3 := mul_lt_mul_of_pos_left (lt_of_not_ge h) hf0
      linarith
    calc (g w).re = Real.log (Real.exp (g w).re) := (Real.log_exp _).symm
      _ ≤ Real.log M := Real.log_le_log (Real.exp_pos _) h2
  have hzb : dist z z₀ ≤ R / 2 := hz
  have hshift : ∀ v ∈ ball (0 : ℂ) R, z₀ + v ∈ ball z₀ R := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact mem_ball_zero_iff.1 hv
  have hmain : ∀ A : ℝ, Real.log M < A → ‖deriv f z / f z‖ ≤ 24 * A / R := by
    intro A hA
    have hA0 : 0 < A := lt_of_le_of_lt (Real.log_nonneg hM) hA
    have hhd : DifferentiableOn ℂ (fun v => g (z₀ + v)) (ball 0 R) := by
      intro v hv
      exact ((hgd _ (hshift v hv)).differentiableAt.comp v
        (differentiableAt_id.const_add z₀)).differentiableWithinAt
    have hhm : Set.MapsTo (fun v => g (z₀ + v)) (ball 0 R) {w | w.re ≤ A} := by
      intro v hv
      exact le_trans (hre _ (hshift v hv)) hA.le
    have hbc : ∀ w ∈ closedBall z₀ (3 * R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      obtain ⟨u, rfl⟩ : ∃ u, w = z₀ + u := ⟨w - z₀, by ring⟩
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left] at hw
      have huR : u ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]
        linarith
      have hB : ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) :=
        Complex.borelCaratheodory_zero hA0 hhd hhm hR huR (by simpa using hg0)
      have hpos : 0 < R - ‖u‖ := by linarith
      calc ‖g (z₀ + u)‖ ≤ 2 * A * ‖u‖ / (R - ‖u‖) := hB
        _ ≤ 6 * A := by
          rw [div_le_iff₀ hpos]
          nlinarith [norm_nonneg u]
    have hR4 : 0 < R / 4 := by linarith
    have hsub : closedBall z (R / 4) ⊆ ball z₀ R := by
      intro w hw
      rw [mem_closedBall] at hw
      rw [mem_ball]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ < R := by linarith
    have hdiff : DiffContOnCl ℂ g (ball z (R / 4)) := by
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball z hR4.ne']
      intro w hw
      exact (hgd w (hsub hw)).differentiableAt.differentiableWithinAt
    have hC : ∀ w ∈ sphere z (R / 4), ‖g w‖ ≤ 6 * A := by
      intro w hw
      apply hbc
      rw [mem_sphere] at hw
      rw [mem_closedBall]
      calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle _ _ _
        _ ≤ 3 * R / 4 := by linarith
    have hzb' : z ∈ ball z₀ R := hsub (mem_closedBall_self hR4.le)
    have hder := norm_deriv_le_of_forall_mem_sphere_norm_le hR4 hdiff hC
    rw [(hgd z hzb').deriv] at hder
    calc ‖deriv f z / f z‖ ≤ 6 * A / (R / 4) := hder
      _ = 24 * A / R := by
        field_simp
        all_goals ring
  apply le_of_forall_pos_le_add
  intro ε hε
  have hεR : 0 < ε * R / 24 := by positivity
  have h := hmain (Real.log M + ε * R / 24) (by linarith)
  calc ‖deriv f z / f z‖ ≤ 24 * (Real.log M + ε * R / 24) / R := h
    _ = 24 * Real.log M / R + ε := by
      field_simp

end Formalism.ZF
end
end
