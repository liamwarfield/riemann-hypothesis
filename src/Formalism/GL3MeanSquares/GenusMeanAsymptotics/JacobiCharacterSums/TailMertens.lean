module

public import Mathlib

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailMertens
open Finset ArithmeticFunction

noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_mertens_psi (N : ℕ) :
    ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ (Real.log 4 + 4) * (N : ℝ) := by
  have h := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (Nat.cast_nonneg N)
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast] at h
  have hsub : ∑ n ∈ Icc 1 N, (Λ n : ℝ) = ∑ n ∈ Icc 0 N, (Λ n : ℝ) := by
    apply Finset.sum_subset
    · intro n hn
      simp only [mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      simp only [mem_Icc] at hn hn'
      have h0 : n = 0 := by omega
      subst h0
      simp
  rw [hsub]
  exact h

theorem tail_mertens_nat (N : ℕ) :
    ∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ) / (n : ℝ) ≤
      (∑ n ∈ Icc 1 (N + 1), (Λ n : ℝ)) / ((N : ℝ) + 1)
        + (Real.log 4 + 4) * Real.log ((N : ℝ) + 1) := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  induction N with
  | zero => simp
  | succ M ih =>
    have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
    have hM2 : (0:ℝ) < (M:ℝ) + 1 + 1 := by positivity
    have hB := tail_mertens_psi (M + 1)
    push_cast at hB
    have hlog : 1 / ((M:ℝ) + 1 + 1) ≤ Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1) := by
      rw [← Real.log_div hM2.ne' hM1.ne']
      have h := Real.one_sub_inv_le_log_of_pos (x := ((M:ℝ) + 1 + 1) / ((M:ℝ) + 1)) (by positivity)
      calc 1 / ((M:ℝ) + 1 + 1) = 1 - (((M:ℝ) + 1 + 1) / ((M:ℝ) + 1))⁻¹ := by
            field_simp
            ring
        _ ≤ _ := h
    simp only [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 + 1 by omega)]
    push_cast
    set B := ∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ) with hBdef
    set L := (Λ (M + 1 + 1) : ℝ) with hLdef
    have key1 : B / ((M:ℝ) + 1) ≤ (B + (Real.log 4 + 4)) / ((M:ℝ) + 1 + 1) := by
      rw [div_le_div_iff₀ hM1 hM2]
      nlinarith
    have key2 : (Real.log 4 + 4) / ((M:ℝ) + 1 + 1) ≤
        (Real.log 4 + 4) * (Real.log ((M:ℝ) + 1 + 1) - Real.log ((M:ℝ) + 1)) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hlog hc
    rw [add_div] at key1 ⊢
    linarith

theorem tail_mertens : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 2 ≤ y →
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ C * Real.log y := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 4 + 4) * (1 / Real.log 2 + 1),
    mul_nonneg hc (add_nonneg (one_div_nonneg.2 hl2.le) zero_le_one), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨M, hM⟩ : ∃ M, ⌊y⌋₊ = M + 1 :=
    ⟨⌊y⌋₊ - 1, by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega⟩
  rw [hM]
  have h1 := tail_mertens_nat M
  have hpsi := tail_mertens_psi (M + 1)
  push_cast at hpsi
  have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
  have hMy : (M:ℝ) + 1 ≤ y := by
    have := Nat.floor_le hy0
    rw [hM] at this
    push_cast at this
    exact this
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlogM : Real.log ((M:ℝ) + 1) ≤ Real.log y := Real.log_le_log hM1 hMy
  have hq : (∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ)) / ((M:ℝ) + 1) ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hM1]
    exact hpsi
  have hone : 1 ≤ Real.log y / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    linarith
  calc _ ≤ (Real.log 4 + 4) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hlogM hc
        linarith
    _ ≤ (Real.log 4 + 4) * (Real.log y / Real.log 2) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hone hc
        linarith
    _ = (Real.log 4 + 4) * (1 / Real.log 2 + 1) * Real.log y := by
        field_simp

end Formalism.HermitianLattices.Ext.BoxTail
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailNum
noncomputable section

namespace Formalism.HermitianLattices.Ext.BoxTail

theorem tail_num_rpow (x ε : ℝ) (hx : 0 < x) :
    (x ^ 400) ^ (1 - 1 / 400 + ε / 1600 : ℝ) = x ^ 399 * x ^ (ε / 4) := by
  rw [← Real.rpow_natCast x 400, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 399,
    ← Real.rpow_add hx]
  congr 1
  push_cast
  ring

theorem tail_num_alg (x Q K l a g : ℝ) (hx : 0 < x) (hQ : 0 < Q) :
    x * ((K * l * (l * (1 / x ^ 2) * (x ^ 399 * a) + (x ^ 400) ^ 2 / Q)
          + x ^ 400 * (1 / x ^ 2) * (x ^ 400 * (1 / x ^ 2) + 1) * g / x ^ 400)
          / (x ^ 400 * (1 / x ^ 2)))
      = K * l ^ 2 * a + K * (l * x ^ 403 / Q) + (x ^ 398 + 1) * g / x ^ 399 := by
  have hx0 : x ≠ 0 := hx.ne'
  have hQ0 : Q ≠ 0 := hQ.ne'
  field_simp

theorem tail_num_third (x : ℝ) (hx : 3 ≤ x) :
    (x ^ 398 + 1) * Real.log (x ^ 400 + x ^ 400 * (1 / x ^ 2)) / x ^ 399 ≤ 802 := by
  suffices h : ∀ n : ℕ,
      (x ^ n + 1) * Real.log (x ^ (n + 2) + x ^ (n + 2) * (1 / x ^ 2)) / x ^ (n + 1)
        ≤ 2 * ((n : ℝ) + 3) by
    have hbound : 2 * ((398 : ℝ) + 3) = 802 := by norm_num
    simpa only [Nat.reduceAdd, Nat.cast_ofNat, hbound] using h 398
  intro n
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hp : 0 < x ^ n := by positivity
  have hp1 : 1 ≤ x ^ n := one_le_pow₀ hx1
  have hA : x ^ (n + 2) + x ^ (n + 2) * (1 / x ^ 2) = x ^ n * (x ^ 2 + 1) := by
    rw [pow_add]
    field_simp
  have hsq : x ^ 2 + 1 ≤ x ^ 3 := by nlinarith
  have hsq_pos : 0 < x ^ 2 + 1 := by positivity
  have hlog_sq : Real.log (x ^ 2 + 1) ≤ 3 * Real.log x := by
    calc Real.log (x ^ 2 + 1) ≤ Real.log (x ^ 3) := Real.log_le_log hsq_pos hsq
      _ = 3 * Real.log x := by rw [Real.log_pow]; norm_num
  have hlog_x : Real.log x ≤ x := by linarith [Real.log_le_sub_one_of_pos hx0]
  have hL1 : Real.log (x ^ n * (x ^ 2 + 1)) ≤ ((n : ℝ) + 3) * x := by
    rw [Real.log_mul hp.ne' hsq_pos.ne', Real.log_pow]
    calc (n : ℝ) * Real.log x + Real.log (x ^ 2 + 1)
        ≤ (n : ℝ) * Real.log x + 3 * Real.log x := add_le_add le_rfl hlog_sq
      _ = ((n : ℝ) + 3) * Real.log x := by ring
      _ ≤ ((n : ℝ) + 3) * x := mul_le_mul_of_nonneg_left hlog_x (by positivity)
  have hxn : x ≤ x ^ (n + 1) := by
    simpa only [pow_succ, one_mul] using mul_le_mul_of_nonneg_right hp1 hx0.le
  rw [hA, div_le_iff₀ (by positivity : (0 : ℝ) < x ^ (n + 1))]
  calc (x ^ n + 1) * Real.log (x ^ n * (x ^ 2 + 1))
      ≤ (x ^ n + 1) * (((n : ℝ) + 3) * x) := mul_le_mul_of_nonneg_left hL1 (by positivity)
    _ = ((n : ℝ) + 3) * (x ^ (n + 1) + x) := by rw [pow_succ]; ring
    _ ≤ ((n : ℝ) + 3) * (x ^ (n + 1) + x ^ (n + 1)) := by gcongr
    _ = 2 * ((n : ℝ) + 3) * x ^ (n + 1) := by ring

end Formalism.HermitianLattices.Ext.BoxTail
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountSt
noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts

def ZeroDensityBox : Prop :=
  ∃ C : ℝ, ∀ (Q : ℝ) (S : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1))), 3 ≤ Q →
    (∀ p ∈ S, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHFinishB
open Finset Complex

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem u_disc (η : ℝ) (hη : 0 < η) (w : ℂ) (hw : η ≤ w.re) :
    ‖(η : ℂ) / w‖ ^ 2 ≤ ((η : ℂ) / w).re := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hw
    linarith
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  rw [norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.div_re, Complex.normSq_ofReal,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  have h1 : η * η ≤ η * w.re := mul_le_mul_of_nonneg_left hw hη.le
  simp only [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hn.le)

theorem u_sum_re (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) :
    (∑ i, ((η : ℂ) / w i) ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := by
  have h : ∑ i, ((η : ℂ) / w i) ^ j = ((η ^ j : ℝ) : ℂ) * ∑ i, 1 / (w i) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [div_pow, div_eq_mul_one_div, Complex.ofReal_pow]
  rw [h, Complex.re_ofReal_mul]


end Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF
end
end
