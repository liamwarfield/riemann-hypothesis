module

public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsKrullAkizuki

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivPredLe
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumPrimeLogDivLe
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumPrimeLogDivLe
namespace GlobalTheory.CompanionTheory.Ar.Small

theorem mertens_first_log_four :
    ∀ x : ℝ, 1 ≤ x →
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + Real.log 4 := by
  intro B hB
  set N := ⌊B⌋₊ with hN
  set P := (Finset.Iic N).filter Nat.Prime with hP
  have hN2 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hB)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNB : (N : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hpos : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le

  have hle : ∏ p ∈ P, p ^ (N / p) ≤ N ^ N :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (GroundTheory.Heights₂.Heights.Model.prod_pow_div_dvd_factorial N)).trans
      (Nat.factorial_le_pow N)
  have hlog : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N := by
    have hprod : (0 : ℝ) < ∏ p ∈ P, ((p : ℝ) ^ (N / p)) :=
      Finset.prod_pos fun p hp => pow_pos (by linarith [hpos p hp]) _
    have h := Real.log_le_log hprod
      (show ∏ p ∈ P, ((p : ℝ) ^ (N / p)) ≤ (N : ℝ) ^ N by exact_mod_cast hle)
    rw [Real.log_prod (fun p hp => (pow_pos (by linarith [hpos p hp]) _).ne'),
      Real.log_pow] at h
    simpa [Real.log_pow] using h

  have hfloor : ∀ p ∈ P, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p :=
    fun p hp => mul_le_mul_of_nonneg_right
      (by rw [← Nat.floor_div_eq_div (K := ℝ)]; exact (Nat.sub_one_lt_floor _).le)
      (Real.log_nonneg (hpos p hp))

  have htheta : ∑ p ∈ P, Real.log p ≤ Real.log 4 * N := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hNpos.le
    have hset : P = (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast, hP]
      ext p
      simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, h1⟩, h2⟩
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hset]; exact h
  have key : (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p ≤ N * Real.log N := by
    calc (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p
        = ∑ p ∈ P, ((N : ℝ) / p - 1) * Real.log p := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p := Finset.sum_le_sum hfloor
      _ ≤ N * Real.log N := hlog
  have hS : ∑ p ∈ P, Real.log p / p ≤ Real.log N + Real.log 4 := by
    have : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
      rw [mul_add]; linarith
    exact le_of_mul_le_mul_left this hNpos
  have hlogNB : Real.log N ≤ Real.log B := Real.log_le_log hNpos hNB
  linarith

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumPrimeLogDivLeStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prime_log_div_le : ∀ x : ℝ, 1 ≤ x → ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + Real.log 4 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four | exact GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.mertens_first_log_four <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivNSqLeTwo
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivNSqLeTwo
namespace GlobalTheory.CompanionTheory.Ar.Small

theorem log_tail_step (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) / ((x + 1) * x) ≤
      (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hL : Real.log (x + 1) - Real.log x ≤ 1 / x := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have he : (x + 1) / x - 1 = 1 / x := by
      field_simp
      ring
    linarith
  have hK : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ 2 := by
    have h1 : (x + 1) * (Real.log (x + 1) - Real.log x) ≤ (x + 1) * (1 / x) :=
      mul_le_mul_of_nonneg_left hL (by linarith)
    have h2 : (x + 1) * (1 / x) ≤ 2 := by
      rw [mul_one_div, div_le_iff₀ hx0]
      linarith
    linarith
  have hE : (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) - Real.log (x + 1) / ((x + 1) * x) =
      (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x) := by
    field_simp
    ring
  have hpos : 0 ≤ (2 - (x + 1) * (Real.log (x + 1) - Real.log x)) / ((x + 1) * x) :=
    div_nonneg (by linarith) (by positivity)
  linarith

theorem log_tail_Icc (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 2 N, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤
      2 - (Real.log N + 2) / N := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_eq_empty (by norm_num)]
    simp
  | succ k hk ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hstep := log_tail_step (k : ℝ) (by exact_mod_cast hk)
    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc]
    have hc2 : (k : ℝ) + 1 - 1 = k := by ring
    rw [hc2]
    linarith

theorem log_tail :
    ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) →
      ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 := by
  intro S hS
  have hN : 1 ≤ max 1 (S.sup id) := le_max_left _ _
  have hsub : S ⊆ Finset.Icc 2 (max 1 (S.sup id)) := by
    intro n hn
    rw [Finset.mem_Icc]
    exact ⟨hS n hn, le_trans (Finset.le_sup (f := id) hn) (le_max_right _ _)⟩
  have hnn : ∀ n ∈ Finset.Icc 2 (max 1 (S.sup id)), 0 ≤ Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.1
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith
  have h1 : (1 : ℝ) ≤ ((max 1 (S.sup id) : ℕ) : ℝ) := by exact_mod_cast hN
  have hq : 0 ≤ (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ) :=
    div_nonneg (by linarith [Real.log_nonneg h1]) (by linarith)
  calc ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
      ≤ ∑ n ∈ Finset.Icc 2 (max 1 (S.sup id)), Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => hnn n hn)
    _ ≤ 2 - (Real.log ((max 1 (S.sup id) : ℕ) : ℝ) + 2) / ((max 1 (S.sup id) : ℕ) : ℝ) :=
        log_tail_Icc _ hN
    _ ≤ 2 := by linarith

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogDivNSqLeTwoStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_log_div_n_sq_le_two : ∀ S : Finset ℕ, (∀ n ∈ S, 2 ≤ n) → ∑ n ∈ S, Real.log n / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.log_tail | exact GlobalTheory.CompanionTheory.Ar.Small.log_tail | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.log_tail <;> assumption)
end
end

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem sum_log_div_pred_le :
    ∀ (x : ℝ) (S : Finset ℕ), 1 ≤ x → (∀ p ∈ S, p.Prime ∧ (p : ℝ) ≤ x) →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ Real.log x + 17 / 5 := by
  intro x S hx hS
  have hsplit : ∀ p ∈ S, Real.log p / ((p : ℝ) - 1)
      = Real.log p / p + Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1.two_le
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h1 : ∑ p ∈ S, Real.log p / (p : ℝ) ≤ Real.log x + Real.log 4 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (GlobalTheory.T.sum_prime_log_div_le x hx)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_Iic]
      exact ⟨Nat.le_floor (hS p hp).2, (hS p hp).1⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  have h2 : ∑ p ∈ S, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 :=
    GlobalTheory.T.sum_log_div_n_sq_le_two S (fun p hp => (hS p hp).1.two_le)
  have hl4 : Real.log 4 < 7 / 5 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h := Real.log_two_lt_d9
    norm_num at h
    linarith
  linarith

end GlobalTheory.CompanionTheory.Ar.Small
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredBound
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem log_div_pred_le_of_lt (B p : ℕ) (hB : 128 ≤ B) (hp : B < p) (hL : 1 ≤ Real.log ((B : ℝ) + 1)) :
    Real.log p / ((p : ℝ) - 1) ≤ Real.log ((B : ℝ) + 1) / B := by
  have hB0 : (0 : ℝ) < B := by
    have : (128 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hpB : (B : ℝ) + 1 ≤ p := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : Real.log p ≤ Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1) := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hp0 hB1)
    rw [Real.log_div hp0.ne' hB1.ne'] at h1
    have h2 : (p : ℝ) / ((B : ℝ) + 1) - 1 = ((p : ℝ) - B - 1) / ((B : ℝ) + 1) := by
      field_simp
      ring
    linarith
  rw [div_le_div_iff₀ hp1 hB0]
  have hd : (0 : ℝ) ≤ (p : ℝ) - B - 1 := by linarith
  have hfrac : (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1)) ≤ ((p : ℝ) - B - 1) * Real.log ((B : ℝ) + 1) := by
    have h3 : (B : ℝ) / ((B : ℝ) + 1) ≤ Real.log ((B : ℝ) + 1) := by
      refine le_trans ?_ hL
      rw [div_le_one hB1]
      linarith
    calc (B : ℝ) * (((p : ℝ) - B - 1) / ((B : ℝ) + 1))
        = ((p : ℝ) - B - 1) * ((B : ℝ) / ((B : ℝ) + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hd
  have h4 : Real.log p * B ≤ (Real.log ((B : ℝ) + 1) + ((p : ℝ) - B - 1) / ((B : ℝ) + 1)) * B :=
    mul_le_mul_of_nonneg_right hlog hB0.le
  nlinarith [h4, hfrac]

theorem sum_log_div_pred_SB :
    ∀ (B : ℕ) (bad S : Finset ℕ), 128 ≤ B → bad.card ≤ B →
      (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ bad)) →
      ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  intro B bad S hB hcard hS
  have hBR : (128 : ℝ) ≤ B := by exact_mod_cast hB
  have hB0 : (0 : ℝ) < B := by linarith
  have hlogB : (4.85 : ℝ) ≤ Real.log B := by
    have h128 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    have h2 := Real.log_two_gt_d9
    have h3 : Real.log 128 ≤ Real.log B := Real.log_le_log (by norm_num) hBR
    rw [h128] at h3
    norm_num at h2 ⊢
    linarith
  have hLle : Real.log ((B : ℝ) + 1) ≤ Real.log B + 1 / B := by
    have hpos : (0 : ℝ) < ((B : ℝ) + 1) / B := by positivity
    have h1 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by positivity) hB0.ne'] at h1
    have h2 : ((B : ℝ) + 1) / B - 1 = 1 / B := by
      field_simp
      ring
    linarith
  have hLge : 1 ≤ Real.log ((B : ℝ) + 1) := by
    have : Real.log B ≤ Real.log ((B : ℝ) + 1) := Real.log_le_log hB0 (by linarith)
    norm_num at hlogB
    linarith
  have hinv : 1 / (B : ℝ) ≤ 1 := by
    rw [div_le_one hB0]
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ≤ B)]
  have hsmall : ∑ p ∈ S.filter (fun p => p ≤ B), Real.log p / ((p : ℝ) - 1)
      ≤ Real.log B + 17 / 5 := by
    refine GlobalTheory.CompanionTheory.Ar.Small.sum_log_div_pred_le (B : ℝ) _ (by linarith) ?_
    intro p hp
    obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
    exact ⟨(hS p hpS).1, by exact_mod_cast hpB⟩
  have hlarge : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1)
      ≤ Real.log ((B : ℝ) + 1) := by
    have hsub : S.filter (fun p => ¬ p ≤ B) ⊆ bad := by
      intro p hp
      obtain ⟨hpS, hpB⟩ := Finset.mem_filter.mp hp
      exact (hS p hpS).2.resolve_left hpB
    have hc : (S.filter (fun p => ¬ p ≤ B)).card ≤ B :=
      (Finset.card_le_card hsub).trans hcard
    have h1 : ∑ p ∈ S.filter (fun p => ¬ p ≤ B), Real.log p / ((p : ℝ) - 1)
        ≤ (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B) := by
      refine Finset.sum_le_card_nsmul _ _ _ ?_
      intro p hp
      exact log_div_pred_le_of_lt B p hB (not_le.mp (Finset.mem_filter.mp hp).2) hLge
    have h2 : (S.filter (fun p => ¬ p ≤ B)).card • (Real.log ((B : ℝ) + 1) / B)
        ≤ (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) := by
      rw [nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right (by exact_mod_cast hc) ?_
      exact div_nonneg (by linarith) hB0.le
    have h3 : (B : ℝ) * (Real.log ((B : ℝ) + 1) / B) = Real.log ((B : ℝ) + 1) := by
      field_simp
    linarith
  norm_num at hlogB
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumLogPrimeDivPredBoundStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_log_prime_div_pred_bound : ∀ (B : ℕ) (bad S : Finset ℕ), 128 ≤ B → bad.card ≤ B → (∀ p ∈ S, p.Prime ∧ (p ≤ B ∨ p ∈ bad)) → ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB | exact GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.sum_log_div_pred_SB <;> assumption)
end
