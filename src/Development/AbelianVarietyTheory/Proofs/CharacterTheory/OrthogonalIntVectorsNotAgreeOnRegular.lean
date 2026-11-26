module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormEightOfFourierVanishingOrderFifteen
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormEightOfFourierVanishingOrderFifteen
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem no_norm_eight_of_fourier_vanishing_order_fifteen :
    ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 →
      (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  intro ω c hω hs hF
  have hinj : Function.Injective (fun j : Fin 15 => ω ^ (j : ℕ)) := by
    intro a b hab
    exact Fin.ext (hω.pow_inj a.2 b.2 hab)
  have hv : (fun i : Fin 15 => ((c ((i + 12) % 15) - c i : ℤ) : ℂ)) = 0 := by
    apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero hinj
    intro j
    have h15 : (ω ^ (j : ℕ)) ^ 15 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hprod : ((ω ^ (j : ℕ)) ^ 3 - 1) *
        ∑ k ∈ Finset.range 15, (c k : ℂ) * (ω ^ (j : ℕ)) ^ k = 0 := by
      by_cases h5 : 5 ∣ (j : ℕ)
      · obtain ⟨m, hm⟩ := h5
        have : (ω ^ (j : ℕ)) ^ 3 = 1 := by
          rw [hm, ← pow_mul, show 5 * m * 3 = 15 * m by ring, pow_mul, hω.pow_eq_one, one_pow]
        rw [this, sub_self, zero_mul]
      · have := hF j j.2 h5
        simp only [pow_mul] at this
        rw [this, mul_zero]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => (ω ^ (j : ℕ)) ^ i * ((c ((i + 12) % 15) - c i : ℤ) : ℂ)) 15]
    generalize ω ^ (j : ℕ) = x at h15 hprod
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hprod ⊢
    push_cast
    linear_combination hprod - ((c 12 : ℂ) + c 13 * x + c 14 * x ^ 2) * h15
  have hp : ∀ i : ℕ, i < 15 → c i = c ((i + 12) % 15) := by
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    simp only [Pi.zero_apply, Int.cast_eq_zero] at this
    linarith
  have h3 : c 3 = c 0 := hp 3 (by norm_num)
  have h4 : c 4 = c 1 := hp 4 (by norm_num)
  have h5 : c 5 = c 2 := hp 5 (by norm_num)
  have h6 : c 6 = c 3 := hp 6 (by norm_num)
  have h7 : c 7 = c 4 := hp 7 (by norm_num)
  have h8 : c 8 = c 5 := hp 8 (by norm_num)
  have h9 : c 9 = c 6 := hp 9 (by norm_num)
  have h10 : c 10 = c 7 := hp 10 (by norm_num)
  have h11 : c 11 = c 8 := hp 11 (by norm_num)
  have h12 : c 12 = c 9 := hp 12 (by norm_num)
  have h13 : c 13 = c 10 := hp 13 (by norm_num)
  have h14 : c 14 = c 11 := hp 14 (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at hs
  rw [h14, h13, h12, h11, h10, h9, h8, h7, h6, h5, h4, h3] at hs
  generalize c 0 ^ 2 = a at hs
  generalize c 1 ^ 2 = b at hs
  generalize c 2 ^ 2 = d at hs
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormEightOfFourierVanishingOrderFifteenStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 15 → ∑ k ∈ Finset.range 15, c k ^ 2 = 8 → (∀ j : ℕ, j < 15 → ¬ 5 ∣ j → ∑ k ∈ Finset.range 15, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | exact GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen | (intros; apply GlobalTheory.no_norm_eight_of_fourier_vanishing_order_fifteen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardNonregularResiduesModPowSubOneLe
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardNonregularResiduesModPowSubOneLe
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem card_nonregular_residues_le (q n : ℕ) (hq : 2 ≤ q) (hn : 0 < n) :
    ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤
      ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  classical
  have hsub : ((Finset.Ioo 0 (q ^ n - 1)).filter
      (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])) ⊆
      n.primeFactors.biUnion (fun p => (Finset.Ioo 0 (q ^ (n / p) - 1)).image
        (fun k => k * ((q ^ n - 1) / (q ^ (n / p) - 1)))) := by
    intro j hj
    rw [Finset.mem_filter, Finset.mem_Ioo] at hj
    obtain ⟨⟨hj0, hjN⟩, e, he, hje⟩ := hj
    rw [Finset.mem_Ioo] at he
    have hqe : 1 ≤ q ^ e := Nat.one_le_pow _ _ (by omega)
    have h1 : q ^ n - 1 ∣ j * (q ^ e - 1) := by
      rw [Nat.mul_sub_one]
      exact (Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_right j hqe)).1 hje.symm
    have h2 : q ^ n - 1 ∣ j * (q ^ Nat.gcd e n - 1) := by
      rw [← Nat.pow_sub_one_gcd_pow_sub_one, ← Nat.gcd_mul_left]
      exact Nat.dvd_gcd h1 (Dvd.intro_left j rfl)
    obtain ⟨m, hm⟩ := Nat.gcd_dvd_right e n
    have hglt : Nat.gcd e n < n := lt_of_le_of_lt (Nat.gcd_le_left n he.1) he.2
    have hm1 : m ≠ 1 := by
      rintro rfl
      omega
    obtain ⟨p, hp, r, hr⟩ := Nat.exists_prime_and_dvd hm1
    have hnp : n = p * (Nat.gcd e n * r) := by
      conv_lhs => rw [hm, hr]
      ring
    have hd : n / p = Nat.gcd e n * r := Nat.div_eq_of_eq_mul_right hp.pos hnp
    have hpn : p ∣ n := ⟨_, hnp⟩
    have hd0 : n / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos).ne'
    have h3 : q ^ n - 1 ∣ j * (q ^ (n / p) - 1) :=
      h2.trans (Nat.mul_dvd_mul_left j
        (Nat.pow_sub_one_dvd_pow_sub_one q ⟨r, hd⟩))
    have h4 : q ^ (n / p) - 1 ∣ q ^ n - 1 :=
      Nat.pow_sub_one_dvd_pow_sub_one q (Nat.div_dvd_of_dvd hpn)
    have hD : 0 < q ^ (n / p) - 1 := by
      have := Nat.one_lt_pow hd0 (show 1 < q by omega)
      omega
    obtain ⟨M, hM⟩ := h4
    rw [Finset.mem_biUnion]
    refine ⟨p, Nat.mem_primeFactors.2 ⟨hp, hpn, hn.ne'⟩, ?_⟩
    rw [hM, mul_comm j] at h3
    obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left hD h3
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Ioo.2 ⟨?_, ?_⟩, ?_⟩
    · rcases Nat.eq_zero_or_pos k with rfl | h
      · omega
      · exact h
    · rw [hM, hk, mul_comm _ M] at hjN
      exact lt_of_mul_lt_mul_left hjN (Nat.zero_le _)
    · rw [hM, Nat.mul_div_cancel_left _ hD, hk, mul_comm]
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine Finset.sum_le_sum fun p _ => Finset.card_image_le.trans ?_
  rw [Nat.card_Ioo]
  omega

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.CardNonregularResiduesModPowSubOneLeStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le : ∀ q n : ℕ, 2 ≤ q → 0 < n → ((Finset.Ioo 0 (q ^ n - 1)).filter (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1])).card ≤ ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) := by
  first | exact @GlobalTheory.CuspGL.card_nonregular_residues_le | exact GlobalTheory.CuspGL.card_nonregular_residues_le | (intros; apply GlobalTheory.CuspGL.card_nonregular_residues_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SeparationNumericalIneqCuspidalGL
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SeparationNumericalIneqCuspidalGL
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem sepIneq_four_mul_add_five_le (k : ℕ) (hk : 5 ≤ k) : 4 * k + 5 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

theorem sepIneq_sum_lt (q n : ℕ) (hq : 2 ≤ q) :
    ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < q ^ (n / 2 + 1) := by
  have hinj : Set.InjOn (fun p => n / p) (n.primeFactors : Set ℕ) := by
    intro a ha b hb hab
    have ha' := Nat.mem_primeFactors.1 (Finset.mem_coe.1 ha)
    have hb' := Nat.mem_primeFactors.1 (Finset.mem_coe.1 hb)
    have h1 := Nat.div_div_self ha'.2.1 ha'.2.2
    have h2 := Nat.div_div_self hb'.2.1 hb'.2.2
    simp only at hab
    rw [← h1, ← h2, hab]
  calc ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) ≤ ∑ p ∈ n.primeFactors, q ^ (n / p) :=
        Finset.sum_le_sum fun p _ => Nat.sub_le _ _
    _ = ∑ k ∈ n.primeFactors.image (fun p => n / p), q ^ k :=
        (Finset.sum_image (f := fun k => q ^ k) hinj).symm
    _ < q ^ (n / 2 + 1) := by
        apply Nat.geomSum_lt hq
        intro k hk
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hk
        have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
        exact Nat.lt_succ_of_le (Nat.div_le_div_left hp2 (by norm_num))

theorem sepIneq_large (q n : ℕ) (hq : 2 ≤ q) (hn : 11 ≤ n) :
    (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  have hS := sepIneq_sum_lt q n hq
  set S := ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2)
  obtain ⟨k, hk⟩ : ∃ k, n = (n / 2 + 1) + k := ⟨n - (n / 2 + 1), by omega⟩
  have hk5 : 5 ≤ k := by omega
  have h1 : 2 * n + 1 ≤ q ^ k := by
    have := sepIneq_four_mul_add_five_le k hk5
    have h2 : 2 ^ k ≤ q ^ k := Nat.pow_le_pow_left hq k
    omega
  have h2 : q ^ k ≤ q ^ (n / 2 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : q ^ n = q ^ (n / 2 + 1) * q ^ k := by rw [← pow_add, ← hk]
  rw [h3]
  set Q := q ^ (n / 2 + 1)
  set R := q ^ k
  have h4 : Q * (2 * n + 1) ≤ Q * R := Nat.mul_le_mul_left _ h1
  obtain ⟨T, hT⟩ : ∃ T, Q * R = T + 1 := ⟨Q * R - 1, by
    have : 0 < Q * R := Nat.mul_pos (by omega) (by omega)
    omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [hT] at h4 ⊢
  simp only [Nat.add_sub_cancel]
  have h5 : 2 * (m + 1) + 1 ≤ Q := le_trans h1 h2
  have h6 : 2 * (m + 1) * (Q * (2 * (m + 1) + 1)) ≤ 2 * (m + 1) * (T + 1) := Nat.mul_le_mul_left _ h4
  have h7 : 4 * (m + 1) ^ 2 * S ≤ 4 * (m + 1) ^ 2 * Q := Nat.mul_le_mul_left _ hS.le
  have h8 : 2 * (m + 1) * (2 * (m + 1) + 1) ≤ 2 * (m + 1) * Q := Nat.mul_le_mul_left _ h5
  nlinarith

theorem sepIneq_sub (t k c : ℕ) (hc : c ≤ 2) (hk : 0 < k) : (((2 + t) ^ k - c : ℕ) : ℤ) = (2 + (t : ℤ)) ^ k - c := by
  have : 2 ≤ (2 + t) ^ k := le_trans (by omega) (Nat.le_self_pow hk.ne' _)
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl

theorem sep_numerical_ineq : ∀ q n : ℕ, 2 ≤ q → 0 < n → ¬ (q = 2 ∧ (n = 4 ∨ n = 6)) → (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  intro q n hq hn hex
  rcases le_or_gt 11 n with h | h
  · exact sepIneq_large q n hq h
  obtain ⟨t, rfl⟩ : ∃ t, q = 2 + t := ⟨q - 2, by omega⟩
  have e1 : Nat.primeFactors 1 = ∅ := by simp
  have e2 : Nat.primeFactors 2 = {2} := by decide +kernel
  have e3 : Nat.primeFactors 3 = {3} := by decide +kernel
  have e4 : Nat.primeFactors 4 = {2} := by decide +kernel
  have e5 : Nat.primeFactors 5 = {5} := by decide +kernel
  have e6 : Nat.primeFactors 6 = {2, 3} := by decide +kernel
  have e7 : Nat.primeFactors 7 = {7} := by decide +kernel
  have e8 : Nat.primeFactors 8 = {2} := by decide +kernel
  have e9 : Nat.primeFactors 9 = {3} := by decide +kernel
  have e10 : Nat.primeFactors 10 = {2, 5} := by decide +kernel
  have ht : (0 : ℤ) ≤ t := by positivity
  have s1 := fun k hk => sepIneq_sub t k 1 (by omega) hk
  have s2 := fun k hk => sepIneq_sub t k 2 (by omega) hk
  have ht1 : n = 4 ∨ n = 6 → (1 : ℤ) ≤ t := by omega
  have p2 : (0:ℤ) ≤ t^2 := by positivity
  have p3 : (0:ℤ) ≤ t^3 := by positivity
  have p4 : (0:ℤ) ≤ t^4 := by positivity
  have p5 : (0:ℤ) ≤ t^5 := by positivity
  have p6 : (0:ℤ) ≤ t^6 := by positivity
  have p7 : (0:ℤ) ≤ t^7 := by positivity
  have p8 : (0:ℤ) ≤ t^8 := by positivity
  have p9 : (0:ℤ) ≤ t^9 := by positivity
  have p10 : (0:ℤ) ≤ t^10 := by positivity
  interval_cases n
  · rw [e1]; simp
  · rw [e2, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith [sq_nonneg ((t:ℤ))]
  · rw [e3, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e4, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    have := ht1 (by norm_num)
    nlinarith
  · rw [e5, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e6, Finset.sum_pair (by norm_num)]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    have := ht1 (by norm_num)
    nlinarith
  · rw [e7, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e8, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e9, Finset.sum_singleton]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith
  · rw [e10, Finset.sum_pair (by norm_num)]; zify; rw [s1 _ (by norm_num), s2 _ (by norm_num), s2 _ (by norm_num)]; norm_num
    nlinarith

end GlobalTheory.CuspGL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SeparationNumericalIneqCuspidalGLStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separation_numerical_ineq_cuspidalGL : ∀ q n : ℕ, 2 ≤ q → 0 < n → ¬ (q = 2 ∧ (n = 4 ∨ n = 6)) → (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  first | exact @GlobalTheory.CuspGL.sep_numerical_ineq | exact GlobalTheory.CuspGL.sep_numerical_ineq | (intros; apply GlobalTheory.CuspGL.sep_numerical_ineq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParsevalBoundIntegerVectorSmallFourierSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParsevalBoundIntegerVectorSmallFourierSupport
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

theorem parsevalSep_orth (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N) (k l : ℕ)
    (hk : k < N) (hl : l < N) :
    ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l)
      = if k = l then (N : ℂ) else 0 := by
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have h0 : ω ≠ 0 := hω.ne_zero hN.ne'
  rw [← Complex.inv_eq_conj h1]
  have hz : ∀ j : ℕ, ω ^ (j * k) * (ω⁻¹) ^ (j * l) = (ω ^ k * (ω ^ l)⁻¹) ^ j := by
    intro j
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l]
  simp_rw [hz]
  split_ifs with h
  · subst h
    simp [mul_inv_cancel₀ (pow_ne_zero k h0)]
  · have hne : ω ^ k * (ω ^ l)⁻¹ ≠ 1 := by
      intro h'
      apply h
      apply hω.pow_inj hk hl
      field_simp at h'
      exact h'
    have hp : (ω ^ k * (ω ^ l)⁻¹) ^ N = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm l, pow_mul, pow_mul,
        hω.pow_eq_one]
      simp
    rw [geom_sum_eq hne, hp]
    simp

theorem parsevalSep_identity (N : ℕ) (ω : ℂ) (hN : 0 < N) (hω : IsPrimitiveRoot ω N)
    (c : ℕ → ℤ) :
    ∑ j ∈ Finset.range N, ‖∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k)‖ ^ 2
      = (N : ℝ) * ((∑ k ∈ Finset.range N, c k ^ 2 : ℤ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, map_mul, map_pow, map_intCast]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.sum_comm]
  have : ∀ l ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
      = if k = l then (c k : ℂ) * c l * N else 0 := by
    intro l hl
    have := parsevalSep_orth N ω hN hω k l (Finset.mem_range.1 hk) (Finset.mem_range.1 hl)
    have e : ∑ j ∈ Finset.range N,
      (c k : ℂ) * ω ^ (j * k) * ((c l : ℂ) * (starRingEnd ℂ ω) ^ (j * l))
       = (c k : ℂ) * c l * ∑ j ∈ Finset.range N, ω ^ (j * k) * (starRingEnd ℂ ω) ^ (j * l) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, this]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos hk]
  ring

theorem parsevalSep_bound : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by
  intro n N ω c S hn hN hω h2 h0 hS
  have h1 : ‖ω‖ = 1 := hω.norm'_eq_one hN.ne'
  have hP := parsevalSep_identity N ω hN hω c
  rw [h2] at hP
  set F : ℕ → ℂ := fun j => ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) with hF
  have hb : ∀ j, ‖F j‖ ≤ 2 * n := by
    intro j
    have h2' : ∑ k ∈ Finset.range N, (c k : ℝ) ^ 2 = 2 * n := by exact_mod_cast h2
    rw [← h2']
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, norm_pow, h1, one_pow, mul_one, Complex.norm_intCast]
    have : |c k| ≤ c k ^ 2 := by
      rw [← sq_abs]
      have := abs_nonneg (c k)
      nlinarith [Int.le_self_sq |c k|]
    exact_mod_cast this
  have hz : ‖F 0‖ ≤ (n : ℝ) - 1 := by
    have : F 0 = ((∑ k ∈ Finset.range N, c k : ℤ) : ℂ) := by simp [hF]
    rw [this, Complex.norm_intCast]
    exact_mod_cast h0
  have hle : ∀ j ∈ Finset.range N, ‖F j‖ ^ 2 ≤
      (if j = 0 then ((n : ℝ) - 1) ^ 2 else 0) + (if j ∈ S then 4 * (n : ℝ) ^ 2 else 0) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      have : ‖F 0‖ ^ 2 ≤ ((n : ℝ) - 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      rw [if_pos rfl]
      split_ifs
      · have : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by positivity
        linarith
      · linarith
    · rw [if_neg hj0, zero_add]
      split_ifs with hjS
      · have := pow_le_pow_left₀ (norm_nonneg _) (hb j) 2
        linarith [show (2 * (n : ℝ)) ^ 2 = 4 * (n : ℝ) ^ 2 by ring]
      · have : F j = 0 := hS j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.1 hj) hjS
        simp [this]
  have hsum := Finset.sum_le_sum hle
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_range.2 hN),
    Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((Finset.range N ∩ S).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hP' : ∑ j ∈ Finset.range N, ‖F j‖ ^ 2 = (N : ℝ) * (2 * n) := by
    rw [hP]; push_cast; ring
  have key : (2 * n * N : ℝ) ≤ ((n : ℝ) - 1) ^ 2 + 4 * (n : ℝ) ^ 2 * S.card := by
    have : ((Finset.range N ∩ S).card : ℝ) * (4 * (n : ℝ) ^ 2) ≤ S.card * (4 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    linarith
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [← hn1] at key
  exact_mod_cast key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ParsevalBoundIntegerVectorSmallFourierSupportStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport : ∀ (n N : ℕ) (ω : ℂ) (c : ℕ → ℤ) (S : Finset ℕ), 0 < n → 0 < N → IsPrimitiveRoot ω N → ∑ k ∈ Finset.range N, c k ^ 2 = 2 * n → |∑ k ∈ Finset.range N, c k| ≤ (n : ℤ) - 1 → (∀ j : ℕ, 0 < j → j < N → j ∉ S → ∑ k ∈ Finset.range N, (c k : ℂ) * ω ^ (j * k) = 0) → 2 * n * N ≤ (n - 1) ^ 2 + 4 * n ^ 2 * S.card := by
  first | exact @GlobalTheory.parsevalSep_bound | exact GlobalTheory.parsevalSep_bound | (intros; apply GlobalTheory.parsevalSep_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythree
section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythree
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory

private theorem sum_range_63_primitiveRoot_pow_eq_ite (ω : ℂ) (hω : IsPrimitiveRoot ω 63) (n : ℕ) :
    ∑ j ∈ Finset.range 63, ω ^ (j * n) = if 63 ∣ n then (63 : ℂ) else 0 := by
  have hpow : ∀ j : ℕ, ω ^ (j * n) = (ω ^ n) ^ j := fun j => by rw [← pow_mul, mul_comm]
  simp_rw [hpow]
  split_ifs with hn
  · rw [(hω.pow_eq_one_iff_dvd n).mpr hn]
    simp
  · have hne : ω ^ n ≠ 1 := fun h => hn ((hω.pow_eq_one_iff_dvd n).mp h)
    have h63 : (ω ^ n) ^ 63 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    have hg := geom_sum_mul (ω ^ n) 63
    rw [h63, sub_self] at hg
    exact (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)

theorem fourier_inv_sixtythree (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63) (m : ℕ)
    (hm : m < 63) :
    ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = 63 * (c m : ℂ) := by
  have hsum := sum_range_63_primitiveRoot_pow_eq_ite ω hω
  calc ∑ j ∈ Finset.range 63, (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))
      = ∑ k ∈ Finset.range 63, (c k : ℂ) * ∑ j ∈ Finset.range 63, ω ^ (j * (k + 62 * m)) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_add, pow_add]
        ring
    _ = ∑ k ∈ Finset.range 63, (c k : ℂ) * (if 63 ∣ k + 62 * m then (63 : ℂ) else 0) := by
        simp_rw [hsum]
    _ = 63 * (c m : ℂ) := by
        rw [Finset.sum_eq_single m]
        · rw [if_pos (by omega)]
          ring
        · intro k hk hkm
          have hk' := Finset.mem_range.mp hk
          rw [if_neg (by omega)]
          simp
        · intro hm'
          exact absurd (Finset.mem_range.mpr hm) hm'

theorem mixed_diff_sixtythree (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63)
    (h : ∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) (m : ℕ) (hm : m < 53) :
    c (m + 10) - c (m + 3) = c (m + 7) - c m := by
  have key : ∀ n, n < 63 → (63 : ℂ) * (c n : ℂ) = ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n)) :=
    fun n hn => (fourier_inv_sixtythree ω c hω n hn).symm
  have hz : ∑ j ∈ Finset.range 63,
      ((∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 10)))
        - (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 3)))
        - (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (m + 7)))
        + (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * m))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    by_cases h21 : 21 ∣ j
    · have hB : ω ^ (186 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
      rw [show j * (62 * (m + 10)) = j * (62 * (m + 7)) + 186 * j by ring,
        show j * (62 * (m + 3)) = j * (62 * m) + 186 * j by ring, pow_add, pow_add, hB]
      ring
    · by_cases h9 : 9 ∣ j
      · have hB : ω ^ (434 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
        rw [show j * (62 * (m + 10)) = j * (62 * (m + 3)) + 434 * j by ring,
          show j * (62 * (m + 7)) = j * (62 * m) + 434 * j by ring, pow_add, pow_add, hB]
        ring
      · rw [h j hj' h21 h9]
        ring
  have h63 : (63 : ℂ) * ((c (m + 10) : ℂ) - c (m + 3) - c (m + 7) + c m) = 0 := by
    rw [mul_add, mul_sub, mul_sub, key (m + 10) (by omega), key (m + 3) (by omega),
      key (m + 7) (by omega), key m (by omega), ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact hz
  have h' : (c (m + 10) : ℂ) - c (m + 3) - c (m + 7) + c m = 0 :=
    (mul_eq_zero.mp h63).resolve_left (by norm_num)
  have h'' : ((c (m + 10) - c (m + 3) - c (m + 7) + c m : ℤ) : ℂ) = 0 := by
    push_cast
    exact h'
  have h3 := Int.cast_eq_zero.mp h''
  linarith

private theorem apply_add_21_eq_of_fourier_vanish_order_63 (ω : ℂ) (c : ℕ → ℤ) (hω : IsPrimitiveRoot ω 63)
    (h : ∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) (n : ℕ) (hn : n < 42) :
    c (n + 21) = c n := by
  have hs : ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * (n + 21)))
      = ∑ j ∈ Finset.range 63,
      (∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k)) * ω ^ (j * (62 * n)) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    by_cases h3 : 3 ∣ j
    · have hB : ω ^ (1302 * j) = 1 := (hω.pow_eq_one_iff_dvd _).mpr (by omega)
      rw [show j * (62 * (n + 21)) = j * (62 * n) + 1302 * j by ring, pow_add, hB, mul_one]
    · rw [h j hj' (by omega) (by omega), zero_mul, zero_mul]
  have e1 := fourier_inv_sixtythree ω c hω (n + 21) (by omega)
  rw [hs, fourier_inv_sixtythree ω c hω n (by omega)] at e1
  have e2 : ((c (n + 21) : ℤ) : ℂ) = (c n : ℂ) :=
    (mul_left_cancel₀ (by norm_num : (63 : ℂ) ≠ 0) e1).symm
  exact_mod_cast e2

theorem no_norm_twelve_order_sixtythree : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 →
    ∑ k ∈ Finset.range 63, c k ^ 2 = 12 →
    (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j →
      ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  intro ω c hω hnorm hF
  have hrel := fun m (hm : m < 53) => mixed_diff_sixtythree ω c hω hF m hm
  have hper := fun n (hn : n < 42) => apply_add_21_eq_of_fourier_vanish_order_63 ω c hω hF n hn
  have hD : ∀ m, m < 56 → c (m + 7) - c m = c (m % 3 + 7) - c (m % 3) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      by_cases h3 : m < 3
      · rw [Nat.mod_eq_of_lt h3]
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
        have e1 := hrel m' (by omega)
        have e2 := ih m' (by omega) (by omega)
        rw [show (m' + 3) % 3 = m' % 3 by omega, show m' + 3 + 7 = m' + 10 by omega]
        linarith
  have hS : ∑ k ∈ Finset.range 63, c k ^ 2 = 3 * ∑ k ∈ Finset.range 21, c k ^ 2 := by
    rw [show (63 : ℕ) = 21 + 21 + 21 from rfl, Finset.sum_range_add, Finset.sum_range_add]
    have h1 : ∑ x ∈ Finset.range 21, c (21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2 :=
      Finset.sum_congr rfl fun x hx => by
        rw [add_comm, hper x (by have := Finset.mem_range.mp hx; omega)]
    have h2 : ∑ x ∈ Finset.range 21, c (21 + 21 + x) ^ 2 = ∑ x ∈ Finset.range 21, c x ^ 2 :=
      Finset.sum_congr rfl fun x hx => by
        have hx' := Finset.mem_range.mp hx
        rw [show 21 + 21 + x = x + 21 + 21 by omega, hper (x + 21) (by omega), hper x (by omega)]
    rw [h1, h2]
    ring
  have hcolsum : ∑ k ∈ Finset.range 21, c k ^ 2 =
      ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
    rw [show (21 : ℕ) = 7 + 7 + 7 from rfl, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 : ∑ x ∈ Finset.range 7, c (7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 7) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [add_comm]
    have h2 : ∑ x ∈ Finset.range 7, c (7 + 7 + x) ^ 2 = ∑ x ∈ Finset.range 7, c (x + 14) ^ 2 :=
      Finset.sum_congr rfl fun x _ => by rw [show 7 + 7 + x = x + 14 by omega]
    rw [h1, h2]
  have hcol : ∀ b, b < 7 → (c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2 ≤
      3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
    intro b hb
    have e1 := hD b (by omega)
    have e2 := hD (b + 7) (by omega)
    have e3 := hD (b + 14) (by omega)
    have p := hper b (by omega)
    rw [show b + 7 + 7 = b + 14 by omega] at e2
    rw [show b + 14 + 7 = b + 21 by omega, p] at e3
    have key : (c (b + 7) - c b) ^ 2 + (c (b + 14) - c (b + 7)) ^ 2 + (c b - c (b + 14)) ^ 2 ≤
        3 * (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) := by
      nlinarith [sq_nonneg (c b + c (b + 7) + c (b + 14))]
    rw [e1, e2, e3] at key
    have hb3 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hb3 with h | h | h
    · rw [show (b + 7) % 3 = 1 by omega, show (b + 14) % 3 = 2 by omega, h] at key
      norm_num at key
      linarith
    · rw [show (b + 7) % 3 = 2 by omega, show (b + 14) % 3 = 0 by omega, h] at key
      norm_num at key
      linarith
    · rw [show (b + 7) % 3 = 0 by omega, show (b + 14) % 3 = 1 by omega, h] at key
      norm_num at key
      linarith
  rw [hS] at hnorm
  have hS21 : ∑ k ∈ Finset.range 21, c k ^ 2 = 4 := by omega
  have hΔ : 7 * ((c 7 - c 0) ^ 2 + (c 8 - c 1) ^ 2 + (c 9 - c 2) ^ 2) ≤ 12 := by
    have hle := Finset.sum_le_sum (s := Finset.range 7) fun b hb => hcol b (Finset.mem_range.mp hb)
    rw [← Finset.mul_sum, ← hcolsum, hS21] at hle
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    push_cast at hle
    linarith
  have hsum0 : (c 7 - c 0) + (c 8 - c 1) + (c 9 - c 2) = 0 := by
    have e2 := hD 7 (by omega)
    have e3 := hD 14 (by omega)
    have p := hper 0 (by omega)
    norm_num at e2 e3 p
    linarith
  have hzero : c 7 - c 0 = 0 ∧ c 8 - c 1 = 0 ∧ c 9 - c 2 = 0 := by
    generalize c 7 - c 0 = x at hΔ hsum0 ⊢
    generalize c 8 - c 1 = y at hΔ hsum0 ⊢
    generalize c 9 - c 2 = z at hΔ hsum0 ⊢
    have hz : z = -x - y := by linarith
    subst hz
    have h14 : 14 * (x ^ 2 + x * y + y ^ 2) ≤ 12 := by nlinarith
    have hq : x ^ 2 + x * y + y ^ 2 ≤ 0 := by omega
    have hy2 : y ^ 2 ≤ 0 := by nlinarith [sq_nonneg (2 * x + y)]
    have hy : y = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hy2 (sq_nonneg y))
    subst hy
    have hx2 : x ^ 2 ≤ 0 := by nlinarith
    have hx : x = 0 := (pow_eq_zero_iff two_ne_zero).mp (le_antisymm hx2 (sq_nonneg x))
    subst hx
    norm_num
  have hp7 : ∀ r, r < 3 → c (r + 7) = c r := by
    intro r hr
    interval_cases r <;> norm_num <;> omega
  have hcolc : ∀ b, b < 7 → c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2 = 3 * c b ^ 2 := by
    intro b hb
    have e1 := hD b (by omega)
    have e2 := hD (b + 7) (by omega)
    rw [show b + 7 + 7 = b + 14 by omega] at e2
    rw [hp7 (b % 3) (Nat.mod_lt _ (by norm_num))] at e1
    rw [hp7 ((b + 7) % 3) (Nat.mod_lt _ (by norm_num))] at e2
    have h1 : c (b + 7) = c b := by linarith
    have h2 : c (b + 14) = c b := by linarith
    rw [h1, h2]
    ring
  have h3 : ∑ b ∈ Finset.range 7, (c b ^ 2 + c (b + 7) ^ 2 + c (b + 14) ^ 2) =
      3 * ∑ b ∈ Finset.range 7, c b ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb => hcolc b (Finset.mem_range.mp hb)
  rw [hcolsum, h3] at hS21
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CharacterTheory.NoNormTwelveOrderSixtythreeStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 : ∀ (ω : ℂ) (c : ℕ → ℤ), IsPrimitiveRoot ω 63 → ∑ k ∈ Finset.range 63, c k ^ 2 = 12 → (∀ j : ℕ, j < 63 → ¬ 21 ∣ j → ¬ 9 ∣ j → ∑ k ∈ Finset.range 63, (c k : ℂ) * ω ^ (j * k) = 0) → False := by
  first | exact @GlobalTheory.no_norm_twelve_order_sixtythree | exact GlobalTheory.no_norm_twelve_order_sixtythree | (intros; apply GlobalTheory.no_norm_twelve_order_sixtythree <;> assumption)
end
end

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

private lemma abs_sum_le_sum_sq_int (s : Finset ℕ) (a : ℕ → ℤ) :
    |∑ k ∈ s, a k| ≤ ∑ k ∈ s, a k ^ 2 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rcases eq_or_ne (a k) 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |a k| := Int.one_le_abs h
    nlinarith [sq_abs (a k)]

theorem orthogonal_int_vectors_not_agree_on_regular :
    ∀ (q n : ℕ) (ω : ℂ) (a b : ℕ → ℤ), 2 ≤ q → 0 < n → IsPrimitiveRoot ω (q ^ n - 1) → ∑ k ∈ Finset.range (q ^ n - 1), a k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), b k ^ 2 = n → ∑ k ∈ Finset.range (q ^ n - 1), a k * b k = 0 → 0 < (∑ k ∈ Finset.range (q ^ n - 1), a k) * (∑ k ∈ Finset.range (q ^ n - 1), b k) → (∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) → ∑ k ∈ Finset.range (q ^ n - 1), (a k : ℂ) * ω ^ (j * k) = ∑ k ∈ Finset.range (q ^ n - 1), (b k : ℂ) * ω ^ (j * k)) → False := by
  intro q n ω a b hq hn hω ha2 hb2 hab hpos hreg
  have hN : 0 < q ^ n - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' (by omega))
  have hc2 : ∑ k ∈ Finset.range (q ^ n - 1), (a k - b k) ^ 2 = 2 * (n : ℤ) := by
    have e : ∀ k, (a k - b k) ^ 2 = a k ^ 2 + b k ^ 2 - 2 * (a k * b k) := fun k => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ha2, hb2, hab]
    ring
  have hcoef : ∀ j : ℕ, (∀ e : ℕ, 0 < e → e < n → ¬ j * q ^ e ≡ j [MOD q ^ n - 1]) →
      ∑ k ∈ Finset.range (q ^ n - 1), (((a k - b k : ℤ)) : ℂ) * ω ^ (j * k) = 0 := by
    intro j hj
    simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hreg j hj, sub_self]
  by_cases hexc : q = 2 ∧ (n = 4 ∨ n = 6)
  · obtain ⟨rfl, rfl | rfl⟩ := hexc
    · refine GlobalTheory.T.false_of_sum_sq_eq_eight_of_fourier_vanish_order_15 ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h5 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h5
            interval_cases j <;> interval_cases e <;> decide))
    · refine GlobalTheory.T.false_of_sum_sq_eq_12_of_fourier_vanish_order_63 ω (fun k => a k - b k) (by simpa using hω) (by simpa using hc2)
        (fun j hj h21 h9 => by
          simpa using hcoef j (fun e he1 he2 => by
            revert h21 h9
            interval_cases j <;> interval_cases e <;> decide))
  · have hsum : |∑ k ∈ Finset.range (q ^ n - 1), (a k - b k)| ≤ (n : ℤ) - 1 := by
      rw [Finset.sum_sub_distrib]
      have hA := abs_le.mp ((abs_sum_le_sum_sq_int _ a).trans ha2.le)
      have hB := abs_le.mp ((abs_sum_le_sum_sq_int _ b).trans hb2.le)
      rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact abs_le.mpr ⟨by omega, by omega⟩
    have h1 := GlobalTheory.T.parseval_bound_integerVector_smallFourierSupport n (q ^ n - 1) ω (fun k => a k - b k)
      ((Finset.Ioo 0 (q ^ n - 1)).filter
        (fun j => ∃ e ∈ Finset.Ioo 0 n, j * q ^ e ≡ j [MOD q ^ n - 1]))
      hn hN hω hc2 hsum (fun j hj0 hjN hjS => by
        refine hcoef j (fun e he1 he2 he => hjS ?_)
        simp only [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨hj0, hjN⟩, e, ⟨he1, he2⟩, he⟩)
    have h2 := GlobalTheory.T.card_nonregular_residues_mod_pow_sub_one_le q n hq hn
    have h3 := GlobalTheory.T.separation_numerical_ineq_cuspidalGL q n hq hn hexc
    exact absurd (lt_of_le_of_lt (h1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _)) h3)
      (lt_irrefl _)

end GlobalTheory.CuspGL
