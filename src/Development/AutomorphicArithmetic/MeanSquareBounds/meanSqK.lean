module

public import Development.AutomorphicArithmetic.MeanSquareBounds.twistK
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMain

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.SumMinLeDiv
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private lemma primePowerSum_le_log_mul_sum_min {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    sP (cN x) N p ≤ Real.log p * ∑ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) := by
  have hp2 : 2 ≤ p := hp.two_le
  have key : ∀ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
      ∃ k ∈ Icc 1 N, p ^ k = n := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hnN⟩, hpp, hmin⟩ := hn
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    rw [hq.pow_minFac hk.ne'] at hmin
    subst hmin
    refine ⟨k, Finset.mem_Icc.2 ⟨hk, ?_⟩, rfl⟩
    exact ((Nat.lt_pow_self (by omega : 1 < q)).le).trans hnN
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  unfold sP
  calc ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), cN x n
      = ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
          Real.log p * min 1 (x / (n : ℝ)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        obtain ⟨k, hk, rfl⟩ := key n hn
        have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
        rw [cN, ArithmeticFunction.vonMangoldt_apply_pow hk0,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * min 1 (x / (n : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
        · intro n hn
          obtain ⟨k, hk, rfl⟩ := key n hn
          exact Finset.mem_image.2 ⟨k, hk, rfl⟩
        · exact mul_nonneg hlogp (le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg _)))
    _ = ∑ k ∈ Icc 1 N, Real.log p * min 1 (x / (p : ℝ) ^ k) := by
        rw [Finset.sum_image fun a _ b _ h => Nat.pow_right_injective hp2 h]
        push_cast
        rfl
    _ = _ := (Finset.mul_sum _ _ _).symm

private lemma sum_min_le_div {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) ≤ 2 * (x / p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  set r : ℝ := 1 / p with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hterm : ∀ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) ≤ x * r ^ i := by
    intro i _
    refine (min_le_right _ _).trans (le_of_eq ?_)
    rw [hr, one_div_pow, mul_one_div]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, mul_zero]
    positivity
  · have h1 := dA_tail_geo r hr0 hr2 1 N hN
    simp only [pow_one] at h1
    have hsplit : ∑ i ∈ Icc 1 N, r ^ i = r + ∑ i ∈ Ioc 1 N, r ^ i := by
      rw [dA_Icc_one_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN]
      simp
    have hle : ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r := by
      rw [hsplit]
      linarith [pow_nonneg hr0 N]
    calc x * ∑ i ∈ Icc 1 N, r ^ i ≤ x * (2 * r) := mul_le_mul_of_nonneg_left hle hx0
      _ = 2 * (x / p) := by rw [hr]; ring

theorem exists_primePowerSum_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N p : ℕ, sP (cN y) N p ≤ C * Real.log y := by
  refine ⟨3, by norm_num, fun y hy N p => ?_⟩
  have hy0 : 0 < y := by linarith
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  by_cases hp : p.Prime
  · have h1 := primePowerSum_le_log_mul_sum_min hy0.le N hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    rcases le_total (p : ℝ) y with hpy | hpy
    · have h2 := dA_sum_min_pow y (by linarith) p hp.two_le N
      have h3 : Real.log p ≤ Real.log y := Real.log_le_log hp0 hpy
      linarith
    · have h2 := mul_le_mul_of_nonneg_left (sum_min_le_div hy0.le N hp) hlogp
      have he : Real.exp 1 ≤ y := by linarith [Real.exp_one_lt_d9]
      have h4 : Real.log p / p ≤ Real.log y / y :=
        Real.log_div_self_antitoneOn he (le_trans he hpy) hpy
      have h5 : Real.log p * (2 * (y / p)) ≤ 2 * Real.log y := by
        have e : Real.log p * (2 * (y / p)) = 2 * y * (Real.log p / p) := by ring
        rw [e]
        calc 2 * y * (Real.log p / p) ≤ 2 * y * (Real.log y / y) := by gcongr
          _ = 2 * Real.log y := by field_simp
      linarith
  · have h0 : sP (cN y) N p = 0 := by
      unfold sP
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter] at hn
      obtain ⟨_, hpp, hmin⟩ := hn
      exact absurd (hmin ▸ Nat.minFac_prime hpp.ne_one) hp
    rw [h0]
    positivity

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.MeanSqAbs
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem meanSq_abs :
    ∀ (P : Finset ℕ) (m₀ a₀ nstar : ℕ) (Z y η B : ℝ) (κ : ℕ → ℂ), 8 ∣ m₀ → a₀.Coprime m₀ → 0 ≤ y → 0 ≤ η →
      (∀ q ∈ P, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ ⌊Z⌋₊ ^ 2 < q) → (∀ n, ‖κ n‖ ≤ 1) → (∀ p, sP (cN y) ⌊Z⌋₊ p ≤ B) →
      (∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊Z⌋₊ ^ 2 → s ≠ nstar →
        |∑ q ∈ P, (jacobiSym (q : ℤ) s : ℝ)| ≤ η * P.card) →
      ∑ q ∈ P, ‖S Z y q κ‖ ^ 2 ≤ ((∑ p ∈ (Icc 1 ⌊Z⌋₊).filter Nat.Prime, sP (cN y) ⌊Z⌋₊ p ^ 2) + RR (cN y) m₀ ⌊Z⌋₊ ^ 2 +
        (2 * B ^ 2 + 2 * B * RR (cN y) m₀ ⌊Z⌋₊) + η * (∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n) ^ 2) * P.card := by
  intro P m₀ a₀ nstar Z y η B κ h8 hcop hy hη hP hκ hB hJ
  set N := ⌊Z⌋₊ with hN
  have hc0 : ∀ n, 0 ≤ cN y n := cN_nonneg y hy
  have hcpp : ∀ n, cN y n ≠ 0 → IsPrimePow n := cN_primePow y
  have hexp := meansq_expand P (Icc 1 N) (cN y) hc0 κ hκ (fun n q => jacobiSym (n : ℤ) q)
  have hpair : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N,
      |∑ q ∈ P, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
        |∑ q ∈ P, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
    intro n hn n' hn'
    rw [Finset.mem_Icc] at hn hn'
    refine abs_pair_sum_eq P m₀ a₀ n n' h8 hcop (by omega) (by omega) ?_
    intro q hq
    obtain ⟨h1, h2, h3⟩ := hP q hq
    refine ⟨h1, h2, lt_of_le_of_lt ?_ h3⟩
    rw [pow_two]
    exact Nat.mul_le_mul hn.2 hn'.2
  have hsplit := meansq_split (Icc 1 N) (cN y) hc0 (fun n n' => soutPart m₀ (n * n'))
    (fun n n' => |∑ q ∈ P, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)|) (P.card : ℝ) η
    (by positivity) hη (max nstar 2)
    (by
      intro n hn n' hn'
      rw [hpair n hn n' hn']
      exact abs_sum_jacobi_le P _)
    (by
      intro n hn n' hn' hr1 hrs
      rw [hpair n hn n' hn']
      rw [Finset.mem_Icc] at hn hn'
      have hpos := soutPart_pos m₀ (n * n')
      have hnn : 0 < n * n' := Nat.mul_pos (by omega) (by omega)
      have hle : soutPart m₀ (n * n') ≤ N ^ 2 := by
        refine (soutPart_le m₀ _ hnn).trans ?_
        rw [pow_two]
        exact Nat.mul_le_mul hn.2 hn'.2
      refine hJ _ (by omega) (soutPart_odd m₀ _ (dvd_trans (by norm_num) h8))
        (soutPart_squarefree m₀ _) (soutPart_coprime m₀ _) hle ?_
      intro h
      apply hrs
      omega)
  beta_reduce at hsplit
  have h1 := pairs_one (cN y) hc0 hcpp m₀ N
  have h2 := pairs_r (cN y) hc0 hcpp m₀ N (max nstar 2) (by omega) B hB
  refine hexp.trans (hsplit.trans ?_)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.SPsqLe
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem sum_log_primes_le_mul_log_four (Y : ℕ) :
    ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ Y * Real.log 4 := by
  rw [← Real.log_prod]
  · have h1 : ((primorial Y : ℕ) : ℝ) ≤ (4 : ℝ) ^ Y := by exact_mod_cast primorial_le_four_pow Y
    have h2 : ((primorial Y : ℕ) : ℝ) = ∏ p ∈ (range (Y + 1)).filter Nat.Prime, (p : ℝ) := by
      simp [primorial, Nat.cast_prod]
    rw [← h2, ← Real.log_pow]
    have hpos : (0 : ℝ) < (primorial Y : ℕ) := by exact_mod_cast primorial_pos Y
    exact Real.log_le_log hpos h1
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

private theorem sum_sP_sq_large_primes_le (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ 96 * Real.log 4 * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  have hY3 : 3 ≤ Y := Nat.le_floor (by exact_mod_cast hy)
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hYlt : y < (Y : ℝ) + 1 := Nat.lt_floor_add_one y
  have hY3r : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hy0 : 0 < y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hset : ((Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ Y) = (Ioc Y N).filter Nat.Prime := by
    ext p
    simp only [mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, hp⟩, h3⟩
      exact ⟨⟨by omega, h2⟩, hp⟩
    · rintro ⟨⟨h1, h2⟩, hp⟩
      exact ⟨⟨⟨by omega, h2⟩, hp⟩, by omega⟩
  rw [hset]
  have hterm : ∀ p ∈ (Ioc Y N).filter Nat.Prime,
      sP (cN y) N p ^ 2 ≤ 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := sP_cN_le_log_div y hy0.le N p hpp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    calc sP (cN y) N p ^ 2 ≤ (2 * y * Real.log p / p) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
        field_simp
        ring
  have htail := sum_log_sq_div_sq_primes_tail_le N (N - Y) Y (by omega) le_rfl
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogY : Real.log Y ≤ Real.log y := Real.log_le_log hY0 hYle
  have hlog2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith)
  have hq : 4 * Real.log 4 * (Real.log Y + 2 * Real.log 2) / Y ≤ 24 * Real.log 4 * Real.log y / y := by
    rw [div_le_div_iff₀ hY0 hy0]
    have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have hE : Real.log Y + 2 * Real.log 2 ≤ 3 * Real.log y := by linarith
    have h1 : (Real.log Y + 2 * Real.log 2) * y ≤ 3 * Real.log y * y :=
      mul_le_mul_of_nonneg_right hE hy0.le
    have h2 : 3 * Real.log y * y ≤ 3 * Real.log y * (2 * Y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (show 0 ≤ 4 * Real.log 4 by positivity)
    nlinarith
  calc ∑ p ∈ (Ioc Y N).filter Nat.Prime, sP (cN y) N p ^ 2
      ≤ ∑ p ∈ (Ioc Y N).filter Nat.Prime, 4 * y ^ 2 * (Real.log p ^ 2 / (p : ℝ) ^ 2) := sum_le_sum hterm
    _ = 4 * y ^ 2 * ∑ p ∈ (Ioc Y N).filter Nat.Prime, Real.log p ^ 2 / (p : ℝ) ^ 2 := by rw [mul_sum]
    _ ≤ 4 * y ^ 2 * (24 * Real.log 4 * Real.log y / y) := by
        gcongr
        exact htail.trans hq
    _ = 96 * Real.log 4 * (y * Real.log y) := by
        field_simp
        ring

private theorem sum_sP_sq_small_primes_le_of_bound (C0 : ℝ) (hC0 : 0 < C0)
    (hb : ∀ (y : ℝ), 3 ≤ y → ∀ (N p : ℕ), sP (cN y) N p ≤ C0 * Real.log y) (y : ℝ) (hy : 3 ≤ y) (N : ℕ) :
    ∑ p ∈ ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ ⌊y⌋₊), sP (cN y) N p ^ 2
      ≤ (4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4) * (y * Real.log y) := by
  set Y := ⌊y⌋₊ with hYdef
  set S := ⌊Real.sqrt y⌋₊ with hSdef
  have hy0 : 0 < y := by linarith
  have hYle : (Y : ℝ) ≤ y := Nat.floor_le hy0.le
  have hsq0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hSle : (S : ℝ) ≤ Real.sqrt y := Nat.floor_le hsq0
  have hSlt : Real.sqrt y < (S : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsqsq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hsq1 : 1 ≤ Real.sqrt y := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by linarith)
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogsq : Real.log (Real.sqrt y) = Real.log y / 2 := Real.log_sqrt hy0.le
  have hlsy : Real.log y ≤ 2 * Real.sqrt y := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt y by linarith)
    rw [hlogsq] at this
    linarith
  have hsub : ((Icc 1 N).filter Nat.Prime).filter (fun p => p ≤ Y) ⊆ (range (Y + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
    exact ⟨by omega, hp.1.2⟩
  have step1 := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p => sP (cN y) N p ^ 2) (fun p _ _ => sq_nonneg _)
  have hterm : ∀ p ∈ (range (Y + 1)).filter Nat.Prime, sP (cN y) N p ^ 2 ≤
      (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0) + 2 * C0 ^ 2 * Real.log y * Real.log p := by
    intro p hp
    have hpp := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hlp : 0 ≤ Real.log p := Real.log_nonneg hp1
    have h0 := sP_cN_nonneg y hy0.le N p
    have h1 := hb y hy N p
    have hsqb : sP (cN y) N p ^ 2 ≤ C0 ^ 2 * Real.log y ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ h0 h1 2
    have hx : 0 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by positivity
    split_ifs with hpS
    · linarith
    · have hpS' : (S : ℝ) + 1 ≤ p := by exact_mod_cast (show S + 1 ≤ p by omega)
      have hlt : Real.sqrt y < p := by linarith
      have hlog : Real.log (Real.sqrt y) ≤ Real.log p := Real.log_le_log (by linarith) hlt.le
      rw [hlogsq] at hlog
      have : C0 ^ 2 * Real.log y ^ 2 ≤ 2 * C0 ^ 2 * Real.log y * Real.log p := by
        have hc : 0 ≤ C0 ^ 2 * Real.log y := by positivity
        nlinarith [mul_le_mul_of_nonneg_left (show Real.log y ≤ 2 * Real.log p by linarith) hc]
      linarith
  have step2 := sum_le_sum hterm
  rw [sum_add_distrib, ← mul_sum] at step2
  have hite : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, (if p ≤ S then C0 ^ 2 * Real.log y ^ 2 else 0)
      ≤ ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
    rw [← sum_filter]
    have hsub2 : ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S) ⊆ range (S + 1) := by
      intro p hp
      simp only [mem_filter, mem_range] at hp ⊢
      omega
    calc ∑ p ∈ ((range (Y + 1)).filter Nat.Prime).filter (fun p => p ≤ S), C0 ^ 2 * Real.log y ^ 2
        ≤ ∑ p ∈ range (S + 1), C0 ^ 2 * Real.log y ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _ => by positivity)
      _ = ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) := by
          rw [sum_const, card_range, nsmul_eq_mul]
          push_cast
          ring
  have htheta := sum_log_primes_le_mul_log_four Y
  have hL : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hA : ((S : ℝ) + 1) * Real.log y ≤ 4 * y := by
    have : ((S : ℝ) + 1) * Real.log y ≤ (Real.sqrt y + 1) * (2 * Real.sqrt y) :=
      mul_le_mul (by linarith) hlsy hly (by linarith)
    nlinarith
  have hA' : ((S : ℝ) + 1) * (C0 ^ 2 * Real.log y ^ 2) ≤ 4 * C0 ^ 2 * (y * Real.log y) := by
    have := mul_le_mul_of_nonneg_right hA (show 0 ≤ C0 ^ 2 * Real.log y by positivity)
    nlinarith
  have hB : 2 * C0 ^ 2 * Real.log y * ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p
      ≤ 2 * C0 ^ 2 * Real.log 4 * (y * Real.log y) := by
    have h1 : ∑ p ∈ (range (Y + 1)).filter Nat.Prime, Real.log p ≤ y * Real.log 4 :=
      htheta.trans (mul_le_mul_of_nonneg_right hYle hL.le)
    have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 2 * C0 ^ 2 * Real.log y by positivity)
    nlinarith
  calc _ ≤ _ := step1
    _ ≤ _ := step2
    _ ≤ _ := by linarith

theorem sPsq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N : ℕ,
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN y) N p ^ 2 ≤ C * y * Real.log y := by
  obtain ⟨C0, hC0, hb⟩ := exists_primePowerSum_le_mul_log
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨4 * C0 ^ 2 + 2 * C0 ^ 2 * Real.log 4 + 96 * Real.log 4, by positivity, ?_⟩
  intro y hy N
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun p => p ≤ ⌊y⌋₊)]
  have h3 := sum_sP_sq_small_primes_le_of_bound C0 hC0 hb y hy N
  have h2 := sum_sP_sq_large_primes_le y hy N
  nlinarith

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.RRLe
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem RR_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ (N m₀ : ℕ) (w : ℝ), 1 ≤ w →
      (∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ N → (p : ℝ) ≤ w) → RR (cN y) m₀ N ≤ C * (Real.sqrt y + w * Real.log y) := by
  obtain ⟨C₁, hC₁, hsP⟩ := exists_primePowerSum_le_mul_log
  have hK := dA_KC_pos
  refine ⟨3 * dA_KC + C₁, by positivity, ?_⟩
  intro y hy N m₀ w hw hm
  have hy0 : (0:ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hf0 : ∀ n, 0 ≤ cN y n := fun n => dA_cN_nonneg hy0 n
  have hsplit : RR (cN y) m₀ N ≤
      (∑ n ∈ Icc 1 N with IsPrimePow n ∧ Even (n.factorization n.minFac), cN y n) +
      ∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac ∣ m₀, cN y n := by
    unfold RR
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n _ => ?_
    have := hf0 n
    by_cases h1 : IsPrimePow n <;> by_cases h2 : Even (n.factorization n.minFac) <;>
      by_cases h3 : n.minFac ∣ m₀ <;> simp [h1, h2, h3, this]
  have hA : (∑ n ∈ Icc 1 N with IsPrimePow n ∧ Even (n.factorization n.minFac), cN y n)
      ≤ 3 * dA_KC * Real.sqrt y := by
    have hsub : (Icc 1 N).filter (fun n => IsPrimePow n ∧ Even (n.factorization n.minFac))
        ⊆ (Icc 1 N).image (fun m => m ^ 2) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpp, hev⟩ := hn
      obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      rw [Nat.pow_minFac hk.ne', hp.minFac_eq, Nat.factorization_pow_self hp] at hev
      obtain ⟨j, rfl⟩ := hev
      refine Finset.mem_image.2 ⟨p ^ j, ?_, by ring⟩
      have h1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
      have h2 : p ^ j ≤ p ^ (j + j) := Nat.pow_le_pow_right hp.pos (by omega)
      exact Finset.mem_Icc.2 ⟨h1, h2.trans hnN⟩
    calc _ ≤ ∑ n ∈ (Icc 1 N).image (fun m => m ^ 2), cN y n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf0 n)
      _ = ∑ m ∈ Icc 1 N, cN y (m ^ 2) :=
          Finset.sum_image (fun a _ b _ h => Nat.pow_left_injective (by norm_num) h)
      _ = ∑ m ∈ Icc 1 N, ArithmeticFunction.vonMangoldt m * min 1 (y / (m:ℝ) ^ 2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [cN, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero, Nat.cast_pow]
      _ ≤ dA_KC * ∑ m ∈ Icc 1 N, min 1 (y / (m:ℝ) ^ 2) := by
          refine dA_vM_major _ (fun n => le_min zero_le_one (div_nonneg hy0 (by positivity))) ?_ N
          intro n hn
          apply min_le_min_left
          apply div_le_div_of_nonneg_left hy0 (pow_pos (Nat.cast_pos.mpr hn) 2)
          have := (Nat.cast_nonneg n : (0:ℝ) ≤ n)
          push_cast
          nlinarith
      _ ≤ dA_KC * (3 * Real.sqrt y) :=
          mul_le_mul_of_nonneg_left (dA_sum_min_sq y (by linarith) N) hK.le
      _ = 3 * dA_KC * Real.sqrt y := by ring
  have hB : (∑ n ∈ Icc 1 N with IsPrimePow n ∧ n.minFac ∣ m₀, cN y n)
      ≤ C₁ * w * Real.log y := by
    set P := (Icc 1 N).filter (fun p => p.Prime ∧ p ∣ m₀ ∧ (p:ℝ) ≤ w) with hP
    have hmaps : ∀ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀),
        n.minFac ∈ P := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnN⟩, hpp, hd⟩ := hn
      have hpr : n.minFac.Prime := Nat.minFac_prime hpp.ne_one
      have hle : n.minFac ≤ N := (Nat.minFac_le (by omega)).trans hnN
      simp only [hP, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hpr.one_lt.le, hle⟩, hpr, hd, hm _ hpr hd hle⟩
    have hcard : (P.card : ℝ) ≤ w := by
      have hs : P ⊆ Icc 1 ⌊w⌋₊ := by
        intro p hp
        simp only [hP, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.1, Nat.le_floor hp.2.2.2⟩
      have h1 := Finset.card_le_card hs
      rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
      calc (P.card : ℝ) ≤ ⌊w⌋₊ := by exact_mod_cast h1
        _ ≤ w := Nat.floor_le (by linarith)
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ ≤ ∑ p ∈ P, C₁ * Real.log y := by
          refine Finset.sum_le_sum fun p _ => ?_
          refine le_trans ?_ (hsP y hy N p)
          unfold sP
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hf0 n)
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          exact ⟨hn.1.1, hn.1.2.1, hn.2⟩
      _ = P.card * (C₁ * Real.log y) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ w * (C₁ * Real.log y) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hC₁.le hlog)
      _ = C₁ * w * Real.log y := by ring
  have hsq : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hwl : 0 ≤ w * Real.log y := mul_nonneg (by linarith) hlog
  calc RR (cN y) m₀ N ≤ _ := hsplit
    _ ≤ 3 * dA_KC * Real.sqrt y + C₁ * w * Real.log y := add_le_add hA hB
    _ ≤ (3 * dA_KC + C₁) * (Real.sqrt y + w * Real.log y) := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3 * dA_KC) hwl, mul_nonneg hC₁.le hsq]

end QH
end

section -- merged from Development.AutomorphicArithmetic.MeanSquareBounds.SumCNLe
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

theorem sum_cN_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y Z : ℝ, 0 ≤ y → 2 ≤ Z → ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n ≤ C * y * Real.log Z := by
  obtain ⟨C, hC, hM⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨C + 1, by linarith, fun y Z hy hZ => ?_⟩
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  calc ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n
        ≤ ∑ n ∈ Icc 1 ⌊Z⌋₊, y * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          simp only [cN]
          calc ArithmeticFunction.vonMangoldt n * min 1 (y / n)
              ≤ ArithmeticFunction.vonMangoldt n * (y / n) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hΛ
            _ = y * (ArithmeticFunction.vonMangoldt n / n) := by ring
    _ = y * ∑ n ∈ Icc 1 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ y * (C * Real.log Z) := mul_le_mul_of_nonneg_left (hM Z hZ) hy
    _ ≤ (C + 1) * y * Real.log Z := by nlinarith [mul_nonneg hy hlog]

end QH
end

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private lemma ev_log (δ A : ℝ) (hδ : 0 < δ) (hA : 0 < A) :
    ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, A * Real.log Y ≤ Y ^ δ := by
  have h := (isLittleO_log_rpow_atTop hδ).bound (c := 1 / A) (by positivity)
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.1 h
  refine ⟨max Y₀ 1, fun Y hY => ?_⟩
  have h1 := hY₀ Y (le_of_max_le_left hY)
  have hY1 : 1 ≤ Y := le_of_max_le_right hY
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hY1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at h1
  calc A * Real.log Y ≤ A * (1 / A * Y ^ δ) := mul_le_mul_of_nonneg_left h1 hA.le
    _ = Y ^ δ := by field_simp

private lemma sizes (y w : ℝ) (hy : 1 ≤ y) (hw0 : 0 ≤ w) (hw : w ≤ y ^ (1 / 5 : ℝ)) :
    Real.log y ≤ 2 * Real.sqrt y ∧ w * Real.log y ≤ 4 * Real.sqrt y := by
  have hy0 : 0 < y := by linarith
  have key : ∀ a : ℝ, 0 < a → a * Real.log y ≤ y ^ a := by
    intro a ha
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 a)
    rw [Real.log_rpow hy0] at h
    linarith
  have hsq : Real.sqrt y = y ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow y
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy
  constructor
  · have := key (1 / 2) (by norm_num)
    rw [hsq]
    linarith
  · have h3 := key (3 / 10) (by norm_num)
    have h3' : Real.log y ≤ 10 / 3 * y ^ (3 / 10 : ℝ) := by linarith
    have hmul : y ^ (1 / 5 : ℝ) * y ^ (3 / 10 : ℝ) = Real.sqrt y := by
      rw [← Real.rpow_add hy0, hsq]
      norm_num
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    calc w * Real.log y ≤ y ^ (1 / 5 : ℝ) * (10 / 3 * y ^ (3 / 10 : ℝ)) :=
          mul_le_mul hw h3' hl (Real.rpow_nonneg hy0.le _)
      _ = 10 / 3 * Real.sqrt y := by rw [← hmul]; ring
      _ ≤ 4 * Real.sqrt y := by linarith

set_option maxHeartbeats 800000 in
theorem meanSqK :
    ∃ C : ℝ, 0 < C ∧ ∀ ε K : ℝ, 0 < ε → ε ≤ 1 → 1 ≤ K → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (U : ℝ) (m₀ a₀ : ℕ),
      admitted ε Y U m₀ a₀ → (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ Y ^ (ε / 5) ∨ (Y ^ K) ^ 400 < (p : ℝ)) →
      MeanSq C ((Y ^ K) ^ 400) (PPset m₀ a₀ U) (Set.Icc Y (Y ^ K)) := by
  obtain ⟨C1, hC1, hRR⟩ := RR_le
  obtain ⟨C2, hC2, hsP⟩ := exists_primePowerSum_le_mul_log
  obtain ⟨C3, hC3, hsPsq⟩ := sPsq_le
  obtain ⟨C4, hC4, hcN⟩ := sum_cN_le
  refine ⟨C3 + 25 * C1 ^ 2 + 4 * C2 ^ 2 + 20 * C1 * C2 + C4 ^ 2, by positivity, ?_⟩
  intro ε K hε hε1 hK
  obtain ⟨Y1, hY1⟩ := ev_log (ε / 6) (1600 * K) (by positivity) (by positivity)
  obtain ⟨Y2, hY2⟩ := ev_log (1 / 2) (400 * K) (by norm_num) (by positivity)
  obtain ⟨Y3, hY3⟩ := twistK ε (800 * K) (K + 1) hε (by positivity) (by positivity)
  refine ⟨max (max Y1 Y2) (max Y3 3), fun Y hY U m₀ a₀ hA hp => ?_⟩
  have hYa : Y1 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY
  have hYb : Y2 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY
  have hYc : Y3 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY
  have hY3' : (3 : ℝ) ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hY
  have hY0 : 0 < Y := by linarith
  have hY1' : (1 : ℝ) ≤ Y := by linarith
  have hLY : 0 ≤ Real.log Y := Real.log_nonneg hY1'
  obtain ⟨nstar, hn⟩ := hY3 Y hYc U m₀ a₀ hA
  set Z := (Y ^ K) ^ 400 with hZ
  have hYK1 : 1 ≤ Y ^ K := Real.one_le_rpow hY1' (by linarith)
  have hYK : Y ≤ Y ^ K := by
    simpa using Real.rpow_le_rpow_of_exponent_le hY1' hK
  have hZY : Y ^ K ≤ Z := le_self_pow₀ hYK1 (by norm_num)
  have hZpos : 0 < Z := by linarith
  have hlogZ : Real.log Z = 400 * K * Real.log Y := by
    rw [hZ, Real.log_pow, Real.log_rpow hY0]; push_cast; ring
  have hZ2 : Z ^ 2 = Real.exp (800 * K * Real.log Y) := by
    have h : Real.log (Z ^ 2) = 800 * K * Real.log Y := by
      rw [Real.log_pow, hlogZ]; push_cast; ring
    rw [← h, Real.exp_log (pow_pos hZpos 2)]
  have hZ2' : Z ^ 2 = Y ^ (800 * K) := by
    rw [hZ2, Real.rpow_def_of_pos hY0]; ring_nf
  have hN : ((⌊Z⌋₊ : ℕ) : ℝ) ≤ Z := Nat.floor_le hZpos.le
  have hN2 : (((⌊Z⌋₊ ^ 2 : ℕ)) : ℝ) ≤ Z ^ 2 := by
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2
  have hq : ∀ q ∈ Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ U, Nat.Prime q ∧ q % m₀ = a₀ % m₀ ∧ ⌊Z⌋₊ ^ 2 < q := by
    intro q hqP
    simp only [Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset, Finset.mem_filter, Finset.mem_Icc] at hqP
    obtain ⟨⟨hq1, hqU⟩, hqp, hqm, hqs⟩ := hqP
    refine ⟨hqp, hqm, ?_⟩
    have hUf : 0 < ⌊U⌋₊ := by omega
    have hU1 : 1 ≤ U := Nat.floor_pos.1 hUf
    have hU0 : 0 < U := by linarith
    have hlo := hA.lo
    have hy1 := hY1 Y hYa
    have h1 : Z ^ 2 ≤ U ^ (1 / 2 : ℝ) := by
      rw [hZ2, Real.rpow_def_of_pos hU0]
      apply Real.exp_le_exp.2
      linarith
    have h2 : (((⌊Z⌋₊ ^ 2 : ℕ)) : ℝ) < (q : ℝ) := by linarith
    exact_mod_cast h2
  have hs : ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊Z⌋₊ ^ 2 → s ≠ nstar →
      |∑ q ∈ Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ U, ((jacobiSym (q : ℤ) s : ℤ) : ℝ)| ≤
        Y ^ (-(K + 1)) * ((Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ U).card : ℝ) := by
    intro s h1 h2 h3 h4 h5 h6
    apply hn s h1 h2 h3 h4 _ h6
    have : ((s : ℕ) : ℝ) ≤ (((⌊Z⌋₊ ^ 2 : ℕ)) : ℝ) := by exact_mod_cast h5
    rw [← hZ2']
    linarith
  set w := Y ^ (ε / 5) with hw
  have hw1 : 1 ≤ w := Real.one_le_rpow hY1' (by positivity)
  have hpw : ∀ p : ℕ, Nat.Prime p → p ∣ m₀ → p ≤ ⌊Z⌋₊ → (p : ℝ) ≤ w := by
    intro p hpr hd hpN
    rcases hp p hpr hd with h | h
    · exact h
    · have : ((p : ℕ) : ℝ) ≤ ((⌊Z⌋₊ : ℕ) : ℝ) := by exact_mod_cast hpN
      linarith
  have hη0 : 0 ≤ Y ^ (-(K + 1)) := Real.rpow_nonneg hY0.le _
  have hprod : Y ^ K * Y * Y ^ (-(K + 1)) = 1 := by
    rw [show Y ^ K * Y * Y ^ (-(K + 1)) = Y ^ (K + 1 + (-(K + 1))) by
      rw [Real.rpow_add hY0, Real.rpow_add hY0, Real.rpow_one]]
    simp
  intro y hy κ hκ
  obtain ⟨hYy, hyYK⟩ := hy
  have hy3 : (3 : ℝ) ≤ y := by linarith
  have hy0 : 0 ≤ y := by linarith
  have hL1 : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hwy : w ≤ y ^ (1 / 5 : ℝ) := by
    calc w ≤ Y ^ (1 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1' (by linarith)
      _ ≤ y ^ (1 / 5 : ℝ) := Real.rpow_le_rpow hY0.le hYy (by norm_num)
  obtain ⟨hsz1, hsz2⟩ := sizes y w (by linarith) (by linarith) hwy
  have hmain := meanSq_abs (Formalism.HermitianLattices.ZeroFreeRegionGL2.PPset m₀ a₀ U) m₀ a₀ nstar Z y (Y ^ (-(K + 1)))
    (C2 * Real.log y) κ hA.eight hA.coprime hy0 hη0 hq hκ (fun p => hsP y hy3 _ p) hs
  refine le_trans hmain ?_
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  set L := Real.log y with hLdef
  set R := RR (cN y) m₀ ⌊Z⌋₊ with hRdef
  set sq := Real.sqrt y with hsqdef
  have hL0 : 0 ≤ L := by linarith
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg y
  have hsq2 : sq * sq = y := Real.mul_self_sqrt hy0
  have hsq1 : 1 ≤ sq := Real.one_le_sqrt.2 (by linarith)
  have hsqy : sq ≤ y := by
    calc sq = sq * 1 := (mul_one sq).symm
      _ ≤ sq * sq := mul_le_mul_of_nonneg_left hsq1 hsq0
      _ = y := hsq2
  have hR0 : 0 ≤ R := by
    rw [hRdef, RR]
    exact Finset.sum_nonneg (fun n _ => cN_nonneg y hy0 n)
  have hRle : R ≤ 5 * C1 * sq := by
    have := hRR y hy3 ⌊Z⌋₊ m₀ w hw1 hpw
    calc R ≤ C1 * (sq + w * L) := this
      _ ≤ C1 * (5 * sq) := mul_le_mul_of_nonneg_left (by linarith) hC1.le
      _ = 5 * C1 * sq := by ring
  have hyL : y ≤ y * L := le_mul_of_one_le_right hy0 hL1
  have hA1 := hsPsq y hy3 ⌊Z⌋₊
  have hR2 : R ^ 2 ≤ 25 * C1 ^ 2 * (y * L) := by
    have h := pow_le_pow_left₀ hR0 hRle 2
    have h' : (5 * C1 * sq) ^ 2 = 25 * C1 ^ 2 * (sq * sq) := by ring
    have h3 : 25 * C1 ^ 2 * y ≤ 25 * C1 ^ 2 * (y * L) :=
      mul_le_mul_of_nonneg_left hyL (by positivity)
    rw [h', hsq2] at h
    linarith
  have hB2 : 2 * (C2 * L) ^ 2 ≤ 4 * C2 ^ 2 * (y * L) := by
    have hL2 : L ≤ 2 * y := by linarith
    have h1 : L * L ≤ 2 * y * L := mul_le_mul_of_nonneg_right hL2 hL0
    have h2 : C2 ^ 2 * (L * L) ≤ C2 ^ 2 * (2 * y * L) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    have h3 : 2 * (C2 * L) ^ 2 = 2 * (C2 ^ 2 * (L * L)) := by ring
    have h4 : 2 * (C2 ^ 2 * (2 * y * L)) = 4 * C2 ^ 2 * (y * L) := by ring
    linarith
  have hBR : 2 * (C2 * L) * R ≤ 20 * C1 * C2 * (y * L) := by
    have h1 : 2 * (C2 * L) * R ≤ 2 * (C2 * L) * (5 * C1 * sq) :=
      mul_le_mul_of_nonneg_left hRle (by positivity)
    have h2 : L * sq ≤ 2 * y := by
      have := mul_le_mul_of_nonneg_right hsz1 hsq0
      rw [mul_assoc, hsq2] at this
      exact this
    have h3 : C1 * C2 * (L * sq) ≤ C1 * C2 * (2 * y) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have h4 : C1 * C2 * y ≤ C1 * C2 * (y * L) := mul_le_mul_of_nonneg_left hyL (by positivity)
    have h5 : 2 * (C2 * L) * (5 * C1 * sq) = 10 * (C1 * C2 * (L * sq)) := by ring
    have h6 : C1 * C2 * (2 * y) = 2 * (C1 * C2 * y) := by ring
    have h7 : 20 * C1 * C2 * (y * L) = 20 * (C1 * C2 * (y * L)) := by ring
    linarith
  have hS0 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n :=
    Finset.sum_nonneg (fun n _ => cN_nonneg y hy0 n)
  have hS : ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n ≤ C4 * y * (400 * K * Real.log Y) := by
    rw [← hlogZ]; exact hcN y Z hy0 (by linarith)
  have hKL : (400 * K * Real.log Y) ^ 2 ≤ Y := by
    have h := hY2 Y hYb
    have h0 : 0 ≤ 400 * K * Real.log Y := by positivity
    have h' := pow_le_pow_left₀ h0 h 2
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hY0.le] at h'
    exact h'
  have hS2 : (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n) ^ 2 ≤ C4 ^ 2 * y ^ 2 * Y := by
    have h := pow_le_pow_left₀ hS0 hS 2
    have h2 : (C4 * y * (400 * K * Real.log Y)) ^ 2 ≤ C4 ^ 2 * y ^ 2 * Y := by
      rw [show (C4 * y * (400 * K * Real.log Y)) ^ 2 = C4 ^ 2 * y ^ 2 * (400 * K * Real.log Y) ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left hKL (by positivity)
    linarith
  have hη1 : y * Y * Y ^ (-(K + 1)) ≤ 1 := by
    calc y * Y * Y ^ (-(K + 1)) ≤ Y ^ K * Y * Y ^ (-(K + 1)) := by gcongr
      _ = 1 := hprod
  have hηt : Y ^ (-(K + 1)) * (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n) ^ 2 ≤ C4 ^ 2 * (y * L) := by
    calc Y ^ (-(K + 1)) * (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, cN y n) ^ 2
        ≤ Y ^ (-(K + 1)) * (C4 ^ 2 * y ^ 2 * Y) := mul_le_mul_of_nonneg_left hS2 hη0
      _ = C4 ^ 2 * y * (y * Y * Y ^ (-(K + 1))) := by ring
      _ ≤ C4 ^ 2 * y * 1 := mul_le_mul_of_nonneg_left hη1 (by positivity)
      _ ≤ C4 ^ 2 * (y * L) := by rw [mul_one]; exact mul_le_mul_of_nonneg_left hyL (sq_nonneg _)
  have hA1' : ∑ p ∈ Finset.Icc 1 ⌊Z⌋₊ with Nat.Prime p, sP (cN y) ⌊Z⌋₊ p ^ 2 ≤ C3 * (y * L) := by
    have : C3 * y * L = C3 * (y * L) := by ring
    linarith
  calc _ ≤ C3 * (y * L) + 25 * C1 ^ 2 * (y * L) + 4 * C2 ^ 2 * (y * L) + 20 * C1 * C2 * (y * L)
        + C4 ^ 2 * (y * L) := by linarith
    _ = (C3 + 25 * C1 ^ 2 + 4 * C2 ^ 2 + 20 * C1 * C2 + C4 ^ 2) * y * L := by ring

end QH
