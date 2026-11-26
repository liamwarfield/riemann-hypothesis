module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZMoll
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqPage
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistB
public import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqPairs
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace Pairs

private lemma factorization_prime_pow_self (p k : ℕ) (hp : p.Prime) : (p ^ k).factorization p = k := by
  simp [Nat.factorization_pow, hp.factorization_self]

theorem soutPart_prime_pow (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    soutPart m₀ (p ^ k) = if Odd k ∧ ¬ p ∣ m₀ then p else 1 := by
  unfold soutPart
  rw [Nat.primeFactors_prime_pow hk hp, Finset.filter_singleton, factorization_prime_pow_self p k hp]
  split_ifs <;> simp

theorem soutPart_mul_of_coprime (m₀ a b : ℕ) (h : a.Coprime b) :
    soutPart m₀ (a * b) = soutPart m₀ a * soutPart m₀ b := by
  have hfac := Nat.factorization_mul_of_coprime h
  have hdisj := Nat.Coprime.disjoint_primeFactors h
  unfold soutPart
  rw [Nat.Coprime.primeFactors_mul h, Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter hdisj)]
  congr 1
  · congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have hqb : q ∉ b.primeFactors := Finset.disjoint_left.1 hdisj hq
    have h0 : b.factorization q = 0 := by
      by_contra hne
      exact hqb (Nat.support_factorization b ▸ Finsupp.mem_support_iff.2 hne)
    rw [hfac, Finsupp.add_apply, h0, add_zero]
  · congr 1
    refine Finset.filter_congr (fun q hq => ?_)
    have hqa : q ∉ a.primeFactors := Finset.disjoint_right.1 hdisj hq
    have h0 : a.factorization q = 0 := by
      by_contra hne
      exact hqa (Nat.support_factorization a ▸ Finsupp.mem_support_iff.2 hne)
    rw [hfac, Finsupp.add_apply, h0, zero_add]

theorem primePow_data {n : ℕ} (h : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ k ≠ 0 ∧ n = p ^ k ∧ n.minFac = p ∧ n.factorization n.minFac = k := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 h
  have hm : (p ^ k).minFac = p := hp.pow_minFac hk.ne'
  refine ⟨p, k, hp, hk.ne', rfl, hm, ?_⟩
  rw [hm, factorization_prime_pow_self p k hp]

def tPart (m₀ n : ℕ) : ℕ :=
  if Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀ then 1 else n.minFac

theorem soutPart_same {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n') (he : n.minFac = n'.minFac) :
    soutPart m₀ (n * n') = 1 ∨ soutPart m₀ (n * n') = n.minFac := by
  obtain ⟨p, k, hp, hk, rfl, hm, -⟩ := primePow_data h
  obtain ⟨q, k', hq, hk', rfl, hm', -⟩ := primePow_data h'
  have hpq : p = q := hm.symm.trans (he.trans hm')
  subst hpq
  rw [← pow_add, soutPart_prime_pow m₀ p (k + k') hp (by omega), hm]
  split_ifs <;> simp

private lemma tPart_prime_pow_eq_soutPart (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    tPart m₀ (p ^ k) = soutPart m₀ (p ^ k) := by
  rw [soutPart_prime_pow m₀ p k hp hk]
  unfold tPart
  rw [hp.pow_minFac hk, factorization_prime_pow_self p k hp]
  rcases Nat.even_or_odd k with h1 | h1
  · have h1' : ¬ Odd k := Nat.not_odd_iff_even.2 h1
    simp [h1, h1']
  · have h1' : ¬ Even k := Nat.not_even_iff_odd.2 h1
    by_cases h2 : p ∣ m₀ <;> simp [h1, h1', h2]

theorem soutPart_diff {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n') (he : n.minFac ≠ n'.minFac) :
    soutPart m₀ (n * n') = tPart m₀ n * tPart m₀ n' := by
  obtain ⟨p, k, hp, hk, rfl, hm, -⟩ := primePow_data h
  obtain ⟨q, k', hq, hk', rfl, hm', -⟩ := primePow_data h'
  have hpq : p ≠ q := fun hpq => he (hm.trans (hpq.trans hm'.symm))
  have hcop : (p ^ k).Coprime (q ^ k') := Nat.Coprime.pow k k' ((Nat.coprime_primes hp hq).2 hpq)
  rw [soutPart_mul_of_coprime m₀ _ _ hcop, tPart_prime_pow_eq_soutPart m₀ p k hp hk, tPart_prime_pow_eq_soutPart m₀ q k' hq hk']

def aW (c : ℕ → ℝ) (p n : ℕ) : ℝ := if IsPrimePow n ∧ n.minFac = p then c n else 0

def gW (c : ℕ → ℝ) (m₀ n : ℕ) : ℝ :=
  if IsPrimePow n ∧ (Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀) then c n else 0

theorem primePowerSum_eq_sum_Icc (c : ℕ → ℝ) (N p : ℕ) : sP c N p = ∑ n ∈ Icc 1 N, aW c p n := by
  simp only [sP, aW, Finset.sum_filter]

theorem RR_eq (c : ℕ → ℝ) (m₀ N : ℕ) : RR c m₀ N = ∑ n ∈ Icc 1 N, gW c m₀ n := by
  simp only [RR, gW, Finset.sum_filter]

theorem aW_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (p n : ℕ) : 0 ≤ aW c p n := by
  unfold aW
  split_ifs
  · exact hc n
  · exact le_refl 0

theorem gW_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (m₀ n : ℕ) : 0 ≤ gW c m₀ n := by
  unfold gW
  split_ifs
  · exact hc n
  · exact le_refl 0

theorem sP_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (N p : ℕ) : 0 ≤ sP c N p := by
  exact Finset.sum_nonneg (fun n _ => hc n)

theorem RR_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (m₀ N : ℕ) : 0 ≤ RR c m₀ N := by
  exact Finset.sum_nonneg (fun n _ => hc n)

theorem aW_self {c : ℕ → ℝ} {n : ℕ} (h : IsPrimePow n) : aW c n.minFac n = c n := by
  unfold aW
  rw [if_pos ⟨h, rfl⟩]

theorem gW_eq_of_tPart_eq_one {c : ℕ → ℝ} {m₀ n : ℕ} (h : IsPrimePow n) (ht : tPart m₀ n = 1) : gW c m₀ n = c n := by
  have hcond : Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀ := by
    unfold tPart at ht
    split_ifs at ht with h1
    · exact h1
    · exact absurd ht (Nat.minFac_prime h.ne_one).one_lt.ne'
  unfold gW
  rw [if_pos ⟨h, hcond⟩]

theorem tPart_cases (m₀ n : ℕ) : tPart m₀ n = 1 ∨ tPart m₀ n = n.minFac := by
  unfold tPart
  split_ifs <;> simp

theorem dbl_sum (s : Finset ℕ) (f g : ℕ → ℝ) :
    ∑ n ∈ s, ∑ n' ∈ s, f n * g n' = (∑ n ∈ s, f n) * ∑ n ∈ s, g n := by
  rw [Finset.sum_mul_sum]

theorem pairs_r_prime (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ)
    (hr : r.Prime) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      sP c N r * sP c N r + sP c N r * RR c m₀ N + RR c m₀ N * sP c N r := by
  have hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n' := by
    intro n n'
    have q1 := mul_nonneg (aW_nonneg hc r n) (aW_nonneg hc r n')
    have q2 := mul_nonneg (aW_nonneg hc r n) (gW_nonneg hc m₀ n')
    have q3 := mul_nonneg (gW_nonneg hc m₀ n) (aW_nonneg hc r n')
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    by_cases he : n.minFac = n'.minFac
    · rcases soutPart_same (m₀ := m₀) hn hn' he with h1 | h1
      · exact absurd (hs.symm.trans h1) hr.one_lt.ne'
      · have hnr : n.minFac = r := h1.symm.trans hs
        have hnr' : n'.minFac = r := he.symm.trans hnr
        have e1 : aW c r n = c n := by unfold aW; rw [if_pos ⟨hn, hnr⟩]
        have e2 : aW c r n' = c n' := by unfold aW; rw [if_pos ⟨hn', hnr'⟩]
        rw [e1, e2]
        have := mul_nonneg (hc n) (gW_nonneg hc m₀ n')
        have := mul_nonneg (gW_nonneg hc m₀ n) (hc n')
        linarith
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      have p1 := Nat.minFac_prime hn.ne_one
      have p2 := Nat.minFac_prime hn'.ne_one
      rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>
        rw [t1, t2] at hd
      · exact absurd (hd.trans (one_mul 1)) hr.one_lt.ne'
      · have e1 : gW c m₀ n = c n := gW_eq_of_tPart_eq_one hn t1
        have e2 : aW c r n' = c n' := by
          unfold aW; rw [if_pos ⟨hn', by rw [hd, one_mul]⟩]
        rw [e1, e2]
        have := mul_nonneg (aW_nonneg hc r n) (hc n')
        linarith
      · have e1 : aW c r n = c n := by
          unfold aW; rw [if_pos ⟨hn, by rw [hd, mul_one]⟩]
        have e2 : gW c m₀ n' = c n' := gW_eq_of_tPart_eq_one hn' t2
        rw [e1, e2]
        have := mul_nonneg (hc n) (aW_nonneg hc r n')
        linarith
      · exfalso
        rw [hd] at hr
        rcases Nat.prime_mul_iff.1 hr with ⟨-, h⟩ | ⟨-, h⟩
        · exact p2.one_lt.ne' h
        · exact p1.one_lt.ne' h
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N,
          (aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n') :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun n' _ => hpt n n'))
    _ = sP c N r * sP c N r + sP c N r * RR c m₀ N + RR c m₀ N * sP c N r := by
        simp only [Finset.sum_add_distrib, dbl_sum, primePowerSum_eq_sum_Icc, RR_eq]

theorem pairs_r_not_prime (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ)
    (hr : 1 < r) (hrp : ¬ r.Prime) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by
  have hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n' := by
    intro n n'
    have q1 := mul_nonneg (aW_nonneg hc r.minFac n) (aW_nonneg hc (r / r.minFac) n')
    have q2 := mul_nonneg (aW_nonneg hc (r / r.minFac) n) (aW_nonneg hc r.minFac n')
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    have p1 := Nat.minFac_prime hn.ne_one
    have p2 := Nat.minFac_prime hn'.ne_one
    by_cases he : n.minFac = n'.minFac
    · exfalso
      rcases soutPart_same (m₀ := m₀) hn hn' he with h1 | h1
      · exact hr.ne' (hs.symm.trans h1)
      · exact hrp (by rw [← hs, h1]; exact p1)
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>
        rw [t1, t2] at hd
      · exact absurd (hd.trans (one_mul 1)) hr.ne'
      · exact absurd (by rw [hd, one_mul]; exact p2) hrp
      · exact absurd (by rw [hd, mul_one]; exact p1) hrp
      · have hmf : r.minFac = n.minFac ∨ r.minFac = n'.minFac := by
          have hpr := Nat.minFac_prime (show r ≠ 1 by omega)
          have hdvd : r.minFac ∣ n.minFac * n'.minFac := by rw [← hd]; exact Nat.minFac_dvd r
          rcases (Nat.Prime.dvd_mul hpr).1 hdvd with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpr p1).1 h)
          · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpr p2).1 h)
        have ha : aW c n.minFac n = c n := aW_self hn
        have hb : aW c n'.minFac n' = c n' := aW_self hn'
        rcases hmf with h | h
        · have hq : r / r.minFac = n'.minFac := by rw [h, hd, Nat.mul_div_cancel_left _ p1.pos]
          rw [hq, h, ha, hb]
          have := mul_nonneg (aW_nonneg hc n'.minFac n) (aW_nonneg hc n.minFac n')
          linarith
        · have hq : r / r.minFac = n.minFac := by rw [h, hd, Nat.mul_div_cancel _ p2.pos]
          rw [hq, h, ha, hb]
          have := mul_nonneg (aW_nonneg hc n'.minFac n) (aW_nonneg hc n.minFac n')
          linarith
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N,
          (aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n') :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun n' _ => hpt n n'))
    _ = sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by
        simp only [Finset.sum_add_distrib, dbl_sum, primePowerSum_eq_sum_Icc]

end Pairs

open Pairs

theorem pairs_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤
      (∑ p ∈ (Icc 1 N).filter Nat.Prime, sP c N p ^ 2) + RR c m₀ N ^ 2 := by
  set P := (Icc 1 N).filter Nat.Prime with hPdef
  have hpt : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N, (if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤
      ∑ p ∈ P, aW c p n * aW c p n' + gW c m₀ n * gW c m₀ n' := by
    intro n hnN n' _
    have h0 : 0 ≤ ∑ p ∈ P, aW c p n * aW c p n' :=
      Finset.sum_nonneg (fun p _ => mul_nonneg (aW_nonneg hc _ _) (aW_nonneg hc _ _))
    have h0' : 0 ≤ gW c m₀ n * gW c m₀ n' := mul_nonneg (gW_nonneg hc _ _) (gW_nonneg hc _ _)
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    have p1 := Nat.minFac_prime hn.ne_one
    by_cases he : n.minFac = n'.minFac
    · have hmem : n.minFac ∈ P := by
        rw [hPdef, Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hnN
        exact ⟨⟨p1.one_lt.le, le_trans (Nat.minFac_le (by omega)) hnN.2⟩, p1⟩
      have hsingle := Finset.single_le_sum (f := fun p => aW c p n * aW c p n')
        (fun p _ => mul_nonneg (aW_nonneg hc _ _) (aW_nonneg hc _ _)) hmem
      have ha : aW c n.minFac n = c n := aW_self hn
      have hb : aW c n.minFac n' = c n' := by rw [he]; exact aW_self hn'
      simp only [ha, hb] at hsingle
      linarith
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      have t1 : tPart m₀ n = 1 := Nat.eq_one_of_mul_eq_one_right hd.symm
      have t2 : tPart m₀ n' = 1 := Nat.eq_one_of_mul_eq_one_left hd.symm
      rw [gW_eq_of_tPart_eq_one hn t1, gW_eq_of_tPart_eq_one hn' t2]
      linarith
  have e : ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, aW c p n * aW c p n' = ∑ p ∈ P, sP c N p ^ 2 := by
    calc _ = ∑ n ∈ Icc 1 N, ∑ p ∈ P, ∑ n' ∈ Icc 1 N, aW c p n * aW c p n' :=
          Finset.sum_congr rfl (fun n _ => Finset.sum_comm)
      _ = ∑ p ∈ P, ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, aW c p n * aW c p n' := Finset.sum_comm
      _ = ∑ p ∈ P, sP c N p ^ 2 := Finset.sum_congr rfl (fun p _ => by rw [dbl_sum, ← primePowerSum_eq_sum_Icc, sq])
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = 1 then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, (∑ p ∈ P, aW c p n * aW c p n' + gW c m₀ n * gW c m₀ n') :=
        Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun n' hn' => hpt n hn n' hn'))
    _ = ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, aW c p n * aW c p n' +
          ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, gW c m₀ n * gW c m₀ n' := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun n _ => Finset.sum_add_distrib)
    _ = (∑ p ∈ P, sP c N p ^ 2) + RR c m₀ N ^ 2 := by
        rw [e, dbl_sum, ← RR_eq, sq]

theorem pairs_r (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ) (hr : 1 < r)
    (B : ℝ) (hB : ∀ p, sP c N p ≤ B) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      2 * B ^ 2 + 2 * B * RR c m₀ N := by
  have hB0 : 0 ≤ B := le_trans (sP_nonneg hc N 0) (hB 0)
  have hR := RR_nonneg hc m₀ N
  by_cases hrp : r.Prime
  · refine le_trans (pairs_r_prime c hc hpp m₀ N r hrp) ?_
    have h1 := sP_nonneg hc N r
    have h2 := hB r
    nlinarith [mul_le_mul h2 h2 h1 hB0, mul_le_mul_of_nonneg_right h2 hR, mul_nonneg hB0 hB0]
  · refine le_trans (pairs_r_not_prime c hc hpp m₀ N r hr hrp) ?_
    have a1 := sP_nonneg hc N r.minFac
    have a2 := sP_nonneg hc N (r / r.minFac)
    have b1 := hB r.minFac
    have b2 := hB (r / r.minFac)
    nlinarith [mul_le_mul b1 b2 a2 hB0, mul_le_mul b2 b1 a1 hB0, mul_nonneg hB0 hR]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqJac
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem soutPart_pos (m₀ N : ℕ) : 0 < soutPart m₀ N := by
  unfold soutPart
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem soutPart_squarefree (m₀ N : ℕ) : Squarefree (soutPart m₀ N) := by
  unfold soutPart
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr => ?_) fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1)).mpr hpr

theorem soutPart_coprime (m₀ N : ℕ) : (soutPart m₀ N).Coprime m₀ := by
  unfold soutPart
  exact Nat.Coprime.prod_left fun p hp =>
    (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).mpr
      (Finset.mem_filter.mp hp).2.2

theorem soutPart_odd (m₀ N : ℕ) (h2 : 2 ∣ m₀) : Odd (soutPart m₀ N) := by
  exact Nat.coprime_two_right.mp ((soutPart_coprime m₀ N).coprime_dvd_right h2)

theorem soutPart_dvd (m₀ N : ℕ) : soutPart m₀ N ∣ N := by
  unfold soutPart
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd N)

theorem soutPart_le (m₀ N : ℕ) (hN : 0 < N) : soutPart m₀ N ≤ N := by
  exact Nat.le_of_dvd hN (soutPart_dvd m₀ N)

theorem jacobiSym_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ) :
    jacobiSym (∏ i ∈ s, f i) b = ∏ i ∈ s, jacobiSym (f i) b := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, jacobiSym.mul_left, ih]

theorem jacobiSym_prod_right {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    jacobiSym a (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym a (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))
    rw [Finset.prod_cons, Finset.prod_cons,
      jacobiSym.mul_right' _ (hf a (Finset.mem_cons.mpr (Or.inl rfl))) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

theorem recip_sign_congr (p q q' : ℕ) (h4 : q % 4 = q' % 4) :
    ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ (p / 2 * (q' / 2)) := by
  have h : (q / 2) % 2 = (q' / 2) % 2 := by omega
  calc ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ ((p / 2 * (q / 2)) % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1) ^ ((p / 2 * (q' / 2)) % 2) := by rw [Nat.mul_mod, h, ← Nat.mul_mod]
    _ = (-1) ^ (p / 2 * (q' / 2)) := (neg_one_pow_eq_pow_mod_two _).symm

theorem gcd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((p : ℤ).gcd (q : ℤ) = 1) ∧ ((q : ℤ).gcd (p : ℤ) = 1) := by
  have h := (Nat.coprime_primes hp hq).mpr hpq.ne
  refine ⟨?_, ?_⟩
  · rw [Int.gcd_natCast_natCast]
    exact h
  · rw [Int.gcd_natCast_natCast]
    exact h.symm

theorem jacobi_prime_in {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : p ∣ m₀) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q = jacobiSym (p : ℤ) q' := by
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  rcases hp.eq_two_or_odd' with rfl | hpo
  · have h8m : q % 8 = q' % 8 := Nat.ModEq.of_dvd h8 hqq
    have hz : (q : ZMod 8) = (q' : ZMod 8) := (ZMod.natCast_eq_natCast_iff' q q' 8).mpr h8m
    simp only [Nat.cast_ofNat]
    rw [jacobiSym.at_two hqo, jacobiSym.at_two hq'o, hz]
  · have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
    have hpm' : q % p = q' % p := Nat.ModEq.of_dvd hpm hqq
    rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o,
      recip_sign_congr p q q' h4, jacobiSym.mod_left (q : ℤ), jacobiSym.mod_left (q' : ℤ),
      ← Int.natCast_mod, ← Int.natCast_mod, hpm']

theorem jacobi_prime_out {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : ¬ p ∣ m₀) (hq : q.Prime)
    (hq' : q'.Prime) (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q * jacobiSym (q : ℤ) p = jacobiSym (p : ℤ) q' * jacobiSym (q' : ℤ) p := by
  have hp2 : p ≠ 2 := fun h => hpm (h ▸ dvd_trans (by norm_num) h8)
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hpo := hp.odd_of_ne_two hp2
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
  have s1 : jacobiSym (q : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq hpq).2
  have s2 : jacobiSym (q' : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq' hpq').2
  rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o, mul_assoc, mul_assoc,
    ← sq, ← sq, s1, s2, recip_sign_congr p q q' h4]

theorem jacobi_class_prod (m₀ N q : ℕ) (hN : 0 < N) :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      ∏ p ∈ N.primeFactors, (jacobiSym (p : ℤ) q ^ (N.factorization p) *
        (if Odd (N.factorization p) ∧ ¬ p ∣ m₀ then jacobiSym (q : ℤ) p else 1)) := by
  have hNfac : (N : ℤ) = ∏ p ∈ N.primeFactors, (p : ℤ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN.ne']
    rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
    simp only [Nat.cast_pow]
  rw [hNfac, jacobiSym_prod_left]
  unfold soutPart
  rw [jacobiSym_prod_right _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero,
    Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [jacobiSym.pow_left]

theorem jacobi_class_congr {m₀ N q q' : ℕ} (h8 : 8 ∣ m₀) (hN : 0 < N) (hq : q.Prime) (hq' : q'.Prime)
    (hqq : q % m₀ = q' % m₀) (hNq : N < q) (hNq' : N < q') :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      jacobiSym (N : ℤ) q' * jacobiSym (q' : ℤ) (soutPart m₀ N) := by
  rw [jacobi_class_prod m₀ N q hN, jacobi_class_prod m₀ N q' hN]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpN : p ≤ N := Nat.le_of_mem_primeFactors hp
  have hpq : p < q := by omega
  have hpq' : p < q' := by omega
  by_cases hpm : p ∣ m₀
  · rw [if_neg (fun h => h.2 hpm), if_neg (fun h => h.2 hpm), mul_one, mul_one,
      jacobi_prime_in h8 hpP hpm hq hq' hqq hpq hpq']
  · have hsq : ∀ r : ℕ, r.Prime → p < r → jacobiSym (p : ℤ) r ^ 2 = 1 := fun r hr hpr =>
      jacobiSym.sq_one (gcd_prime_lt hpP hr hpr).1
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (N.factorization p)
    · have hnodd : ¬ Odd (N.factorization p) := Nat.not_odd_iff_even.mpr ⟨k, by omega⟩
      rw [if_neg (fun h => hnodd h.1), if_neg (fun h => hnodd h.1), mul_one, mul_one, hk, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow]
    · have hodd : Odd (N.factorization p) := ⟨k, hk⟩
      rw [if_pos ⟨hodd, hpm⟩, if_pos ⟨hodd, hpm⟩, hk, pow_succ, pow_succ, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow, one_mul, one_mul]
      exact jacobi_prime_out h8 hpP hpm hq hq' hqq hpq hpq'

theorem jacobi_class (m₀ a₀ N : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hN : 0 < N) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ q : ℕ, q.Prime → q % m₀ = a₀ % m₀ → N < q →
      jacobiSym (N : ℤ) q = σ * jacobiSym (q : ℤ) (soutPart m₀ N) := by
  have hcop1 : ∀ q : ℕ, q.Prime → N < q → (N : ℤ).gcd q = 1 := by
    intro q hq hNq
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => absurd (Nat.le_of_dvd hN h) (by omega)).symm
  have hcop2 : ∀ q : ℕ, q.Prime → N < q → (q : ℤ).gcd (soutPart m₀ N) = 1 := by
    intro q hq hNq
    have hle := soutPart_le m₀ N hN
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h =>
      absurd (Nat.le_of_dvd (soutPart_pos m₀ N) h) (by omega)
  by_cases hex : ∃ q₀ : ℕ, q₀.Prime ∧ q₀ % m₀ = a₀ % m₀ ∧ N < q₀
  · obtain ⟨q₀, hq₀, hq₀m, hNq₀⟩ := hex
    refine ⟨jacobiSym (N : ℤ) q₀ * jacobiSym (q₀ : ℤ) (soutPart m₀ N), ?_, fun q hq hqm hNq => ?_⟩
    · rcases jacobiSym.eq_one_or_neg_one (hcop1 q₀ hq₀ hNq₀) with h | h <;>
        rcases jacobiSym.eq_one_or_neg_one (hcop2 q₀ hq₀ hNq₀) with h' | h' <;> simp [h, h']
    · have hc := jacobi_class_congr h8 hN hq hq₀ (hqm.trans hq₀m.symm) hNq hNq₀
      have hsq : jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 = 1 := jacobiSym.sq_one (hcop2 q hq hNq)
      rw [← hc]
      calc jacobiSym (N : ℤ) q = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 := by
            rw [hsq, mul_one]
        _ = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) * jacobiSym (q : ℤ) (soutPart m₀ N) := by
            ring
  · exact ⟨1, Or.inl rfl, fun q hq hqm hNq => absurd ⟨q, hq, hqm, hNq⟩ hex⟩

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMainA
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem meansq_expand (PP I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ)
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (J : ℕ → ℕ → ℤ) :
    (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by
  have key : ((∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, ((c n : ℝ) : ℂ) * ((c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
        ((∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ) : ℝ) : ℂ) := by
    have h1 : ∀ q, ((‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
        ∑ n ∈ I, ∑ n' ∈ I, ((c n : ℝ) : ℂ) * ((c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
          (((J n q * J n' q : ℤ) : ℝ) : ℂ) := by
      intro q
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
      simp only [map_mul, Complex.conj_ofReal, map_intCast]
      push_cast
      ring
    rw [Complex.ofReal_sum, Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [Complex.ofReal_sum, Finset.mul_sum]
  calc (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2)
      ≤ ‖((∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real]; exact le_abs_self _
    _ ≤ ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by
        rw [key]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
        rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
          RCLike.norm_conj, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hc n),
          abs_of_nonneg (hc n')]
        have h2 : ‖κ n‖ * ‖κ n'‖ ≤ 1 := by
          have := mul_le_mul (hκ n) (hκ n') (norm_nonneg _) zero_le_one
          simpa using this
        have h3 : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
        have h4 : c n * c n' * (‖κ n‖ * ‖κ n'‖) ≤ c n * c n' := by
          simpa using mul_le_mul_of_nonneg_left h2 h3
        exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqMainB
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem meansq_split (I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (r : ℕ → ℕ → ℕ) (A : ℕ → ℕ → ℝ)
    (P η : ℝ) (hP : 0 ≤ P) (hη : 0 ≤ η) (nstar : ℕ)
    (hA : ∀ n ∈ I, ∀ n' ∈ I, A n n' ≤ P)
    (hA' : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar → A n n' ≤ η * P) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
        (∑ n ∈ I, ∑ n' ∈ I, if r n n' = nstar then c n * c n' else 0) + η * (∑ n ∈ I, c n) ^ 2) * P := by
  have hpt : ∀ n ∈ I, ∀ n' ∈ I, c n * c n' * A n n' ≤
      ((if r n n' = 1 then c n * c n' else 0) + (if r n n' = nstar then c n * c n' else 0) +
        η * (c n * c n')) * P := by
    intro n hn n' hn'
    have hcc : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
    have hAP := mul_le_mul_of_nonneg_left (hA n hn n' hn') hcc
    have hηP : 0 ≤ η * (c n * c n') * P := mul_nonneg (mul_nonneg hη hcc) hP
    have hccP : 0 ≤ c n * c n' * P := mul_nonneg hcc hP
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · have hA2 := mul_le_mul_of_nonneg_left (hA' n hn n' hn' h1 h2) hcc
      linarith
  calc ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n'
      ≤ ∑ n ∈ I, ∑ n' ∈ I, ((if r n n' = 1 then c n * c n' else 0) +
          (if r n n' = nstar then c n * c n' else 0) + η * (c n * c n')) * P :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn'
    _ = _ := by
        rw [sq, Finset.sum_mul_sum]
        simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

open Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem cN_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cN x n := by
  unfold cN
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))

theorem cN_primePow (x : ℝ) (n : ℕ) (h : cN x n ≠ 0) : IsPrimePow n := by
  unfold cN at h
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)

theorem RR_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (m₀ N : ℕ) : 0 ≤ RR c m₀ N :=
  Finset.sum_nonneg fun n _ => hc n

theorem abs_sum_jacobi_le (PP : Finset ℕ) (s : ℕ) :
    |∑ q ∈ PP, (jacobiSym (q : ℤ) s : ℝ)| ≤ (PP.card : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ PP, |(jacobiSym (q : ℤ) s : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy (q : ℤ) s with h | h | h <;> simp [h]
  simpa using Finset.sum_le_sum this

theorem abs_pair_sum_eq (PP : Finset ℕ) (m₀ a₀ n n' : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hn : 0 < n)
    (hn' : 0 < n') (hPP : ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q) :
    |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
  obtain ⟨σ, hσ, h⟩ := jacobi_class m₀ a₀ (n * n') h8 ha (Nat.mul_pos hn hn')
  have h1 : ∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ) =
      (σ : ℝ) * ∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hp, hm, hlt⟩ := hPP q hq
    have := h q hp hm hlt
    rw [← jacobiSym.mul_left, ← Int.cast_mul, ← this]
    push_cast
    rfl
  rw [h1, abs_mul]
  rcases hσ with h | h <;> simp [h]

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
