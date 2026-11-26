module

public import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
public import Formalism.PadicSubsetSums.StableGradedCounts.SquareSetMemExceptionalUnion
public import Formalism.PadicSubsetSums.StableGradedCounts.ProdPowFactorizationLe

@[expose] public section

section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.PropertyWOfEstimates
section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateThird
section -- merged from Formalism.PadicSubsetSums.StableGradedCounts.FourMulSumLeProduct
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

private theorem sum_le_prod_of_two_le (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ l ∈ s, 2 ≤ f l) :
    ∑ l ∈ s, f l ≤ ∏ l ∈ s, f l ∧ 1 ≤ ∏ l ∈ s, f l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun l hl => hf l (Finset.mem_insert_of_mem hl)
    have hfa : 2 ≤ f a := hf a (Finset.mem_insert_self a s)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, by nlinarith⟩
    rcases s.eq_empty_or_nonempty with hs | ⟨b, hb⟩
    · subst hs
      simp
    · have hP2 : 2 ≤ ∏ l ∈ s, f l :=
        (hf b (Finset.mem_insert_of_mem hb)).trans
          (Finset.single_le_prod' (fun l hl => by
            have := hf l (Finset.mem_insert_of_mem hl)
            omega) hb)
      nlinarith

private theorem one_sub_sum_mul_prod_le_prod (q x y z T P : ℕ) (hx : 16 ≤ x) (hy : q ≤ y) (hz : 16 ≤ z) (hqz : q ≤ z)
    (hT : T ≤ P) (hP : 1 ≤ P) : 4 * q * (x + (y + (z + T))) ≤ x * (y * (z * P)) := by
  have h1 : 16 * q ≤ y * z * P := by
    calc 16 * q = q * 16 * 1 := by ring
      _ ≤ y * z * P := Nat.mul_le_mul (Nat.mul_le_mul hy hz) hP
  have h2 : 16 * q ≤ x * z * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * z * P := Nat.mul_le_mul (Nat.mul_le_mul hx hqz) hP
  have h3 : 16 * q ≤ x * y * P := by
    calc 16 * q = 16 * q * 1 := by ring
      _ ≤ x * y * P := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hP
  have h4 : 16 * q * T ≤ x * y * z * P := by
    have h5 : 16 * q ≤ x * y * z := by
      calc 16 * q = 16 * q * 1 := by ring
        _ ≤ x * y * z := Nat.mul_le_mul (Nat.mul_le_mul hx hy) (by omega)
    exact Nat.mul_le_mul h5 hT
  nlinarith [Nat.mul_le_mul_left x h1, Nat.mul_le_mul_left y h2, Nat.mul_le_mul_left z h3]

theorem prime_power_order_share : PrimePowerOrderShare := by
  intro g q₁ d hg hq hd hqd hq2 hd2 hM h16 hqn hdn
  set n := g - 1 with hn
  have hn0 : n ≠ 0 := by omega
  have h2n : 2 ∣ n := (show 2 ∣ 16 by norm_num).trans h16
  have hmem : ∀ l, l.Prime → l ∣ n → l ∈ n.primeFactors := fun l hl hln =>
    Nat.mem_primeFactors.mpr ⟨hl, hln, hn0⟩
  have hge : ∀ l, l.Prime → l ∣ n → l ≤ l ^ padicValNat l n := by
    intro l hl hln
    haveI := Fact.mk hl
    have hv : 1 ≤ padicValNat l n := by
      simpa only [Nat.padicValNat_def] using one_le_multiplicity_of_dvd hn0 hln
    calc l = l ^ 1 := (pow_one l).symm
      _ ≤ l ^ padicValNat l n := Nat.pow_le_pow_right hl.pos hv
  have hf2 : 16 ≤ 2 ^ padicValNat 2 n := by
    haveI := Fact.mk Nat.prime_two
    have hv : 4 ≤ padicValNat 2 n := ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hn0).mp (by norm_num; exact h16)
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ padicValNat 2 n := Nat.pow_le_pow_right (by norm_num) hv
  have h2m := hmem 2 Nat.prime_two h2n
  have hqm : q₁ ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨hq2, hmem q₁ hq hqn⟩
  have hdm : d ∈ (n.primeFactors.erase 2).erase q₁ :=
    Finset.mem_erase.mpr ⟨fun h => hqd h.symm, Finset.mem_erase.mpr ⟨hd2, hmem d hd hdn⟩⟩
  have hsum : ∑ l ∈ n.primeFactors, l ^ padicValNat l n =
      2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
        ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    rw [← Finset.add_sum_erase _ _ h2m, ← Finset.add_sum_erase _ _ hqm, ← Finset.add_sum_erase _ _ hdm]
  have hprod : n = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
        ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by
    have h1 : ∏ l ∈ n.primeFactors, l ^ padicValNat l n = n := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
      rw [Finsupp.prod, Nat.support_factorization]
      refine Finset.prod_congr rfl fun l hl => ?_
      rw [Nat.factorization_def n (Nat.prime_of_mem_primeFactors hl), Nat.padicValNat_def]
    rw [← Finset.mul_prod_erase _ _ h2m, ← Finset.mul_prod_erase _ _ hqm,
      ← Finset.mul_prod_erase _ _ hdm] at h1
    exact h1.symm
  have hR2 : ∀ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, 2 ≤ l ^ padicValNat l n := by
    intro l hl
    have hl' : l ∈ n.primeFactors :=
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
    have hlp := Nat.prime_of_mem_primeFactors hl'
    exact hlp.two_le.trans (hge l hlp (Nat.dvd_of_mem_primeFactors hl'))
  obtain ⟨hTP, hP1⟩ := sum_le_prod_of_two_le _ (fun l => l ^ padicValNat l n) hR2
  have hq16 := hge q₁ hq hqn
  have hd16 := hge d hd hdn
  have hnat : (∑ l ∈ n.primeFactors, l ^ padicValNat l n) * (4 * min q₁ d) ≤ n := by
    rw [hsum]
    rcases le_total q₁ d with hle | hle
    · rw [min_eq_left hle]
      have key := one_sub_sum_mul_prod_le_prod q₁ _ _ _ _ _ hf2 hq16 (le_trans (by omega : 16 ≤ d) hd16)
        (hle.trans hd16) hTP hP1
      calc _ = 4 * q₁ * (2 ^ padicValNat 2 n + (q₁ ^ padicValNat q₁ n + (d ^ padicValNat d n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = n := hprod.symm
    · rw [min_eq_right hle]
      have key := one_sub_sum_mul_prod_le_prod d (2 ^ padicValNat 2 n) (d ^ padicValNat d n) (q₁ ^ padicValNat q₁ n) _ _
        hf2 hd16 (le_trans (by omega : 16 ≤ q₁) hq16) (hle.trans hq16) hTP hP1
      calc _ = 4 * d * (2 ^ padicValNat 2 n + (d ^ padicValNat d n + (q₁ ^ padicValNat q₁ n +
            ∑ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n))) := by ring
        _ ≤ _ := key
        _ = 2 ^ padicValNat 2 n * (q₁ ^ padicValNat q₁ n * (d ^ padicValNat d n *
            ∏ l ∈ ((n.primeFactors.erase 2).erase q₁).erase d, l ^ padicValNat l n)) := by ring
        _ = n := hprod.symm
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hmpos : (0 : ℝ) < 4 * ((min q₁ d : ℕ) : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (lt_min hq.pos hd.pos))
  rw [← Nat.cast_sum, div_le_div_iff₀ hnpos hmpos, one_mul]
  exact_mod_cast hnat

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace E4

theorem geom_part (Q : ℝ) (hQ : 1 < Q) (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ ≤ (1 - (Q ^ M)⁻¹) / (Q - 1) := by
  have hQ1 : Q - 1 ≠ 0 := (sub_pos.mpr hQ).ne'
  have hQ0 : Q ≠ 0 := by positivity
  suffices h : ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ = (1 - (Q ^ M)⁻¹) / (Q - 1) from h.le
  induction M with
  | zero =>
    rw [show Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) by decide]
    simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1), ih, Nat.add_sub_cancel]
    field_simp
    ring

theorem harm_part (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹ ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
  induction M with
  | zero =>
    rw [show Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) by decide]
    simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1)]
    have h1 : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos h1 h2)
    rw [Real.log_div h1.ne' h2.ne'] at hlog
    have hab : ((m + 1 : ℕ) : ℝ) = ((m + 1 + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
    have hdiv : ((m + 1 : ℕ) : ℝ) / ((m + 1 + 1 : ℕ) : ℝ) = 1 - (((m + 1 + 1 : ℕ) : ℝ))⁻¹ := by
      rw [hab, sub_div, div_self h2.ne', one_div]
    linarith

theorem term_le (q δ b : ℕ) (hq : 2 ≤ q) (hδ : 2 ≤ δ)
    (h : δ * b ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    (b : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤ ((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹ := by
  have hq1 : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hB : (0:ℝ) < (q:ℝ) - 1 := by linarith
  have hD : (0:ℝ) < δ := by exact_mod_cast (by omega : 0 < δ)
  have hP1 : (1:ℝ) ≤ (q:ℝ) ^ (δ - 1) := one_le_pow₀ hq1.le
  have hP0 : (q:ℝ) ^ (δ - 1) ≠ 0 := by positivity
  have hpow : (q:ℝ) ^ δ = (q:ℝ) * (q:ℝ) ^ (δ - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hA : (0:ℝ) < (q:ℝ) ^ δ - 1 := by nlinarith
  have hcast : ((q ^ δ - 1 : ℕ) : ℝ) = (q:ℝ) ^ δ - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hcast2 : ((q - 1 : ℕ) : ℝ) = (q:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hR : (δ:ℝ) * b ≤ δ * ((q:ℝ) - 1) + ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) := by
    have h' : ((δ * b : ℕ) : ℝ) ≤ ((δ * (q - 1) + (q ^ δ - 1) / (q - 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr h
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, hcast2] at h'
    have h'' : (((q ^ δ - 1) / (q - 1) : ℕ) : ℝ) ≤ ((q ^ δ - 1 : ℕ) : ℝ) / ((q - 1 : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [hcast, hcast2] at h''
    linarith
  have hstep : (b:ℝ) ≤ ((q:ℝ) - 1) + ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) / δ := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hD]
    nlinarith
  have e1 : ((q:ℝ) ^ (δ - 1))⁻¹ * ((q:ℝ) ^ δ - 1) = (q:ℝ) - ((q:ℝ) ^ (δ - 1))⁻¹ := by
    rw [hpow, mul_comm (q:ℝ) ((q:ℝ) ^ (δ - 1)), mul_sub, inv_mul_cancel_left₀ hP0, mul_one]
  have e2 : ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹ * ((q:ℝ) ^ δ - 1) =
      ((q:ℝ) ^ δ - 1) / ((q:ℝ) - 1) / δ := by
    ring
  have hPinv : ((q:ℝ) ^ (δ - 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP1
  have key : (b:ℝ) ≤ (((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹) * ((q:ℝ) ^ δ - 1) := by
    rw [add_mul, e1, e2]
    linarith
  calc (b:ℝ) * ((q:ℝ) ^ δ - 1)⁻¹
      ≤ ((((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹) * ((q:ℝ) ^ δ - 1)) *
          ((q:ℝ) ^ δ - 1)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.mpr hA.le)
    _ = ((q:ℝ) ^ (δ - 1))⁻¹ + ((δ:ℝ))⁻¹ * ((q:ℝ) - 1)⁻¹ := mul_inv_cancel_right₀ hA.ne' _

theorem arith (q N : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (b : ℕ → ℕ) (m : ℝ)
    (h1 : (b 1 : ℝ) * ((q : ℝ) - 1)⁻¹ ≤ m)
    (h2 : ∀ δ, 2 ≤ δ → δ * b δ ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    ∑ δ ∈ Finset.Icc 1 N, (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      m + (1 + Real.log N) / ((q : ℝ) - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hQ : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hQ1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ M + 1)]
  have hI : Finset.Ioc 1 (M + 1) = Finset.Icc 2 (M + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hI, pow_one]
  have h3 : ∑ δ ∈ Finset.Icc 2 (M + 1), (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      ∑ δ ∈ Finset.Icc 2 (M + 1), (((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹) :=
    Finset.sum_le_sum fun δ hδ =>
      term_le q δ (b δ) hq (Finset.mem_Icc.1 hδ).1 (h2 δ (Finset.mem_Icc.1 hδ).1)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h3
  have h4 := geom_part (q : ℝ) hQ M
  have h5 := harm_part M
  have h6 : (1 - ((q : ℝ) ^ M)⁻¹) / ((q : ℝ) - 1) ≤ 1 / ((q : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ hQ1.le
    have : 0 ≤ ((q : ℝ) ^ M)⁻¹ := by positivity
    linarith
  have h7 : (∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹) * ((q : ℝ) - 1)⁻¹ ≤
      Real.log ((M + 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right h5 (inv_nonneg.2 hQ1.le)
  have h8 : (1 + Real.log ((M + 1 : ℕ) : ℝ)) / ((q : ℝ) - 1) =
      1 / ((q : ℝ) - 1) + Real.log ((M + 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ := by
    rw [add_div, div_eq_mul_inv (Real.log _)]
  rw [h8]
  linarith

theorem exists_prime_pow_eq {M : Type} [Monoid M] (n : ℕ) (hn : 2 ≤ n) (u : M) (hu : u ^ n = 1)
    (l a : ℕ) (hl : l.Prime) (hla : u ^ (l ^ a) = 1) :
    ∃ l' ∈ n.primeFactors, u ^ (l' ^ padicValNat l' n) = 1 := by
  have hd1 : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one hu
  have hd2 : orderOf u ∣ l ^ a := orderOf_dvd_of_pow_eq_one hla
  obtain ⟨k, _, hk'⟩ := (Nat.dvd_prime_pow hl).mp hd2
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · rw [h0, pow_zero, orderOf_eq_one_iff] at hk'
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩, by rw [hk', one_pow]⟩
  · have hln : l ^ k ∣ n := by
      rw [← hk']
      exact hd1
    have hl_n : l ∣ n := (dvd_pow_self l hpos.ne').trans hln
    refine ⟨l, Nat.mem_primeFactors.mpr ⟨hl, hl_n, by omega⟩, ?_⟩
    rw [← orderOf_dvd_iff_pow_eq_one, hk']
    apply pow_dvd_pow
    haveI := Fact.mk hl
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (by omega)).mp hln

variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]

theorem key (P : K[X]) (hP : Irreducible P) (hm : P.Monic) (x : L) (hx : aeval x P = 0)
    (hx0 : x ≠ 0) (c₀ : Kˣ) (l : ℕ) (hl : l.Prime)
    (h : primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))) (hq : 3 ≤ Fintype.card K) :
    ∃ l' ∈ (Fintype.card K ^ P.natDegree - 1).primeFactors,
      P ∣ X ^ (l' ^ padicValNat l' (Fintype.card K ^ P.natDegree - 1)) -
        C ((c₀ : K) ^ (l' ^ padicValNat l' (Fintype.card K ^ P.natDegree - 1))) := by
  classical
  set q := Fintype.card K with hqdef
  set d := P.natDegree with hd
  set n := q ^ d - 1 with hn
  have hint : IsIntegral K x := ⟨P, hm, by rwa [Polynomial.aeval_def] at hx⟩
  have hmin : P = minpoly K x := minpoly.eq_of_irreducible_of_monic hP hx hm
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hP)
  have hqd : 3 ≤ q ^ d := le_trans hq (Nat.le_self_pow (by omega) q)
  have hn2 : 2 ≤ n := by omega
  have hxn : x ^ n = 1 := by
    haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
    letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _
    have hcard : Fintype.card (IntermediateField.adjoin K {x}) = q ^ d := by
      rw [Module.card_eq_pow_finrank (K := K), IntermediateField.adjoin.finrank hint, ← hmin]
    have hxE : (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x}) ≠ 0 := by
      intro h0
      exact hx0 (congrArg Subtype.val h0)
    have h1 := FiniteField.pow_card_sub_one_eq_one _ hxE
    rw [hcard] at h1
    have h2 := congrArg (fun e : IntermediateField.adjoin K {x} => (e : L)) h1
    simpa using h2
  have hc0 : (c₀ : K) ≠ 0 := c₀.ne_zero
  have hcK : (c₀ : K) ^ n = 1 := by
    have h1 := FiniteField.pow_card_pow d (c₀ : K)
    have h2 : (c₀ : K) ^ n * (c₀ : K) = (c₀ : K) := by
      rw [← pow_succ, hn, Nat.sub_add_cancel (by omega : 1 ≤ q ^ d)]
      exact h1
    exact mul_right_cancel₀ hc0 (h2.trans (one_mul _).symm)
  have hcL : algebraMap K L (c₀ : K) ≠ 0 := (_root_.map_ne_zero _).mpr hc0
  have hcn : algebraMap K L (c₀ : K) ^ n = 1 := by rw [← map_pow, hcK, map_one]
  have aux : ∀ z : L, z ≠ 0 → z ^ n = 1 →
      ∃ E : ℕ, (z / Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart l z) ^ (l ^ E) = 1 := by
    intro z hz0 hzn
    have ho : 0 < orderOf z :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, by omega, hzn⟩)
    have key2 : ∀ a b : ℕ, a ≡ b [MOD orderOf z] → z ^ a = z ^ b := fun a b hab => by
      rw [← pow_mod_orderOf z a, ← pow_mod_orderOf z b]
      exact congrArg (fun k => z ^ k) hab
    refine ⟨(orderOf z).factorization l, ?_⟩
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart.eq_1]
    have hcop : (l ^ (orderOf z).factorization l).Coprime
        (orderOf z / l ^ (orderOf z).factorization l) :=
      (Nat.coprime_ordCompl hl ho.ne').pow_left _
    have hmod := (Nat.ModEq.pow_totient hcop).mul_right' (l ^ (orderOf z).factorization l)
    rw [one_mul, Nat.div_mul_cancel (Nat.ordProj_dvd (orderOf z) l)] at hmod
    rw [div_pow, ← pow_mul z, key2 _ _ hmod, div_self (pow_ne_zero _ hz0)]
  obtain ⟨E1, hE1⟩ := aux x hx0 hxn
  obtain ⟨E2, hE2⟩ := aux _ hcL hcn
  rw [h] at hE1
  have hp0 : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart l (algebraMap K L (c₀ : K)) ≠ 0 := by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart.eq_1]
    exact pow_ne_zero _ hcL
  have hyE : (x / algebraMap K L (c₀ : K)) ^ (l ^ (E1 + E2)) = 1 := by
    rw [← div_div_div_cancel_right₀ hp0 x (algebraMap K L (c₀ : K)), div_pow, pow_add,
      pow_mul (x / _), hE1, one_pow, mul_comm (l ^ E1), pow_mul, hE2, one_pow, div_one]
  have hyn : (x / algebraMap K L (c₀ : K)) ^ n = 1 := by
    rw [div_pow, hxn, hcn, div_one]
  obtain ⟨l', hl', hyl'⟩ := exists_prime_pow_eq n hn2 (x / algebraMap K L (c₀ : K)) hyn l (E1 + E2) hl hyE
  refine ⟨l', hl', ?_⟩
  have hdiv := minpoly.dvd K x (p := (X ^ (l' ^ padicValNat l' n) -
    C ((c₀ : K) ^ (l' ^ padicValNat l' n)) : K[X])) ?_
  · rwa [← hmin] at hdiv
  · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_pow, sub_eq_zero]
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hcL)] at hyl'
    exact hyl'


open Classical in
noncomputable def Bset (K : Type) [Field K] [Fintype K] (δ : ℕ) (c₀ : Kˣ) : Finset (Fin δ → K) := by
  classical
  exact Finset.univ.filter (fun c => Irreducible (monicOf c) ∧
    ∃ l' ∈ (Fintype.card K ^ δ - 1).primeFactors,
      monicOf c ∣ X ^ (l' ^ padicValNat l' (Fintype.card K ^ δ - 1)) -
        C ((c₀ : K) ^ (l' ^ padicValNat l' (Fintype.card K ^ δ - 1))))

theorem count (δ : ℕ) (c₀ : Kˣ) :
    δ * (Bset K δ c₀).card ≤
      ∑ l ∈ (Fintype.card K ^ δ - 1).primeFactors, l ^ padicValNat l (Fintype.card K ^ δ - 1) := by
  classical
  have hmon : ∀ c : Fin δ → K, (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).Monic := fun c => by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hdegc : ∀ c : Fin δ → K, (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).natDegree = δ := fun c => by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1, Polynomial.natDegree_add_eq_left_of_degree_lt,
      Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt _
  have hcoeff : ∀ (c : Fin δ → K) (j : Fin δ), (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).coeff j = c j := by
    intro c j
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.finsetSum_coeff]
    simp [Polynomial.coeff_C_mul_X_pow, Fin.val_inj, j.isLt.ne]
  have hinj : Function.Injective (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf : (Fin δ → K) → K[X]) :=
    fun c c' h => funext fun j => by rw [← hcoeff c j, ← hcoeff c' j, h]
  have hgen : ∀ (k : ℕ) (a : K), 0 < k → δ * (Finset.univ.filter (fun c : Fin δ → K =>
      Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a)).card ≤ k := by
    intro k a hk
    have hF0 : (X ^ k - C a : K[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hk a
    have hprod : ∏ c ∈ Finset.univ.filter (fun c : Fin δ → K =>
        Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a),
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a := by
      apply Finset.prod_dvd_of_coprime
      · intro c hc c' hc' hne
        have hi := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2.1
        have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2.1
        show IsCoprime (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c')
        rw [hi.coprime_iff_not_dvd]
        intro hdvd
        apply hne
        apply hinj
        exact Polynomial.eq_of_monic_of_associated (hmon c) (hmon c') (hi.associated_of_dvd hi' hdvd)
      · intro c hc
        exact (Finset.mem_filter.mp hc).2.2
    have hdeg := Polynomial.natDegree_le_of_dvd hprod hF0
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => hmon c),
      Polynomial.natDegree_X_pow_sub_C _] at hdeg
    simp only [hdegc, Finset.sum_const, smul_eq_mul] at hdeg
    rw [mul_comm]
    exact hdeg
  set m := Fintype.card K ^ δ - 1 with hmdef
  have hsub : Bset K δ c₀ ⊆ m.primeFactors.biUnion (fun l' => Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))) := by
    intro c hc
    simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hirr, l', hl', hdvd⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨l', hl', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hirr, hdvd⟩⟩
  calc δ * (Bset K δ c₀).card
      ≤ δ * (m.primeFactors.biUnion (fun l' => Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m))))).card :=
        Nat.mul_le_mul le_rfl (Finset.card_le_card hsub)
    _ ≤ δ * ∑ l' ∈ m.primeFactors, (Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))).card :=
        Nat.mul_le_mul le_rfl Finset.card_biUnion_le
    _ = ∑ l' ∈ m.primeFactors, δ * (Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))).card := by
        rw [Finset.mul_sum]
    _ ≤ ∑ l' ∈ m.primeFactors, l' ^ padicValNat l' m := by
        apply Finset.sum_le_sum
        intro l' hl'
        exact hgen _ _ (pow_pos (Nat.prime_of_mem_primeFactors hl').pos _)

theorem sqWeight_irred (P : K[X]) (hP : Irreducible P) (hm : P.Monic) :
    sqWeight P = ((Fintype.card K : ℝ) ^ P.natDegree - 1)⁻¹ := by
  classical
  rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight.eq_1, UniqueFactorizationMonoid.normalizedFactors_irreducible hP,
    hm.normalize_eq_self]
  simp

theorem weight_le (N : ℕ) (c₀ : Kˣ) (hq : 3 ≤ Fintype.card K) :
    wtOf (fun c : Fin N → K => sqWeight (monicOf c)) {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
        l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} ≤
      ∑ δ ∈ Finset.Icc 1 N, ((Bset K δ c₀).card : ℝ) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
  classical
  set μ : (Fin N → K) → ℝ := fun c => sqWeight (monicOf c) with hμ
  have hμ0 : ∀ c, 0 ≤ μ c := fun c => sqWeight_nonneg _
  have hsub : {c : Fin N → K | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
        l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} ⊆
      ⋃ δ ∈ Finset.Icc 1 N, ⋃ c' ∈ Bset K δ c₀,
        {c : Fin N → K | c ∈ sqSet K N ∧ monicOf c' ∣ monicOf c} := by
    rintro c ⟨hc, l, hl, -, x, hx, hpt⟩
    have hfx : aeval x (monicOf c) = 0 := (mem_rootSet.1 hx).2
    have hint : IsIntegral K x := ⟨monicOf c, monicOf_monic c, hfx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply ((mem_sqSet c).1 hc).2
      have : aeval (0 : L) (monicOf c) = algebraMap K L ((monicOf c).coeff 0) := by
        rw [aeval_def, eval₂_at_zero]
      rw [this, map_eq_zero] at hfx
      exact hfx
    set P := minpoly K x with hPdef
    have hPi : Irreducible P := minpoly.irreducible hint
    have hPm : P.Monic := minpoly.monic hint
    have hPd : P ∣ monicOf c := minpoly.dvd K x hfx
    have hdeg : P.natDegree ≤ N := by
      have := natDegree_le_of_dvd hPd (monicOf_monic c).ne_zero
      rwa [monicOf_natDegree] at this
    obtain ⟨l', hl', hdv⟩ := key P hPi hPm x (minpoly.aeval K x) hx0 c₀ l hl hpt hq
    have hco : monicOf (fun i : Fin P.natDegree => P.coeff i) = P := monicOf_coeffs hPm rfl
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨P.natDegree, Finset.mem_Icc.2 ⟨hPi.natDegree_pos, hdeg⟩,
      fun i : Fin P.natDegree => P.coeff i, ?_, hc, by rw [hco]; exact hPd⟩
    unfold Bset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hco]
    exact ⟨hPi, l', hl', hdv⟩
  refine (wtOf_mono μ hμ0 hsub).trans ((wtOf_biUnion_le μ hμ0 _ _).trans ?_)
  refine Finset.sum_le_sum fun δ hδ => ?_
  refine (wtOf_biUnion_le μ hμ0 _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun c' hc' => ?_
  have hi : Irreducible (monicOf c') := (Finset.mem_filter.mp hc').2.1
  rw [wtOf_eq_filter']
  have := divisor_square_weight_sum_le square_mass_le_one K N (monicOf c') (monicOf_monic c')
    (by rw [monicOf_natDegree]; exact (Finset.mem_Icc.1 hδ).2)
    ((sqSet K N).filter (fun c => monicOf c' ∣ monicOf c))
    (fun c hc => by simpa only [Finset.mem_filter] using hc)
  rw [sqWeight_irred _ hi (monicOf_monic c'), monicOf_natDegree] at this
  exact this

end E4

theorem local_estimate_third : LocalEstimateIII := by
  classical
  intro K L _ _ _ _ _ N q₁ d c₀ hN hq1 hd hne h12 hd2 hmax h16 hq1d hdd
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq17 : 17 ≤ Fintype.card K := by
    have := Nat.le_of_dvd (by omega) h16
    omega
  have hw := E4.weight_le (L := L) N c₀ (by omega)
  rw [wtOf_eq_filter'] at hw
  have c1 : ((Fintype.card K - 1 : ℕ) : ℝ) = (Fintype.card K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1 : (((E4.Bset K 1 c₀).card : ℕ) : ℝ) * ((Fintype.card K : ℝ) - 1)⁻¹ ≤
      1 / (4 * (min q₁ d : ℕ)) := by
    have hc := E4.count 1 c₀
    rw [one_mul, pow_one] at hc
    have hs := prime_power_order_share (Fintype.card K) q₁ d hq2 hq1 hd hne h12 hd2 hmax h16
      hq1d hdd
    refine le_trans ?_ hs
    rw [c1, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hc
    · apply inv_nonneg.2
      have : (17 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast hq17
      linarith
  have h2 : ∀ δ, 2 ≤ δ → δ * (E4.Bset K δ c₀).card ≤
      δ * (Fintype.card K - 1) + (Fintype.card K ^ δ - 1) / (Fintype.card K - 1) := fun δ hδ =>
    (E4.count δ c₀).trans (prime_power_order_count (Fintype.card K) δ hq2
      (dvd_trans (by norm_num) h16) (by omega))
  have ha := E4.arith (Fintype.card K) N hN hq2 (fun δ => (E4.Bset K δ c₀).card) _ h1 h2
  exact hw.trans ha

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem property_W_of_estimates : PropW := propW_of_localEstimates local_estimate_second local_estimate_third

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

open Finset Polynomial

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.ConcNWeight

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN

local instance factG {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩

local instance neZeroG {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩

def TieVecW {D : D7} (A : AllRows D) : Prop :=
  ∃ ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ, (∀ k, ψ₀ k ≠ 1) ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k), A.eVec k v = eUk D k (ψ₀ k) ∨ A.eVec k v = eJk D k (ψ₀ k)

def RangeW (D : D7) : Prop := 100 ≤ D.R.r ∧ ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k

section Weights

variable {D : D7}

theorem wtOf_eq_zero_of_not_label {k : Fin 2} (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    {f : (ZMod (D.host.g k))[X]} (hf : ¬ IsLabel D k f) : wtOf D k a f = 0 := by
  unfold wtOf
  rw [D.ntypes.eSer_zero k f hf, mul_zero]
  simp

theorem sum_eSer (k : Fin 2) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c) = 1 := by
  classical
  obtain ⟨S, hS, hsum⟩ := D.ntypes.eSer_sum k
  have hcoeff : ∀ (c : Fin D.R.r → ZMod (D.host.g k)) (i : Fin D.R.r),
      (Formalism.CyclotomicNorms.monicOf c).coeff (i : ℕ) = c i := by
    intro c i
    unfold Formalism.CyclotomicNorms.monicOf
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg i.isLt.ne, zero_add,
      Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      exact fun h => hj (Fin.ext h).symm
    · simp
  have hinj : Function.Injective (fun c : Fin D.R.r → ZMod (D.host.g k) => Formalism.CyclotomicNorms.monicOf c) := by
    intro c c' h
    funext i
    have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (i : ℕ)) h
    simpa [hcoeff] using this
  have hsurj : ∀ f ∈ S, f = Formalism.CyclotomicNorms.monicOf (fun i : Fin D.R.r => f.coeff (i : ℕ)) := by
    intro f hf
    obtain ⟨hm, hdeg, -⟩ := (hS f).1 hf
    conv_lhs => rw [hm.as_sum, hdeg]
    unfold Formalism.CyclotomicNorms.monicOf
    congr 1
    exact (Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (f.coeff i) * Polynomial.X ^ i) _).symm
  have himg : ∑ f ∈ Finset.univ.image (fun c : Fin D.R.r → ZMod (D.host.g k) => Formalism.CyclotomicNorms.monicOf c),
      D.ntypes.eSer k f = ∑ c, D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c) :=
    Finset.sum_image (fun a _ b _ h => hinj h)
  rw [← himg, ← hsum]
  symm
  apply Finset.sum_subset
  · intro f hf
    rw [Finset.mem_image]
    exact ⟨_, Finset.mem_univ _, (hsurj f hf).symm⟩
  · intro f _ hf
    exact D.ntypes.eSer_zero k f (fun h => hf ((hS f).2 h))

theorem sum_wtOf (k : Fin 2) (a : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (ha : (a.coeff 1).re ≠ 0) :
    ∑ c : Fin D.R.r → ZMod (D.host.g k), wtOf D k a (Formalism.CyclotomicNorms.monicOf c) = 1 := by
  have h := sum_eSer (D := D) k
  let L : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) →+ ℝ :=
    AddMonoidHom.mk' (fun x => (x.coeff 1).re) (fun x y => by simp)
  have hL : ∀ x, L x = (x.coeff 1).re := fun x => rfl
  have hs := map_sum L (fun c : Fin D.R.r → ZMod (D.host.g k) => a * D.ntypes.eSer k (Formalism.CyclotomicNorms.monicOf c)) Finset.univ
  simp only [hL] at hs
  rw [← Finset.mul_sum, h, mul_one] at hs
  unfold wtOf
  rw [← Finset.sum_div, ← hs, div_self ha]

end Weights

section Value

theorem entN_one_ne {A : Type} [Zero A] [One A] {N : ℕ} {a b : ℕ} (h : a ≠ b) :
    entN (1 : Matrix (Fin N) (Fin N) A) a b = 0 := by
  unfold entN
  split_ifs with h'
  · exact Matrix.one_apply_ne (fun he => h (congrArg Fin.val he))
  · rfl

theorem eDat_coeff_one_re_pos (g N : ℕ) [NeZero g] (P : Matrix (Fin N) (Fin N) (ZMod g) → Prop)
    (φ : Matrix (Fin N) (Fin N) (ZMod g) → ZMod g) (ψ₀ : AddChar (ZMod g) ℂ) (hP : P 1) (hφ : φ 1 = 0) :
    0 < ((eDat g N P φ ψ₀).coeff 1).re := by
  classical
  have h1 : (ψ₀ (φ 1))⁻¹ = 1 := by rw [hφ, AddChar.map_zero_eq_one, inv_one]
  have hc : 0 < (Finset.univ.filter
      (fun u : GL (Fin N) (ZMod g) => P (u : Matrix (Fin N) (Fin N) (ZMod g)))).card :=
    Finset.card_pos.mpr ⟨1, by simp [hP]⟩
  unfold eDat
  simp [h1, hP]
  rw [Finset.sum_eq_single (1 : GL (Fin N) (ZMod g))]
  · simp [h1, hφ]
    first
      | exact hc
      | positivity
      | exact inv_pos.mpr (by exact_mod_cast hc)
      | exact Finset.card_pos.mp hc
      | exact ⟨1, by simp [hP]⟩
      | exact (rfl : (0:ℕ) = 0)
  · intro b _ hb
    simp [Finsupp.single_apply, hb]
  · intro h
    exact absurd (by simp [hP]) h

theorem eU_coeff_one_re_pos (g N : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) :
    0 < ((eU g N ψ₀).coeff 1).re := by
  unfold eU
  refine eDat_coeff_one_re_pos g N _ _ ψ₀ ?_ ?_
  · intro a b
    exact ⟨fun hab => Matrix.one_apply_ne hab.ne', fun hab => by subst hab; exact Matrix.one_apply_eq a⟩
  · beta_reduce
    exact Finset.sum_eq_zero fun i _ => entN_one_ne (by omega)

theorem eJ_coeff_one_re_pos (g N kk s : ℕ) [NeZero g] (ψ₀ : AddChar (ZMod g) ℂ) :
    0 < ((eJ g N kk s ψ₀).coeff 1).re := by
  unfold eJ
  have e : ∀ a b : ℕ, a ≠ b → entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) a b = 0 :=
    fun a b h => entN_one_ne h
  refine eDat_coeff_one_re_pos g N _ _ ψ₀ ?_ ?_
  · refine ⟨?_, fun a _ h2 => e _ _ (by omega)⟩
    intro a b
    exact ⟨fun hab => Matrix.one_apply_ne hab.ne', fun hab => by subst hab; exact Matrix.one_apply_eq a⟩
  · unfold phiJ
    have h1 : ∑ i ∈ Finset.range (s - 1), entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) i (i + 1) = 0 :=
      Finset.sum_eq_zero fun i _ => e _ _ (by omega)
    have h2 : ∑ i ∈ Finset.range (s - 1),
        entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) (s + kk + 1 + i) (s + kk + 2 + i) = 0 :=
      Finset.sum_eq_zero fun i _ => e _ _ (by omega)
    have h3 : ∑ a ∈ Finset.range (kk - 1), entN (1 : Matrix (Fin N) (Fin N) (ZMod g)) (s + a) (s + a + 1) = 0 :=
      Finset.sum_eq_zero fun a _ => e _ _ (by omega)
    rw [h1, h2, h3]
    split_ifs with hs
    · rw [e (s - 1) (s + kk) (by omega), e (s + kk) (s + kk + 1) (by omega)]
      simp
    · simp

theorem eUk_coeff_one_re_pos {D : D7} (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    0 < ((eUk D k ψ₀).coeff 1).re := by
  exact eU_coeff_one_re_pos (D.host.g k) D.R.r ψ₀

theorem eJk_coeff_one_re_pos {D : D7} (k : Fin 2) (ψ₀ : AddChar (ZMod (D.host.g k)) ℂ) :
    0 < ((eJk D k ψ₀).coeff 1).re := by
  exact eJ_coeff_one_re_pos (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ₀

end Value

section PropWRec

variable {D : D7}

theorem host_facts (hA : TieAdmG D) (k : Fin 2) :
    D.host.q.Prime ∧ D.host.d.Prime ∧ D.host.q ≠ D.host.d ∧ D.host.q ≠ 2 ∧ D.host.d ≠ 2 ∧
      16 ≤ max D.host.q D.host.d ∧ 16 ∣ D.host.g k - 1 ∧ D.host.q ∣ D.host.g k - 1 ∧
      D.host.d ∣ D.host.g k - 1 := by
  have hadm := hA k
  unfold Formalism.BasicNotions.NTypes.admissible at hadm
  have hmod : D.host.g k % (D.host.QS * D.host.q * D.host.d) = 1 := hadm.2.2.2
  have hM : D.host.QS * D.host.q * D.host.d ∣ D.host.g k - 1 := by
    have h := Nat.dvd_sub_mod (n := D.host.QS * D.host.q * D.host.d) (D.host.g k)
    rwa [hmod] at h
  have h16 : 16 ∣ D.host.QS := by
    have h := (Nat.pow_dvd_pow 2 (show 4 ≤ D.R.toFrame.e + 2 by have := D.host.two_le_e; omega)).trans
      D.host.tower_dvd
    simpa using h
  have h2 : 2 ∣ D.host.QS := (show 2 ∣ 16 by norm_num).trans h16
  have hc : Nat.Coprime 2 (D.host.q * D.host.d) := Nat.Coprime.coprime_dvd_left h2 D.host.QS_coprime
  have hq2 : D.host.q ≠ 2 := by
    intro h
    have := Nat.Coprime.coprime_dvd_right (dvd_mul_right D.host.q D.host.d) hc
    rw [h] at this
    exact absurd this (by decide)
  have hd2 : D.host.d ≠ 2 := by
    intro h
    have := Nat.Coprime.coprime_dvd_right (dvd_mul_left D.host.d D.host.q) hc
    rw [h] at this
    exact absurd this (by decide)
  have hbig : 16 ≤ max D.host.q D.host.d := by
    have hq := D.host.qd_big.1
    have hr : 6 ≤ D.R.r := by
      have e1 : D.R.r = D.R.k + D.R.m - 1 := rfl
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      omega
    have ht : 11 ≤ D.R.t := by
      have := D.R.two_le_m
      have := D.R.m_add_three_le_k
      have := D.R.rank_add_five_le
      omega
    have hTR : 11 * 6 ≤ D.R.t * D.R.r := Nat.mul_le_mul ht hr
    have e2 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := Nat.mul_assoc _ _ _
    rw [e2] at hq
    exact le_max_of_le_left (by omega)
  refine ⟨?_, ?_, ?_, hq2, hd2, hbig, (h16.trans (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)).trans hM,
    (dvd_mul_of_dvd_left (dvd_mul_left _ _) _).trans hM, (dvd_mul_left _ _).trans hM⟩
  · obtain ⟨x1, -, -⟩ := D.host.hyp
    exact x1
  · obtain ⟨-, x2, -⟩ := D.host.hyp
    exact x2
  · obtain ⟨-, -, x3, x4, -⟩ := D.host.hyp
    intro h
    rw [h] at x3
    omega

theorem rangeW_of_sizes {x ε Cs : ℝ} (h : SizesRec D x ε Cs) (hx : 3 / 2 ≤ x ^ ε) : RangeW D := by
  unfold Formalism.L2.GlobalTheoryTheory.ConcN.SizesRec Formalism.L2.GlobalTheoryTheory.ConcN.SizesAt at h
  unfold RangeW
  refine ⟨(h 0).2.2.2.2.1, fun k => ?_⟩
  have hg := (h k).1
  have h2 : (2:ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ)
    linarith
  have h12 : Real.exp 1 ^ 12 ≤ Real.exp (8 * x ^ ε) := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have h3 : (2:ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := by gcongr
  have h4 : ((2 ^ 12 : ℕ) : ℝ) ≤ (D.host.g k : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h4

theorem locShare_le_Wg (A : AllRows D) (hL : admLq D) (hA : TieAdmG D) (hR : RangeW D) (hV : TieVecW A)
    (k : Fin 2) (S : Finset (Tup D k)) (hS : ∀ t ∈ S, ¬ goodAt D k t) :
    locShare D A.eVec k S ≤ Wg D.R.f D.R.m D.R.r (D.host.g k) D.host.q D.host.d := by
  classical
  obtain ⟨ψ₀, hψ, hv⟩ := hV
  obtain ⟨hnn, hsq, hcmp, -⟩ := hL k (ψ₀ k) (hψ k)
  obtain ⟨hq, hd, hqd, hq2, hd2, h16m, h16, hqg, hdg⟩ := host_facts hA k
  let wJ : D.nd.PlG k → (Fin D.R.r → ZMod (D.host.g k)) → ℝ :=
    fun v c => wtOf D k (A.eVec k v) (Formalism.CyclotomicNorms.monicOf c)
  let P : (Fin D.R.r → ZMod (D.host.g k)) → ℝ := fun c => wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c)
  have hJnn : ∀ v f, 0 ≤ wtOf D k (A.eVec k v) f := by
    intro v f
    rcases hv k v with h | h <;> rw [h]
    · exact (hnn f).1
    · exact (hnn f).2
  have hPnn : ∀ c, 0 ≤ P c := fun c => (hnn _).1
  have hJsum : ∀ v, ∑ c, wJ v c = 1 := by
    intro v
    rcases hv k v with h | h
    · simp only [wJ]; rw [h]; exact sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
    · simp only [wJ]; rw [h]; exact sum_wtOf k _ (eJk_coeff_one_re_pos k _).ne'
  have hPsum : ∑ c, P c = 1 := sum_wtOf k _ (eUk_coeff_one_re_pos k _).ne'
  have hg1 : (1 : ℝ) ≤ (D.host.g k : ℝ) := by exact_mod_cast (D.host.g_prime k).one_lt.le
  have hcmpv : ∀ v c, (1 - 1 / (D.host.g k : ℝ)) * P c ≤ wJ v c := by
    intro v c
    have hle : 1 - 1 / (D.host.g k : ℝ) ≤ 1 := sub_le_self _ (by positivity)
    rcases hv k v with h | h
    · have : wJ v c = P c := by simp only [wJ, P]; rw [h]
      rw [this]
      exact mul_le_of_le_one_left (hPnn c) hle
    · have : wJ v c = wtOf D k (eJk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) := by simp only [wJ]; rw [h]
      rw [this]
      by_cases hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c)
      · exact hcmp _ hlab
      · simp only [P]
        rw [wtOf_eq_zero_of_not_label _ hlab, wtOf_eq_zero_of_not_label _ hlab, mul_zero]

  have hred : locShare D A.eVec k S ≤
      ∑ x ∈ (Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter
        (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r
          (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (x v)) (D.nd.chiT k)), ∏ v, wJ v (x v) := by
    unfold locShare
    let cv : Tup D k → (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k)) := fun t v i => (t v).coeff i
    have hS' : ∑ t ∈ S, ∏ v, wtOf D k (A.eVec k v) (t v) =
        ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, wtOf D k (A.eVec k v) (t v) := by
      rw [Finset.sum_filter_of_ne]
      intro t _ hne v
      by_contra hv'
      exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (wtOf_eq_zero_of_not_label _ hv'))
    have hcv : ∀ t : Tup D k, (∀ v, IsLabel D k (t v)) → ∀ v, Formalism.CyclotomicNorms.monicOf (cv t v) = t v :=
      fun t ht v => Formalism.CyclotomicNorms.Sqf.monicOf_coeffs (t v) (ht v).1 (ht v).2.1
    rw [hS']
    calc ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, wtOf D k (A.eVec k v) (t v)
        = ∑ t ∈ S.filter (fun t => ∀ v, IsLabel D k (t v)), ∏ v, wJ v (cv t v) := by
          refine Finset.sum_congr rfl fun t ht => ?_
          have ht := (Finset.mem_filter.1 ht).2
          refine Finset.prod_congr rfl fun v _ => ?_
          simp only [wJ]
          rw [hcv t ht v]
      _ = ∑ x ∈ (S.filter (fun t => ∀ v, IsLabel D k (t v))).image cv, ∏ v, wJ v (x v) := by
          rw [Finset.sum_image]
          intro t ht t' ht' h
          have ht := (Finset.mem_filter.1 ht).2
          have ht' := (Finset.mem_filter.1 ht').2
          funext v
          rw [← hcv t ht v, ← hcv t' ht' v]
          exact congrArg Formalism.CyclotomicNorms.monicOf (congrFun h v)
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            fun x _ _ => Finset.prod_nonneg fun v _ => hJnn v _
          intro x hx
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨htS, htl⟩ := Finset.mem_filter.1 ht
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hgood => hS t htS ?_⟩
          have hfun : (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (cv t v)) = t := funext fun v => hcv t htl v
          rw [hfun] at hgood
          exact Formalism.MainNotions.N.PlaceLabelTeichmuller.good_of D.R.r t (D.nd.chiT k) hgood

  have hT := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.comparison_transfer_holds (D.nd.PlG k) (fun _ => Fin D.R.r → ZMod (D.host.g k))
    (fun _ => P) wJ (D.host.g k : ℝ)
    ((Finset.univ : Finset (D.nd.PlG k → Fin D.R.r → ZMod (D.host.g k))).filter
        (fun x => ¬ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.GoodAt (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) D.R.r
          (fun v => Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf (x v)) (D.nd.chiT k)))
    hg1 (fun _ => hPnn) (fun _ => hPsum) hJsum hcmpv
  have hW := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.property_W_of_estimates (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (D.nd.PlG k)
    (Fin D.R.m) D.R.r D.host.q D.host.d (D.nd.chiT k) P hR.1 (by rw [ZMod.card]; exact hR.2 k) hq hd hqd hq2
    hd2 h16m (by rw [ZMod.card]; exact h16) (by rw [ZMod.card]; exact hqg) (by rw [ZMod.card]; exact hdg)
    hPnn hPsum (by
      intro c hc
      have hc' : c ∈ (Finset.univ : Finset (Fin D.R.r → ZMod (D.host.g k))).filter
          (fun c => Squarefree (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).coeff 0 ≠ 0) := by
        unfold Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqSet at hc
        convert hc
      obtain ⟨-, hsqf, h0⟩ := Finset.mem_filter.1 hc'
      have hlab : IsLabel D k (Formalism.CyclotomicNorms.monicOf c) :=
        ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf c, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf c, h0⟩
      show wtOf D k (eUk D k (ψ₀ k)) (Formalism.CyclotomicNorms.monicOf c) = _
      rw [hsq _ hlab hsqf, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.sqWeight, ZMod.card, one_div, ← Multiset.prod_map_inv]
      convert rfl <;> rfl)
  refine le_trans hred (le_trans hT ?_)
  refine le_trans (add_le_add hW le_rfl) (le_of_eq ?_)
  rw [ZMod.card, D.nd.card_PlG k, Fintype.card_fin]
  unfold Wg
  ring

end PropWRec

theorem weightAllRows_of {D : D7} (A : AllRows D) (hL : admLq D) (hA : TieAdmG D) (hR : RangeW D)
    (hV : TieVecW A) : WeightAllRows A := by
  unfold WeightAllRows
  refine ⟨fun k v f => ?_, fun k S hS => locShare_le_Wg A hL hA hR hV k S hS⟩
  obtain ⟨ψ₀, hne, hv⟩ := hV
  unfold admLq at hL
  rcases hv k v with h | h
  · rw [h]
    exact ((hL k (ψ₀ k) (hne k)).1 f).1
  · rw [h]
    exact ((hL k (ψ₀ k) (hne k)).1 f).2

end Formalism.L2.GlobalTheoryTheory.ConcNWeight
