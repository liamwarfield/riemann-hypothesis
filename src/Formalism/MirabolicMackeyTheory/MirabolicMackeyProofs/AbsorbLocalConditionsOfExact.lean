module

public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverP
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.BoundsChain

@[expose] public section

section -- merged from Formalism.MirabolicMackeyTheory.StatementC
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

def AbsorbOnC : Prop :=
  ∀ (c C Cb L xe f m b k ws Se Y X2 bad : ℝ), 0 ≤ c → 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m →
    0 < b → 1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2 * c * (C * k * ws) / X2 + c * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + (14 + 10 * c) * C + Cb + 12) * xe * (f * m * b * L)

def ThetaLog4 : Prop :=
  ∀ (Y : ℝ), 0 ≤ Y → ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
    ∑ p ∈ Q, Real.log (p : ℝ) ≤ Real.log 4 * Y

def DepthSums (T Cth Cadd : ℝ) (th add : ℕ → ℝ) : Prop :=
  (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → ∑ p ∈ Q, th p * Real.log (p : ℝ) ≤ Cth) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime) → T * ∑ p ∈ Q, add p * Real.log (p : ℝ) ≤ Cadd)

end Formalism.EigenvalueLevelCeiling
end
end

section -- merged from Formalism.MirabolicMackeyTheory.ErrSumGoodExact
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

def ErrSumGoodExact : Prop :=
  ∀ (PI : Finset ℕ), (∀ p ∈ PI, p.Prime) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → DepthSums T Cth Cadd th add →
      ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y)

def OnSumExact : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Bad : Finset ℕ) (eb : ℕ → ℝ), (∀ p, 0 ≤ eb p) →
  ∀ (Y X2 A1 A2 kw T Cth Cadd : ℝ) (th add : ℕ → ℝ), 1 < Y → 0 < X2 → 0 ≤ A1 → 0 ≤ A2 → 0 ≤ kw →
    0 ≤ T → (∀ p, 0 ≤ th p) → (∀ p, 0 ≤ add p) → DepthSums T Cth Cadd th add →
  ∀ (errl : HeightOneSpectrum (𝓞 K) → ℝ),
    (∀ w ∈ S, errl w ≤ if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w)) →
      ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
        2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y) +
          ∑ p ∈ Bad, Real.log (p : ℝ) * eb p

def AbsorbOnExact : Prop :=
  ∀ (C Cb L xe f m b k ws Se Y X2 bad : ℝ), 1 ≤ C → 0 ≤ Cb → 1 ≤ L → L ≤ xe → 1 ≤ f → 1 ≤ m → 0 < b →
    1 ≤ k → Real.log k ≤ L → 0 ≤ ws → ws ≤ 2 * f * b → 0 ≤ Se → k * Se * L ≤ m * b → 1 < Y →
    Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 → bad ≤ Cb * (f * m * b * L) →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2.04 * (C * k * ws) / X2 + Real.log 4 * Y) + bad + 12 * (f * m * b) ≤
        (4 * C ^ 2 + 25 * C + Cb + 12) * xe * (f * m * b * L)

def LeadExact : Prop :=
  ∀ (C L f m b k ws Se Y X2 : ℝ), 1 ≤ C → 1 ≤ f → 1 ≤ m → 0 < b → 1 ≤ k → 0 ≤ ws → ws ≤ 2 * f * b →
    0 ≤ Se → k * Se * L ≤ m * b → 1 < Y → Real.log Y ≤ 2 * L → Y ≤ m * b → k ≤ X2 →
      2 * (C * (Real.log k * m * ws + f * k * Se) * Real.log Y + C * k * ws * (C / k) + C * (m * b) +
          2.04 * (C * k * ws) / X2 + Real.log 4 * Y) ≤
        4 * C * L * Real.log k * m * ws + (4 * C ^ 2 + 17 * C) * (f * m * b)

end Formalism.EigenvalueLevelCeiling
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PrimeLogOverPSqTail
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PrimeLogarithmTail.SumLogDivSqLeDiv
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PrimeLogarithmTail.SumLogBlock
namespace PI.TailWork

open Finset

theorem sum_log_block (n : ℕ) :
    ∑ p ∈ (Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ) ≤ (n : ℝ) * Real.log 4 := by
  classical
  have hdvd : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ∣ Nat.centralBinom n := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Finset.mem_filter.1 hp).2.prime
    · intro p hp
      obtain ⟨hI, hpr⟩ := Finset.mem_filter.1 hp
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hI
      rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
      exact hpr.dvd_choose_add h1 h1 (by omega)
  have hle : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ≤ 4 ^ n :=
    (Nat.le_of_dvd (Nat.centralBinom_pos n) hdvd).trans (Nat.centralBinom_le_four_pow n)
  have hpos : ∀ p ∈ (Ioc n (2 * n)).filter Nat.Prime, ((p : ℕ) : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
  rw [← Real.log_prod hpos, ← Real.log_pow]
  apply Real.log_le_log
  · apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.pos
  · have : ((∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p : ℕ) : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hle
    push_cast at this
    exact this

noncomputable def g (n : ℕ) : ℝ := 1 / ((n : ℝ) * ((n : ℝ) - 1))

noncomputable def h (n : ℕ) : ℝ := 1 / ((n : ℝ) - 1) + 1 / (n : ℝ)

theorem sum_Ico_tele (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

theorem w_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ g n - g (n + 1) := by
  unfold g
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le
  · nlinarith
  · nlinarith

theorem w_mul (n : ℕ) (hn : 2 ≤ n) : (g n - g (n + 1)) * (n : ℝ) = h n - h (n + 1) := by
  unfold g h
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (n : ℝ) ≠ 0 := by linarith
  have h4 : (n : ℝ) + 1 ≠ 0 := by linarith
  push_cast
  simp only [add_sub_cancel_right]
  field_simp
  ring

theorem weighted (k : ℕ) (hk : 1 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)
      ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) := by
  classical
  set N := k + 1 + Q.sup id + 1 with hN
  have hw : ∀ p ∈ Q, g ((p + 1) / 2) - g p = ∑ m ∈ Ico ((p + 1) / 2) p, (g m - g (m + 1)) := by
    intro p hp
    have := (hQ p hp).2
    rw [sum_Ico_tele g _ _ (by omega)]
  have hL : ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)
      = ∑ m ∈ Ico (k + 1) N, (g m - g (m + 1)) *
          ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ) := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [hw p hp, Finset.mul_sum])]
    rw [Finset.sum_comm' (t' := Ico (k + 1) N)
      (s' := fun m => Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p))]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)
    · intro p m
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨hp, h1, h2⟩
        have := (hQ p hp).2
        have hs : p ≤ Q.sup id := Finset.le_sup (f := id) hp
        exact ⟨⟨hp, h1, h2⟩, by omega, by omega⟩
      · rintro ⟨⟨hp, h1, h2⟩, _, _⟩
        exact ⟨hp, h1, h2⟩
  rw [hL]
  have hb : ∀ m ∈ Ico (k + 1) N, (g m - g (m + 1)) *
      ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)
        ≤ Real.log 4 * (h m - h (m + 1)) := by
    intro m hm
    have hm2 : 2 ≤ m := by simp only [Finset.mem_Ico] at hm; omega
    have hin : ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)
        ≤ (m : ℝ) * Real.log 4 := by
      refine le_trans ?_ (sum_log_block m)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
        exact ⟨⟨hp.2.2, by omega⟩, (hQ p hp.1).1⟩
      · intro p _ _
        exact Real.log_natCast_nonneg p
    calc _ ≤ (g m - g (m + 1)) * ((m : ℝ) * Real.log 4) :=
          mul_le_mul_of_nonneg_left hin (w_nonneg m hm2)
      _ = Real.log 4 * ((g m - g (m + 1)) * m) := by ring
      _ = _ := by rw [w_mul m hm2]
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum, sum_Ico_tele h _ _ (by omega)]
  have hk1 : h (k + 1) = 1 / (k : ℝ) + 1 / ((k : ℝ) + 1) := by
    unfold h
    push_cast
    rw [add_sub_cancel_right]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hN0 : 0 ≤ h N := by
    unfold h
    exact add_nonneg (one_div_nonneg.2 (by linarith)) (one_div_nonneg.2 (by linarith))
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [hk1]
  exact mul_le_mul_of_nonneg_left (by linarith) hl

theorem log_four_lt : Real.log 4 < 1.3863 := by
  have h2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  norm_num at h2 ⊢
  linarith

theorem weight_ge (k p : ℕ) (hk : 1 ≤ k) (hp : 2 * k + 1 ≤ p) (hodd : p % 2 = 1) :
    (3 - 1 / (2 * (k : ℝ) + 1)) / (p : ℝ) ^ 2 ≤ g ((p + 1) / 2) - g p := by
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 := ⟨p / 2, by omega⟩
  have hq : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  rw [hq]
  have hjk : k ≤ j := by omega
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (k : ℝ) ≤ j := by exact_mod_cast hjk
  have hj1 : (1 : ℝ) ≤ j := le_trans hk' hj'
  unfold g
  push_cast
  simp only [add_sub_cancel_right]
  have hmid : 3 - 1 / (2 * (k : ℝ) + 1) ≤ 3 - 1 / (2 * (j : ℝ) + 1) := by
    have : 1 / (2 * (j : ℝ) + 1) ≤ 1 / (2 * (k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have key : 1 / (((j : ℝ) + 1) * j) - 1 / ((2 * (j : ℝ) + 1) * (2 * j))
      - (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2
      = (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1))) := by
    have : (j : ℝ) ≠ 0 := by linarith
    have : (j : ℝ) + 1 ≠ 0 := by linarith
    have : 2 * (j : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 ≤ (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1))) := by positivity
  have hstep : (3 - 1 / (2 * (k : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2
      ≤ (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2 :=
    div_le_div_of_nonneg_right hmid (by positivity)
  linarith

theorem tail_odd (k : ℕ) (hk : 3 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := by
  have hk1 : 1 ≤ k := by omega
  have hW := weighted k hk1 Q hQ
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcpos : 0 < 3 - 1 / (2 * (k : ℝ) + 1) := by
    have : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hterm : ∀ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1)) := by
    intro p hp
    obtain ⟨hpr, hpk⟩ := hQ p hp
    have hodd : p % 2 = 1 := by
      rcases hpr.eq_two_or_odd with h2 | h2
      · omega
      · exact h2
    have hwg := weight_ge k p hk1 hpk hodd
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    rw [le_div_iff₀ hcpos]
    calc Real.log (p : ℝ) / (p : ℝ) ^ 2 * (3 - 1 / (2 * (k : ℝ) + 1))
        = Real.log (p : ℝ) * ((3 - 1 / (2 * (k : ℝ) + 1)) / (p : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwg hlog
  have hl := log_four_lt
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have e : Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1))
      = Real.log 4 * (2 * (k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2)) := by
    have : (k : ℝ) ≠ 0 := by linarith
    have : (k : ℝ) + 1 ≠ 0 := by linarith
    have : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
    have : 6 * (k : ℝ) + 2 ≠ 0 := by linarith
    have hc : 3 - 1 / (2 * (k : ℝ) + 1) = (6 * (k : ℝ) + 2) / (2 * (k : ℝ) + 1) := by
      field_simp
      ring
    rw [hc]
    field_simp
    ring
  have A : Real.log 4 * (2 * (k : ℝ) + 1) ^ 3 ≤ 1.3863 * (2 * (k : ℝ) + 1) ^ 3 :=
    mul_le_mul_of_nonneg_right hl.le (by positivity)
  have hk3 : 0 ≤ (k : ℝ) - 3 := by linarith
  have B : 1.3863 * (2 * (k : ℝ) + 1) ^ 3 ≤ 2.04 * ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2)) := by
    nlinarith [mul_nonneg (mul_nonneg hk3 hk3) hk3, mul_nonneg hk3 hk3, hk3]
  calc ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1)) :=
        Finset.sum_le_sum hterm
    _ = (∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)) / (3 - 1 / (2 * (k : ℝ) + 1)) := by
        rw [Finset.sum_div]
    _ ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hW hcpos.le
    _ ≤ 2.04 / (2 * (k : ℝ) + 1) := by
        rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [A, B]

end PI.TailWork
end

namespace PI.TailWork

open Finset

theorem log_three_le : Real.log 3 ≤ 1.11 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (0.11 : ℝ)
  have he : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11 := by
    rw [← Real.exp_add]; norm_num
  rw [he]
  have := mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
  linarith

theorem log_five_le : Real.log 5 ≤ 1.62 := by
  have h25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h24 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have hq : Real.log 25 - Real.log 24 ≤ 25 / 24 - 1 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_le_sub_one_of_pos (by norm_num)
  linarith [Real.log_two_lt_d9, log_three_le]

theorem small_split (a : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ a < p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ ({2, 3, 5} : Finset ℕ).filter (fun p => a < p), Real.log (p : ℝ) / (p : ℝ) ^ 2
        + 2.04 / 7 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p => p ∈ ({2, 3, 5} : Finset ℕ))]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.2, (hQ p hp.1).2⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  · have h := tail_odd 3 le_rfl
      (Q.filter (fun p => p ∉ ({2, 3, 5} : Finset ℕ))) (by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpQ, hpT⟩ := hp
        have hpr := (hQ p hpQ).1
        refine ⟨hpr, ?_⟩
        by_contra hlt
        replace hlt : p < 2 * 3 + 1 := not_le.mp hlt
        have h2 := hpr.two_le
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpT
        obtain ⟨n2, n3, n5⟩ := hpT
        interval_cases p
        all_goals first
          | exact (n2 rfl).elim
          | exact (n3 rfl).elim
          | exact (n5 rfl).elim
          | exact absurd hpr (by norm_num))
    norm_num at h ⊢
    linarith

private theorem sum_small_primes_log_div_sq_add_le (a : ℕ) (ha : a < 5) :
    ∑ p ∈ ({2, 3, 5} : Finset ℕ).filter (fun p => a < p), Real.log (p : ℝ) / (p : ℝ) ^ 2
      + 2.04 / 7 ≤ 2.04 / ((a : ℝ) + 1) := by
  have l2 := Real.log_two_lt_d9
  have l3 := log_three_le
  have l5 := log_five_le
  interval_cases a <;> norm_num [Finset.sum_filter, Finset.sum_insert] <;> linarith

theorem sum_log_div_sq_le_div (X : ℝ) (hX : 0 < X) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, ⌊X⌋₊ = m := ⟨_, rfl⟩
  have hXm : X < (m : ℝ) + 1 := hm ▸ Nat.lt_floor_add_one X
  have hmX : (m : ℝ) ≤ X := hm ▸ Nat.floor_le hX.le
  have hlt : ∀ p ∈ Q, m < p := fun p hp => hm ▸ (Nat.floor_lt hX.le).2 (hQ p hp).2
  rcases lt_or_ge X 5 with h5 | h5
  · have hm5 : m < 5 := by exact_mod_cast (lt_of_le_of_lt hmX h5)
    have h1 := small_split m Q (fun p hp => ⟨(hQ p hp).1, hlt p hp⟩)
    have h2 := sum_small_primes_log_div_sq_add_le m hm5
    have hinv : 1 / ((m : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX hXm.le
    have h3 : 2.04 / ((m : ℝ) + 1) ≤ 2.04 / X := by
      calc 2.04 / ((m : ℝ) + 1) = 2.04 * (1 / ((m : ℝ) + 1)) := by ring
        _ ≤ 2.04 * (1 / X) := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 2.04 / X := by ring
    linarith
  · have hm5 : 5 ≤ m := by
      rw [← hm]; exact Nat.le_floor (by exact_mod_cast h5)
    obtain ⟨k, hk⟩ : ∃ k, (m + 1) / 2 = k := ⟨_, rfl⟩
    have hk3 : 3 ≤ k := by omega
    have hQk : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p := by
      intro p hp
      have hpr := (hQ p hp).1
      have hmp := hlt p hp
      refine ⟨hpr, ?_⟩
      rcases hpr.eq_two_or_odd with h | h
      · omega
      · omega
    have h := tail_odd k hk3 Q hQk
    have hkX : X ≤ 2 * (k : ℝ) + 1 := by
      have hn : m + 1 ≤ 2 * k + 1 := by omega
      have : (m : ℝ) + 1 ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast hn
      linarith
    have hinv : 1 / (2 * (k : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX hkX
    calc ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := h
      _ = 2.04 * (1 / (2 * (k : ℝ) + 1)) := by ring
      _ ≤ 2.04 * (1 / X) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 2.04 / X := by ring

end PI.TailWork
end

theorem prime_log_over_sq_tail : PI.PrimeLogOverPSqTail :=
  fun X hX Q hQ => PI.TailWork.sum_log_div_sq_le_div X hX Q hQ
end

section -- merged from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsComposeGeneral
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem chebyshev_theta_log_four : ThetaLog4 := by
  classical
  intro Y hY Q hQ
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x hY)
  unfold Chebyshev.theta
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := hQ p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1.pos, Nat.le_floor h2⟩, h1⟩
  · intro p _ _
    exact Real.log_natCast_nonneg p

end Formalism.EigenvalueLevelCeiling
end

open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem primeBoundsExact (Y X2 : ℝ) (hY : 1 < Y) (hX2 : 0 < X2) :
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) → ∑ p ∈ Q, Real.log (p : ℝ) ≤ Real.log 4 * Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X2) :=
  ⟨_root_.sum_log_p_over_p Y hY, chebyshev_theta_log_four Y (by linarith),
    _root_.prime_log_over_sq_tail X2 hX2⟩

theorem error_sum_good_places_exact : ErrSumGoodExact := by
  intro PI hPI Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD
  obtain ⟨hB1, hB2, hB3⟩ := primeBoundsExact Y X2 hY hX2
  obtain ⟨hD1, hD2⟩ := hD
  have hQ : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime ∧ (p : ℝ) ≤ Y := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨hPI p hp.1, hp.2⟩
  have hQ' : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime := fun p hp => (hQ p hp).1
  have hR : ∀ p ∈ (PI.filter (fun p : ℕ => (p : ℝ) ≤ Y)).filter (fun p : ℕ => X2 < (p : ℝ)),
      p.Prime ∧ X2 < (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hQ p hp.1).1, hp.2⟩
  have e1 := hB1 _ hQ
  have e2 := hB2 _ hQ
  have e3 := hB3 _ hR
  have e4 := hD1 _ hQ'
  have e5 := hD2 _ hQ'
  rw [Finset.sum_filter] at e1 e2 e4 e5
  rw [Finset.sum_filter, Finset.sum_filter] at e3
  have hsum : ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p =
      2 * A1 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) / (p : ℝ) else 0) +
      2 * kw * (∑ p ∈ PI, if (p : ℝ) ≤ Y then th p * Real.log (p : ℝ) else 0) +
      2 * (T * ∑ p ∈ PI, if (p : ℝ) ≤ Y then add p * Real.log (p : ℝ) else 0) +
      2 * A2 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then
        (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) else 0) +
      2 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold errGood
    split_ifs <;> ring
  rw [hsum]
  have h1 := mul_le_mul_of_nonneg_left e1 hA1
  have h2 := mul_le_mul_of_nonneg_left e4 hkw
  have h4 := mul_le_mul_of_nonneg_left e3 hA2
  have h4' : A2 * (2.04 / X2) = 2.04 * A2 / X2 := by ring
  linarith

theorem onSumExact_of (hP : PlaceSum) (hR : RamBasic) (hE : ErrSumGoodExact) : OnSumExact := by
  intro K _ _ _ S Bad eb heb Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD errl herr
  have hG : ∀ p : ℕ, 0 ≤ errGood Y X2 A1 A2 kw T th add p := by
    intro p
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    unfold errGood
    split_ifs <;>
      linarith [div_nonneg hA1 hp, mul_nonneg hkw (hth p), mul_nonneg hT (hadd p),
        div_nonneg hA2 (pow_nonneg hp 2)]
  have hX : ∀ p : ℕ, 0 ≤ (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) := by
    intro p
    split_ifs
    · exact heb p
    · exact hG p
  have step1 : ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
      ∑ w ∈ S, lw w * ((ramw w : ℝ) *
        (if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w))) := by
    apply Finset.sum_le_sum
    intro w hw
    have hl : 0 ≤ lw w := by
      unfold lw
      exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    have hr : (0 : ℝ) ≤ (ramw w : ℝ) :=
      by exact_mod_cast (le_trans zero_le_one (hR K w).2.1)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (herr w hw) hr) hl
  have step2 := hP K S (fun p => if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) hX
  have hprime : ∀ p ∈ S.image plc, p.Prime := by
    intro p hp
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hR K w).1
  have hbadpart : ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) ≤
      ∑ p ∈ Bad, Real.log (p : ℝ) * eb p := by
    have hsub : (S.image plc).filter (fun p => p ∈ Bad) ⊆ Bad := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ) * eb p) hsub
      (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (heb p))
    rwa [Finset.sum_filter] at h
  have hgoodpart : ∑ p ∈ S.image plc,
      (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) ≤
      2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y) := by
    have h := hE ((S.image plc).filter (fun p => p ∉ Bad))
      (fun p hp => hprime p (Finset.mem_filter.mp hp).1) Y X2 A1 A2 kw T Cth Cadd th add
      hY hX2 hA1 hA2 hkw hT hth hadd hD
    rwa [Finset.sum_filter] at h
  have hsplit : ∑ p ∈ S.image plc, Real.log (p : ℝ) *
        (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) =
      ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) +
      ∑ p ∈ S.image plc,
        (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p ∈ Bad <;> simp [h]
  linarith

theorem local_sum_exact : OnSumExact := onSumExact_of place_sum ramified_basic_bound error_sum_good_places_exact

private theorem lead_exact : LeadExact := by
  intro C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2
  have hl4 : Real.log 4 < 1.3863 := by
    have h := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith
  have hC0 : 0 ≤ C := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 < k := by linarith
  have hX0 : 0 < X2 := by linarith
  have hY0 : 0 < Y := by linarith
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hmb : 0 ≤ m * b := mul_nonneg hm0 hb.le
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb.le
  have e1 : C * (Real.log k * m * ws) * Real.log Y ≤ C * (Real.log k * m * ws) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hlk hm0) hws0))
  have e2 : C * (f * k * Se) * Real.log Y ≤ C * (f * k * Se) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hf0 hk0.le) hSe))
  have e2b : C * f * (k * Se * L) ≤ C * f * (m * b) :=
    mul_le_mul_of_nonneg_left hkS (mul_nonneg hC0 hf0)
  have e3 : C * k * ws * (C / k) = C ^ 2 * ws := by
    rw [show C * k * ws * (C / k) = C ^ 2 * ws * (k / k) by ring, div_self hk0.ne', mul_one]
  have e3b : C ^ 2 * ws ≤ C ^ 2 * (2 * (f * b)) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg C)
  have hfbm : f * b ≤ f * b * m := le_mul_of_one_le_right hfb hm
  have e3c : C ^ 2 * (f * b) ≤ C ^ 2 * (f * b * m) := mul_le_mul_of_nonneg_left hfbm (sq_nonneg C)
  have hmbf : m * b ≤ f * (m * b) := le_mul_of_one_le_left hmb hf
  have e4 : C * (m * b) ≤ C * (f * (m * b)) := mul_le_mul_of_nonneg_left hmbf hC0
  have hCws : 0 ≤ C * ws := mul_nonneg hC0 hws0
  have hkX : k / X2 ≤ 1 := (div_le_one hX0).mpr hX2
  have e5 : C * k * ws / X2 ≤ C * ws := by
    calc C * k * ws / X2 = C * ws * (k / X2) := by ring
      _ ≤ C * ws * 1 := mul_le_mul_of_nonneg_left hkX hCws
      _ = C * ws := mul_one _
  have e5' : 2.04 * (C * k * ws) / X2 ≤ 2.04 * (C * ws) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left e5 (by norm_num)
  have e5b : C * ws ≤ C * (2 * (f * b)) := mul_le_mul_of_nonneg_left (by linarith) hC0
  have e5c : C * (f * b) ≤ C * (f * b * m) := mul_le_mul_of_nonneg_left hfbm hC0
  have e6 : Real.log 4 * Y ≤ 1.3863 * Y := mul_le_mul_of_nonneg_right hl4.le hY0.le
  have hCf : 1 ≤ C * f := one_le_mul_of_one_le_of_one_le hC hf
  have e6b : m * b ≤ C * f * (m * b) := le_mul_of_one_le_left hmb hCf
  have e7 : 0 ≤ C * f * (m * b) := mul_nonneg (mul_nonneg hC0 hf0) hmb
  linarith

theorem absorb_local_conditions_exact : AbsorbOnExact := by
  intro C Cb L xe f m b k ws Se Y X2 bad hC hCb hL hxe hf hm hb hk hlk hws0 hws hSe hkS hY hlY hYb hX2 hbad
  have hlead := lead_exact C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hZ : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb.le
  have hxe1 : 1 ≤ xe := by linarith
  have hxL : 1 ≤ xe * L := one_le_mul_of_one_le_of_one_le hxe1 hL
  have a1 : Real.log k * (C * L * (m * ws)) ≤ L * (C * L * (m * ws)) :=
    mul_le_mul_of_nonneg_right hlk (mul_nonneg (mul_nonneg hC0 hL0) (mul_nonneg hm0 hws0))
  have a2 : C * L * L * (m * ws) ≤ C * L * L * (m * (2 * f * b)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hws hm0) (mul_nonneg (mul_nonneg hC0 hL0) hL0)
  have a3 : C * (f * m * b) * (L * L) ≤ C * (f * m * b) * (xe * L) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxe hL0) (mul_nonneg hC0 hZ)
  have hq : 0 ≤ 4 * C ^ 2 + 17 * C := add_nonneg (by positivity) (by linarith)
  have a5 : (4 * C ^ 2 + 17 * C) * (f * m * b) ≤ (4 * C ^ 2 + 17 * C) * (f * m * b) * (xe * L) :=
    le_mul_of_one_le_right (mul_nonneg hq hZ) hxL
  have a6 : Cb * (f * m * b * L) ≤ Cb * (f * m * b * L) * xe :=
    le_mul_of_one_le_right (mul_nonneg hCb (mul_nonneg hZ hL0)) hxe1
  have a7 : 12 * (f * m * b) ≤ 12 * (f * m * b) * (xe * L) :=
    le_mul_of_one_le_right (by linarith) hxL
  linarith

end Formalism.EigenvalueLevelCeiling
