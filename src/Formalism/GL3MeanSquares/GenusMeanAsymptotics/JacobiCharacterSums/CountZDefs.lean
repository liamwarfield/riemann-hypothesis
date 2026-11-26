module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailMertens
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountZDefs
open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD

abbrev PC := Σ N : ℕ, DirichletCharacter ℂ (N + 1)

def cv (p : PC) (n : ℕ) : ℂ := p.2 (n : ZMod (p.1 + 1))

def s0 : ℝ := 1 - 1 / 400

def mco (Y N n : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 Y ×ˢ Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 = n), (((μ p.1 : ℤ)) : ℂ)

def blk (Y N U : ℕ) (p : PC) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc U (2 * U), mco Y N n * cv p n * (n : ℂ) ^ (-s)

def DualIneq : Prop :=
  ∀ (ι κ : Type) (S : Finset ι) (I : Finset κ) (b : κ → ℂ) (v : ι → κ → ℂ) (Δ : ℝ), 0 ≤ Δ →
    (∀ i ∈ S, ∑ j ∈ S, ‖∑ n ∈ I, v i n * (starRingEnd ℂ) (v j n)‖ ≤ Δ) →
    ∑ i ∈ S, ‖∑ n ∈ I, b n * v i n‖ ^ 2 ≤ (∑ n ∈ I, ‖b n‖ ^ 2) * Δ

def PairSum : Prop :=
  ∀ p p' : PC, p.2.IsPrimitive → p'.2.IsPrimitive → p ≠ p' → ∀ M : ℕ,
    ‖∑ n ∈ range M, cv p n * (starRingEnd ℂ) (cv p' n)‖ ≤ (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ)

def PairTwist : Prop :=
  ∀ p p' : PC, p.2.IsPrimitive → p'.2.IsPrimitive → p ≠ p' → ∀ w : ℂ, 0 < w.re → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), cv p n * (starRingEnd ℂ) (cv p' n) * (n : ℂ) ^ (-w)‖ ≤
      2 * (((p.1 + 1) * (p'.1 + 1) : ℕ) : ℝ) * (1 + ‖w‖)

def MollId : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (Y N K : ℕ), 1 ≤ Y → Y ≤ N → Y * N ≤ K →
    (∑ n ∈ Icc 1 N, χ (n : ZMod q) * (n : ℂ) ^ (-s)) *
        (∑ d ∈ Icc 1 Y, (((μ d : ℤ)) : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)) =
      1 + ∑ n ∈ Ioc Y K, mco Y N n * χ (n : ZMod q) * (n : ℂ) ^ (-s)

def CoeffSq : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ Y N U : ℕ, 1 ≤ U →
    ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))

def q0 (Q : ℝ) : ℕ := ⌈Q⌉₊
def pY (Q : ℝ) : ℕ := q0 Q ^ 4
def pJ (Q : ℝ) : ℕ := 8 * (Nat.log 2 (q0 Q) + 1)
def pN (Q : ℝ) : ℕ := 2 ^ pJ Q

def Detect : Prop :=
  ∀ (Q : ℝ), 20 ≤ Q → ∀ p : PC, p.2.IsPrimitive → p.1 ≠ 0 → ((p.1 + 1 : ℕ) : ℝ) ≤ Q →
    ∀ ρ : ℂ, s0 < ρ.re → |ρ.im| ≤ Q → DirichletCharacter.LFunction p.2 ρ = 0 →
      ∃ j ∈ range (pJ Q), 1 / (2 * (pJ Q : ℝ)) ≤ ‖blk (pY Q) (pN Q) (pY Q * 2 ^ j) p ρ‖

def BlockCount : Prop :=
  ∀ C : ℝ, 0 ≤ C → (∀ Y N U : ℕ, 1 ≤ U →
      ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-s0)) ^ 2 ≤ C * (U : ℝ) ^ (-(197 / 200 : ℝ))) →
  ∀ (Q : ℝ), 3 ≤ Q → ∀ (Y N U J : ℕ), 1 ≤ U → 1 ≤ J →
    8 * Q ^ 3 * C * (U : ℝ) ^ (-(197 / 200 : ℝ)) ≤ 1 / (8 * (J : ℝ) ^ 2) →
    ∀ (T : Finset PC) (ρ : PC → ℂ),
      (∀ p ∈ T, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ s0 < (ρ p).re ∧ (ρ p).re < 1 ∧
        |(ρ p).im| ≤ Q ∧ 1 / (2 * (J : ℝ)) ≤ ‖blk Y N U p (ρ p)‖) →
      (T.card : ℝ) ≤ 8 * (J : ℝ) ^ 2 * C * (U : ℝ) ^ (3 / 200 : ℝ)

def Num : Prop :=
  ∀ C : ℝ, 0 ≤ C → ∃ Q₀ C' : ℝ, 20 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
    (∀ j ∈ range (pJ Q), 8 * Q ^ 3 * C * ((pY Q * 2 ^ j : ℕ) : ℝ) ^ (-(197 / 200 : ℝ)) ≤
      1 / (8 * (pJ Q : ℝ) ^ 2)) ∧
    1 + (pJ Q : ℝ) * (8 * (pJ Q : ℝ) ^ 2 * C * ((pY Q * 2 ^ pJ Q : ℕ) : ℝ) ^ (3 / 200 : ℝ)) ≤ C' * Q ^ (1 / 4 : ℝ)

def PairTwistOf : Prop := PairSum → PairTwist
def CoeffSqOf : Prop := Formalism.FX.DivisorBound → CoeffSq
def DetectOf : Prop := MollId → Detect
def BlockCountOf : Prop := DualIneq → PairTwist → BlockCount
def FinalOf : Prop := CoeffSq → Detect → BlockCount → Num → ZeroDensityBox

end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqTwistC
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

private lemma intervalIntegrable_inv_log_two {Y : ℝ} (hY : 2 ≤ Y) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume 2 Y := by
  apply ContinuousOn.intervalIntegrable
  refine continuousOn_const.div (Real.continuousOn_log.mono ?_) ?_
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact Set.mem_compl_singleton_iff.2 (by linarith [ht.1] : (0 : ℝ) < t).ne'
  · intro t ht
    rw [Set.uIcc_of_le hY] at ht
    exact (Real.log_pos (by linarith [ht.1])).ne'

theorem liX_upper {Y : ℝ} (hY : 2 ≤ Y) : 0 ≤ liX Y ∧ liX Y ≤ 2 * Y := by
  have hpos : ∀ t ∈ Set.Icc (2 : ℝ) Y, 0 < Real.log t := fun t ht => Real.log_pos (by linarith [ht.1])
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  constructor
  · unfold liX
    exact intervalIntegral.integral_nonneg hY (fun t ht => (one_div_pos.2 (hpos t ht)).le)
  · unfold liX
    calc ∫ t in (2 : ℝ)..Y, 1 / Real.log t ≤ ∫ t in (2 : ℝ)..Y, (2 : ℝ) := by
          apply intervalIntegral.integral_mono_on hY (intervalIntegrable_inv_log_two hY) intervalIntegrable_const
          intro t ht
          have h1 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1
          rw [div_le_iff₀ (hpos t ht)]
          linarith
      _ = (Y - 2) * 2 := by simp
      _ ≤ 2 * Y := by linarith

theorem liX_lower {X : ℝ} (hX : 4 ≤ X) : X / (2 * Real.log X) ≤ liX X := by
  have hX2 : (2 : ℝ) ≤ X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos (by linarith)
  have hmono : ∫ t in (2 : ℝ)..X, 1 / Real.log X ≤ liX X := by
    unfold liX
    apply intervalIntegral.integral_mono_on hX2 intervalIntegrable_const (intervalIntegrable_inv_log_two hX2)
    intro t ht
    have ht0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    exact one_div_le_one_div_of_le ht0 (Real.log_le_log (by linarith [ht.1]) ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  rw [mul_one_div, div_le_div_iff₀ (by linarith) hLX]
  nlinarith [mul_le_mul_of_nonneg_right hX hLX.le]

theorem liX_pow_le {X β δ : ℝ} (hX : 4 ≤ X) (hβ1 : 1 / 2 ≤ β) (hβ2 : β ≤ 1 - δ) :
    |liX (X ^ β)| ≤ 4 * Real.log X * Real.exp (-(δ * Real.log X)) * liX X := by
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log X := ⟨_, rfl⟩
  rw [← hL]
  have hXpos : 0 < X := by linarith
  have hL0 : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
  have hXL : X = Real.exp L := by rw [hL, Real.exp_log hXpos]
  have hXb2 : 2 ≤ X ^ β := by
    have h4 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (2 : ℝ) = 4 ^ ((1 : ℝ) / 2) := h4.symm
      _ ≤ X ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
      _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) hβ1
  obtain ⟨h0, hup⟩ := liX_upper hXb2
  have hlow : X / (2 * L) ≤ liX X := by rw [hL]; exact liX_lower hX
  calc |liX (X ^ β)| = liX (X ^ β) := abs_of_nonneg h0
    _ ≤ 2 * X ^ β := hup
    _ = 2 * Real.exp (β * L) := by rw [Real.rpow_def_of_pos hXpos, ← hL, mul_comm L β]
    _ ≤ 2 * Real.exp ((1 - δ) * L) := by
        have : β * L ≤ (1 - δ) * L := mul_le_mul_of_nonneg_right hβ2 hL0.le
        have := Real.exp_le_exp.2 this
        linarith
    _ = 4 * L * Real.exp (-(δ * L)) * (X / (2 * L)) := by
        rw [hXL, show (1 - δ) * L = -(δ * L) + L by ring, Real.exp_add]
        field_simp
        ring
    _ ≤ 4 * L * Real.exp (-(δ * L)) * liX X :=
        mul_le_mul_of_nonneg_left hlow (by positivity)


theorem eventually_log_cube (K a : ℝ) (hK : 0 < K) (ha : 0 < a) :
    ∃ x₂ : ℝ, ∀ x : ℝ, x₂ ≤ x → K * Real.log x ^ 3 ≤ x ^ a := by
  have h := (isLittleO_log_rpow_rpow_atTop 3 ha).bound (by positivity : (0 : ℝ) < 1 / K)
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x₂, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₂ x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos h2 a)] at h1
  have h3 : Real.log x ^ 3 = Real.log x ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [h3]
  calc K * Real.log x ^ (3 : ℝ) ≤ K * |Real.log x ^ (3 : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hK.le
    _ ≤ K * (1 / K * x ^ a) := mul_le_mul_of_nonneg_left h1 hK.le
    _ = x ^ a := by field_simp

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqOrth
open Finset Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem jacobi_congr {a b s : ℕ} (h : a ≡ b [MOD s]) : jacobiSym (a : ℤ) s = jacobiSym (b : ℤ) s := by
  rw [jacobiSym.mod_left (a : ℤ), jacobiSym.mod_left (b : ℤ)]
  have h' : a % s = b % s := h
  rw [← Int.natCast_mod, ← Int.natCast_mod, h']

theorem exists_jacobi_neg_one (m t : ℕ) (ht : Odd t) (hsq : Squarefree t) (h1 : 1 < t)
    (hc : t.Coprime m) : ∃ u : ℕ, u ≡ 1 [MOD m] ∧ jacobiSym (u : ℤ) t = -1 := by
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (show t ≠ 1 by omega)
  haveI := Fact.mk hp
  obtain ⟨t', rfl⟩ := hpt
  have ht0 : t' ≠ 0 := by
    rintro rfl
    simp at h1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr ht) (even_two_mul t')
  have hpt' : ¬ p ∣ t' := by
    rintro ⟨k, rfl⟩
    have := hsq p ⟨k, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  have hcp : p.Coprime t' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpt'
  have hpm : p.Coprime m := Nat.Coprime.coprime_dvd_left (Dvd.intro t' rfl) hc
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.Coprime.mul_right hcp hpm) a.val 1
  refine ⟨k, Nat.ModEq.of_mul_left t' hk2, ?_⟩
  haveI : NeZero t' := ⟨ht0⟩
  rw [jacobiSym.mul_right, jacobi_congr hk1, jacobi_congr (Nat.ModEq.of_mul_right m hk2),
    ← jacobiSym.legendreSym.to_jacobiSym p, (legendreSym.eq_neg_one_iff p).mpr (by simpa using ha)]
  simp

private theorem dvd_of_jacobiSym_agree_on_residue_class (m₀ s₁ s₂ : ℕ) (h1 : Odd s₁) (h2 : Odd s₂)
    (hq1 : Squarefree s₁) (hc1 : s₁.Coprime m₀)
    (h : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime (s₁ * s₂) → jacobiSym (u : ℤ) s₁ = jacobiSym (u : ℤ) s₂) :
    s₁ ∣ s₂ := by
  by_contra hnd
  have hs1 : s₁ ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h1) ⟨0, rfl⟩
  have hs2 : s₂ ≠ 0 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h2) ⟨0, rfl⟩
  have hgd : Nat.gcd s₁ s₂ ∣ s₁ := Nat.gcd_dvd_left s₁ s₂
  have hg0 : Nat.gcd s₁ s₂ ≠ 0 := Nat.gcd_ne_zero_left hs1
  have hga : Nat.gcd s₁ s₂ * (s₁ / Nat.gcd s₁ s₂) = s₁ := Nat.mul_div_cancel' hgd
  have hgb : Nat.gcd s₁ s₂ * (s₂ / Nat.gcd s₁ s₂) = s₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right s₁ s₂)
  set g := Nat.gcd s₁ s₂ with hg
  set a := s₁ / g with ha
  set b := s₂ / g with hb
  have ha0 : a ≠ 0 := by
    rintro h0
    rw [h0, mul_zero] at hga
    exact hs1 hga.symm
  have ha1 : a ≠ 1 := by
    rintro h0
    rw [h0, mul_one] at hga
    exact hnd (hga ▸ Nat.gcd_dvd_right s₁ s₂)
  have hadv : a ∣ s₁ := Dvd.intro_left g hga
  have hao : Odd a := Odd.of_dvd_nat h1 hadv
  have haq : Squarefree a := Squarefree.squarefree_of_dvd hadv hq1
  have hag : a.Coprime g := by
    have := hq1
    rw [← hga] at this
    exact (Nat.squarefree_mul_iff.mp this).1.symm
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero hg0)
  have has2 : a.Coprime s₂ := by
    rw [← hgb]
    exact Nat.Coprime.mul_right hag hab
  have ham : a.Coprime m₀ := Nat.Coprime.coprime_dvd_left hadv hc1
  obtain ⟨u, hu1, hJ⟩ := exists_jacobi_neg_one (m₀ * s₂) a hao haq
    (lt_of_le_of_ne (Nat.pos_of_ne_zero ha0) (Ne.symm ha1))
    (Nat.Coprime.mul_right ham has2)
  have hum : u ≡ 1 [MOD m₀] := Nat.ModEq.of_mul_right s₂ hu1
  have hus : u ≡ 1 [MOD s₂] := Nat.ModEq.of_mul_left m₀ hu1
  have hug : u ≡ 1 [MOD g] := Nat.ModEq.of_dvd (Nat.gcd_dvd_right s₁ s₂) hus
  haveI : NeZero g := ⟨hg0⟩
  haveI : NeZero a := ⟨ha0⟩
  have hJs : jacobiSym (u : ℤ) s₂ = 1 := by
    rw [jacobi_congr hus]
    simp
  have hJg : jacobiSym (u : ℤ) g = 1 := by
    rw [jacobi_congr hug]
    simp
  have hJ1 : jacobiSym (u : ℤ) s₁ = -1 := by
    rw [← hga, jacobiSym.mul_right, hJg, hJ]
    ring
  have hua : u.Coprime a := by
    by_contra hn
    have h0 : jacobiSym (u : ℤ) a = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hn
    rw [h0] at hJ
    norm_num at hJ
  have hus' : u.Coprime s₂ := by
    have e : Nat.gcd u s₂ = Nat.gcd 1 s₂ := Nat.ModEq.gcd_eq hus
    rw [Nat.gcd_one_left] at e
    exact e
  have hug' : u.Coprime g := Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right s₁ s₂) hus'
  have hus1 : u.Coprime s₁ := by
    rw [← hga]
    exact Nat.Coprime.mul_right hug' hua
  have := h u hum (Nat.Coprime.mul_right hus1 hus')
  rw [hJ1, hJs] at this
  norm_num at this

theorem jacobi_separate (m₀ s₁ s₂ : ℕ) (hm : 0 < m₀) (h1 : Odd s₁) (h2 : Odd s₂) (hq1 : Squarefree s₁)
    (hq2 : Squarefree s₂) (hc1 : s₁.Coprime m₀) (hc2 : s₂.Coprime m₀)
    (h : ∀ u : ℕ, u % m₀ = 1 % m₀ → u.Coprime (s₁ * s₂) → jacobiSym (u : ℤ) s₁ = jacobiSym (u : ℤ) s₂) :
    s₁ = s₂ := by
  apply Nat.dvd_antisymm
  · exact dvd_of_jacobiSym_agree_on_residue_class m₀ s₁ s₂ h1 h2 hq1 hc1 h
  · exact dvd_of_jacobiSym_agree_on_residue_class m₀ s₂ s₁ h2 h1 hq2 hc2
      (fun u hu hc => (h u hu (by rwa [mul_comm])).symm)

end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end
