module

public import Formalism.GrowthSums.StatementG
public import Formalism.GrowthSums.FactorialBaseGrowth.Harmonic

@[expose] public section

section -- merged from Formalism.GrowthSums.FactorialBaseGrowth.PathBasisOfCount
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

theorem summable_min_div_pow_two_mul_add_one {n : ℕ} (p : ℝ) (hp : 1 < p) (a : ℝ) (ha : 0 ≤ a)
    (cap : ZMod n → ℝ) (hcap : ∀ s, 0 ≤ cap s) (s : ZMod n) :
    Summable (fun e : ℕ => min (a / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n)))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hq0 : 0 ≤ (p ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
  have hq1 : (p ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hp two_ne_zero)
  have hgeom : Summable (fun e : ℕ => a / p * ((p ^ 2)⁻¹) ^ e) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left (a / p)
  refine Summable.of_nonneg_of_le (fun e => le_min (div_nonneg ha (pow_nonneg hp0.le _)) (hcap _))
    (fun e => (min_le_left _ _).trans (le_of_eq ?_)) hgeom
  rw [inv_pow, ← pow_mul, pow_succ]
  field_simp

theorem cappedGainSubLE : CappedGainSubLE := by
  intro n p TT TTodd al cap de v i₀ i E hp hsub hal hcap hi hiE h1 h2 h3
  unfold gainG
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hsplit : ∑ s ∈ TT, ∑ e ∈ E, i s e =
      ∑ s ∈ TT \ TTodd, ∑ e ∈ E, i s e + ∑ s ∈ TTodd, ∑ e ∈ E, i s e :=
    (Finset.sum_sdiff hsub).symm
  have hodd : ∑ s ∈ TTodd, ∑ e ∈ E, i s e ≤
      ∑ s ∈ TTodd, ∑' e : ℕ, min (al s / p ^ (2 * e + 1)) (cap (s + ((2 * e + 1 : ℕ) : ZMod n))) := by
    refine Finset.sum_le_sum fun s hs => ?_
    refine (Finset.sum_le_sum fun e _ => h3 s hs e).trans ?_
    exact Summable.sum_le_tsum E
      (fun e _ => le_min (div_nonneg (hal s) (pow_nonneg hp0.le _)) (hcap _))
      (summable_min_div_pow_two_mul_add_one p hp (al s) (hal s) cap hcap s)
  linarith

end Formalism.GrowthSums
end
end

section -- merged from Formalism.GrowthSums.FactorialBaseGrowth.LogCoef
section -- merged from Formalism.GrowthSums.StatementC
noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

def LogCoefVal : Prop :=
  ∀ p t s : ℕ, p.Prime → 5 ≤ p → 1 ≤ s →
    ((s : ℝ) + 1) / 4 ≤
      (padicValRat p (((p ^ (t + 1) : ℕ) : ℚ) ^ s * (∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s) / s) : ℝ)
        - 1 / ((p : ℝ) - 1)

end Formalism.GrowthSums
end
end

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

theorem four_mul_add_two_le_three_mul_five_pow (v : ℕ) : 4 * v + 2 ≤ 3 * 5 ^ v := by
  induction v with
  | zero => norm_num
  | succ n ih =>
    have h1 : 1 ≤ 5 ^ n := Nat.one_le_pow n 5 (by norm_num)
    rw [pow_succ]
    omega

theorem four_padicValNat_le (p s : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 1 ≤ s) :
    4 * padicValNat p s + 2 ≤ 3 * s := by
  have hv := four_mul_add_two_le_three_mul_five_pow (padicValNat p s)
  have h1 : 5 ^ padicValNat p s ≤ p ^ padicValNat p s := Nat.pow_le_pow_left hp5 _
  have h2 : p ^ padicValNat p s ≤ s := Nat.le_of_dvd (by omega) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  omega

theorem padicValHarmonicPowerSumDivLowerBound : LogCoefVal := by
  intro p t s hp hp5 hs
  have := Fact.mk hp
  set X : ℚ := ((p ^ (t + 1) : ℕ) : ℚ) ^ s * (∑ y ∈ Ico 1 (p ^ (t + 1)), 1 / (y : ℚ) ^ s) with hX
  have hH : (s : ℤ) ≤ padicValRat p X := padicValHarmonicPowerSum p t s hp
  have hp1 : 1 < p ^ (t + 1) := Nat.one_lt_pow (Nat.succ_ne_zero t) hp.one_lt
  have hpos : 0 < X := by
    apply mul_pos
    · have : (0 : ℚ) < ((p ^ (t + 1) : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < p ^ (t + 1))
      positivity
    · apply Finset.sum_pos
      · intro i hi
        have : 1 ≤ i := (Finset.mem_Ico.mp hi).1
        have : (0 : ℚ) < (i : ℚ) := by exact_mod_cast (by omega : 0 < i)
        positivity
      · exact ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, hp1⟩⟩
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have key : (s : ℤ) - (padicValNat p s : ℤ) ≤ padicValRat p (X / s) := by
    rw [padicValRat.div (ne_of_gt hpos) hs0, padicValRat.of_nat]
    rw [Nat.padicValNat_def]
    omega
  have hk : (s : ℝ) - (padicValNat p s : ℝ) ≤ ((padicValRat p (X / s) : ℤ) : ℝ) := by
    exact_mod_cast key
  have h4 : 4 * (padicValNat p s : ℝ) + 2 ≤ 3 * (s : ℝ) := by
    exact_mod_cast four_padicValNat_le p s hp hp5 hs
  have hq : (4 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (5 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp5
    linarith
  have hinv : 1 / ((p : ℝ) - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hq
  linarith

end Formalism.GrowthSums
end
end
