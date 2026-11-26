module

public import Formalism.LocalRingCardinality.DataParams₂

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
noncomputable section

namespace GlobalTheory.EX

open Formalism.BasicNotions

structure Scales (la : ℝ) where
  J : ℝ
  one_le_J : 1 ≤ J
  Win : Set ℝ
  windows : ∀ y : ℝ, ∃ Y : ℝ, y ≤ Y ∧ ∀ x : ℝ, Y ≤ x → x ≤ Y ^ la → x ∈ Win

namespace Scales

variable {la : ℝ}

def Mem (S : Scales la) (s : Scale) : Prop := s.J = S.J ∧ s.x ∈ S.Win

theorem unb (S : Scales la) (hla : 1 ≤ la) (y : ℝ) : ∃ x ∈ S.Win, y ≤ x := by
  obtain ⟨Y, hY, hW⟩ := S.windows (max y 1)
  have h1 : 1 ≤ Y := le_trans (le_max_right y 1) hY
  refine ⟨Y, hW Y le_rfl ?_, le_trans (le_max_left y 1) hY⟩
  calc Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
    _ ≤ Y ^ la := Real.rpow_le_rpow_of_exponent_le h1 hla

def scale (S : Scales la) (x eps : ℝ) (hx : 1 < x) (h0 : 0 < eps) (h1 : eps < 1 / 52) : Scale :=
  ⟨x, eps, hx, h0, h1, S.J, S.one_le_J⟩

end Scales

end GlobalTheory.EX

end
end

section -- merged from Development.AutomorphicArithmetic.PrimeDiscriminants.SplitLow
namespace UpperTheory.Host

open Formalism.BasicNotions

theorem le_floor_ez (s : Scale) {c : ℝ} (hc : 0 < c) (hce : c ≤ s.ez) (B : ℕ) (hx : (B : ℝ) ^ (5 / c) ≤ s.x) :
    B ≤ ⌊s.x ^ (s.ez / 5)⌋₊ := by
  refine Nat.le_floor ?_
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have e : (B : ℝ) = ((B : ℝ) ^ (5 / c)) ^ (c / 5) := by
    rw [← Real.rpow_mul hB, show 5 / c * (c / 5) = 1 by field_simp, Real.rpow_one]
  calc (B : ℝ) = ((B : ℝ) ^ (5 / c)) ^ (c / 5) := e
    _ ≤ s.x ^ (c / 5) := Real.rpow_le_rpow (Real.rpow_nonneg hB _) hx (by positivity)
    _ ≤ s.x ^ (s.ez / 5) := Real.rpow_le_rpow_of_exponent_le s.one_lt_alt.le (by linarith)

end UpperTheory.Host
end
