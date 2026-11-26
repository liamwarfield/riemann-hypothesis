module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_third'

private lemma key {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  obtain ⟨y, hy0, hy⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)).exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  obtain h | h := Int.natAbs_eq y
  · rw [h, zsmul_eq_mul] at hy
    simpa using hy
  · rw [h, zsmul_eq_mul] at hy
    simpa using hy.neg

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
      (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
      Submodule.span E (SetLike.coe L) = ⊤ → ∀ (w : Fin n → E), ∃ (m : ℕ), 0 < m ∧ m • w ∈ L := by
  intro E _ _ n L hL w
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [e]
    exact L.add_mem (nsmul_mem hax b) (nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨d, hd, hdc⟩ := key c
    refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
    have h1 := L.smul_mem (⟨(d : E) * c, hdc⟩ : NumberField.RingOfIntegers E) hax
    convert h1 using 1
    ext i
    rw [Pi.smul_apply, Algebra.smul_def]
    change _ = ((d : E) * c) * _
    simp [nsmul_eq_mul]
    ring

end Bl.general_b_fact_third'
