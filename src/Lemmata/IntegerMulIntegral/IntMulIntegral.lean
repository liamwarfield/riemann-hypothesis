module

public import Mathlib

@[expose] public section

namespace Bl.IntegerMulIntegral

private lemma int_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℤ, d ≠ 0 ∧ IsIntegral ℤ ((d : E) * a) := by
  have hx : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ a)
  obtain ⟨y, hy, hi⟩ := hx.exists_integral_multiple
  exact ⟨y, hy, by simpa [zsmul_eq_mul] using hi⟩

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
      (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
      ∀ v ∈ Submodule.span E (SetLike.coe L), ∃ (m : ℤ), m ≠ 0 ∧ m • v ∈ L := by
  intro E _ _ n L v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, h1, hm1⟩ := hx
    obtain ⟨m2, h2, hm2⟩ := hy
    refine ⟨m1 * m2, mul_ne_zero h1 h2, ?_⟩
    have e : (m1 * m2) • (x + y) = m2 • (m1 • x) + m1 • (m2 • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm m2 m1]
    rw [e]
    exact L.add_mem (L.toAddSubgroup.zsmul_mem hm1 m2) (L.toAddSubgroup.zsmul_mem hm2 m1)
  | smul a x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨d, hd, hi⟩ := int_mul_integral a
    refine ⟨d * m, mul_ne_zero hd hm, ?_⟩
    obtain ⟨r, hr⟩ : ∃ r : NumberField.RingOfIntegers E,
        algebraMap (NumberField.RingOfIntegers E) E r = (d : E) * a := ⟨⟨_, hi⟩, rfl⟩
    have hmem := L.smul_mem r hmx
    convert hmem using 1
    ext i
    change (d * m) • (a * x i) = r • ((m • x) i)
    rw [← algebraMap_smul E r, hr, Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
    ring

end Bl.IntegerMulIntegral
