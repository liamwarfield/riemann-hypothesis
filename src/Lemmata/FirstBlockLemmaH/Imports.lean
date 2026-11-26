module

public import Mathlib

@[expose] public section

namespace Bl.FirstBlockLemmaH

theorem goal1 :
    ∀ {E : Type} [inst : Field E] [NumberField E] {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module E V] [inst_4 : _root_.Module (NumberField.RingOfIntegers E) V]
      [IsScalarTower (NumberField.RingOfIntegers E) E V] {ι : Type} [Fintype ι] [DecidableEq ι]
      {b : Module.Basis ι E V} {M : Submodule (NumberField.RingOfIntegers E) V},
      Module.Finite (NumberField.RingOfIntegers E) ↥M →
        ∃ s ∈ nonZeroDivisors (NumberField.RingOfIntegers E),
          ∀ v ∈ M,
            ∀ (i : ι),
              (algebraMap (NumberField.RingOfIntegers E) E) s * (b.repr v) i ∈
                (algebraMap (NumberField.RingOfIntegers E) E).range := by
  intro E _ _ V _ _ _ _ ι _ _ b M hM
  obtain ⟨S, hS⟩ := Module.Finite.iff_fg.mp hM
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (NumberField.RingOfIntegers E))
    (S ×ˢ (Finset.univ : Finset ι)) (fun p : V × ι => b.repr p.1 p.2)
  refine ⟨s, s.2, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    intro i
    have h := hs (x, i) (Finset.mem_product.mpr ⟨Finset.mem_coe.mp hx, Finset.mem_univ _⟩)
    rw [IsLocalization.IsInteger, Algebra.smul_def] at h
    exact RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h)
  | zero =>
    intro i
    rw [map_zero, Finsupp.zero_apply, mul_zero]
    exact zero_mem _
  | add x y _ _ hx hy =>
    intro i
    rw [map_add (f := _), Finsupp.add_apply, mul_add]
    exact add_mem (hx i) (hy i)
  | smul a x _ hx =>
    intro i
    rw [← algebraMap_smul E a x, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]
    exact mul_mem (RingHom.mem_range_self _ a) (hx i)

end Bl.FirstBlockLemmaH
