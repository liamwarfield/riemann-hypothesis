module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_third_alt_form

theorem goal1 :
    ∀ {E : Type} [inst : CommRing E] {O : Subring E} {V : Type} [inst_1 : AddCommGroup V]
      [inst_2 : _root_.Module E V] {ι : Type} [inst_3 : Fintype ι] [inst_4 : DecidableEq ι]
      (g b : ι → V),
      LinearIndependent (↥O) g →
        Submodule.span (↥O) (Set.range g) = Submodule.span (↥O) (Set.range b) →
          ∃ (Q : Matrix ι ι ↥O) (P : Matrix ι ι ↥O), (∀ (j : ι), g j = ∑ i : ι, Q i j • b i) ∧ P * Q = 1 := by
  intro E _ O V _ _ ι _ _ g b hg hspan
  have hgb : ∀ j, g j ∈ Submodule.span O (Set.range b) := fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩
  have hbg : ∀ i, b i ∈ Submodule.span O (Set.range g) := fun i => hspan.symm ▸ Submodule.subset_span ⟨i, rfl⟩
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun O).1 (hgb j)
  choose d hd using fun i => (Submodule.mem_span_range_iff_exists_fun O).1 (hbg i)
  have key : ∀ j, ∑ k, ((Matrix.of fun k i => d i k) * (Matrix.of fun i j => c j i)) k j • g k = g j := by
    intro j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul]
    conv_rhs => rw [← hc j]
    simp only [← hd, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  refine ⟨Matrix.of fun i j => c j i, Matrix.of fun k i => d i k, fun j => (hc j).symm, ?_⟩
  ext k j
  have hz := Fintype.linearIndependent_iff.1 hg
    (fun k => ((Matrix.of fun k i => d i k) * (Matrix.of fun i j => c j i)) k j - (1 : Matrix ι ι O) k j) ?_ k
  · exact congrArg Subtype.val (sub_eq_zero.1 hz)
  · simp only [sub_smul, Finset.sum_sub_distrib, key, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

end Bl.general_b_fact_third_alt_form
