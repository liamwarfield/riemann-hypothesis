module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.SecondBlockLemmaA

theorem goal1 :
    ∀ {O : Type u_1} [inst : CommRing O] [inst_1 : IsDomain O] [inst_2 : IsDiscreteValuationRing O]
      {ι : Type u_2} (s : Finset ι) (a : ι → O),
      (IsDiscreteValuationRing.addVal O) (∏ i ∈ s, a i) =
        ∑ i ∈ s, (IsDiscreteValuationRing.addVal O) (a i) := by
  intro O _ _ _ ι s a
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  | insert i t hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, AddValuation.map_mul, ih]

end Bl.SecondBlockLemmaA
