module

public import Mathlib
public import Lemmata.SecondBlockLemmaA.Imports

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact'''''''

theorem goal1 :
    ∀ {O : Type u_1} [inst : CommRing O] [inst_1 : IsDomain O] [inst_2 : IsDiscreteValuationRing O]
      {ι : Type u_2} (s : Finset ι) (a : ι → O),
      (IsDiscreteValuationRing.addVal O) (∏ i ∈ s, a i) =
        ∑ i ∈ s, (IsDiscreteValuationRing.addVal O) (a i) := by
  exact Bl.SecondBlockLemmaA.goal1
end Bl.general_b_fact'''''''
