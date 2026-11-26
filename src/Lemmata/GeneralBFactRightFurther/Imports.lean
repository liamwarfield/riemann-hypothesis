module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_right_further

theorem goal1 :
    ∀ {n : ℕ} (J : Finset (Fin n)) {k : ℕ} (h : J.card = k) (i : Fin k),
      {x ∈ J | x < (J.orderEmbOfFin h) i}.card = ↑i := by
  intro n J k h i
  have key : Finset.filter (fun (x : Fin n) ↦ x < J.orderEmbOfFin h i) J
      = (Finset.Iio i).map (J.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio]
    constructor
    · rintro ⟨hx, hlt⟩
      have hr : x ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨j, rfl⟩ := hr
      exact ⟨j, (J.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem J h j, (J.orderEmbOfFin h).lt_iff_lt.mpr hj⟩
  rw [key, Finset.card_map, Fin.card_Iio]

end Bl.general_b_fact_right_further
