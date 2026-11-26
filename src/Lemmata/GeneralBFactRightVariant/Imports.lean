module

public import Mathlib

@[expose] public section

universe u_1

namespace Bl.general_b_fact_right_variant

theorem goal1 :
    ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R) [hP : P.IsPrime] (n : ℕ),
      n ≠ 0 → ↑n ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ ↑p ∈ P := by
  intro R _ P hP n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    by_cases h1 : n = 1
    · subst h1
      rw [Nat.cast_one] at hmem
      exact absurd ((Ideal.eq_top_iff_one P).2 hmem) hP.ne_top
    · have hp := Nat.minFac_prime h1
      obtain ⟨m, hm⟩ := Nat.minFac_dvd n
      have hmem' : ((n.minFac : R) * (m : R)) ∈ P := by
        rw [← Nat.cast_mul, ← hm]
        exact hmem
      rcases hP.mem_or_mem hmem' with h | h
      · exact ⟨_, hp, Nat.minFac_dvd n, h⟩
      · have hm0 : m ≠ 0 := by
          rintro rfl
          exact hn (by simpa using hm)
        have hpos : 0 < m := Nat.pos_of_ne_zero hm0
        have h2 := hp.two_le
        have hlt : m < n := by nlinarith
        obtain ⟨p, pp, pd, pm⟩ := ih m hlt hm0 h
        exact ⟨p, pp, Dvd.dvd.trans pd ⟨n.minFac, hm.trans (Nat.mul_comm _ _)⟩, pm⟩

end Bl.general_b_fact_right_variant
