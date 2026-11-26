module

public import Mathlib

@[expose] public section

namespace Bl.FirstBlockLemmaK

theorem goal1 :
    ∀ {R : Type} [inst : CommRing R] {A : Type} [inst_1 : CommRing A] [inst_2 : Algebra R A]
      (aug : A →ₐ[R] R), IsNilpotent (RingHom.ker aug) → ∀ (a : A), IsUnit (aug a) → IsUnit a := by
  intro R _ A _ _ aug hI a ha
  obtain ⟨u, hu⟩ := ha
  obtain ⟨n, hn⟩ := hI
  set c : A := a * algebraMap R A (↑u⁻¹ : R) with hc
  have hker : c - 1 ∈ RingHom.ker aug := by
    rw [RingHom.mem_ker]
    simp only [hc, map_sub, map_mul, AlgHom.commutes, map_one, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← hu]
    simp
  have hnil : IsNilpotent (c - 1) := by
    refine ⟨n, ?_⟩
    have h1 : (c - 1) ^ n ∈ (RingHom.ker aug) ^ n := Ideal.pow_mem_pow hker n
    rw [hn] at h1
    simpa using h1
  have hcu : IsUnit c := by
    have := hnil.isUnit_one_add
    simpa using this
  exact isUnit_of_mul_isUnit_left hcu

end Bl.FirstBlockLemmaK
