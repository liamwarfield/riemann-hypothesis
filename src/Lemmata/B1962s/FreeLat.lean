module

public import Mathlib

@[expose] public section

noncomputable def Bl.FreeLattices.FreeLat :
    Prop:=
    ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (σ : Type) (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
      (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
      FiniteDimensional ℚ_[p] ↥W →
        (∀ x ∈ L, x ∈ W) →
          L.FG →
            ∃ (m : ℕ) (f : Fin m → MvPolynomial σ ℚ_[p]),
              (∀ (a : Fin m), f a ∈ L) ∧
                LinearIndependent ℤ_[p] f ∧ Submodule.span ℤ_[p] (Set.range f) = L

namespace Bl.FreeLattices

private theorem tf (p : Nat) [Fact (Nat.Prime p)] (σ : Type) :
    Module.IsTorsionFree (PadicInt p) (MvPolynomial σ (Padic p)) := by
  refine Module.IsTorsionFree.comap (S := Padic p) (algebraMap (PadicInt p) (Padic p)) ?_ ?_
  · intro r hr
    have h0 : r ≠ 0 := hr.ne_zero
    have h1 : algebraMap (PadicInt p) (Padic p) r ≠ 0 := by
      simpa using h0
    exact IsRegular.of_ne_zero h1
  · intro r m
    exact algebraMap_smul (Padic p) r m

theorem goal1 :
  Bl.FreeLattices.FreeLat := by
  intro p _ σ L W _ _ hL
  have := tf p σ
  have : Module.Finite (PadicInt p) L := Module.Finite.iff_fg.mpr hL
  let b := Module.finBasis (PadicInt p) L
  refine ⟨Module.finrank (PadicInt p) L, fun i => (b i : MvPolynomial σ (Padic p)), ?_, ?_, ?_⟩
  · intro a
    exact (b a).2
  · exact b.linearIndependent.map' L.subtype L.ker_subtype
  · have h := congrArg (Submodule.map L.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
    exact h

end Bl.FreeLattices
