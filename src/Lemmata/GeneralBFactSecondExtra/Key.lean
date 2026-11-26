module

public import Mathlib

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact_second'''

private lemma key {O : Type*} {Y : Type*} [CommRing O] [AddCommGroup Y] [Module O Y]
    (R S D E : Submodule O Y) (hD : ∀ y, y ∈ D ↔ y ∈ R ∧ y ∈ S) (hE : E ≤ D) :
    Module.length O (R ⧸ E.comap R.subtype) =
      Module.length O (R ⧸ S.comap R.subtype) + Module.length O (D ⧸ E.comap D.subtype) := by
  have hDR : D ≤ R := fun y hy => ((hD y).1 hy).1
  have hES : E.comap R.subtype ≤ (S.comap R.subtype).comap LinearMap.id :=
    fun x hx => ((hD x).1 (hE hx)).2
  have hEE : E.comap D.subtype ≤ (E.comap R.subtype).comap (Submodule.inclusion hDR) :=
    fun x hx => hx
  let f := Submodule.mapQ (E.comap D.subtype) (E.comap R.subtype) (Submodule.inclusion hDR) hEE
  let g := Submodule.mapQ (E.comap R.subtype) (S.comap R.subtype) LinearMap.id hES
  rw [add_comm]
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · refine (injective_iff_map_eq_zero f).2 ?_
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx ⊢
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      simp only [g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      have hyD : (y : Y) ∈ D := (hD y).2 ⟨y.2, hy⟩
      exact ⟨Submodule.Quotient.mk ⟨y, hyD⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      simp only [f, g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ((hD x).1 x.2).2

theorem goal1 :
    ∀ {O : Type u_1} {Y : Type u_2} [inst : CommRing O] [inst_1 : AddCommGroup Y]
      [inst_2 : _root_.Module O Y] (R S D E : Submodule O Y),
      (∀ (y : Y), y ∈ D ↔ y ∈ R ∧ y ∈ S) →
        E ≤ D →
          Module.length O (↥R ⧸ Submodule.comap R.subtype E) =
            Module.length O (↥R ⧸ Submodule.comap R.subtype S) +
              Module.length O (↥D ⧸ Submodule.comap D.subtype E) := by
  intro O Y _ _ _ R S D E hD hE
  exact key R S D E hD hE

end Bl.general_b_fact_second'''
