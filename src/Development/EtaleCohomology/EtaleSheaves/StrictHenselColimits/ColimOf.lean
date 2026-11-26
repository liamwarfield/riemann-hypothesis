module

public import Development.EtaleCohomology.EtaleSheaves.StalkGermPf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.SHLocPf

namespace LateralTheory.E.ColimPf

def Absorb : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (O : CommRingCat.{0}) (f : A ⟶ O) (ψ : O →+* Ω), IE f ∧ ψ.comp f.hom = ι ∧
    (∀ x : O, ψ x ≠ 0 → IsUnit x) ∧
    ∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φ : B →+* Ω, φ.comp g.hom = ι →
      ∃ h : B ⟶ O, g ≫ h = f ∧ ψ.comp h.hom = φ

def Rigid : Prop := ∀ (A B O : CommRingCat.{0}) (Ω : Type) [Field Ω] (ψ : O →+* Ω) (g : A ⟶ B), Et g →
  (∀ x : O, ψ x ≠ 0 → IsUnit x) → ∀ (u v : B ⟶ O), g ≫ u = g ≫ v → ψ.comp u.hom = ψ.comp v.hom → u = v

def Descend : Prop := ∀ (A O : CommRingCat.{0}) (f : A ⟶ O), IE f →
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C],
  ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (d : B ⟶ O) (C' : CommRingCat.{0}) (e : B ⟶ C') (c : C' →+* C),
    Et g ∧ Et e ∧ g ≫ d = f ∧ c.comp e.hom = (algebraMap O C).comp d.hom ∧
    (∀ k : C' ⟶ O, e ≫ k = d → ∃ s : C →ₐ[O] O, s.toRingHom.comp c = k.hom) ∧
    (∀ (R : Type) [CommRing R] (α β : C →+* R), α.comp (algebraMap O C) = β.comp (algebraMap O C) →
      α.comp c = β.comp c → α = β)

theorem et_comp {A B C : CommRingCat.{0}} {g : A ⟶ B} {e : B ⟶ C} (hg : Et g) (he : Et e) : Et (g ≫ e) := by
  change (g ≫ e).hom.Etale
  rw [CommRingCat.hom_comp]
  exact RingHom.Etale.stableUnderComposition _ _ hg he

theorem Colim_of (hA : Absorb) (hR : Rigid) (hD : Descend) : Colim := by
  intro A Ω _ ι
  obtain ⟨O, f, ψ, hIE, hcomp, hloc, habs⟩ := hA A Ω ι
  refine ⟨O, f, ψ, hIE, hcomp, ?_⟩
  intro C _ _ _ χ hχ
  obtain ⟨B, g, d, C', e, c, hg, he, hgd, hce, hext, hgen⟩ := hD A O f hIE C
  have ce : ∀ y, c (e.hom y) = algebraMap O C (d.hom y) := fun y => DFunLike.congr_fun hce y
  have cχ : ∀ z, χ (algebraMap O C z) = ψ z := fun z => DFunLike.congr_fun hχ z
  have gd : ∀ x, d.hom (g.hom x) = f.hom x := fun x => by rw [← hgd]; rfl
  have hpt : (χ.comp c).comp (g ≫ e).hom = ι := by
    ext x
    simp only [RingHom.comp_apply, CommRingCat.hom_comp]
    rw [ce, cχ, gd, ← hcomp]; rfl
  obtain ⟨h, hh1, hh2⟩ := habs C' (g ≫ e) (et_comp hg he) (χ.comp c) hpt
  have hed : e ≫ h = d := by
    refine hR A B O Ω ψ g hg hloc (e ≫ h) d ?_ ?_
    · rw [← Category.assoc, hh1, hgd]
    · ext y
      have := DFunLike.congr_fun hh2 (e.hom y)
      simp only [RingHom.comp_apply, CommRingCat.hom_comp] at this ⊢
      rw [this, ce, cχ]
  obtain ⟨s, hs⟩ := hext h hed
  refine ⟨s, hgen Ω _ _ ?_ ?_⟩
  · ext x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
    rw [cχ]; rfl
  · ext y
    have h1 := DFunLike.congr_fun hs y
    have h2 := DFunLike.congr_fun hh2 y
    simp only [RingHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]

end LateralTheory.E.ColimPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits.EtaleLiftToStrictLocalRingUniqueOnResidueField
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut TensorProduct

namespace LateralTheory.E.ColimPf.RigidPf

theorem etale_lift_to_strict_local_ring_unique_on_residue_field : LateralTheory.E.ColimPf.Rigid := by
  intro A B O Ω _ ψ g hg hloc u v huv hψ
  let : Algebra A B := g.hom.toAlgebra
  let : Algebra A O := (g ≫ u).hom.toAlgebra
  have : Algebra.Etale A B := hg
  let u' : B →ₐ[A] O := { u.hom with commutes' := fun _ => rfl }
  have hv : ∀ a, v.hom (g.hom a) = (g ≫ u).hom a := fun a => by rw [huv]; rfl
  let v' : B →ₐ[A] O := { v.hom with commutes' := hv }
  obtain ⟨e, he, hsp⟩ : ∃ e, IsIdempotentElem e ∧ KaehlerDifferential.ideal A B = B ⊗[A] B ∙ e :=
    (Ideal.isIdempotentElem_iff_of_fg _ (KaehlerDifferential.ideal_fg A B)).mp <|
      (Ideal.cotangent_subsingleton_iff _).mp <| inferInstanceAs <| Subsingleton Ω[B⁄A]
  let w : B ⊗[A] B →ₐ[A] O := Algebra.TensorProduct.productMap u' v'
  have hψu : ∀ b, ψ (v.hom b) = ψ (u.hom b) := fun b => (DFunLike.congr_fun hψ b).symm
  have hpt : ∀ t : B ⊗[A] B, ψ (w t) = ψ (u.hom (Algebra.TensorProduct.lmul' A t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [w, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
      change ψ (u.hom x) * ψ (v.hom y) = ψ (u.hom x) * ψ (u.hom y)
      rw [hψu]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have he0 : e ∈ KaehlerDifferential.ideal A B := by rw [hsp]; exact Submodule.mem_span_singleton_self e
  have hwe : ψ (w e) = 0 := by
    rw [hpt]
    have : Algebra.TensorProduct.lmul' A e = 0 := he0
    rw [this, map_zero, map_zero]
  have hwe0 : w e = 0 := by
    have hu : IsUnit (1 - w e) := hloc _ (by rw [map_sub, map_one, hwe, sub_zero]; exact one_ne_zero)
    have hid : w e * (1 - w e) = 0 := by
      have := (he.map w).eq
      rw [mul_sub, mul_one, this, sub_self]
    simpa using (hu.mul_left_eq_zero).1 hid
  ext b
  have hb : b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ b ∈ KaehlerDifferential.ideal A B := by
    rw [KaehlerDifferential.ideal, RingHom.mem_ker, map_sub]
    simp
  rw [hsp] at hb
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hb
  have := congrArg w hr
  rw [smul_eq_mul, map_mul, hwe0, mul_zero, map_sub] at this
  simp only [w, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one, one_mul] at this
  exact sub_eq_zero.1 this.symm

end LateralTheory.E.ColimPf.RigidPf
end
end

namespace LateralTheory.E.ColimPf.Main

theorem Colim_of (hA : LateralTheory.E.ColimPf.Absorb) (hD : LateralTheory.E.ColimPf.Descend) : LateralTheory.E.SHLocPf.Colim :=
  LateralTheory.E.ColimPf.Colim_of hA LateralTheory.E.ColimPf.RigidPf.etale_lift_to_strict_local_ring_unique_on_residue_field hD

end LateralTheory.E.ColimPf.Main
