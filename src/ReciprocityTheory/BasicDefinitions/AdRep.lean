module

public import Mathlib

@[expose] public section

section -- merged from ReciprocityTheory.BasicDefinitions.ExistsUnique
namespace ReciprocityTheory.Def

open IsLocalRing Matrix

universe u v w w'

class IsCNL (O : Type u) (A : Type w) [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] : Prop where
  noeth : IsNoetherianRing A
  complete : IsAdicComplete (maximalIdeal A) A
  localHom : IsLocalHom (algebraMap O A)
  resSurj : Function.Surjective fun x : O => residue A (algebraMap O A x)

attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom

structure Pattern (n : ℕ) where
  rel : Fin n → Fin n → Prop
  refl : ∀ i, rel i i
  trans : ∀ i j l, rel i j → rel j l → rel i l

namespace Pattern

variable {n : ℕ}

end Pattern

section Lift

variable (O : Type u) [CommRing O] [IsLocalRing O]
variable {G : Type v} [Group G] [TopologicalSpace G] {n : ℕ}

def push {A : Type w} {B : Type w'} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (f : A →ₐ[O] B)
    (ρ : G →* GL (Fin n) A) : G →* GL (Fin n) B :=
  (Matrix.GeneralLinearGroup.map f.toRingHom).comp ρ

end Lift

end ReciprocityTheory.Def
end

namespace ReciprocityTheory.Def

open Matrix

variable {k : Type*} [CommRing k] {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*} [AddCommGroup M] [Module k M]

def C1 (G : Type*) [TopologicalSpace G] (N : Submodule k M) : Submodule k (G → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g, c g ∈ N}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g => N.add_mem (ha.2 g) (hb.2 g)⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => N.zero_mem⟩
  smul_mem' := fun c x hx => ⟨hx.1.comp (fun m => c • m), fun g => N.smul_mem c (hx.2 g)⟩

def C2 (G : Type*) [TopologicalSpace G] (N : Submodule k M) : Submodule k (G × G → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ x, c x ∈ N}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g => N.add_mem (ha.2 g) (hb.2 g)⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, fun _ => N.zero_mem⟩
  smul_mem' := fun c x hx => ⟨hx.1.comp (fun m => c • m), fun g => N.smul_mem c (hx.2 g)⟩

def d0 (π : Representation k G M) : M →ₗ[k] (G → M) where
  toFun m := fun g => π g m - m
  map_add' := fun a b => by ext g; simp; abel
  map_smul' := fun c a => by ext g; simp [smul_sub]

def d1 (π : Representation k G M) : (G → M) →ₗ[k] (G × G → M) where
  toFun c := fun x => π x.1 (c x.2) - c (x.1 * x.2) + c x.1
  map_add' := fun a b => by ext x; simp; abel
  map_smul' := fun c a => by ext x; simp [smul_sub, smul_add]

def d2 (π : Representation k G M) : (G × G → M) →ₗ[k] (G × G × G → M) where
  toFun z := fun x => π x.1 (z (x.2.1, x.2.2)) - z (x.1 * x.2.1, x.2.2) + z (x.1, x.2.1 * x.2.2) - z (x.1, x.2.1)
  map_add' := fun a b => by ext x; simp; abel
  map_smul' := fun c a => by ext x; simp [smul_sub, smul_add]

def Z1 (π : Representation k G M) (N : Submodule k M) : Submodule k (G → M) :=
  C1 G N ⊓ LinearMap.ker (d1 π)

def B1 (π : Representation k G M) (N : Submodule k M) : Submodule k (G → M) := N.map (d0 π)

def Z2 (π : Representation k G M) (N : Submodule k M) : Submodule k (G × G → M) :=
  C2 G N ⊓ LinearMap.ker (d2 π)

def B2 (π : Representation k G M) (N : Submodule k M) : Submodule k (G × G → M) := (C1 G N).map (d1 π)

abbrev H1 (π : Representation k G M) (N : Submodule k M) : Type _ := Z1 π N ⧸ (B1 π N).submoduleOf (Z1 π N)

abbrev H2 (π : Representation k G M) (N : Submodule k M) : Type _ := Z2 π N ⧸ (B2 π N).submoduleOf (Z2 π N)

end ReciprocityTheory.Def
