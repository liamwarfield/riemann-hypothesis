module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CtrlDefs
noncomputable section

open IsLocalRing Matrix

namespace UpperTheory.V.Hi

def mIm (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] (k : ℕ) : Submodule O Ω :=
  Submodule.map (Algebra.linearMap O Ω) (maximalIdeal O ^ k)

theorem mem_mIm {O Ω : Type} [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] {k : ℕ} {w : Ω} :
    w ∈ mIm O Ω k ↔ ∃ x ∈ maximalIdeal O ^ k, algebraMap O Ω x = w := Iff.rfl

namespace Frame

variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {Ω : Type} [Field Ω]
  {O : Type} [CommRing O] [IsLocalRing O] [Algebra O Ω] (m : ℕ) (W : WtRep X.I O Ω)

def unt : Module.End Ω (Fin m → X.Fn Ω (W.d + 1)) where
  toFun F i g := ((W.ξ g.2)⁻¹).val *ᵥ F i g
  map_add' F F' := by ext i g k; simp only [Pi.add_apply, mulVec_add]
  map_smul' c F := by ext i g k; simp only [Pi.smul_apply, mulVec_smul, RingHom.id_apply]

theorem unt_apply (F : Fin m → X.Fn Ω (W.d + 1)) (i : Fin m) (g : Ga × Gp) :
    X.unt m W F i g = ((W.ξ g.2)⁻¹).val *ᵥ F i g := rfl

theorem ctrl_apply (F : Fin m → X.Fn Ω (W.d + 1)) (g : Ga × Gp) (i : Fin m) :
    X.ctrl m W F g i = X.unt m W F i g 0 := rfl

def Lat (Λ : Submodule O Ω) : Submodule O (Fin m → X.Fn Ω (W.d + 1)) where
  carrier := {F | ∀ i g k, X.unt m W F i g k ∈ Λ}
  add_mem' h h' i g k := by
    simpa only [map_add, Pi.add_apply] using Λ.add_mem (h i g k) (h' i g k)
  zero_mem' i g k := by rw [map_zero]; exact zero_mem _
  smul_mem' c F h i g k := by
    rw [LinearMap.map_smul_of_tower]; exact Λ.smul_mem c (h i g k)

theorem mem_lat (Λ : Submodule O Ω) (F : Fin m → X.Fn Ω (W.d + 1)) :
    F ∈ X.Lat m W Λ ↔ ∀ i g k, X.unt m W F i g k ∈ Λ := Iff.rfl


variable {m} in
abbrev ClO (τ : X.Ub →* GL (Fin m) O) (U : Subgroup X.Ub) (c : ℕ) (φ : X.I.T →* Oˣ) :
    Submodule Ω (Fin m → X.Fn Ω (W.d + 1)) :=
  X.Cl ((Matrix.GeneralLinearGroup.map (algebraMap O Ω)).comp τ) W.ξ U c ((Units.map (algebraMap O Ω).toMonoidHom).comp φ)

end Frame

end UpperTheory.V.Hi
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckeCommRing
noncomputable section

open IsLocalRing

namespace UpperTheory.V.Hi

variable {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M]

instance heckeCommRing (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] : CommRing (heckeAlg Y op) :=
  { (inferInstance : Ring (heckeAlg Y op)) with
    mul_comm := fun a b => by
      have key : {t : Module.End A Y | ∃ i, Restr t (op i)}.Pairwise Commute := by
        rintro s ⟨i, hi⟩ t ⟨j, hj⟩ _
        change s * t = t * s
        refine LinearMap.ext fun y => Subtype.ext ?_
        change (s (t y) : M) = t (s y)
        rw [hi, hj, hj, hi]
        exact h.out.2 i j y y.2
      exact (Algebra.isMulCommutative_adjoin A key).is_comm.comm a b }

def heckeGen (Y : Submodule A M) (op : ι → Module.End A M) [h : Fact (CommOn Y op)] (i : ι) : heckeAlg Y op :=
  ⟨(op i).restrict (h.out.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩

theorem IsCNL.ofCO (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R] [Algebra O R]
    [Alg.IsCO O R] : IsCNL R := by
  exact
    { complete := inferInstance
      finite := Finite.of_surjective (ResidueField.map (algebraMap O R))
        (Alg.resMap_bijective O R).2 }

end UpperTheory.V.Hi
end
end
