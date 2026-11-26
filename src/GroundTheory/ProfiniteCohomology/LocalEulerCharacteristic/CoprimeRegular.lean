module

public import Mathlib

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CoprimeRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Representation TensorProduct

section Regular

variable {k Γ N : Type*} [CommRing k] [Group Γ] [Fintype Γ] [DecidableEq Γ] [AddCommGroup N]
  [Module k N] (σ : Representation k Γ N)

noncomputable def regularTensorEquiv : MonoidAlgebra k Γ ⊗[k] N ≃ₗ[k] (Γ →₀ N) :=
  TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k) (LinearEquiv.refl k N) ≪≫ₗ
    finsuppScalarLeft k N Γ

omit [Group Γ] [Fintype Γ] in
theorem regularTensorEquiv_single_tmul (g : Γ) (r : k) (n : N) :
    regularTensorEquiv (MonoidAlgebra.single g r ⊗ₜ[k] n) = Finsupp.single g (r • n) := by
  ext γ
  simp only [regularTensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul]
  rw [finsuppScalarLeft_apply_tmul_apply]
  simp [Finsupp.single_apply]


omit [Fintype Γ] in
theorem regularTensorEquiv_tprod_apply (h : Γ) (x : MonoidAlgebra k Γ ⊗[k] N) (γ : Γ) :
    regularTensorEquiv (((leftRegular k Γ).tprod σ) h x) γ =
      σ h (regularTensorEquiv x (h⁻¹ * γ)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul p n =>
    induction p using MonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq =>
      rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), Finsupp.add_apply, hp, hq, map_add (f := _),
        Finsupp.add_apply, map_add]
    | single g r =>
      rw [Representation.tprod_apply, TensorProduct.map_tmul, ofMulAction_single, regularTensorEquiv_single_tmul,
        regularTensorEquiv_single_tmul, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases hg : h * g = γ
      · subst hg
        simp
      · have : ¬ g = h⁻¹ * γ := fun e => hg (by rw [e, mul_inv_cancel_left])
        simp [hg, this]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, hx, hy, map_add (f := _), Finsupp.add_apply, map_add (f := _)]

omit [Fintype Γ] in
theorem mem_invariants_regular_iff (x : MonoidAlgebra k Γ ⊗[k] N) :
    x ∈ ((leftRegular k Γ).tprod σ).invariants ↔
      ∀ γ, regularTensorEquiv x γ = σ γ (regularTensorEquiv x 1) := by
  rw [mem_invariants]
  constructor
  · intro hx γ
    conv_lhs => rw [← hx γ]
    rw [regularTensorEquiv_tprod_apply, inv_mul_cancel]
  · intro hx h
    apply regularTensorEquiv.injective
    ext γ
    rw [regularTensorEquiv_tprod_apply, hx (h⁻¹ * γ), hx γ, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel_left]

noncomputable def regularInvariantOf : N →ₗ[k] MonoidAlgebra k Γ ⊗[k] N :=
  regularTensorEquiv.symm.toLinearMap ∘ₗ (Finsupp.linearEquivFunOnFinite k N Γ).symm.toLinearMap ∘ₗ
    LinearMap.pi fun γ => σ γ

theorem regularTensorEquiv_regularInvariantOf (n : N) (γ : Γ) :
    regularTensorEquiv (regularInvariantOf σ n) γ = σ γ n := by
  simp [regularInvariantOf]

theorem regularInvariantOf_mem (n : N) :
    regularInvariantOf σ n ∈ ((leftRegular k Γ).tprod σ).invariants := by
  rw [mem_invariants_regular_iff]
  intro γ
  rw [regularTensorEquiv_regularInvariantOf, regularTensorEquiv_regularInvariantOf, map_one,
    Module.End.one_apply]

noncomputable def invariantsLeftRegularTensorEquiv :
    ((leftRegular k Γ).tprod σ).invariants ≃ₗ[k] N where
  toFun x := regularTensorEquiv (x : MonoidAlgebra k Γ ⊗[k] N) 1
  map_add' x y := by simp
  map_smul' c x := by simp
  invFun n := ⟨regularInvariantOf σ n, regularInvariantOf_mem σ n⟩
  left_inv x := by
    apply Subtype.ext
    apply regularTensorEquiv.injective
    ext γ
    simp only
    rw [regularTensorEquiv_regularInvariantOf, ← (mem_invariants_regular_iff σ _).1 x.2 γ]
  right_inv n := by
    simp only
    rw [regularTensorEquiv_regularInvariantOf, map_one, Module.End.one_apply]

theorem finrank_invariants_leftRegular_tprod :
    Module.finrank k ((leftRegular k Γ).tprod σ).invariants = Module.finrank k N :=
  (invariantsLeftRegularTensorEquiv σ).finrank_eq

end Regular

section Comp

variable {k Γ₁ Γ₂ X : Type*} [CommRing k] [Group Γ₁] [Group Γ₂] [AddCommGroup X] [Module k X]

theorem invariants_comp_of_surjective (ρ : Representation k Γ₁ X) (e : Γ₂ →* Γ₁)
    (he : Function.Surjective e) :
    Representation.invariants (ρ.comp e) = ρ.invariants := by
  ext x
  simp only [mem_invariants]
  exact ⟨fun h γ => by obtain ⟨δ, rfl⟩ := he γ; exact h δ, fun h δ => h (e δ)⟩

end Comp

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

universe u v

open Representation

abbrev TorsN (A : Type*) [AddCommGroup A] (n : ℕ) : Type _ :=
  ↥(LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)))

theorem mem_ker_lsmul_iff {A : Type*} [AddCommGroup A] (n : ℕ) (x : A) :
    x ∈ LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)) ↔ n • x = 0 := by
  simp

theorem TorsN.nsmul_eq_zero {A : Type*} [AddCommGroup A] {n : ℕ} (x : TorsN A n) :
    n • x = 0 :=
  Subtype.ext (by simpa using (mem_ker_lsmul_iff n (x : A)).1 x.2)

instance TorsN.instModule (A : Type*) [AddCommGroup A] (n : ℕ) : Module (ZMod n) (TorsN A n) :=
  AddCommGroup.zmodModule TorsN.nsmul_eq_zero

instance additiveDistribMulAction {Γ M : Type*} [Monoid Γ] [Monoid M] [MulDistribMulAction Γ M] :
    DistribMulAction Γ (Additive M) where
  smul γ a := Additive.ofMul (γ • a.toMul)
  one_smul a := congrArg Additive.ofMul (one_smul Γ a.toMul)
  mul_smul γ δ a := congrArg Additive.ofMul (mul_smul γ δ a.toMul)
  smul_zero γ := congrArg Additive.ofMul (smul_one γ)
  smul_add γ a b := congrArg Additive.ofMul (smul_mul' γ a.toMul b.toMul)

section Rep

def piRep {k Γ X : Type*} [CommSemiring k] [Monoid Γ] [AddCommMonoid X] [Module k X] (ι : Type*)
    (ρ : Representation k Γ X) : Representation k Γ (ι → X) where
  toFun γ := LinearMap.pi fun i => ρ γ ∘ₗ LinearMap.proj i
  map_one' := by ext; simp
  map_mul' γ δ := by ext; simp

@[simp]
theorem piRep_apply {k Γ X : Type*} [CommSemiring k] [Monoid Γ] [AddCommMonoid X] [Module k X]
    (ι : Type*) (ρ : Representation k Γ X) (γ : Γ) (x : ι → X) (i : ι) :
    piRep ι ρ γ x i = ρ γ (x i) :=
  rfl

variable {Γ : Type*} [Group Γ]

def intRepToZMod (n : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod n) V]
    (ρ : Representation ℤ Γ V) : Representation (ZMod n) Γ V where
  toFun γ := (ρ γ).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

variable (Γ) (A : Type*) [AddCommGroup A] [DistribMulAction Γ A] (n : ℕ)

theorem range_lsmul_le_comap (γ : Γ) :
    LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.range (LinearMap.lsmul ℤ A (n : ℤ))).comap (ofDistribMulAction ℤ Γ A γ) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨γ • x, by simp⟩

theorem ker_lsmul_le_comap (γ : Γ) :
    LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ)) ≤
      (LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ))).comap (ofDistribMulAction ℤ Γ A γ) := by
  intro x hx
  simp only [LinearMap.mem_ker, LinearMap.lsmul_apply, Submodule.mem_comap,
    ofDistribMulAction_apply_apply] at hx ⊢
  rw [← smul_comm γ (n : ℤ) x, hx, smul_zero]

noncomputable def modNRep : Representation (ZMod n) Γ (ModN A n) :=
  intRepToZMod n ((ofDistribMulAction ℤ Γ A).quotient _ (range_lsmul_le_comap Γ A n))

def torsNRep : Representation (ZMod n) Γ (TorsN A n) :=
  intRepToZMod n ((ofDistribMulAction ℤ Γ A).subrepresentation _ (ker_lsmul_le_comap Γ A n))

@[simp]
theorem modNRep_mk (γ : Γ) (x : A) :
    modNRep Γ A n γ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ • x) :=
  rfl

end Rep

structure AdditiveFunction (l : ℕ) (Γ : Type v) [Group Γ] where

  toFun : ∀ (X : Type u) [AddCommGroup X] [Module (ZMod l) X] [Finite X],
    Representation (ZMod l) Γ X → ℤ

  additive : ∀ {X₁ X₂ X₃ : Type u} [AddCommGroup X₁] [Module (ZMod l) X₁] [Finite X₁]
    [AddCommGroup X₂] [Module (ZMod l) X₂] [Finite X₂]
    [AddCommGroup X₃] [Module (ZMod l) X₃] [Finite X₃]
    (ρ₁ : Representation (ZMod l) Γ X₁) (ρ₂ : Representation (ZMod l) Γ X₂)
    (ρ₃ : Representation (ZMod l) Γ X₃) (f : X₁ →ₗ[ZMod l] X₂) (g : X₂ →ₗ[ZMod l] X₃),
    ρ₁.IsIntertwiningMap ρ₂ f → ρ₂.IsIntertwiningMap ρ₃ g →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    toFun X₂ ρ₂ = toFun X₁ ρ₁ + toFun X₃ ρ₃

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

noncomputable def g (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] : ℤ :=
  open Classical in
  if h : Finite (ModN A l) ∧ Finite (TorsN A l) then
    haveI := h.1
    haveI := h.2
    d.toFun (ModN A l) (modNRep Γ A l) - d.toFun (TorsN A l) (torsNRep Γ A l)
  else 0

theorem g_eq (A : Type u) [AddCommGroup A] [DistribMulAction Γ A] [Finite (ModN A l)]
    [Finite (TorsN A l)] :
    d.g A = d.toFun (ModN A l) (modNRep Γ A l) - d.toFun (TorsN A l) (torsNRep Γ A l) := by
  rw [g, dite_eq_left ⟨‹_›, ‹_›⟩]

theorem g_of_not_finite (A : Type u) [AddCommGroup A] [DistribMulAction Γ A]
    (h : ¬ (Finite (ModN A l) ∧ Finite (TorsN A l))) : d.g A = 0 := by
  rw [g, dite_eq_right h]

noncomputable def one [NeZero l] : ℤ :=
  d.toFun (ULift.{u} (ZMod l)) (Representation.trivial (ZMod l) Γ (ULift.{u} (ZMod l)))

end AdditiveFunction

end GroundTheory.ProfCoh
end
