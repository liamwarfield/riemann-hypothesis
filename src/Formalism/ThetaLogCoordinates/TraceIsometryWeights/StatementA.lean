module

public import Mathlib

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.TraceIsometryWeights.DivStable
namespace Formalism.InvariantFactorPaths.PW

open Finset

section gen

variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]

def GlRel (E : ι → ι → Module.End K W) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def Om (E : ι → ι → Module.End K W) (S : Finset ι) (z : ι) : ℕ → Module.End K W
  | 0 => 1
  | q + 1 => ∑ i ∈ S, E z i * Om E S z q * E i z

def Pstep (E : ι → ι → Module.End K W) (S : Finset ι) (z : ι) (l : ℕ) : Module.End K W :=
  ∑ q ∈ range (l + 1),
    (((-1 : K) ^ q * (S.card.factorial : K)) / (((q + S.card).factorial : K) * (q.factorial : K))) • Om E S z q

def InvOp (E : ι → ι → Module.End K W) (l : ℕ) : List ι → Module.End K W
  | [] => 1
  | z :: L => Pstep E L.toFinset z l * InvOp E l L

def homAct {V : Type} [AddCommGroup V] [Module K V] (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W)
    (a b : ι) : Module.End K (V →ₗ[K] W) where
  toFun := fun φ => EW a b ∘ₗ φ - φ ∘ₗ EV a b
  map_add' := by
    intro φ ψ; ext x; simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _)]; abel
  map_smul' := by
    intro c φ; ext x
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply, smul_sub]

def DivStable (E : ι → ι → Module.End K W) (M : AddSubgroup W) : Prop :=
  ∀ a b, a ≠ b → ∀ k : ℕ, ∀ x ∈ M, ((k.factorial : K))⁻¹ • ((E a b) ^ k) x ∈ M

def HomLat {V : Type} [AddCommGroup V] [Module K V] (L : AddSubgroup V) (M : AddSubgroup W) :
    AddSubgroup (V →ₗ[K] W) where
  carrier := {φ | ∀ x ∈ L, φ x ∈ M}
  add_mem' := fun {φ ψ} hφ hψ x hx => by rw [LinearMap.add_apply]; exact M.add_mem (hφ x hx) (hψ x hx)
  zero_mem' := fun x _ => by rw [LinearMap.zero_apply]; exact M.zero_mem
  neg_mem' := fun {φ} hφ x hx => by rw [LinearMap.neg_apply]; exact M.neg_mem (hφ x hx)

end gen

def ZpClosed (p : ℕ) [Fact p.Prime] {W : Type} [AddCommGroup W] [Module ℚ_[p] W] (M : AddSubgroup W) : Prop :=
  ∀ c : ℚ_[p], ‖c‖ ≤ 1 → ∀ x ∈ M, c • x ∈ M

end Formalism.InvariantFactorPaths.PW
end

namespace Formalism.InvariantFactorPaths.PW

open Finset

def InvInv : Prop :=
  ∀ (K W ι : Type) [Field K] [CharZero K] [AddCommGroup W] [Module K W] [DecidableEq ι]
    (E : ι → ι → Module.End K W), GlRel E → ∀ (l : ℕ) (NN : Submodule K W),
    (∀ a b, ∀ x ∈ NN, E a b x ∈ NN) →
    (∀ (z : ι) (k : ℤ), ∀ x ∈ NN, E z z x = (k : K) • x → (l : ℤ) < |k| → x = 0) →
    ∀ L : List ι, L.Nodup → ∀ u ∈ NN, (∀ a ∈ L, E a a u = 0) →
      (∀ a ∈ L, ∀ b ∈ L, E a b (InvOp E l L u) = 0) ∧ InvOp E l L u ∈ NN ∧
      InvOp E l L u - u ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b)

def InvNat : Prop :=
  ∀ (K W W' ι : Type) [Field K] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W'] [DecidableEq ι]
    (E : ι → ι → Module.End K W) (E' : ι → ι → Module.End K W') (θ : W →ₗ[K] W'),
    (∀ a b x, θ (E a b x) = E' a b (θ x)) → ∀ (l : ℕ) (L : List ι) (x : W),
      θ (InvOp E l L x) = InvOp E' l L (θ x)

def InvInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (W ι : Type) [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]
    (E : ι → ι → Module.End ℚ_[p] W), GlRel E → ∀ (M : AddSubgroup W), ZpClosed p M → DivStable E M →
    ∀ (l : ℕ) (L : List ι), L.Nodup → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (L.length.choose 2 * Nat.log p (l + L.length - 1))) • InvOp E l L u ∈ M

def HomRel : Prop :=
  ∀ (K V W ι : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [DecidableEq ι]
    (EV : ι → ι → Module.End K V) (EW : ι → ι → Module.End K W), GlRel EV → GlRel EW → GlRel (homAct EV EW)

def HomDiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (V W ι : Type) [AddCommGroup V] [Module ℚ_[p] V] [AddCommGroup W] [Module ℚ_[p] W]
    [DecidableEq ι] (EV : ι → ι → Module.End ℚ_[p] V) (EW : ι → ι → Module.End ℚ_[p] W)
    (L : AddSubgroup V) (M : AddSubgroup W), ZpClosed p M → DivStable EV L → DivStable EW M →
      ZpClosed p (HomLat (K := ℚ_[p]) L M) ∧ DivStable (homAct EV EW) (HomLat (K := ℚ_[p]) L M)

def HomTrace : Prop :=
  ∀ (K V ι : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [DecidableEq ι]
    (EV : ι → ι → Module.End K V) (ψ : V →ₗ[K] V),
    ψ ∈ (⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (homAct EV EV a b)) → LinearMap.trace K V ψ = 0

end Formalism.InvariantFactorPaths.PW
