module

public import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HarishChandraLabels.SupportExistsOf

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ]

def IsIrr {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule ℂ V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤

def zIdem [Fintype Γ] (τ : FDRep ℂ Γ) : MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹))

def centralIdem [Fintype Γ] {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) :
    MonoidAlgebra ℂ Γ :=
  ∑ γ : Γ, MonoidAlgebra.single γ
    ((Module.finrank ℂ V : ℂ) / Fintype.card Γ * LinearMap.trace ℂ V (ρ γ⁻¹))

theorem zIdem_eq_centralIdem [Fintype Γ] (τ : FDRep ℂ Γ) : zIdem τ = centralIdem τ.ρ := rfl



end Gen

section GeneralLinearIntegers

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

abbrev IsCuspidal {ι : Type} [Fintype ι] [DecidableEq ι] (τ : FDRep ℂ (GL ι K)) : Prop :=
  Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal K τ



variable {K}



variable (K) in
def pm {ι : Type} [Fintype ι] [DecidableEq ι] (σ : Equiv.Perm ι) : GL ι K :=
  (Matrix.permMatrixHom (n := ι) (R := K)).toHomUnits σ


variable (K) in
def patSet {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) : Set (GL ι K) :=
  {u | ∀ i j, (i = j → (u : Matrix ι ι K) i j = 1) ∧ (i ≠ j → ¬ Φ i j → (u : Matrix ι ι K) i j = 0)}

def patChar {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → ι → K) (ψ₀ : AddChar K ℂ) (u : GL ι K) : ℂ :=
  ψ₀ (∑ i, ∑ j, E i j * (u : Matrix ι ι K) i j)


open Classical in
def wh {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : ι → ι → Prop) (E : ι → ι → K) (ψ₀ : AddChar K ℂ)
    (χ : GL ι K → ℂ) : ℂ :=
  by
    classical
    exact ((patSet (K := K) Φ).ncard : ℂ)⁻¹ * ∑ u, if u ∈ patSet (K := K) Φ then (patChar E ψ₀ u)⁻¹ * χ u else 0

def IsPat {ι : Type} (Φ : ι → ι → Prop) : Prop := (∀ i, ¬ Φ i i) ∧ ∀ i j k, Φ i j → Φ j k → Φ i k



variable (K) in
def cutE (N k : ℕ) (i j : Fin N) : K := if (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k then 1 else 0




end GeneralLinearIntegers

namespace Lq

end Lq

end ReciprocityTheory.Ty.Fin
end
end

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin.St

def SimpleIffIrr : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ ↔ IsIrr τ.ρ) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Nonempty (τ ≅ σ) ↔ ∃ e : τ ≃ₗ[ℂ] σ, ∀ γ v, e (τ.ρ γ v) = σ.ρ γ (e v)

def CentralIdemAct : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W), IsIrr ρ → IsIrr σ →
    σ.asAlgebraHom (centralIdem ρ) = (open Classical in if Nonempty (Representation.Equiv ρ σ) then 1 else 0)

def SepIrr : Prop :=
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (x : MonoidAlgebra ℂ Γ), (∀ τ : FDRep ℂ Γ, Simple τ → Representation.asAlgebraHom τ.ρ x = 0) → x = 0

def ZIdemFacts : Prop :=
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ), Simple τ → zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → Simple σ → ¬ Nonempty (τ ≅ σ) → zIdem τ * zIdem σ = 0) ∧
  (∀ (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ), Simple τ → Simple σ → Nonempty (τ ≅ σ) → Representation.asAlgebraHom σ.ρ (zIdem τ) = 1) ∧
  ∀ (Γ : Type) [Group Γ] [Fintype Γ] (I : Type) [Fintype I] (V : I → FDRep ℂ Γ), (∀ i, Simple (V i)) →
    (∀ i j, Nonempty (V i ≅ V j) → i = j) → (∀ W : FDRep ℂ Γ, Simple W → ∃ i, Nonempty (W ≅ V i)) → ∑ i, zIdem (V i) = 1

def CuspWh : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ) (τ : FDRep ℂ (GL (Fin d) K)), ψ₀ ≠ 1 → IsCuspidal K τ →
    (Module.finrank ℂ τ : ℂ) = wh (fun i j : Fin d => i < j) (cutE K d 0) ψ₀ τ.character *
      ∏ i ∈ Finset.Ico 1 d, ((Fintype.card K : ℂ) ^ i - 1)

end ReciprocityTheory.Ty.Fin.St
