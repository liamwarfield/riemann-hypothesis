module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.LatSizeCont
noncomputable section

namespace PI.LatSizeCont

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace Size

variable (I : Formalism.MainNotions.S.AutInst)

def latSet (x : I.GA) : Set (Fin I.n → I.E) :=
  {u | (I.fmat x.2⁻¹) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf}

end Size

end PI.LatSizeCont
end
end

noncomputable section

open NumberField Matrix
open PI.LatSizeCont

namespace PI.UnitaryGroupMassFormula.LSC

def nsq {n : ℕ} (w : Fin n → ℂ) : ℝ := ∑ i, ‖w i‖ ^ 2

def LatIs : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), ∃ Λ : Submodule (𝓞 I.E) (Fin I.n → I.E), Λ.FG ∧
    Submodule.span I.E (Λ : Set (Fin I.n → I.E)) = ⊤ ∧ Size.latSet I x = (Λ : Set (Fin I.n → I.E))

def DetMono : Prop :=
  ∀ (n j : ℕ) (C : Matrix (Fin n) (Fin j) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (κ : ℝ), 0 ≤ κ →
    (∀ w : Fin n → ℂ, nsq (M *ᵥ w) ≤ κ * nsq w) →
    0 ≤ ((Cᴴ * C).det).re ∧ (((M * C)ᴴ * (M * C)).det).re ≤ κ ^ j * ((Cᴴ * C).det).re

def NormProd : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (m : I.E), ∏ v : InfinitePlace I.F, ‖I.φ v m‖ ^ 2 = |((Algebra.norm ℚ m : ℚ) : ℝ)|

end PI.UnitaryGroupMassFormula.LSC
