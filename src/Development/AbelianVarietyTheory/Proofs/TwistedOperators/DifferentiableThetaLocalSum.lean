module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

noncomputable section

namespace GlobalTheory.RatMoveFock

section SlopeTestRemainingChoices

open Matrix

variable {D : D7}

private def NormOne {F : Type} [NormedField F] (lam : Qbar →+* F) (x : ℂ) : Prop := ∃ h : x ∈ Qbar, ‖lam ⟨x, h⟩‖ = 1

section
variable {F : Type} [NormedField F] {lam : Qbar →+* F}

private theorem NormOne.of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (hx : NormOne lam (x ^ n)) : NormOne lam x := by
  obtain ⟨h1, h2⟩ := hx
  have h3 : x ∈ Qbar := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 h1))
  refine ⟨h3, ?_⟩
  rw [show (⟨x ^ n, h1⟩ : Qbar) = ⟨x, h3⟩ ^ n from rfl, map_pow, norm_pow] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

end

end SlopeTestRemainingChoices

open Matrix GlobalTheory.AdForm.RatMove
open scoped ComplexOrder

variable {D : D7}

end GlobalTheory.RatMoveFock

end
