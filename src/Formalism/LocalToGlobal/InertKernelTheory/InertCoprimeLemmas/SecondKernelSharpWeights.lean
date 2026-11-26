module

public import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

@[expose] public section

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.DefsSharp
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSharpWeights

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

end Gen

def SharpWtIs : Prop :=
  ∀ (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ), j < D.R.m →
    ∀ (τ : D.what₂.Tau) (r : Fin (D.R.N j)),
      ((((nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ : ℤ)) : ℚ) =
        ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2

end Formalism.L2.KerInert.SecondKernelSharpWeights
end
end

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSharpWeights

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

theorem sharp_weight_formula : SharpWtIs := by
  intro D Tw u μ j hj τ r
  have h1 := (nu_t_identity D u j hj τ r).1
  have h2 := (D.chTw u μ).sSharp_eq j hj τ
  have h3 := (Tw.fm u μ).lam_eq j hj.le τ r
  have h2' : (((D.chTw u μ).sSharp j τ : ℤ) : ℝ) =
      (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) + ((j : ℝ) + 1) * ((D.R.t : ℝ) + 1)) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h2
    simp only [sExp', Ranks.N] at this
    push_cast at this
    exact this
  have he : ∀ (k : ℕ) (hk : k < D.R.m), k = j → (D.hc τ).e ⟨k, hk⟩ = (D.hcW u τ).e ⟨j, hj⟩ := by
    rintro k hk rfl; rw [D.hcW_e]
  apply Rat.cast_injective (α := ℝ)
  have hw : ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℝ) = (((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  push_cast
  rw [h1, h2', hw, h3]
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dite_eq_left (show 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m by omega), he _ _ (by omega)]
  simp only [Ranks.N]
  by_cases hr : r.1 < D.R.k
  · rw [dite_eq_left hr, dite_eq_left hr]
    simp only [hcToWeightQ, rhoVec]
    push_cast
    ring
  · have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by
      have := D.R.blk_lt hj.le r hr
      omega
    rw [dite_eq_right hr, dite_eq_right hr, dite_eq_left hb]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hrk : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + (D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1) := by omega
      exact_mod_cast this
    simp only [wG]
    push_cast
    rw [hrk]
    ring

end Formalism.L2.KerInert.SecondKernelSharpWeights
