module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.RootMeasBig

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.BetaLUniq
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PI.BetaLUniq

abbrev Lt (D : D7) : Type := Submodule (𝓞 D.host.E) (hS D).V

abbrev Fl (D : D7) (T : ℕ) : Type := LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)

end PI.BetaLUniq

namespace PI


open PI.BetaLUniq in
def BetaLUniq : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word),
  ∀ (Λ : Lt D) (F : Fl D (Tu D u)) (F' F'' : Fl D (Tu D u')) (β₁ β₂ : (hS D).V ≃ₗ[D.host.E] (hS D).V),
    FixedHyp D Λ F → IsTerm Λ (gS D) F F' → IsTerm Λ (gS D) F F'' → IsGeneric Λ (gS D) F F' → IsGeneric Λ (gS D) F F'' →
    IsPair Λ F F' F'' β₁ (gS D) → IsPair Λ F F' F'' β₂ (gS D) →
    Lat.s0 Λ F F' F'' β₁ D.R.k = 1 → Lat.s0 Λ F F' F'' β₂ D.R.k = 1 →
      ∀ x ∈ orth (hS D) (Xsp F'), β₂ x - β₁ x ∈ Xsp F''

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.PairCorankPos
noncomputable section

open scoped Classical

namespace PI.PairCorankPos

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

def CorankPosG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r k : ℕ),
    finrank E S.V = k + 2 * r + 1 →
    ∀ Λ : Submodule (𝓞 E) S.V, Submodule.IsFullLattice E Λ →
    ∀ (T T' : E) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V),
      IsLift Λ F → IsLift Λ F' → Gval F F' ≠ 0 → 1 ≤ Formalism.MainNotions.S.Lat.s0 Λ F F' F'' β k

end PI.PairCorankPos
end
end

section -- merged from Formalism.PeriodIntegrals.AmpRoot
open MeasureTheory
open scoped ENNReal

noncomputable section

namespace PI.AmpRoot

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def RootJac : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (μ₀ : Measure (Mt k r)), IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ →
    μ₀ {x | Matrix.of x ∉ Rset k r g₀} = 0 →
    μ₀.map (rootCoords k r L.z' p) = ENNReal.ofReal ((‖L.c‖ / (2 * Real.pi)) ^ (rootPat p).card) • volume →
    IsRootMeas L p g₀ (μ₀.map (fun x => fun i j => (g₀ * Matrix.of x * g₀⁻¹) i j))

def RelAtPt : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (p : Point ℂ (r + 1)) (g₀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    star L.c = L.c → IsPtRepO L p g₀ → 0 < Gf k r L.z L.z' g₀ → IsRelStab L g₀

end PI.AmpRoot
end
end
