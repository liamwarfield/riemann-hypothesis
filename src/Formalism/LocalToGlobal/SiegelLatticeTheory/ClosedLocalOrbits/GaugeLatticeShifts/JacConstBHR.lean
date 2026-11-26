module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfD

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR
noncomputable section

open MeasureTheory Filter Topology Classical
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

def rhoS (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (x : Mt k r) : ℝ≥0∞ :=
  ⨅ (Y : Formalism.MainNotions.S.lieE S)
    (_ : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x),
    (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)

def Qf (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : ℝ≥0∞ :=
  rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + rhoS k r (Formalism.FourierDecayAlt.B2.UWb k r) m ^ 2 +
    rhoS k r (Nset k r) n' ^ 2

def Psi (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : Mt k r :=
  fun i j => (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) i j

def Sandwich : Prop :=
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ Formalism.FourierDecayAlt.B2.UWb k r →
      Matrix.of n' ∈ Nset k r →
      (Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)) ∧
      (Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ)

def Vol (k r : ℕ) (μb : Measure (Mt k r)) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (Formalism.FourierDecayAlt.B2.cWeight k r c) *
    ∫⁻ n, ∫⁻ m, ∫⁻ n', (if Qf k r n c m n' < ENNReal.ofReal (s ^ 2) then (1 : ℝ≥0∞) else 0)
      ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1) ∂μb ∂(Formalism.MainNotions.S.haarLie (Nset k r) 1)

def VolLim : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    Tendsto (fun s : ℝ => (Vol k r μb s).toReal / gVol k r s) (𝓝[>] 0) (𝓝 ((2 : ℝ) ^ r)⁻¹)

end Formalism.L2.SG.Pf.BH
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGEB
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB

def RhsHaar : Prop :=
  ∀ (k r : ℕ) (μb : Measure (Mt k r)), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μb →
    ∃ ν : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) ν ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂ν = rhs k r μb φ

def RhsWHaar : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ) μsec,
    WbData k r z z' μW μW' a a' μsec →
    ∃ ν : Measure (Mt k r), Formalism.MainNotions.S.IsHaarOn (Formalism.FourierDecayAlt.B2.UWb k r) ν ∧
      ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ x, φ x ∂ν = rhsW k r z z' μW μW' μsec φ

def WbDataEx : Prop :=
  ∀ k r : ℕ, 1 ≤ k → ∃ (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), WbData k r z z' μW μW' a a' μsec

def ExistsGaugeMeasureForEachRank : Prop := ∀ r : ℕ, ∃ μ : Measure (Mt 0 r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb 0 r) μ

end Formalism.L2.SG.Pf.GE
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfE
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

def IotaG (q : E) (abelian₂ : Submodule M.L.O V) {r : ℕ} (f₀ f₁ f₂ : Fin (r + 1) → V) (e : V ≃ₗ[E] V) : Prop :=
  (∀ x x' : V, x ∈ abelian₂ → x' ∈ abelian₂ → x ∈ H.perp (H.X f₀) → x' ∈ H.perp (H.X f₁) → x - x' ∈ H.smulLat q abelian₂ →
    ∃ y y'' : V, y ∈ abelian₂ ∧ y'' ∈ abelian₂ ∧ y ∈ H.perp (H.X f₀) ∧ y'' ∈ H.perp (H.X f₂) ∧ x - y ∈ H.X f₀ ∧
      e x' - y'' ∈ H.X f₂ ∧ y - y'' ∈ H.smulLat q abelian₂) ∧
  (∀ x x'' : V, x ∈ abelian₂ → x'' ∈ abelian₂ → x ∈ H.perp (H.X f₀) → x'' ∈ H.perp (H.X f₂) →
    x - x'' ∈ H.smulLat q abelian₂ →
    ∃ y y' : V, y ∈ abelian₂ ∧ y' ∈ abelian₂ ∧ y ∈ H.perp (H.X f₀) ∧ y' ∈ H.perp (H.X f₁) ∧ x - y ∈ H.X f₀ ∧
      e.symm x'' - y' ∈ H.X f₁ ∧ y - y' ∈ H.smulLat q abelian₂)

end Generic

end Formalism.L2.SG.Pf.ScalarFramePf
end
end
