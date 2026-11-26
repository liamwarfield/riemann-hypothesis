module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def FinMu {r : ℕ} (X : Data E r) : Prop :=
  ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF ∧ muF X x0 FF < ⊤

def IsValBasisM {r δ m : ℕ} (X : Data E r) (xs : Fin m → Frame X.Ψ r) (t : Fin δ → Frame X.Ψ r → ℂ) :
    Prop :=
  (∀ v : Fin m → ℂ, ∃ a : Fin δ → ℂ, ∀ j, ∑ k, a k * t k (xs j) = v j) ∧
  ∀ a : Fin δ → ℂ, (∀ j, ∑ k, a k * t k (xs j) = 0) → a = 0

def leviO {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (g : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  leviM X g x0 z ξ

def leviRh {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re

def leviDens {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re

def InterpStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt Xa.Fp 0, ∀ j, F (Fl.xs j) = v j

def ModeHalfStatement {r : ℕ} (X : Data E r) : Prop :=
  ∀ (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) (ps : Frame X.Ψ r → ℝ) (a : ℝ), X.IsSec la F →
    cfwM X ps a → 0 ≤ a →
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ENNReal.ofReal (X.pnorm la F x) ≤ ENNReal.ofReal C *
        ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
          ENNReal.ofReal (Real.exp (ps (cpt X x z) / 2))) →
    ∀ ξ, X.IsIso ξ → ∀ ν : X.Ψ → ℝ, ∑ τ, ν τ < a → ∀ x ∈ X.dom, X.fj la ξ ν F x = 0

def InterpCStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + (1 + Xa.c1 / Xa.a1) * leviO X x0 Xa.ps0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    ModeHalfStatement X →
    ∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt Xa.Fp Xa.c1, ∀ j, F (Fl.xs j) = v j

def KronHolPsiStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X →
    ∀ ψ : Frame X.Ψ r → ℝ, IsInvFn X ψ →
    (∀ x0, IsOrth X x0 → ContDiffOn ℝ ∞ (fun z => ψ (cpt X x0 z)) (OmF X x0)) →
    (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 ψ z ξ) →
    (∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + leviO X x0 ψ z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ j, ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ)
      (P : Frame X.Ψ r → ℂ) (γ0 : GL (Fin r) E),
      IsOrth X x0 ∧ IsMetricW X Xa.Fp W ∧ WLower X Xa.Fp W ∧
      (∀ x ∈ X.dom, ENNReal.ofReal (Real.exp (-(phla X Xa.Fp x + ψ x))) ≤ W x) ∧
      4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X Xa.Fp P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ γ0 ∈ X.Γ ∧ P (lact γ0 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ γ0 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0

def VanS {r δ : ℕ} (X : Data E r) (xs : Fin δ → Frame X.Ψ r) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    (a : ℕ) (g : Frame X.Ψ r → ℂ) : Prop :=
  ∀ j, ∃ ρ : ℝ, 0 < ρ ∧
    ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖g (cpt X (xs j) z)‖ ^ 2 *
      (∑ k, ‖s k (cpt X (xs j) z)‖ ^ 2) ^ (-((a : ℝ) + (nd X : ℝ) - 1 / 2))) < ⊤

def DivCoreStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    (∀ P, X.IsBddSec (Xa.Fp + nd X • Xa.L) P → P ∈ X.SS (Xa.Fp + nd X • Xa.L)) →
    (∀ P, X.IsBddSec Xa.Fp P → P ∈ X.SS Xa.Fp) →
    (∀ P, X.IsBddSec (Xa.Fp + Xa.T • Xa.L) P → P ∈ X.SS (Xa.Fp + Xa.T • Xa.L)) →
    (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) →
    ∀ (δ : ℕ) (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsBddSec Xa.Fp (t k)) → IsValBasisM X Fl.xs t →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ →
      ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      VanS X Fl.xs Fl.s (Xa.T - nd X) (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x) →
      ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
          X.IsBddSec (Xa.Fp + nd X • Xa.L) (h α)) ∧
        ∀ x ∈ X.dom, f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x =
          ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * h α x

def DivStartStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    ∀ (δ : ℕ) (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsBddSec Xa.Fp (t k)) →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) f (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ →
      ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
      X.IsBddSec (Xa.Fp + Xa.T • Xa.L) (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x) ∧
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L)
        (fun x => f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x) (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤

def EtaStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 →
    ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ +
        leviO X x0 (fun x => (1 + Xa.c1 / Xa.a1) * Xa.ps0 x) z ξ

def WSk {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  open Classical in
  if x ∈ X.dom then
  ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x)) *
    ENNReal.ofReal (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ)) *
    ENNReal.ofReal ((∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) / ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))
  else 0

def weightFunctionOnFrames {r : ℕ} (X : Data E r) (Xa : ArchInM X) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-phla X (Xa.Fp + nd X • Xa.L) x))

def UpDivStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    ∀ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m →
      (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ x0, IsOrth X x0 →
    ∀ F : V (nd X) → ℂ, DifferentiableOn ℂ F (OmF X x0) → InAt X x0 (WSk X Xa Fl) bb F →
      ∃ H : (Fin (nd X) → ℕ) → V (nd X) → ℂ,
        (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
          DifferentiableOn ℂ (H α) (OmF X x0) ∧ InAt X x0 (weightFunctionOnFrames X Xa) bb (H α)) ∧
        ∀ z ∈ OmF X x0, F z = ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X),
          (∏ k, Fl.s k (cpt X x0 z) ^ α k) * H α z

def OntoWeightStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa), PropDisc X → FinMu X →
    ∀ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
      bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m →
      (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) →
    (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) →
    ∀ x0, IsOrth X x0 → ∀ FF, IsFundSet X x0 FF →
    ∃ (Ps : Frame X.Ψ r → ℝ) (g1 : V (nd X) → ℂ),
      IsMetricW X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) ∧ WLower X (Xa.Fp + Xa.T • Xa.L) (WSk X Xa Fl) ∧
      DifferentiableOn ℂ g1 (OmF X x0) ∧ (∃ z ∈ OmF X x0, g1 z ≠ 0) ∧
      ContDiffOn ℝ ∞ (fun z => Ps (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} ∧
      (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → WSk X Xa Fl (cpt X x0 z) = ENNReal.ofReal (Real.exp (-Ps (cpt X x0 z)))) ∧
      (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
        m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
          (leviV (nd X) (fun w => ((Ps (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re) ∧
      ∀ g : Frame X.Ψ r → ℂ, g ∈ X.SS (Xa.Fp + Xa.T • Xa.L) →
        ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g (cpt X x0 z) ^ 2 *
          (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ →
        VanS X Fl.xs Fl.s (Xa.T - nd X) g → InFF X x0 (WSk X Xa Fl) FF g

def LocalUnfoldBStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ FF, IsFundSet X x0 FF →
    ∀ x1 ∈ X.dom, ∃ ρ0 : ℝ, 0 < ρ0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ0 →
    IsOpen {x | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
      x = lact γ (rmul (cpt X x1 z') b)} ∧
    ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, G (lact γ x) = G x) →
      ∫⁻ z in FF ∩ {z | ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ,
          cpt X x0 z = lact γ (rmul (cpt X x1 z') b)}, G (cpt X x0 z) ∂muF X x0 ≤
        K * ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, G (cpt X x1 z)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfB
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

namespace ModeHalfB

open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def Nid (r : ℕ) : Fin r → Fin r → ℂ := fun a b => if a = b then 1 else 0

theorem chosenFrame_isOrthogonal (X : Data E r) : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2

private theorem sum_castLE_lemma {p0 : ℕ} (hp : p0 ≤ r) (f : Fin r → ℝ) :
    ∑ a : Fin p0, f (Fin.castLE hp a) = ∑ k : Fin r, if (k : ℕ) < p0 then f k else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hp a) ?_ ?_ ?_ ?_
  · intro a _
    simp [a.2]
  · intro a _ b _ h
    exact Fin.castLE_injective hp h
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact ⟨⟨k, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro a _
    rfl

theorem Ms_id (X : Data E r) (τ : X.Ψ) (v : Fin r → ℂ) :
    Ms X.p0 X.p0_le (Nid r) v = ∑ k, ‖v k‖ ^ 2 := by
  have hA : Ag X.p0 X.p0_le (Nid r) = 1 := by
    ext a b
    simp only [Ag, Matrix.of_apply, sf, cl, Nid, Matrix.one_apply]
    rw [Finset.sum_eq_single (Fin.castLE X.p0_le a)]
    · have hs : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by simp [sgn, a.2]
      by_cases hab : a = b
      · subst hab; simp [hs, sgn, a.2]
      · have : Fin.castLE X.p0_le a ≠ Fin.castLE X.p0_le b := fun h => hab (Fin.castLE_injective X.p0_le h)
        simp [hab, this]
    · intro k _ hk; simp [hk]
    · simp
  have hsf : ∀ c : Fin r, sf X.p0 v (cl (Nid r) c) = ((sgn X.p0 c : ℝ) : ℂ) * v c := by
    intro c
    simp only [sf, cl, Nid]
    rw [Finset.sum_eq_single c]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  have hin : (∑ a : Fin X.p0, ∑ b : Fin X.p0, sf X.p0 v (cl (Nid r) (Fin.castLE X.p0_le a)) *
      (1 : Matrix (Fin X.p0) (Fin X.p0) ℂ) a b * conj (sf X.p0 v (cl (Nid r) (Fin.castLE X.p0_le b)))) =
      ∑ a : Fin X.p0, ((Complex.normSq (v (Fin.castLE X.p0_le a)) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [Matrix.one_apply_eq, mul_one, hsf, map_mul, Complex.conj_ofReal]
      have : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by simp [sgn, a.2]
      rw [this]
      push_cast
      rw [one_mul, one_mul, Complex.mul_conj]
    · intro b _ hb
      rw [Matrix.one_apply_ne (Ne.symm hb), mul_zero, zero_mul]
    · simp
  have hvv : (sf X.p0 v v).re = ∑ k : Fin r, sgn X.p0 (k : ℕ) * Complex.normSq (v k) := by
    simp only [sf, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [Ms, hA, inv_one]
  rw [hin, hvv, Complex.re_sum]
  simp only [Complex.ofReal_re]
  rw [sum_castLE_lemma X.p0_le (fun k => Complex.normSq (v k)), Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [Complex.sq_norm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn]
  split_ifs <;> ring

theorem sf_smul_left (p0 : ℕ) (c : ℝ) (α β : Fin r → ℂ) :
    sf p0 ((c : ℂ) • α) β = c * sf p0 α β := by
  simp only [sf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sf_smul_right (p0 : ℕ) (c : ℝ) (α β : Fin r → ℂ) :
    sf p0 α ((c : ℂ) • β) = c * sf p0 α β := by
  simp only [sf, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem Ms_smul (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) (c : ℝ) (v : Fin r → ℂ) :
    Ms p0 hp N ((c : ℂ) • v) = c ^ 2 * Ms p0 hp N v := by
  have h1 : (∑ a : Fin p0, ∑ b : Fin p0, sf p0 ((c : ℂ) • v) (cl N (Fin.castLE hp a)) *
      (Ag p0 hp N)⁻¹ a b * conj (sf p0 ((c : ℂ) • v) (cl N (Fin.castLE hp b)))) =
      ((c ^ 2 : ℝ) : ℂ) * ∑ a : Fin p0, ∑ b : Fin p0, sf p0 v (cl N (Fin.castLE hp a)) *
        (Ag p0 hp N)⁻¹ a b * conj (sf p0 v (cl N (Fin.castLE hp b))) := by
    simp only [sf_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have h2 : sf p0 ((c : ℂ) • v) ((c : ℂ) • v) = ((c ^ 2 : ℝ) : ℂ) * sf p0 v v := by
    rw [sf_smul_left, sf_smul_right]
    push_cast
    ring
  simp only [Ms]
  rw [h1, h2, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

noncomputable def Mt (p0 : ℕ) (hp : p0 ≤ r) (q : (Fin r → ℂ) × (Fin r → Fin r → ℂ) × Matrix (Fin p0) (Fin p0) ℂ) : ℝ :=
  2 * (∑ a : Fin p0, ∑ b : Fin p0, sf p0 q.1 (cl q.2.1 (Fin.castLE hp a)) * q.2.2 a b *
    conj (sf p0 q.1 (cl q.2.1 (Fin.castLE hp b)))).re - (sf p0 q.1 q.1).re

private theorem continuous_sf {T : Type*} [TopologicalSpace T] (p0 : ℕ) {f g : T → Fin r → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => sf p0 (f x) (g x) := by
  simp only [sf]
  exact continuous_finsetSum _ fun k _ =>
    (continuous_const.mul ((continuous_apply k).comp hf)).mul
      (Complex.continuous_conj.comp ((continuous_apply k).comp hg))

theorem Mt_cont (p0 : ℕ) (hp : p0 ≤ r) : Continuous (Mt p0 hp) := by
  have hc : ∀ c : Fin r, Continuous fun q : (Fin r → ℂ) × (Fin r → Fin r → ℂ) ×
      Matrix (Fin p0) (Fin p0) ℂ => sf p0 q.1 (cl q.2.1 c) := fun c =>
    continuous_sf p0 continuous_fst
      (continuous_pi fun k => (continuous_apply c).comp ((continuous_apply k).comp continuous_snd.fst))
  unfold Mt
  exact (continuous_const.mul (Complex.continuous_re.comp (continuous_finsetSum _ fun a _ =>
    continuous_finsetSum _ fun b _ =>
      ((hc _).mul ((continuous_apply b).comp ((continuous_apply a).comp continuous_snd.snd))).mul
        (Complex.continuous_conj.comp (hc _))))).sub
    (Complex.continuous_re.comp (continuous_sf p0 continuous_fst continuous_fst))

theorem Ag_cont (p0 : ℕ) (hp : p0 ≤ r) : Continuous (Ag p0 hp) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [Ag, Matrix.of_apply]
  exact continuous_sf p0 (continuous_pi fun k => (continuous_apply _).comp (continuous_apply k))
    (continuous_pi fun k => (continuous_apply _).comp (continuous_apply k))

theorem Ag_Nid (p0 : ℕ) (hp : p0 ≤ r) : Ag p0 hp (Nid r) = 1 := by
  ext a b
  simp only [Ag, Matrix.of_apply, sf, cl, Nid, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.castLE hp a)]
  · have hs : sgn p0 ((Fin.castLE hp a : Fin r) : ℕ) = 1 := by simp [sgn, a.2]
    by_cases hab : a = b
    · subst hab; simp [hs, sgn, a.2]
    · have : Fin.castLE hp a ≠ Fin.castLE hp b := fun h => hab (Fin.castLE_injective hp h)
      simp [hab, this]
  · intro k _ hk; simp [hk]
  · simp

theorem Ms_contAt (p0 : ℕ) (hp : p0 ≤ r) (v0 : Fin r → ℂ) :
    ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ms p0 hp p.1 p.2) (Nid r, v0) := by
  have hinv : ContinuousAt (fun M : Matrix (Fin p0) (Fin p0) ℂ => M⁻¹) (Ag p0 hp (Nid r)) := by
    rw [Ag_Nid]
    apply continuousAt_matrix_inv
    rw [Matrix.det_one]
    have := NormedRing.inverse_continuousAt (1 : ℂˣ)
    rwa [Units.val_one] at this
  have hAg : ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ag p0 hp p.1) (Nid r, v0) :=
    ((Ag_cont p0 hp).comp continuous_fst).continuousAt
  have h1 : ContinuousAt (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) =>
      ((p.2, p.1, (Ag p0 hp p.1)⁻¹) : (Fin r → ℂ) × (Fin r → Fin r → ℂ) × Matrix (Fin p0) (Fin p0) ℂ))
      (Nid r, v0) :=
    continuous_snd.continuousAt.prodMk
      (continuous_fst.continuousAt.prodMk (ContinuousAt.comp_of_eq hinv hAg rfl))
  have heq : (fun p : (Fin r → Fin r → ℂ) × (Fin r → ℂ) => Ms p0 hp p.1 p.2) =
      fun p => Mt p0 hp (p.2, p.1, (Ag p0 hp p.1)⁻¹) := by
    funext p
    simp only [Ms, Mt]
  rw [heq]
  exact (Mt_cont p0 hp).continuousAt.comp h1

theorem Ms_zero (p0 : ℕ) (hp : p0 ≤ r) (N : Fin r → Fin r → ℂ) : Ms p0 hp N 0 = 0 := by
  simp [Ms, sf]

theorem Ms_unif (X : Data E r) (τ : X.Ψ) {κ : ℝ} (hκ : 1 < κ) :
    ∀ᶠ N in 𝓝 (Nid r), ∀ v : Fin r → ℂ, κ⁻¹ * ∑ k, ‖v k‖ ^ 2 ≤ Ms X.p0 X.p0_le N v ∧
      Ms X.p0 X.p0_le N v ≤ κ * ∑ k, ‖v k‖ ^ 2 := by
  set S : Set (Fin r → ℂ) := {v | ∑ k, ‖v k‖ ^ 2 = 1} with hS
  have hScont : Continuous fun v : Fin r → ℂ => ∑ k, ‖v k‖ ^ 2 :=
    continuous_finsetSum _ fun k _ => ((continuous_apply k).norm).pow 2
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded (isClosed_eq hScont continuous_const)
    refine (Metric.isBounded_closedBall (x := (0 : Fin r → ℂ)) (r := 1)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro k
    have h1 : ‖v k‖ ^ 2 ≤ 1 := by
      have hv' : ∑ k, ‖v k‖ ^ 2 = 1 := hv
      rw [← hv']
      exact Finset.single_le_sum (f := fun k => ‖v k‖ ^ 2) (fun i _ => sq_nonneg _)
        (Finset.mem_univ k)
    nlinarith [norm_nonneg (v k)]
  have hev : ∀ᶠ N in 𝓝 (Nid r), ∀ v ∈ S,
      κ⁻¹ < Ms X.p0 X.p0_le N v ∧ Ms X.p0 X.p0_le N v < κ := by
    apply hSc.eventually_forall_of_forall_eventually
    intro v0 hv0
    have hc := Ms_contAt X.p0 X.p0_le v0
    have hval : Ms X.p0 X.p0_le (Nid r) v0 = 1 := by
      rw [Ms_id X τ]
      exact hv0
    have hmem : Set.Ioo κ⁻¹ κ ∈ 𝓝 (Ms X.p0 X.p0_le (Nid r) v0) := by
      rw [hval]
      exact Ioo_mem_nhds (inv_lt_one_of_one_lt₀ hκ) hκ
    filter_upwards [hc.preimage_mem_nhds hmem] with p hp
    exact hp
  filter_upwards [hev] with N hN
  intro v
  by_cases hv : ∑ k, ‖v k‖ ^ 2 = 0
  · have hv0 : v = 0 := by
      funext k
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖v i‖)).mp hv k
        (Finset.mem_univ k)
      simpa using h
    subst hv0
    simp [Ms_zero]
  · have hpos : 0 < ∑ k, ‖v k‖ ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hv)
    set s := Real.sqrt (∑ k, ‖v k‖ ^ 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hpos
    have hss : s ^ 2 = ∑ k, ‖v k‖ ^ 2 := Real.sq_sqrt hpos.le
    set u : Fin r → ℂ := ((s⁻¹ : ℝ) : ℂ) • v with hu
    have huS : u ∈ S := by
      show ∑ k, ‖u k‖ ^ 2 = 1
      have hk : ∀ k, ‖u k‖ ^ 2 = s⁻¹ ^ 2 * ‖v k‖ ^ 2 := by
        intro k
        simp only [hu, Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hs0), mul_pow]
      simp only [hk, ← Finset.mul_sum, ← hss]
      field_simp
    have hvu : v = ((s : ℝ) : ℂ) • u := by
      rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hs0.ne', Complex.ofReal_one, one_smul]
    have hMs : Ms X.p0 X.p0_le N v = s ^ 2 * Ms X.p0 X.p0_le N u := by
      rw [hvu, Ms_smul]
    obtain ⟨h1, h2⟩ := hN u huS
    rw [hMs, ← hss]
    have hs2 : 0 < s ^ 2 := pow_pos hs0 2
    constructor
    · nlinarith [mul_lt_mul_of_pos_left h1 hs2]
    · nlinarith [mul_lt_mul_of_pos_left h2 hs2]

end ModeHalfB

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bridge
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
  {E : Type} [Field E] [NumberField E] [IsCMField E]

structure Reading (d : Data K ι Ω WT A) (c : ι) {r : ℕ} (X : FD.Data E r) (sg : K →+* ℂ) where

  Rg : Subring (A c)
  w_mem : ∀ j, d.w j c ∈ Rg
  rd : Rg →+* (Frame X.Ψ r → ℂ)

  WE : AddSubgroup WT
  wL_mem : d.wL ∈ WE
  wt : WE →+ Wt X.Ψ r

  Gen : Set (Frame X.Ψ r)
  Gen_sub : Gen ⊆ X.dom
  Gen_dense : X.dom ⊆ closure Gen
  pt : Frame X.Ψ r → (Ω c →+* ℂ)
  pt_mem : ∀ x ∈ Gen, pt x ∈ PT (Ω := Ω c) sg
  pt_onto : ∀ P ∈ PT (Ω := Ω c) sg, ∃ x ∈ Gen, pt x = P

  w_nz : ∀ x ∈ X.dom, ∃ j, rd ⟨d.w j c, w_mem j⟩ x ≠ 0
  sec : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → X.IsSec (wt ⟨G, hG⟩) (rd ⟨f, hf⟩)
  inj : ∀ G, ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → (∀ x ∈ X.dom, rd ⟨f, hf⟩ x = 0) → f = 0
  norm : ∀ G (hG : G ∈ WE), ∀ f (hf : f ∈ Rg), f ∈ 𝒜 c G → ∀ x ∈ Gen,
    X.pnorm (wt ⟨G, hG⟩) (rd ⟨f, hf⟩) x = d.nrm c G f (pt x)
  ratio_rd : ∀ G, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 → ∀ x ∈ Gen,
    rd ⟨f, hf⟩ x = pt x (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x

  Gen_inv : ∀ x ∈ Gen, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ Gen ∧ pt (lact γ (rmul x b)) = pt x
  orbit_inj : ∀ x ∈ Gen, ∀ x' ∈ Gen, pt x = pt x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x' = lact γ (rmul x b)

  Gen_max : ∀ x ∈ X.dom, ∀ P ∈ PT (Ω := Ω c) sg,
    (∀ G ∈ WE, ∀ f (hf : f ∈ Rg) g (hg : g ∈ Rg), f ∈ 𝒜 c G → g ∈ 𝒜 c G → g ≠ 0 →
      rd ⟨f, hf⟩ x = P (ratio (Ω := Ω c) f g) * rd ⟨g, hg⟩ x) → x ∈ Gen ∧ pt x = P

  bir : ∀ a : Ω c, ∃ (G : WT) (f p : A c), f ∈ Rg ∧ p ∈ Rg ∧ f ∈ 𝒜 c G ∧ p ∈ 𝒜 c G ∧ p ≠ 0 ∧
    p ∈ Algebra.adjoin K (Set.range fun j => d.w j c) ∧ a = ratio (Ω := Ω c) f p

  coordAt : ∀ x ∈ Gen, ∃ (j0 : Fin (d.N + 1)) (jj : Fin (nd X) → Fin (d.N + 1)),
    rd ⟨d.w j0 c, w_mem j0⟩ x ≠ 0 ∧
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      rd ⟨d.w (jj k) c, w_mem (jj k)⟩ (cpt X x z) / rd ⟨d.w j0 c, w_mem j0⟩ (cpt X x z) : V (nd X))) 0).det ≠ 0

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end
