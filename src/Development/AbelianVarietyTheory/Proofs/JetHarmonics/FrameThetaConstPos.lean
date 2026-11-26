module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BasePsiLeviLowerBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaWeightedNorm
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ContDiff

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsInv (X : Data E r) (φ : Frame X.Ψ r → ℝ) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x

def levi (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun y => ((φ (cpt X x0 y) : ℝ) : ℂ)) z ξ).re

def rh (X : Data E r) (x : Frame X.Ψ r) : ℝ :=
  -∑ τ, Real.log ‖dmin X.Gm x τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖

def phK (X : Data E r) (x : Frame X.Ψ r) : ℝ :=
  -2 * ∑ τ, ∑ i : Fin r, Real.log ‖dmin X.Gm x τ i.castSucc‖

def Everywhere (X : Data E r) (p : ((Frame X.Ψ r → ℝ) → ℝ) → Prop) : Prop :=
  ∀ x0 : Frame X.Ψ r, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    p fun φ => levi X x0 φ z ξ

def EverywhereNe (X : Data E r) (p : ((Frame X.Ψ r → ℝ) → ℝ) → Prop) : Prop :=
  ∀ x0 : Frame X.Ψ r, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
    p fun φ => levi X x0 φ z ξ

def GapsGe (X : Data E r) (la : Wt X.Ψ r) (g : ℝ) : Prop :=
  ∀ (τ : X.Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → g ≤ ((la τ i - la τ j : ℤ) : ℝ)

def PairingGe (X : Data E r) (la : Wt X.Ψ r) (m : ℝ) : Prop :=
  ∀ (τ : X.Ψ) (i0 i1 : Fin r), (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → m ≤ ((la τ i1 - la τ i0 : ℤ) : ℝ)

def IsTwoDelta (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ (τ : X.Ψ) (i j : Fin r),
    (((i : ℕ) < X.p0 ↔ (j : ℕ) < X.p0) → la τ i = la τ j) ∧
    ((i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → la τ j = la τ i + 2)

def CuspDecay (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ, (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)) ∧
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ →
      (∀ τ : X.Ψ, X.c τ * X.maj x τ (Data.emb τ.1 ξ) ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ : X.Ψ, X.tt ξ x τ

def IsExtra (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ IsInv X ps ∧ ContDiffOn ℝ ∞ ps X.dom ∧ (∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C) ∧
    CuspDecay X ps a

def wnorm (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm la (w j) x ^ 2)

def bb (X : Data E r) : ℝ := 5 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2

def Crh (X : Data E r) : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ)

structure ThetaIn (X : Data E r) where

  L : Wt X.Ψ r

  Fp : Wt X.Ψ r

  de2 : Wt X.Ψ r
  twoDelta_spec : IsTwoDelta X de2
  L_gaps : GapsGe X L 0
  L_pair : PairingGe X L 1
  Fp_gaps : GapsGe X Fp 0
  Fp_pair : PairingGe X Fp 1

  T : ℕ

  i : ℕ

  g0h : ℕ

  c : ℝ

  RR : ℝ
  dp : ℝ
  qp : ℝ

  a1 : ℝ

  η : ℝ
  two_le_D : 2 ≤ nd X
  T_ge : 11 * nd X ^ 2 ≤ T
  i_pos : 0 < i
  genusHeight_pos : 0 < g0h
  c_pos : 0 < c
  one_le_RR : 1 ≤ RR
  dp_pos : 0 < dp
  qp_pos : 0 < qp
  frame_theta_weight_pos : 0 < a1
  η_pos : 0 < η

  Tcg : (T : ℝ) * c * (2 * g0h) ≤ 1

  tr_le : (1 + RR * T * c * dp ^ 2 * qp / 2 / a1) * r ≤ 2 * T

  marginA : bb X < 19 / 5 * (T : ℝ) - 2 * T

  marginB : bb X ^ 2 * Crh X + bb X < 19 / 10 * ((nd X : ℝ) + 2) * T

  N : ℕ
  w : Fin N → Frame X.Ψ r → ℂ
  et : Frame X.Ψ r → ℂ
  th1 : Frame X.Ψ r → ℂ
  th2 : Frame X.Ψ r → ℂ
  thp : Frame X.Ψ r → ℂ
  w_bdd : ∀ j, X.IsBddSec L (w j)

  et_bdd : X.IsBddSec ((i * g0h) • de2) et

  firstTheta_bounded : X.IsBddSec (2 • L - de2) th1

  secondTheta_bounded : X.IsBddSec ((nd X + 4) • L - Fp) th2
  thp_bdd : X.IsBddSec Fp thp
  et_ne : ∃ x ∈ X.dom, et x ≠ 0
  firstTheta_ne_zero : ∃ x ∈ X.dom, th1 x ≠ 0
  secondTheta_ne_zero : ∃ x ∈ X.dom, th2 x ≠ 0
  thp_ne : ∃ x ∈ X.dom, thp x ≠ 0

  ph : Frame X.Ψ r → ℝ
  ph_inv : IsInv X ph
  ph_nonneg : ∀ x ∈ X.dom, 0 ≤ ph x

  w_lower : ∃ C : ℝ, ∀ x ∈ X.dom, Real.exp (-(C + c * ph x)) ≤ wnorm X L w x

  et_upper : ∃ P : ℝ, ∀ x ∈ X.dom,
    X.pnorm ((i * g0h) • de2) et x ≤ Real.exp (-((i : ℝ) * (ph x - P)))

  ph_lower : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ X.dom, X.la1 x < ε →
    1 / (4 * RR * dp ^ 2 * X.la1 x ^ 2) ≤ ph x

  ph_upper : ∀ x ∈ X.dom, ph x ≤ qp * dp ^ 2 / (2 * X.la1 x ^ 2)

  ps0 : Frame X.Ψ r → ℝ
  extraDivisor_isExtra : IsExtra X ps0 a1

  curvature_lower_bound : Everywhere X fun Lv => -((r : ℝ) / 2 * Lv (phla X de2)) ≤ Lv ps0

  L_curv : EverywhereNe X fun Lv => 0 < Lv (phla X L)

  Lde_curv : EverywhereNe X fun Lv => 1 / 2 * Lv (phla X de2) < Lv (phla X L)

  curvA : Everywhere X fun Lv =>
    2 * η * Lv (phla X L) + 19 / 5 * (T : ℝ) * Lv (rh X) ≤
      Lv (phla X Fp) - Lv (phK X) - (nd X : ℝ) * Lv (phla X L)

  curvB : Everywhere X fun Lv =>
    19 / 10 * ((nd X : ℝ) + 2) * T * Lv (rh X) ≤ Lv (phla X Fp) - Lv (phK X)

namespace ThetaIn

variable {X : Data E r} (I : ThetaIn X)

end ThetaIn

end

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm
open GlobalTheory.FrameThetaCompare (transfer curv_lin diagForm chart_smooth smooth_of_chart mem_SS_iff lower_iff
  upper_iff bdd_of_upper curvDe_eq_omRh curvDe_nonneg card_pos)

namespace GlobalTheory.ThetaRecordCompare

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private lemma twoDelta_sub_eq_two_mul_blockWt_sub {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {de : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X de) (τ : X.Ψ) (a b : Fin r) :
    ((de τ a : ℤ) : ℝ) - ((de τ b : ℤ) : ℝ) =
      2 * (((_root_.GlobalTheory.CurvMargin.blockWt X τ a : ℤ) : ℝ) -
        ((_root_.GlobalTheory.CurvMargin.blockWt X τ b : ℤ) : ℝ)) := by
  have key : de τ a - de τ b =
      2 * (_root_.GlobalTheory.CurvMargin.blockWt X τ a - _root_.GlobalTheory.CurvMargin.blockWt X τ b) := by
    by_cases ha : (a : ℕ) < X.p0 <;> by_cases hb : (b : ℕ) < X.p0
    · have := (h τ a b).1 (iff_of_true ha hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ a b).2 ha (not_lt.1 hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ b a).2 hb (not_lt.1 ha)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
    · have := (h τ a b).1 (iff_of_false ha hb)
      simp only [_root_.GlobalTheory.CurvMargin.blockWt, ha, hb, ↓reduceIte]
      omega
  exact_mod_cast key

theorem _root_.GlobalTheory.ThetaRecordCompare.levi_twoDelta {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {de : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsTwoDelta X de) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (ho : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) {z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)} (hz : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0)
    (ξ : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.levi X x0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X de) z ξ = 2 * _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviRh X x0 z ξ := by
  rw [_root_.GlobalTheory.CurvMargin.leviRh_eq X x0 ho hz ξ]
  obtain ⟨x1, D, -, -, -, hdiag, -⟩ := _root_.GlobalTheory.FrameThetaCompare.transfer X x0 z hz
  change _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 de z ξ =
    2 * _root_.GlobalTheory.IndefiniteRowSideFullHecke.CurvatureFamilyNorm.curv X x0 (_root_.GlobalTheory.CurvMargin.blockWt X) z ξ
  rw [hdiag, hdiag]
  unfold _root_.GlobalTheory.FrameThetaCompare.diagForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [twoDelta_sub_eq_two_mul_blockWt_sub h]
  ring

theorem _root_.GlobalTheory.ThetaRecordCompare.leviRh_nonneg (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}
    (ho : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0) {z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)}
    (hz : z ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x0) (ξ : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) : 0 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviRh X x0 z ξ := by
  have h0 := _root_.GlobalTheory.FrameThetaCompare.curvDe_nonneg X (x0 := x0) hz ξ
  rw [_root_.GlobalTheory.FrameThetaCompare.curvDe_eq_omRh X ho hz ξ] at h0
  exact h0

theorem _root_.GlobalTheory.ThetaRecordCompare.gapsGe_mono {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {g g' : ℝ}
    (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la g) (hg : g' ≤ g) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la g' :=
  fun τ i j hij hne => hg.trans (h τ i j hij hne)

theorem _root_.GlobalTheory.ThetaRecordCompare.cusp_of_gaps {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} (hn : 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)
    (h0 : 0 < X.p0) (hr : X.p0 < r) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    (hg : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la 0) (hp : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la 1) {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hP : X.IsBddSec la P) :
    P ∈ X.SS la := by
  obtain ⟨τ0, hτ0⟩ := Finset.card_pos.1 (_root_.GlobalTheory.FrameThetaCompare.card_pos hn)
  have key := @_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.cuspStatement_holds E _ _ _
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.CuspStatement at key
  refine key r X la ⟨τ0, hτ0⟩ h0 hr (fun i j hij hne => ?_) (fun i0 i1 hi0 hi1 => ?_) P hP
  · have h1 : (0 : ℤ) ≤ la ⟨τ0, hτ0⟩ i - la ⟨τ0, hτ0⟩ j := by exact_mod_cast hg _ i j hij hne
    omega
  · have h1 : (1 : ℤ) ≤ la ⟨τ0, hτ0⟩ i1 - la ⟨τ0, hτ0⟩ i0 := by
      exact_mod_cast hp _ i0 i1 hi0 hi1
    omega

theorem _root_.GlobalTheory.ThetaRecordCompare.two_le_r {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r} (hn : 2 ≤ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) : 2 ≤ r := by
  by_contra hlt
  push_neg at hlt
  have hempty : IsEmpty (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent
    refine ⟨fun ⟨_, ⟨p, hp⟩⟩ => ?_⟩
    have h1 := p.1.isLt
    have h2 : (p.2 : ℕ) < p.1 := hp
    omega
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd at hn
  rw [Fintype.card_eq_zero_iff.2 hempty] at hn
  omega

section Records

variable {X : Data E r}

private lemma cpt_zero_jet_harmonics (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x0 : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 = x0 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.mat]
  funext τ a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    simp only [Matrix.of_apply]
    split_ifs <;> first | exact mul_zero _ | simp_all
  · simp

private lemma exists_surjective_diagForm_leviM (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) :
    ∃ x0 ∈ X.dom, _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 ∈ X.dom ∧
      ∃ D : (Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) →ₗ[ℂ] Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ, Function.Surjective D ∧
        ∀ la ξ, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.leviM X (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la) x0 0 ξ = _root_.GlobalTheory.FrameThetaCompare.diagForm X la (D ξ) := by
  obtain ⟨x0, hx0, -⟩ := A.et_ne
  have hd : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 0 ∈ X.dom := by rw [cpt_zero_jet_harmonics]; exact hx0
  obtain ⟨x1, D, -, hD, -, hdiag, -⟩ := _root_.GlobalTheory.FrameThetaCompare.transfer X x0 0 hd
  exact ⟨x0, hx0, hd, D, LinearMap.injective_iff_surjective.1 hD, fun la ξ => hdiag la ξ⟩

private lemma diagForm_L_pos (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) {η : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ} (hη : η ≠ 0) :
    0 < _root_.GlobalTheory.FrameThetaCompare.diagForm X A.L η := by
  obtain ⟨x0, hx0, hd, D, hD, hdiag⟩ := exists_surjective_diagForm_leviM A
  obtain ⟨ξ, rfl⟩ := hD η
  have hξ : ξ ≠ 0 := by rintro rfl; exact hη (map_zero D)
  rw [← hdiag]
  exact A.posL x0 hx0 0 hd ξ hξ

private lemma single_ne_zero_jet_harmonics (τ : X.Ψ) (i j : Fin r) (h : i < j) :
    (fun k : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) =>
      if (k : ℕ) = (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) then (1 : ℂ) else 0 :
      Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) ≠ 0 := fun hz => by
  have := congrFun hz (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩))
  simp only [if_pos rfl] at this
  exact one_ne_zero this

private lemma diagForm_single' (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (τ : X.Ψ) (i j : Fin r) (h : i < j) :
    _root_.GlobalTheory.FrameThetaCompare.diagForm X la
        (fun k : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) =>
          if (k : ℕ) = (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) then 1 else 0) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i * (((la τ i : ℤ) : ℝ) - ((la τ j : ℤ) : ℝ)) := by
  unfold _root_.GlobalTheory.FrameThetaCompare.diagForm
  rw [Finset.sum_eq_single (τ, ⟨(j, i), h⟩)]
  · simp
  · intro e _ he
    have hne : ((Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) e : Fin _) : ℕ) ≠
        (Fintype.equivFin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.Ent X) (τ, ⟨(j, i), h⟩) : ℕ) := fun h' =>
      he ((Fintype.equivFin _).injective (Fin.ext h'))
    simp only [hne, if_false]
    simp
  · simp

private lemma diagForm_Fp_sub_pos (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) {η : Fin (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ} (hη : η ≠ 0) :
    0 < _root_.GlobalTheory.FrameThetaCompare.diagForm X (A.Fp - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW X - _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X • A.L) η := by
  obtain ⟨x0, hx0, hd, D, hD, hdiag⟩ := exists_surjective_diagForm_leviM A
  obtain ⟨ξ, rfl⟩ := hD η
  have hξ : ξ ≠ 0 := by rintro rfl; exact hη (map_zero D)
  obtain ⟨c, hc, hF⟩ := A.posF
  have h1 := A.posL x0 hx0 0 hd ξ hξ
  have h2 := hF 0 le_rfl (by rw [zero_mul]; positivity) x0 hx0 0 hd ξ
  rw [← hdiag]
  have h3 := mul_pos (mul_pos two_pos hc) h1
  linarith

theorem _root_.GlobalTheory.ThetaRecordCompare.arch_gaps (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) (h0 : 0 < X.p0)
    (hr : X.p0 < r) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X A.L 1 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X A.L 1 ∧ _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X A.Fp 0 ∧
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X A.Fp 1 := by
  have hn : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) := by exact_mod_cast A.n_ge
  have gL : ∀ (τ : X.Ψ) (i j : Fin r), (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 →
      1 ≤ A.L τ i - A.L τ j := by
    intro τ i j hij hne
    have hlt : i < j := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i = 1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      by_cases hj : (j : ℕ) < X.p0
      · rw [if_pos hj, if_pos (by omega)]; norm_num
      · rw [if_neg hj, if_neg (by omega)]; norm_num
    have h1 := diagForm_L_pos A (single_ne_zero_jet_harmonics τ i j hlt)
    rw [diagForm_single' A.L τ i j hlt, hs, one_mul] at h1
    have h2 : (0 : ℤ) < A.L τ i - A.L τ j := by
      exact_mod_cast (by linarith : (0 : ℝ) < ((A.L τ i : ℤ) : ℝ) - ((A.L τ j : ℤ) : ℝ))
    omega
  have pL : ∀ (τ : X.Ψ) (i0 i1 : Fin r), (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 →
      1 ≤ A.L τ i1 - A.L τ i0 := by
    intro τ i0 i1 hi0 hi1
    have hlt : i0 < i1 := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i0 = -1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      rw [if_neg (by omega), if_pos (by omega)]; norm_num
    have h1 := diagForm_L_pos A (single_ne_zero_jet_harmonics τ i0 i1 hlt)
    rw [diagForm_single' A.L τ i0 i1 hlt, hs] at h1
    have h2 : (0 : ℤ) < A.L τ i1 - A.L τ i0 := by
      exact_mod_cast (by linarith : (0 : ℝ) < ((A.L τ i1 : ℤ) : ℝ) - ((A.L τ i0 : ℤ) : ℝ))
    omega
  refine ⟨fun τ i j hij hne => by exact_mod_cast gL τ i j hij hne,
    fun τ i0 i1 hi0 hi1 => by exact_mod_cast pL τ i0 i1 hi0 hi1, ?_, ?_⟩
  · intro τ i j hij hne
    have hlt : i < j := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i = 1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      by_cases hj : (j : ℕ) < X.p0
      · rw [if_pos hj, if_pos (by omega)]; norm_num
      · rw [if_neg hj, if_neg (by omega)]; norm_num
    have h1 := diagForm_Fp_sub_pos A (single_ne_zero_jet_harmonics τ i j hlt)
    rw [diagForm_single' _ τ i j hlt, hs, one_mul] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW] at h1
    push_cast at h1
    have hR : (0 : ℝ) < ((A.Fp τ i - A.Fp τ j + 2 * ((j : ℤ) - i) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) : ℤ) : ℝ) := by
      push_cast; linarith
    have hZ : (0 : ℤ) < A.Fp τ i - A.Fp τ j + 2 * ((j : ℤ) - i) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) := by exact_mod_cast hR
    have hg := gL τ i j hij hne
    have hji : (j : ℤ) - i = 1 := by omega
    have hm : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i - A.L τ j) := by nlinarith
    have : (0 : ℤ) ≤ A.Fp τ i - A.Fp τ j := by linarith
    exact_mod_cast this
  · intro τ i0 i1 hi0 hi1
    have hlt : i0 < i1 := by rw [Fin.lt_def]; omega
    have hs : _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i1 * _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 i0 = -1 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
      rw [if_neg (by omega), if_pos (by omega)]; norm_num
    have h1 := diagForm_Fp_sub_pos A (single_ne_zero_jet_harmonics τ i0 i1 hlt)
    rw [diagForm_single' _ τ i0 i1 hlt, hs] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.kapW] at h1
    push_cast at h1
    have hR : (0 : ℝ) < ((A.Fp τ i1 - A.Fp τ i0 - 2 * ((i1 : ℤ) - i0) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) : ℤ) : ℝ) := by
      push_cast; linarith
    have hZ : (0 : ℤ) < A.Fp τ i1 - A.Fp τ i0 - 2 * ((i1 : ℤ) - i0) -
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) := by exact_mod_cast hR
    have hg := pL τ i0 i1 hi0 hi1
    have hji : (0 : ℤ) ≤ (i1 : ℤ) - i0 := by omega
    have hm : (2 : ℤ) ≤ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X : ℤ) * (A.L τ i1 - A.L τ i0) := by nlinarith
    have : (1 : ℤ) ≤ A.Fp τ i1 - A.Fp τ i0 := by linarith
    exact_mod_cast this

theorem _root_.GlobalTheory.ThetaRecordCompare.arch_extra (A : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ArchInM X) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsExtra X A.ps0 A.a1 := by
  have hinv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.IsInv X A.ps0 :=
    (_root_.GlobalTheory.FrameThetaCompare.isInv_iff X _).2 A.potential_invariant
  refine ⟨A.frame_theta_weight_pos.le, hinv, ?_, ?_, ?_⟩
  · exact _root_.GlobalTheory.FrameThetaCompare.smooth_of_chart X hinv.1 A.potential_smooth
  · obtain ⟨B, hB⟩ := _root_.GlobalTheory.FlatCompare.bdd_add_log X A.base_psi_weighted_cf A.frame_theta_weight_pos 0
    exact ⟨B, fun x hx => by simpa using hB x hx⟩
  · obtain ⟨A', hdec, C, hC⟩ := (_root_.GlobalTheory.FlatCompare.extraBounds_iff X A.ps0 A.frame_theta_weight_pos.le).2 A.base_psi_weighted_cf
    exact ⟨A', ⟨C, hC⟩, fun η hη => hdec η hη⟩

theorem _root_.GlobalTheory.ThetaRecordCompare.gaps_add {la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la 0)
    (h' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X la' 0) (k : ℕ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.GapsGe X (la + k • la') 0 := by
  intro τ i j hij hne
  have a1 : (0 : ℤ) ≤ la τ i - la τ j := by exact_mod_cast h τ i j hij hne
  have a2 : (0 : ℤ) ≤ la' τ i - la' τ j := by exact_mod_cast h' τ i j hij hne
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have : (0 : ℤ) ≤ (la + k • la') τ i - (la + k • la') τ j := by
    simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    nlinarith
  exact_mod_cast this

theorem _root_.GlobalTheory.ThetaRecordCompare.pair_add {la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la 1)
    (h' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X la' 1) (k : ℕ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightedNorm.PairingGe X (la + k • la') 1 := by
  intro τ i0 i1 hi0 hi1
  have a1 : (1 : ℤ) ≤ la τ i1 - la τ i0 := by exact_mod_cast h τ i0 i1 hi0 hi1
  have a2 : (1 : ℤ) ≤ la' τ i1 - la' τ i0 := by exact_mod_cast h' τ i0 i1 hi0 hi1
  have hk : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have : (1 : ℤ) ≤ (la + k • la') τ i1 - (la + k • la') τ i0 := by
    simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    nlinarith
  exact_mod_cast this

end Records

end

end GlobalTheory.ThetaRecordCompare
