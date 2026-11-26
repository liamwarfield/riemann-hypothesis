module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def phla {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) : ℝ := -2 * Real.log (X.nfac la x)

def IsBEq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  DifferentiableOn ℂ P X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, P (rmul x b) = bchar la b * P x

def IsFundSet {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) : Prop :=
  MeasurableSet FF ∧ FF ⊆ OmF X x0 ∧
  (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r,
    cpt X x0 z' = lact γ (rmul (cpt X x0 z) b) → z = z') ∧
  ∀ᵐ z ∂muF X x0, ∃ z' ∈ FF, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
    cpt X x0 z = lact γ (rmul (cpt X x0 z') b)

def ExhaustFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∃ S : EtaleStein (nd X) (OmF X x0), S.z = Subtype.val ∧ S.e = fun y => eF X x0 y.1

def MeasInvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 x0' : Frame X.Ψ r), IsOrth X x0 → IsOrth X x0' →
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 = ∫⁻ z, φ (cpt X x0' z) ∂muF X x0'

def ExtFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (F : V (nd X) → ℂ),
    DifferentiableOn ℂ F (OmF X x0) →
    (∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) →
    ∃ P : Frame X.Ψ r → ℂ, IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z

def FundSetStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∃ FF : Set (V (nd X)), IsFundSet X x0 FF

def IsMetricW {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) : Prop :=
  Measurable W ∧
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, W (rmul x b) = W x / ENNReal.ofReal (‖bchar la b‖ ^ 2)) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, W (lact γ x) = W x

def WLower {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x ∈ X.dom, ENNReal.ofReal (c * Real.exp (-phla X la x)) ≤ W x

def InAt {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ) (F : V (nd X) → ℂ) :
    Prop :=
  ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 < ⊤

def InFF {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (FF : Set (V (nd X)))
    (f : Frame X.Ψ r → ℂ) : Prop :=
  ∫⁻ z in FF, ENNReal.ofReal (‖f (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0 < ⊤

def PoinStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F →
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
    (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (lact γ.1 x)‖) ∧
    X.IsBddSec la (poin X la P) ∧
    (∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)) ∧
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ENNReal.ofReal ‖poin X la P x‖ ≤ ENNReal.ofReal C *
        ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
          (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)) ∧
    ∀ (la' : Wt X.Ψ r) (g : Frame X.Ψ r → ℂ), X.IsSec la' g → ∀ x ∈ X.dom,
      poin X (la + la') (fun y => g y * P y) x = g x * poin X la P x

def OntoStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞)
    (Ps : Frame X.Ψ r → ℝ) (g1 : V (nd X) → ℂ) (bb m : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m →
    DifferentiableOn ℂ g1 (OmF X x0) → (∃ z ∈ OmF X x0, g1 z ≠ 0) →
    ContDiffOn ℝ ∞ (fun z => Ps (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0} →
    (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → W (cpt X x0 z) = ENNReal.ofReal (Real.exp (-Ps (cpt X x0 z)))) →
    (∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
      m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
        (leviV (nd X) (fun w => ((Ps (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re) →
    (∀ P, X.IsBddSec la P → P ∈ X.SS la) →
    ∀ FF, IsFundSet X x0 FF →
    (∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS la, InFF X x0 W FF f →
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x) →
    ∀ f ∈ X.SS la, InFF X x0 W FF f →
    ∃ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
      IsBEq X la P ∧ (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ ∀ x ∈ X.dom, poin X la P x = f x

def CuspStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (τ0 : X.Ψ), 0 < X.p0 → X.p0 < r →
    (∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ0 j ≤ la τ0 i) →
    (∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ0 i0 < la τ0 i1) →
    ∀ P, X.IsBddSec la P → P ∈ X.SS la

def RhGradFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
    Complex.normSq (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) z * ξ j) ≤
      ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) *
        (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re

def ExhaustGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ g1 : V (nd X) → ℂ,
    DifferentiableOn ℂ g1 (OmF X x0) →
    ∃ S : EtaleStein (nd X) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0},
      S.z = Subtype.val ∧ S.e = fun y => eF X x0 y.1 + (‖g1 y.1‖ ^ 2)⁻¹

def KaUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ FF, IsFundSet X x0 FF → ∀ bb : ℝ,
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
      (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x) →
      ∫⁻ z, ENNReal.ofReal (kaF X x0 bb z) * φ (cpt X x0 z) ∂muF X x0 ≤
        C * ∫⁻ z in FF, φ (cpt X x0 z) ∂muF X x0

def PairUnfoldStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ),
    IsMetricW X la W → WLower X la W → 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb →
    ∀ (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (OmF X x0) → InAt X x0 W bb F →
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) →
    ∀ FF, IsFundSet X x0 FF → ∀ f0 ∈ X.SS la, InFF X x0 W FF f0 →
      ∫ z in FF, poin X la P (cpt X x0 z) * (starRingEnd ℂ) (f0 (cpt X x0 z)) *
          ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0 =
        ∫ z, F z * (starRingEnd ℂ) (f0 (cpt X x0 z)) * ((W (cpt X x0 z)).toReal : ℂ) ∂muF X x0

def BigCellStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ),
    IsBEq X la P → (∀ z ∈ OmF X x0, P (cpt X x0 z) = 0) → ∀ x ∈ X.dom, P x = 0

def OmFConnStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → IsPreconnected (OmF X x0)

def OrthoStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ x1, IsOrth X x1 ∧ ∃ b ∈ Bor X.Ψ r, x = rmul x1 b

def VanishAtSStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), 0 < nd X → IsOrth X x1 → x1 ∈ X.dom →
    ∀ (u w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ρ : ℝ), 0 < ρ →
    DifferentiableOn ℂ (fun z => u (cpt X x1 z)) (Metric.ball 0 ρ) →
    (∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x1 z)) (Metric.ball 0 ρ)) →
    DifferentiableOn ℂ (fun z => w0 (cpt X x1 z)) (Metric.ball 0 ρ) →
    w0 x1 ≠ 0 → (∀ k, s k x1 = 0) →
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      s k (cpt X x1 z) / w0 (cpt X x1 z) : V (nd X))) 0).det ≠ 0 →
    ∫⁻ z in Metric.ball 0 ρ, ENNReal.ofReal (‖u (cpt X x1 z)‖ ^ 2 *
      (∑ k, ‖s k (cpt X x1 z)‖ ^ 2) ^ (-(nd X : ℝ))) < ⊤ →
    u x1 = 0

def LUStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
    ∃ (Δ : Frame X.Ψ r → ℂ) (zOf : Frame X.Ψ r → V (nd X)) (bOf : Frame X.Ψ r → Frame X.Ψ r),
      Differentiable ℂ Δ ∧ (∀ x ∈ X.dom, ∀ ε > 0, ∃ y ∈ Metric.ball x ε, Δ y ≠ 0) ∧
      DifferentiableOn ℂ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0} ∧
      DifferentiableOn ℂ bOf {x | x ∈ X.dom ∧ Δ x ≠ 0} ∧
      (∀ x ∈ X.dom, Δ x ≠ 0 → zOf x ∈ OmF X x0 ∧ bOf x ∈ Bor X.Ψ r ∧
        x = rmul (cpt X x0 (zOf x)) (bOf x)) ∧
      ∀ z ∈ OmF X x0, ∀ b ∈ Bor X.Ψ r, Δ (rmul (cpt X x0 z) b) ≠ 0 ∧
        zOf (rmul (cpt X x0 z) b) = z ∧ bOf (rmul (cpt X x0 z) b) = b

def FrameMeasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ C : Set (Frame X.Ψ r), IsCompact C →
    C ⊆ X.dom → ∃ K : ℝ≥0∞, K < ⊤ ∧
    ∀ G : Frame X.Ψ r → ℝ≥0∞, Measurable G → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, G (rmul x b) = G x) →
      ∫⁻ x in C, G x ≤ K * ∫⁻ z in sat X x0 C, G (cpt X x0 z) ∂muF X x0

def FundSetMeasStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (FF : Set (V (nd X))), IsOrth X x0 → IsFundSet X x0 FF →
    (∃ x1, IsOrth X x1 ∧ ∃ CechHodgeFiltration, IsFundSet X x1 CechHodgeFiltration ∧ muF X x1 CechHodgeFiltration < ⊤) → muF X x0 FF < ⊤

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPfA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RGF

open Filter Topology Set ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff

noncomputable section

theorem gc_wdb_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wdb n j (g ∘ F) v = ∑ a, wdb d a g (F v) * (starRingEnd ℂ) (J (bas n j) a) := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wdb, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination ((D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 -
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

theorem gc_wd_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (j : Fin n) :
    wd n j (g ∘ F) v = ∑ a, wd d a g (F v) * J (bas n j) a := by
  have hd : fderiv ℝ (g ∘ F) v = (fderiv ℝ g (F v)).comp (J.restrictScalars ℝ) :=
    (hg.hasFDerivAt.comp v (hF.restrictScalars ℝ)).fderiv
  rw [wd, hd]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul]
  set D := fderiv ℝ g (F v)
  set c := J (bas n j)
  rw [fc_clm_decomp d D c, fc_clm_decomp d D (Complex.I • c), Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, wdb, wd]
  linear_combination (-(D (bas d a) - Complex.I * D (Complex.I • bas d a)) / 2 * c a / 2 +
    (D (bas d a) + Complex.I * D (Complex.I • bas d a)) / 2 * (starRingEnd ℂ) (c a) / 2) *
      Complex.I_sq

theorem gc_toLp_apply (n d : ℕ) (J : V n →L[ℂ] V d) (ξ : Fin n → ℂ) (b : Fin d) :
    J (WithLp.toLp 2 ξ) b = ∑ j, ξ j * J (bas n j) b := by
  have h : WithLp.toLp 2 ξ = ∑ j, ξ j • bas n j := by
    ext k
    simp [bas, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, map_sum]
  simp [map_smul]

theorem gc_sum_wd_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (J : V n →L[ℂ] V d) (v : V n)
    (hg : DifferentiableAt ℝ g (F v)) (hF : HasFDerivAt F J v) (ξ : Fin n → ℂ) :
    ∑ j, wd n j (g ∘ F) v * ξ j = ∑ a, wd d a g (F v) * J (WithLp.toLp 2 ξ) a := by
  simp only [gc_wd_comp n d g F J v hg hF, gc_toLp_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => by ring

theorem sum_four_indices_comm (n d : ℕ) (f : Fin n → Fin n → Fin d → Fin d → ℂ) :
    ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := by
  calc ∑ j, ∑ k, ∑ a, ∑ b, f j k a b = ∑ j, ∑ k, ∑ b, ∑ a, f j k a b :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ j, ∑ b, ∑ k, ∑ a, f j k a b := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ k, ∑ a, f j k a b := Finset.sum_comm
    _ = ∑ b, ∑ j, ∑ a, ∑ k, f j k a b :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ j, ∑ k, f j k a b := Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem gc_leviV_comp (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (U : Set (V n)) (hU : IsOpen U)
    (v : V n) (hv : v ∈ U) (hF : ContDiffOn ℂ 2 F U) (hg : ContDiffAt ℝ 2 g (F v))
    (ξ : Fin n → ℂ) :
    leviV n (g ∘ F) v ξ = leviV d g (F v) (fun b => fderiv ℂ F v (WithLp.toLp 2 ξ) b) := by
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y) :=
    (hFd v hv).continuousAt.eventually (hg.eventually (by simp))
  have hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v]
      fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a) := by
    intro k
    filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU
    exact gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (F v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v) := by
    intro a
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) +
      Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)
    have h1 := hD.clm_apply (differentiableAt_const (bas d a))
    have h2 := hD.clm_apply (differentiableAt_const (Complex.I • bas d a))
    have h3 := (h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  have hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v := fun a =>
    (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt
  have hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt
      (by norm_num)
  have hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v := fun k a =>
    (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a
  have hCa : ∀ k a, DifferentiableAt ℝ
      (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v := by
    intro k a
    have := Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)
    simpa [Function.comp_def] using this
  have step : ∀ j k, wd n j (wdb n k (g ∘ F)) v = ∑ a, ∑ b,
      wd d b (wdb d a g) (F v) * fderiv ℂ F v (bas n j) b *
        (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a) := by
    intro j k
    rw [wd_congr n j _ _ v (hwdb k),
      fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) *
        (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero,
      mul_zero, add_zero]
    have := gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j
    rw [show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]
  unfold leviV
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [step, gc_toLp_apply, Finset.sum_mul, map_sum, map_mul, Finset.mul_sum]
  rw [sum_four_indices_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.RGF
end
