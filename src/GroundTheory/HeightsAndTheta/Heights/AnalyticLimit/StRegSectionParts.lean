module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsCompatChart)
open ReciprocityTheory.AnForm.A (coordDiv)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData RegCharts)

noncomputable section

section Objects

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}

def bdDom (R : RegChartData A) (j : Fin R.n) : Set X := (R.ψ j).source ∩ R.ψ j ⁻¹' R.W j

theorem isOpen_bdDom (R : RegChartData A) (j : Fin R.n) : IsOpen (bdDom R j) :=
  (R.ψ j).isOpen_inter_preimage (R.isOpen_kappaOpenNeighbourhood j)

def bdEq (R : RegChartData A) (j : Fin R.n) (y : X) : ℂ := ∏ i ∈ R.S j, R.ψ j y i

def bdIdx (R : RegChartData A) (x : X) : Fin R.n := (R.cover x).choose

theorem mem_V''_bdIdx (R : RegChartData A) (x : X) : x ∈ R.V'' (bdIdx R x) :=
  (R.cover x).choose_spec

theorem V''_subset_bdDom (R : RegChartData A) (j : Fin R.n) : R.V'' j ⊆ bdDom R j :=
  fun _ hx => ⟨hx.1, R.closure_W'_subset j (subset_closure (R.closure_W''_subset j (subset_closure hx.2)))⟩

theorem mem_bdDom_bdIdx (R : RegChartData A) (x : X) : x ∈ bdDom R (bdIdx R x) :=
  V''_subset_bdDom R _ (mem_V''_bdIdx R x)

def bdPot (R : RegChartData A) (φ : Fin R.n → X → ℝ) (c : ℝ) : LocPot X where
  U x := bdDom R (bdIdx R x)
  isOpen_U _ := isOpen_bdDom R _
  mem_U x := mem_bdDom_bdIdx R x
  φ x y := φ (bdIdx R x) y + c

def bdSec (R : RegChartData A) (x : X) : X → ℂ := bdEq R (bdIdx R x)

def IsBdMetric (R : RegChartData A) (φ : Fin R.n → X → ℝ) : Prop :=
  (∀ j, A.SmoothOn (bdDom R j) (φ j)) ∧
  (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ,
      A.HoloOn W G ∧ ∀ z ∈ W ∩ (bdDom R j ∩ bdDom R k), φ j z - φ k z = (G z).re) ∧
  ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k,
    ‖bdEq R j y‖ * Real.exp (-φ j y) = ‖bdEq R k y‖ * Real.exp (-φ k y)

def bdWeight (R : RegChartData A) (χ : Fin R.n → X → ℝ) (g : Fin R.n → Fin R.n → X → ℂ)
    (j : Fin R.n) (y : X) : ℝ :=
  ∑ l, (bdDom R l).indicator (fun z => χ l z * ‖g j l z‖ ^ 2) y

end Objects

def RegYoDense.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A), Dense R.Yo

def RegRCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A),
    ContinuousOn R.r R.Yo

def ChartCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U : Set X), IsOpen U →
    (∀ f : X → ℝ, A.SmoothOn U f → ContinuousOn f U) ∧
    ∀ g : X → ℂ, A.HoloOn U g → ContinuousOn g U

def BdEqHolo.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j : Fin R.n),
    A.HoloOn (bdDom R j) (bdEq R j) ∧ ∀ y ∈ bdDom R j, (bdEq R j y = 0 ↔ y ∉ R.Yo)

def HyperplaneDivisible.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (F : (Fin D → ℂ) → ℂ) (i : Fin D), IsOpen Ω →
    AnalyticOnNhd ℂ F Ω → (∀ z ∈ Ω, z i = 0 → F z = 0) →
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ z ∈ Ω, F z = z i * G z

def CoordDivDivisible.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Set (Fin D → ℂ)) (F : (Fin D → ℂ) → ℂ) (S : Finset (Fin D)), IsOpen Ω →
    AnalyticOnNhd ℂ F Ω → (∀ z ∈ Ω, z ∈ coordDiv S → F z = 0) →
    ∃ G : (Fin D → ℂ) → ℂ, AnalyticOnNhd ℂ G Ω ∧ ∀ z ∈ Ω, F z = (∏ i ∈ S, z i) * G z

def BdDivides.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j k : Fin R.n),
    ∃ u : X → ℂ, A.HoloOn (bdDom R j ∩ bdDom R k) u ∧ ContinuousOn u (bdDom R j ∩ bdDom R k) ∧
      ∀ y ∈ bdDom R j ∩ bdDom R k, bdEq R k y = u y * bdEq R j y

def BdTransition.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j k : Fin R.n),
    ∃ g : X → ℂ, A.HoloOn (bdDom R j ∩ bdDom R k) g ∧
      ∀ y ∈ bdDom R j ∩ bdDom R k, g y ≠ 0 ∧ bdEq R j y = g y * bdEq R k y

def BdCocycle.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (g : Fin R.n → Fin R.n → X → ℂ), (∀ j k, ContinuousOn (g j k) (bdDom R j ∩ bdDom R k)) →
    (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, bdEq R j y = g j k y * bdEq R k y) →
    ∀ j k l, ∀ y ∈ bdDom R j ∩ bdDom R k ∩ bdDom R l, g j l y = g j k y * g k l y

def BdPartition.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ χ : Fin R.n → X → ℝ, (∀ j, A.Smooth (χ j)) ∧ (∀ j y, 0 ≤ χ j y) ∧
      (∀ y, ∑ j, χ j y = 1) ∧ ∀ j, tsupport (χ j) ⊆ bdDom R j

def LogNormHolo.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (W : Set X) (g : X → ℂ),
    IsOpen W → A.HoloOn W g → (∀ y ∈ W, g y ≠ 0) → ∀ y ∈ W, ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re

def IndicatorSmooth.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U O : Set X) (χ h : X → ℝ),
    IsOpen U → IsOpen O → A.Smooth χ → tsupport χ ⊆ O → A.SmoothOn (U ∩ O) h →
    A.SmoothOn U (O.indicator fun y => χ y * h y)

def NormSqSmooth.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (U : Set X) (g : X → ℂ),
    A.HoloOn U g → A.SmoothOn U (fun y => ‖g y‖ ^ 2)

def BdWeight.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A) (g : Fin R.n → Fin R.n → X → ℂ),
    (∀ j k, A.HoloOn (bdDom R j ∩ bdDom R k) (g j k)) →
    (∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, g j k y ≠ 0) →
    (∀ j k l, ∀ y ∈ bdDom R j ∩ bdDom R k ∩ bdDom R l, g j l y = g j k y * g k l y) →
    ∃ w : Fin R.n → X → ℝ, (∀ j, A.SmoothOn (bdDom R j) (w j)) ∧
      (∀ j, ∀ y ∈ bdDom R j, 0 < w j y) ∧
      ∀ j k, ∀ y ∈ bdDom R j ∩ bdDom R k, w j y = ‖g j k y‖ ^ 2 * w k y

def BdMetric.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ φ : Fin R.n → X → ℝ, IsBdMetric R φ

def BddOnInner.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A) (j : Fin R.n)
    (u : X → ℝ), ContinuousOn u (bdDom R j) → ∃ B : ℝ, ∀ y ∈ R.V'' j, |u y| ≤ B

def BdSectionProps.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    IsPotential A (bdPot R φ c) ∧ IsSection A (bdPot R φ c) (bdSec R) ∧ secOpen (bdSec R) = R.Yo

def BdNormCont.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    Continuous fun y => ‖bdSec R y y‖ * Real.exp (-(bdPot R φ c).φ y y)

def BdComparison.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (D : ℕ) (A : FinHolAtlas D X) (R : RegChartData A)
    (φ : Fin R.n → X → ℝ), IsBdMetric R φ → ∀ c : ℝ,
    ∃ B : ℝ, ∀ y ∈ R.Yo, |R.r y - rSec (bdPot R φ c) (bdSec R) y| ≤ B

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 holoOn_const)

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StatementsPullback
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential HoloMap)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe (compat_chart levi_base_indep)

noncomputable section

def C2ConvOn {E : ℕ} {Z : Type} [TopologicalSpace Z] (A : FinHolAtlas E Z) (V : Set Z)
    (g : ℝ → Z → ℝ) (φ : Z → ℝ) : Prop :=
  ∀ (k : Fin A.n) (K : Set (Fin E → ℂ)), IsCompact K →
    K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V →
    TendstoUniformlyOn (fun t y => g t ((A.chart k).symm y)) (fun y => φ ((A.chart k).symm y))
        (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K

def C2ConvergencePullback.Statement : Prop :=
  ∀ {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (B : FinHolAtlas D Y)
    (A : FinHolAtlas E Z) (f : Y → Z), HoloMap B A f →
    ∀ (V : Set Z), IsOpen V → ∀ (g : ℝ → Z → ℝ) (φ : Z → ℝ) (φ' : Y → ℝ),
      A.SmoothOn V φ → (∀ y ∈ f ⁻¹' V, φ' y = φ (f y)) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (g t)) →
      C2ConvOn A V g φ → C2ConvOn B (f ⁻¹' V) (fun t => g t ∘ f) φ'

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UniformIntegrability
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (mInt)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem mixedForms_all {W : Type} [TopologicalSpace W] {D : ℕ} (Om : ReciprocityTheory.AnForm.M.LocPot W)
    (T : Fin (D + 1) → ReciprocityTheory.AnForm.M.LocPot W) : mixedForms Om T (D + 1) = T :=
  funext fun i => if_pos i.isLt

theorem UniformIntegrability.proof (h₀ : GreenMassZero.Statement) (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement := by
  intro D W _ _ _ S
  have key : ∀ a, a ≤ D + 1 → ∀ η, 0 < η → ∃ ε₀, 0 < ε₀ ∧ ∃ t₁, 0 < t₁ ∧ ∀ ε t, 0 < ε →
      ε ≤ ε₀ → 0 < t → t ≤ t₁ → S.ell₀ ≤ ell t → S.J a ε t ≤ η := by
    intro a
    induction a with
    | zero =>
      intro _ η hη
      obtain ⟨ε₀, hε₀, h⟩ := h₀ S η hη
      exact ⟨ε₀, hε₀, 1, one_pos, fun ε t hε hεle _ _ _ => h ε hε hεle t⟩
    | succ a ih =>
      intro haD η hη
      have ha : a < D + 1 := haD
      obtain ⟨Cκ, hCκ, hR⟩ := h₂ S
      have hδ : 0 < η / (2 * (Cκ + 2)) := by positivity
      obtain ⟨τ, hτ, hE⟩ := h₃ S a ha _ hδ

      have ht₀ : 0 < min τ (Real.exp (-S.ell₀)) := lt_min hτ (Real.exp_pos _)
      have hell : S.ell₀ ≤ ell (min τ (Real.exp (-S.ell₀))) := by
        have h : Real.log (min τ (Real.exp (-S.ell₀))) ≤ -S.ell₀ :=
          (Real.log_le_iff_le_exp ht₀).2 (min_le_right _ _)
        show S.ell₀ ≤ Real.log (min τ (Real.exp (-S.ell₀)))⁻¹
        rw [Real.log_inv]
        linarith
      obtain ⟨K, hK, hRK⟩ := hR a ha _ ht₀ hell
      obtain ⟨ε₁, hε₁, t₂, ht₂, hih⟩ := ih (Nat.le_of_succ_le haD) (η / (2 * (K + 1)))
        (by positivity)
      refine ⟨min ε₁ 1, lt_min hε₁ one_pos, min t₂ (min τ (Real.exp (-S.ell₀))),
        lt_min ht₂ ht₀, ?_⟩
      intro ε t hε hεle ht htle htell
      have hJ := hih ε t hε (hεle.trans (min_le_left _ _)) ht (htle.trans (min_le_left _ _)) htell
      have hPL := h₁ S a ha ε t hε ht htell
      have hRep := hRK ε t hε (hεle.trans (min_le_right _ _)) ht (htle.trans (min_le_right _ _))
      obtain ⟨hW, hD⟩ := hE _ t ht (htle.trans (min_le_right _ _)) (min_le_left _ _) hell
      have e1 : (1 + K) * S.J a ε t ≤ η / 2 := by
        calc (1 + K) * S.J a ε t ≤ (1 + K) * (η / (2 * (K + 1))) :=
              mul_le_mul_of_nonneg_left hJ (by linarith)
          _ = η / 2 := by field_simp; ring
      have e2 : Cκ * S.errW a ha (min τ (Real.exp (-S.ell₀))) t +
          2 * S.errDiv a ha (min τ (Real.exp (-S.ell₀))) t ≤ η / 2 := by
        have := mul_le_mul_of_nonneg_left hW hCκ
        calc _ ≤ Cκ * (η / (2 * (Cκ + 2))) + 2 * (η / (2 * (Cκ + 2))) := by linarith
          _ = η / 2 := by field_simp
      linarith
  intro η hη
  obtain ⟨ε₀, hε₀, t₁, ht₁, h⟩ := key (D + 1) le_rfl η hη
  refine ⟨ε₀, hε₀, t₁, ht₁, fun ε t hε hεle ht htle htell => ?_⟩
  have := h ε t hε hεle ht htle htell
  rwa [UIData.J, UIData.T, mixedForms_all] at this

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
