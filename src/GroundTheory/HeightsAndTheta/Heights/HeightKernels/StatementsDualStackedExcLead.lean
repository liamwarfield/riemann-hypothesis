module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcResidue
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartCutoffParts

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

def stackedFormEval {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) :
    MRing (stackedBlocks T) →+* MvPolynomial (Fin i) K :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl _, t⟩ => ∑ j, C ((b' t : Fin i → K) j) * X j
    | ⟨.inr _, t⟩ => ∑ j, C ((b t : Fin i → K) j) * X j

def bidegree (d e : ℕ) : Unit ⊕ Unit → ℕ := Sum.elim (fun _ => d) (fun _ => e)

def DualStackedGraphBihomog.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ f ∈ stackedGraph b' a, ∃ (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → MRing (stackedBlocks T)),
      f = ∑ p ∈ s, g p ∧ ∀ p ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g p) (bidegree p.1 p.2) ∧ stackedFormEval b b' (g p) = 0

def DualStackedExcLeadForm.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (α : T → k) (M : T → Fin i → k), IsExcResidueData b b' α M →
      ∀ (d e : ℕ) (f : MRing (stackedBlocks T)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (bidegree d e) →
        stackedFormEval b b' f = 0 → linPointMap α M f = 0

namespace DualStackedExcLeadExample

theorem stackedFormEval_first {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) (t : T) :
    stackedFormEval b b' (graphFirst t) = ∑ j, C ((b' t : Fin i → K) j) * X j := by
  simp [stackedFormEval, graphFirst]

theorem stackedFormEval_second {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) (t : T) :
    stackedFormEval b b' (graphSecond t) = ∑ j, C ((b t : Fin i → K) j) * X j := by
  simp [stackedFormEval, graphSecond]

end DualStackedExcLeadExample

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsIntCoordChange
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

variable {T T₂ : Type} [Fintype T] [DecidableEq T] [Fintype T₂]

def intCoordSubst (A : Matrix T T₂ ℤ) : MRing (dualBlocks T₂) →ₐ[ℤ] MRing (dualBlocks T) :=
  aeval fun p => ∑ t, C (A t p.2) * X (⟨(), t⟩ : Σ _ : Unit, T)

def intCoordPt (A : Matrix T T₂ ℤ) (z : (Σ _ : Unit, T) → ℂ) : (Σ _ : Unit, T₂) → ℂ :=
  fun p => ∑ t, z ⟨(), t⟩ * (A t p.2 : ℂ)

theorem intCoordPt_ne_zero {A : Matrix T T₂ ℤ} (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    {z : (Σ _ : Unit, T) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, intCoordPt A z ⟨k, i⟩ ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := hA
  rintro ⟨⟩
  obtain ⟨t, ht⟩ := hz ()
  by_contra h
  push Not at h
  apply ht
  have h1 : ∀ t', (((A * B) t' t : ℤ) : ℂ) = ∑ s, (A t' s : ℂ) * (B s t : ℂ) := by
    intro t'
    simp [Matrix.mul_apply]
  have key : z ⟨(), t⟩ = ∑ s, intCoordPt A z ⟨(), s⟩ * (B s t : ℂ) := by
    simp only [intCoordPt, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, ← h1, hB, Matrix.one_apply]
    simp
  rw [key]
  exact Finset.sum_eq_zero fun s _ => by rw [h s, zero_mul]

def intCoordLine (A : Matrix T T₂ ℤ) (hA : ∃ B : Matrix T₂ T ℤ, A * B = 1)
    (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)) : ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T) where
  a := L.a
  h z := L.h (intCoordPt A z)
  pos z hz := L.pos _ (intCoordPt_ne_zero hA hz)
  smul c z hc := by
    have hz : intCoordPt A (fun p => c p.1 * z p) = fun p => c p.1 * intCoordPt A z p := by
      funext p
      obtain ⟨⟨⟩, s⟩ := p
      simp only [intCoordPt, Finset.mul_sum, mul_assoc]
    rw [hz, L.smul c _ hc]

def IntCoordChange.Statement : Prop :=
  ∀ (T T₂ : Type) [Fintype T] [DecidableEq T] [Fintype T₂] [DecidableEq T₂] (A : Matrix T T₂ ℤ)
    (B : Matrix T₂ T ℤ) (hAB : A * B = 1), B * A = 1 → ∀ (II : IntersectionSystem),
    IsIntersectionSystem II → ∀ (P : Ideal (MRing (dualBlocks T₂))) (n : ℕ)
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (dualBlocks T₂)), 1 ≤ n → IsArithVar P n → (∀ j, IsSmoothHerm (L j)) →
    II Unit (dualBlocks T) (P.map (intCoordSubst A)) n (fun j => intCoordLine A ⟨B, hAB⟩ (L j)) =
      II Unit (dualBlocks T₂) P n L

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartIbpSymm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo Matrix MeasureTheory Filter Topology ChartIntegrationByPartsSymmetry
open scoped ComplexOrder

noncomputable section

theorem ChartIbpSymm.proof (hCut : ChartIbpCutoff.Statement) : ChartIbpSymm.Statement := by
  intro n A B C D T hA hB hC hD hT
  have hF := integrable_pot_mul_maDensity hA hB hC hD hT
  have hG := integrable_pot_mul_maDensity hC hD hA hB hT
  have hFG := hF.sub hG
  have hlim : Tendsto (fun k : ℕ => ∫ y : Fin (n + 1) → ℂ, chartCutoff k y *
      ((hermChartPot A y - hermChartPot B y) *
          maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
            fun i => hermChartPot (T i)) y -
        (hermChartPot C y - hermChartPot D y) *
          maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
            fun i => hermChartPot (T i)) y))
      atTop (𝓝 (∫ y : Fin (n + 1) → ℂ,
        ((hermChartPot A y - hermChartPot B y) *
            maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
              fun i => hermChartPot (T i)) y -
          (hermChartPot C y - hermChartPot D y) *
            maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
              fun i => hermChartPot (T i)) y))) := by
    refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hFG.norm (fun k => ?_) ?_
    · exact (contDiff_chartCutoff k 0).continuous.aestronglyMeasurable.mul hFG.aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (chartCutoff_nonneg k y)]
      exact chartCutoff_le_one k y
    · refine Eventually.of_forall fun y => ?_
      simpa using (tendsto_chartCutoff y).mul_const
        ((hermChartPot A y - hermChartPot B y) *
            maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y')
              fun i => hermChartPot (T i)) y -
          (hermChartPot C y - hermChartPot D y) *
            maDensity (Fin.cons (fun y' => hermChartPot A y' - hermChartPot B y')
              fun i => hermChartPot (T i)) y)
  have h0 := tendsto_nhds_unique hlim (hCut n A B C D T hA hB hC hD hT)
  rw [integral_sub hF hG] at h0
  linarith

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDiffEnergy
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyDifferenceBound

theorem cross_le {u U χ a p G : ℝ} (hU : |u| ≤ U) (hχ : 0 ≤ χ) (hp : 0 ≤ p) (hG : 0 ≤ G)
    (ha : |a| ≤ Real.sqrt p * Real.sqrt G) :
    -(u * (χ * a + χ * a)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by
  have hsp := Real.sq_sqrt hp
  have hsG := Real.sq_sqrt hG
  have h0 : 0 ≤ |u| := abs_nonneg u
  have hua : -(u * a) ≤ |u| * |a| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have h1 : -(u * (χ * a + χ * a)) ≤ 2 * χ * (|u| * |a|) := by
    nlinarith [mul_le_mul_of_nonneg_left hua hχ]
  have hb : |u| * |a| ≤ U * (Real.sqrt p * Real.sqrt G) := mul_le_mul hU ha (abs_nonneg a) (h0.trans hU)
  have h2 : 2 * χ * (|u| * |a|) ≤ 2 * χ * (U * (Real.sqrt p * Real.sqrt G)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : 2 * χ * (U * (Real.sqrt p * Real.sqrt G)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by
    nlinarith [sq_nonneg (2 * U * Real.sqrt p - χ * Real.sqrt G)]
  linarith

end ChartEnergyDifferenceBound

open ChartIntegrationByPartsSymmetry ChartEnergyDifferenceBound

theorem ChartDiffEnergy.proof (hE : ChartCutoffEnergy.Statement) : ChartDiffEnergy.Statement := by
  intro n A B T hA hB hT
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  set u : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot A y - hermChartPot B y with hudef
  have hφ3 : ∀ i, ContDiff ℝ 3 (φ i) := fun i => contDiff_hermChartPot_of_le 3 (hT i)
  have hφ2 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => contDiff_hermChartPot_of_le 2 (hT i)
  have hu3 : ContDiff ℝ 3 u := (contDiff_hermChartPot_of_le 3 hA).sub (contDiff_hermChartPot_of_le 3 hB)
  have hu1 : ContDiff ℝ 1 u := hu3.of_le (by norm_num)
  have hGc : Continuous (gradDens φ u u) := continuous_gradDens hφ2 hu1 hu1
  have hG0 : ∀ y, 0 ≤ gradDens φ u u y := gradDens_chart_nonneg hT u
  obtain ⟨U, hU⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hA hB
  have hUa : ∀ y, |u y| ≤ U := fun y => by
    have := hU y
    rwa [Real.norm_eq_abs] at this
  obtain ⟨K, hK⟩ := hE n T hT
  have hI : Integrable (fun y => u y * maDens (Fin.cons u φ) y) :=
    integrable_pot_mul_maDensity hA hB hA hB hT
  set I : ℝ := ∫ y, |u y * maDens (Fin.cons u φ) y| with hIdef
  have hψG : ∀ k : ℕ, Integrable (fun y => chartCutoff k y * chartCutoff k y * gradDens φ u u y) := fun k =>
    (((contDiff_chartCutoff k 0).continuous.mul (contDiff_chartCutoff k 0).continuous).mul
      hGc).integrable_of_hasCompactSupport (hasCompactSupport_chartCutoff k).mul_right.mul_right
  have hX : ∀ k : ℕ, ∫ y, chartCutoff k y * chartCutoff k y * gradDens φ u u y ≤ 2 * I + 4 * U ^ 2 * K := by
    intro k
    set χ : (Fin (n + 1) → ℂ) → ℝ := chartCutoff k with hχdef
    have hχ3 : ContDiff ℝ 3 χ := contDiff_chartCutoff k 3
    have hχ1 : ContDiff ℝ 1 χ := contDiff_chartCutoff k 1
    have hψ3 : ContDiff ℝ 3 (fun y => χ y * χ y) := hχ3.mul hχ3
    have hψc : HasCompactSupport (fun y => χ y * χ y) := (hasCompactSupport_chartCutoff k).mul_right
    obtain ⟨i1, i2, i3, heq⟩ := parts_cutoff hφ3 hψ3 hψc hu3 hu3
    have hP : Integrable (gradDens φ χ χ) :=
      (continuous_gradDens hφ2 hχ1 hχ1).integrable_of_hasCompactSupport
        (hasCompactSupport_gradDens_left φ χ (hasCompactSupport_chartCutoff k))
    have hL : ∀ y, gradDens φ (fun y => χ y * χ y) u y = χ y * gradDens φ χ u y + χ y * gradDens φ χ u y :=
      fun y => (gradDensLeibniz_thm n φ χ χ u y (hχ1.differentiable one_ne_zero y)
        (hχ1.differentiable one_ne_zero y)).1
    have hpt : ∀ y, -(χ y * χ y * u y * maDens (Fin.cons u φ) y) - u y * gradDens φ (fun y => χ y * χ y) u y ≤
        |u y * maDens (Fin.cons u φ) y| + (2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2) := by
      intro y
      rw [hL y]
      have h0 : 0 ≤ χ y := chartCutoff_nonneg k y
      have h1 : χ y ≤ 1 := chartCutoff_le_one k y
      have hψ0 : 0 ≤ χ y * χ y := mul_nonneg h0 h0
      have hψ1 : χ y * χ y ≤ 1 := by nlinarith
      have ht := neg_abs_le (u y * maDens (Fin.cons u φ) y)
      have ht0 := abs_nonneg (u y * maDens (Fin.cons u φ) y)
      have ha : -(χ y * χ y * u y * maDens (Fin.cons u φ) y) ≤ |u y * maDens (Fin.cons u φ) y| := by
        nlinarith [mul_nonneg hψ0 (by linarith : 0 ≤ |u y * maDens (Fin.cons u φ) y| + u y * maDens (Fin.cons u φ) y),
          mul_nonneg (by linarith : 0 ≤ 1 - χ y * χ y) ht0]
      have hb := cross_le (hUa y) h0 (gradDens_chart_nonneg hT χ y) (hG0 y) (abs_gradDens_chart_le hT χ u y)
      linarith
    have i1n : Integrable (fun y => -(χ y * χ y * u y * maDens (Fin.cons u φ) y)) := i1.neg
    have iL : Integrable (fun y => -(χ y * χ y * u y * maDens (Fin.cons u φ) y) -
        u y * gradDens φ (fun y => χ y * χ y) u y) := i1n.sub i3
    have iA : Integrable (fun y => |u y * maDens (Fin.cons u φ) y|) := hI.abs
    have iP : Integrable (fun y => 2 * U ^ 2 * gradDens φ χ χ y) := hP.const_mul _
    have iG : Integrable (fun y => χ y * χ y * gradDens φ u u y / 2) := i2.div_const 2
    have iPG : Integrable (fun y => 2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2) := iP.add iG
    have iR : Integrable (fun y => |u y * maDens (Fin.cons u φ) y| +
        (2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2)) := iA.add iPG
    have hXeq : ∫ y, χ y * χ y * gradDens φ u u y =
        ∫ y, (-(χ y * χ y * u y * maDens (Fin.cons u φ) y) - u y * gradDens φ (fun y => χ y * χ y) u y) := by
      rw [integral_sub i1n i3, integral_neg]
      linarith
    have hmono := integral_mono iL iR hpt
    rw [← hXeq, integral_add iA iPG, integral_add iP iG, integral_const_mul, integral_div] at hmono
    have hKk : 2 * U ^ 2 * ∫ y, gradDens φ χ χ y ≤ 2 * U ^ 2 * K :=
      mul_le_mul_of_nonneg_left (hK k) (by positivity)
    linarith
  set f : ℕ → (Fin (n + 1) → ℂ) → ENNReal :=
    fun k y => ENNReal.ofReal (chartCutoff k y * chartCutoff k y * gradDens φ u u y) with hfdef
  have hmono : ∀ y, Monotone fun k => f k y := by
    intro y a b hab
    apply ENNReal.ofReal_le_ofReal
    have h1 := chartCutoff_mono y hab
    have h0 := chartCutoff_nonneg a y
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h1 h0 (h0.trans h1)) (hG0 y)
  have htend : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (ENNReal.ofReal (gradDens φ u u y))) := by
    intro y
    have h := ((tendsto_chartCutoff y).mul (tendsto_chartCutoff y)).mul_const (gradDens φ u u y)
    rw [one_mul, one_mul] at h
    exact (ENNReal.continuous_ofReal.tendsto _).comp h
  have hfm : ∀ k, AEMeasurable (f k) volume := fun k => (hψG k).1.aemeasurable.ennreal_ofReal
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hfm (Eventually.of_forall hmono)
    (Eventually.of_forall htend)
  have hbd : ∀ k, ∫⁻ y, f k y ≤ ENNReal.ofReal (2 * I + 4 * U ^ 2 * K) := by
    intro k
    have hnn : ∀ y, 0 ≤ chartCutoff k y * chartCutoff k y * gradDens φ u u y := fun y =>
      mul_nonneg (mul_nonneg (chartCutoff_nonneg k y) (chartCutoff_nonneg k y)) (hG0 y)
    rw [hfdef, ← ofReal_integral_eq_lintegral_ofReal (hψG k) (Eventually.of_forall hnn)]
    exact ENNReal.ofReal_le_ofReal (hX k)
  refine ⟨hGc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hG0)]
  exact lt_of_le_of_lt (le_of_tendsto' hlim hbd) ENNReal.ofReal_lt_top

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartIbpCutoff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open ChartIntegrationByPartsSymmetry
open scoped ComplexOrder

noncomputable section

namespace ChartIntegrationByPartsCutoff

variable {n : ℕ}

theorem sqrt_mul_sqrt_le {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    Real.sqrt a * Real.sqrt b ≤ ε * a + b / (4 * ε) := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := sq_nonneg (2 * ε * Real.sqrt a - Real.sqrt b)
  have h4 : 0 < 4 * ε := by positivity
  have key : 4 * ε * (Real.sqrt a * Real.sqrt b) ≤ 4 * ε * (ε * a + b / (4 * ε)) := by
    rw [mul_add, mul_div_cancel₀ _ h4.ne']
    have e : (2 * ε * Real.sqrt a - Real.sqrt b) ^ 2 =
        4 * ε * (ε * a) + b - 4 * ε * (Real.sqrt a * Real.sqrt b) := by
      rw [sub_sq, mul_pow, mul_pow, h1, h2]
      ring
    linarith
  exact le_of_mul_le_mul_left key h4

def outer (n k : ℕ) : Set (Fin (n + 1) → ℂ) := {y | ((k : ℝ) + 1) ^ 2 ≤ ∑ i, ‖y i‖ ^ 2}

theorem measurableSet_outer (k : ℕ) : MeasurableSet (outer n k) :=
  (isClosed_le continuous_const (continuous_finsetSum _ fun i _ =>
    (continuous_norm.comp (continuous_apply i)).pow 2)).measurableSet

theorem tendsto_integral_outer {g : (Fin (n + 1) → ℂ) → ℝ} (hg : Integrable g) :
    Tendsto (fun k : ℕ => ∫ y, (outer n k).indicator g y) atTop (𝓝 0) := by
  have h0 : (∫ _y : Fin (n + 1) → ℂ, (0 : ℝ)) = 0 := integral_zero _ _
  rw [← h0]
  refine tendsto_integral_of_dominated_convergence (fun y => ‖g y‖)
    (fun k => (hg.indicator (measurableSet_outer k)).aestronglyMeasurable) hg.norm
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rw [Set.indicator]
    split_ifs
    · exact le_rfl
    · simp
  · obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, ‖y i‖ ^ 2)
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun k hk => ?_
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have : ¬ y ∈ outer n k := by
      simp only [outer, Set.mem_ofPred_eq, not_le]
      nlinarith
    simp [Set.indicator_of_notMem this]

theorem tendsto_boundary {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    {u w : (Fin (n + 1) → ℂ) → ℝ} {W : ℝ} (hW : ∀ y, ‖w y‖ ≤ W)
    (hE : Integrable (gradDens (fun i => hermChartPot (T i)) u u)) {K : ℝ}
    (hK : ∀ k : ℕ, ∫ y, gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K) :
    Tendsto (fun k : ℕ => ∫ y, w y * gradDens (fun i => hermChartPot (T i)) (chartCutoff k) u y) atTop (𝓝 0) := by
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  have h2 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => contDiff_hermChartPot_of_le 2 (hT i)
  have hone : ((1 : ℕ) : WithTop ℕ∞) ≤ 3 := by norm_num
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
  set t : ℕ → ℝ := fun k => ∫ y, (outer n k).indicator (gradDens φ u u) y with htdef
  have ht0 : ∀ k, 0 ≤ t k := fun k => integral_nonneg fun y =>
    Set.indicator_nonneg (fun y _ => gradDens_chart_nonneg hT u y) y
  set ε : ℕ → ℝ := fun k => Real.sqrt (t k + 1 / ((k : ℝ) + 1)) with hεdef
  have hεpos : ∀ k, 0 < ε k := fun k => Real.sqrt_pos.mpr (by have := ht0 k; positivity)
  have htε : ∀ k, t k ≤ ε k ^ 2 := fun k => by
    rw [hεdef, Real.sq_sqrt (by have := ht0 k; positivity)]
    have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hbound : ∀ k, |∫ y, w y * gradDens φ (chartCutoff k) u y| ≤ W * (ε k * (K + 1 / 4)) := by
    intro k
    have hχ3 := contDiff_chartCutoff (D := n + 1) k 3
    have hcc := hasCompactSupport_chartCutoff (D := n + 1) k
    have hiχ : Integrable (gradDens φ (chartCutoff k) (chartCutoff k)) :=
      (continuous_gradDens h2 (hχ3.of_le hone) (hχ3.of_le hone)).integrable_of_hasCompactSupport
        (hasCompactSupport_gradDens_left φ _ hcc)
    have hiO : Integrable ((outer n k).indicator (gradDens φ u u)) := hE.indicator (measurableSet_outer k)
    have hpt : ∀ y, ‖w y * gradDens φ (chartCutoff k) u y‖ ≤
        W * (ε k * gradDens φ (chartCutoff k) (chartCutoff k) y +
          (outer n k).indicator (gradDens φ u u) y / (4 * ε k)) := by
      intro y
      rw [norm_mul]
      have hnn := gradDens_chart_nonneg hT (chartCutoff k) y
      by_cases hy : y ∈ outer n k
      · rw [Set.indicator_of_mem hy]
        have hcs : ‖gradDens φ (chartCutoff k) u y‖ ≤
            ε k * gradDens φ (chartCutoff k) (chartCutoff k) y + gradDens φ u u y / (4 * ε k) :=
          (abs_gradDens_chart_le hT (chartCutoff k) u y).trans
            (sqrt_mul_sqrt_le hnn (gradDens_chart_nonneg hT u y) (hεpos k))
        exact mul_le_mul (hW y) hcs (norm_nonneg _) hW0
      · have hlt : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2 := by simpa [outer] using hy
        rw [gradDens_chartCutoff_left φ u hlt, Set.indicator_of_notMem hy, norm_zero, mul_zero, zero_div,
          add_zero]
        exact mul_nonneg hW0 (mul_nonneg (hεpos k).le hnn)
    have hint : Integrable fun y => W * (ε k * gradDens φ (chartCutoff k) (chartCutoff k) y +
        (outer n k).indicator (gradDens φ u u) y / (4 * ε k)) :=
      ((hiχ.const_mul (ε k)).add (hiO.div_const (4 * ε k))).const_mul W
    have h1 := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    rw [integral_const_mul, integral_add (hiχ.const_mul _) (hiO.div_const _), integral_const_mul, integral_div]
    refine mul_le_mul_of_nonneg_left ?_ hW0
    have hq : t k / (4 * ε k) ≤ ε k / 4 := by
      rw [div_le_div_iff₀ (by have := hεpos k; positivity) (by norm_num)]
      nlinarith [htε k, hεpos k]
    have := mul_le_mul_of_nonneg_left (hK k) (hεpos k).le
    change ε k * _ + t k / (4 * ε k) ≤ _
    nlinarith
  have htt : Tendsto t atTop (𝓝 0) := tendsto_integral_outer hE
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := ((htt.add hinv).sqrt)
    simpa [hεdef] using this
  have hB : Tendsto (fun k => W * (ε k * (K + 1 / 4))) atTop (𝓝 0) := by
    simpa using (hε.mul_const (K + 1 / 4)).const_mul W
  exact squeeze_zero_norm (fun k => (hbound k).trans_eq' (Real.norm_eq_abs _)) hB

end ChartIntegrationByPartsCutoff


open ChartIntegrationByPartsCutoff in
theorem ChartIbpCutoff.proof (hE : ChartCutoffEnergy.Statement) (hD : ChartDiffEnergy.Statement) :
    ChartIbpCutoff.Statement := by
  intro n A B C D T hA hB hC hD' hT
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  set u : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot A y - hermChartPot B y with hudef
  set w : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot C y - hermChartPot D y with hwdef
  have h3 : ∀ i, ContDiff ℝ 3 (φ i) := fun i => contDiff_hermChartPot_of_le 3 (hT i)
  have hu : ContDiff ℝ 3 u := (contDiff_hermChartPot_of_le 3 hA).sub (contDiff_hermChartPot_of_le 3 hB)
  have hw : ContDiff ℝ 3 w := (contDiff_hermChartPot_of_le 3 hC).sub (contDiff_hermChartPot_of_le 3 hD')
  obtain ⟨Wu, hWu⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hA hB
  obtain ⟨Ww, hWw⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hC hD'
  obtain ⟨K, hK⟩ := hE n T hT
  have key : ∀ k : ℕ, (∫ y, chartCutoff k y * (u y * maDensity (Fin.cons w φ) y - w y * maDensity (Fin.cons u φ) y))
      = (∫ y, w y * gradDens φ (chartCutoff k) u y) - ∫ y, u y * gradDens φ (chartCutoff k) w y := by
    intro k
    obtain ⟨i1, -, -, e1⟩ := parts_cutoff h3 (contDiff_chartCutoff k 3) (hasCompactSupport_chartCutoff k) hu hw
    obtain ⟨i2, -, -, e2⟩ := parts_cutoff h3 (contDiff_chartCutoff k 3) (hasCompactSupport_chartCutoff k) hw hu
    have hsplit : ∀ y, chartCutoff k y * (u y * maDensity (Fin.cons w φ) y - w y * maDensity (Fin.cons u φ) y) =
        chartCutoff k y * u y * maDens (Fin.cons w φ) y - chartCutoff k y * w y * maDens (Fin.cons u φ) y :=
      fun y => by change _ = _ * _ * maDensity _ y - _ * _ * maDensity _ y; ring
    simp_rw [hsplit]
    rw [integral_sub i1 i2, e1, e2]
    simp_rw [show ∀ y, gradDens φ w u y = gradDens φ u w y from gradDens_chart_comm hT w u]
    ring
  refine Tendsto.congr (fun k => (key k).symm) ?_
  rw [← sub_zero (0 : ℝ)]
  exact (tendsto_boundary hT hWw (hD n A B T hA hB hT) hK).sub (tendsto_boundary hT hWu (hD n C D T hC hD' hT) hK)

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualLatticeModPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualLatticeModPrime.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (𝔭 : Ideal (𝓞 K)), 𝔭.IsMaximal →
    ∃ σ : dualLattice F →+ (Fin i → 𝓞 K ⧸ 𝔭), Function.Surjective σ ∧
      ∀ (μ : 𝓞 K) (φ ψ : dualLattice F), (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) →
        σ ψ = Ideal.Quotient.mk 𝔭 μ • σ φ

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualCotangentKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def DualCotangentKer.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    (_b : Module.Basis T ℤ (dualLattice F)) (k : Type) [Field k] (ρ : 𝓞 K →+* k)
    (σ : dualLattice F →+ (Fin i → k)),
    Function.Surjective ρ → Function.Surjective σ →
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → σ ψ = ρ μ • σ φ) →
    ∀ ψ : dualLattice F, σ ψ = 0 →
      ψ ∈ Submodule.span ℤ {v : dualLattice F | ∃ (μ : 𝓞 K) (φ : dualLattice F), ρ μ = 0 ∧
        (v : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K)}

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcLinear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalLinearForms

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]
  {k : Type} [Field k] {b : Module.Basis T ℤ (dualLattice F)} {b' : Module.Basis T ℤ (dualLattice F')}
  {α : T → k} {M : T → Fin i → k}

theorem span_alpha (h : IsExcResidueData b b' α M) : Submodule.span ℤ (Set.range α) = ⊤ := by
  obtain ⟨-, ρ', -, -, hρ', -, -, -, -, hα, -⟩ := h
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨φ, rfl⟩ := hρ' x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← b'.sum_repr φ, map_sum]
  refine Submodule.sum_mem _ fun t _ => ?_
  rw [map_zsmul, ← hα t]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem linFormsIndep (h : IsExcResidueData b b' α M) : LinFormsIndep M := by
  obtain ⟨-, -, σ, -, -, hσ, -, -, -, -, hM⟩ := h
  intro w hw
  funext j
  obtain ⟨φ, hφ⟩ := hσ (Pi.single j 1)
  have hcomb : ∀ j', σ φ j' = ∑ t, (b.repr φ t : k) * M t j' := by
    intro j'
    have hs : σ φ = ∑ t, b.repr φ t • M t := by
      conv_lhs => rw [← b.sum_repr φ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [map_zsmul, hM]
    rw [hs, Finset.sum_apply]
    simp only [Pi.smul_apply, zsmul_eq_mul]
  have key : ∑ j', σ φ j' * w j' = 0 := by
    simp only [hcomb, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun t _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum, hw t, mul_zero]
  rw [hφ] at key
  simpa [Pi.single_apply] using key

end StackedExceptionalLinearForms


open StackedExceptionalLinearForms in
theorem DualStackedExcLinear.proof (hEx : DualStackedExcResidueExists.Statement)
    (hBase : DualStackedExcBaseLe.Statement) (hLe : DualStackedExcLinPrimeLe.Statement) :
    DualStackedExcLinear.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab E hE
  obtain ⟨k, hk, hkf, α, M, hD, hcard⟩ := hEx K i F F' T b b' a hi hlt hcov hab
  have h1 : stackedBase b' a ≤ linPrime α M := hBase K i F F' T b b' a hi hlt hcov hab k α M hD
  have h2 : linPrime α M ≤ E := hLe K i F F' T b b' a hi hlt hcov hab k α M hD E hE.1.1.1 hE.1.1.2 hE.2
  have hprime : (linPrime α M).IsPrime := RingHom.ker_isPrime _
  exact ⟨k, hk, hkf, α, M, span_alpha hD, linFormsIndep hD, le_antisymm (hE.1.2 ⟨hprime, h1⟩ h2) h2, hcard⟩

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChartParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField Matrix

noncomputable section

def latCombo {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    (b' : Module.Basis T ℤ (dualLattice F')) (c : T → ℤ) : Fin i → K :=
  ∑ t, c t • (b' t : Fin i → K)

def graphFirstForm {T : Type} [Fintype T] (c : T → ℤ) : MRing (stackedBlocks T) :=
  ∑ t, C (c t) * graphFirst t

def graphSecondForm {T : Type} [Fintype T] (d : T → ℤ) : MRing (stackedBlocks T) :=
  ∑ t, C (d t) * graphSecond t

def QuadIdentity {K : Type} [Field K] {i : ℕ} (φ₁ φ₂ φ₃ φ₄ : Fin i → K) : Prop :=
  ∀ x : Fin i → K, (φ₁ ⬝ᵥ x) * (φ₂ ⬝ᵥ x) = (φ₃ ⬝ᵥ x) * (φ₄ ⬝ᵥ x)

def excChartIdeal {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (u : T) :
    Ideal (MRing (stackedBlocks T)) :=
  stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u}

abbrev excChartRing {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (v u : T) : Type :=
  Localization.Away (Ideal.Quotient.mk (excChartIdeal b' a u) (graphFirst v * graphSecond u))

def excChartMap {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (v u : T) :
    MRing (stackedBlocks T) →+* excChartRing b' a v u :=
  (algebraMap (MRing (stackedBlocks T) ⧸ excChartIdeal b' a u) (excChartRing b' a v u)).comp
    (Ideal.Quotient.mk (excChartIdeal b' a u))

def DualStackedGraphQuadRel.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ),
    (∀ c₁ c₂ c₃ c₄ : T → ℤ,
      QuadIdentity (latCombo b' c₁) (latCombo b' c₂) (latCombo b' c₃) (latCombo b' c₄) →
      graphFirstForm c₁ * graphFirstForm c₂ - graphFirstForm c₃ * graphFirstForm c₄ ∈ stackedGraph b' a) ∧
    (∀ c₁ d₂ c₃ d₄ : T → ℤ,
      QuadIdentity (latCombo b' c₁) (latCombo b' fun t => d₂ t * a t) (latCombo b' c₃)
        (latCombo b' fun t => d₄ t * a t) →
      graphFirstForm c₁ * graphSecondForm d₂ - graphFirstForm c₃ * graphSecondForm d₄ ∈ stackedGraph b' a)

def DualStackedExcChartForms.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (ρ : 𝓞 K →+* k) (π : 𝓞 K) (y₀ : Fin i → K) (m : ℕ) (g : Fin m → Fin i → K)
      (α : T → k) (M : T → Fin (m + 1) → k), IsExcCoords F F' b b' ρ π y₀ g α M →
      ∀ v u : T, ∃ σ₀ : k →+* excChartRing b' a v u,
        (∀ (ω : 𝓞 K) (c : T → ℤ), latCombo b' c = algebraMap (𝓞 K) K ω • (b' v : Fin i → K) →
          σ₀ (ρ ω) * excChartMap b' a v u (graphFirst v) = excChartMap b' a v u (graphFirstForm c)) ∧
        ∃ W : Fin (m + 1) → excChartRing b' a v u,
          ∀ t, ∑ j, σ₀ (M t j) * W j = excChartMap b' a v u (graphSecond t)

namespace DualStackedExcChartPartsExample

end DualStackedExcChartPartsExample

end

end GroundTheory.Heights₂.Heights
end
