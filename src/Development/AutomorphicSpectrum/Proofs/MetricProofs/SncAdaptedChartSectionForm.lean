module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeLeOfMetricBoundedMap
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionForm
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionForm
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalModel

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousAt_of_chart {E : Type} [TopologicalSpace E] (A : FinHolAtlas e X) (j : Fin A.n) {p : X}
    (hp : p ∈ (A.chart j).source) (f : X → E)
    (h : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j p)) : ContinuousAt f p := by
  have h1 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp (f := A.chart j) h ((A.chart j).continuousAt hp)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hp] with z hz
  simp [(A.chart j).left_inv hz]

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {p : X} (hp : p ∈ U) : ContinuousAt g p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj g ?_
  refine (hg j _ ⟨(A.chart j).map_source hj, ?_⟩).continuousAt
  simpa [(A.chart j).left_inv hj] using hp

theorem continuousAt_of_smoothOn (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) {p : X} (hp : p ∈ U) : ContinuousAt f p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj f ?_
  have hmem : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hp⟩
  exact (hf j).continuousOn.continuousAt
    (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hmem)

theorem zero_set_and_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ (x : X) (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ → Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target → φ.source ⊆ L.U x → (∀ i ∈ S, 1 ≤ μ i) → A.HoloOn φ.source v → (∀ y ∈ φ.source, v y ≠ 0) → (∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i) → (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧ ∃ M : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s → |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
  intro e X _ A L s hL hs x φ S μ v hφ hball hsrc hμ hv hv0 hsv

  have glue : ∀ y ∈ φ.target, ‖s x (φ.symm y)‖ * Real.exp (-L.φ x (φ.symm y)) =
      ‖s (φ.symm y) (φ.symm y)‖ * Real.exp (-L.φ (φ.symm y) (φ.symm y)) := fun y hy =>
    hs.2 x (φ.symm y) (φ.symm y) ⟨hsrc (φ.map_target hy), L.mem_U _⟩
  have hform : ∀ y ∈ φ.target, s x (φ.symm y) = v (φ.symm y) * ∏ i ∈ S, y i ^ μ i := by
    intro y hy
    rw [hsv _ (φ.map_target hy)]
    simp only [φ.right_inv hy]
  have hzero : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
    intro y hy
    have h1 : s (φ.symm y) (φ.symm y) = 0 ↔ s x (φ.symm y) = 0 := by
      have hg := glue y hy
      constructor
      · intro h0
        rw [h0] at hg
        simpa [Real.exp_ne_zero] using hg
      · intro h0
        rw [h0, norm_zero, zero_mul] at hg
        rcases mul_eq_zero.1 hg.symm with h | h
        · exact norm_eq_zero.1 h
        · exact absurd h (Real.exp_ne_zero _)
    change s (φ.symm y) (φ.symm y) = 0 ↔ _
    rw [h1, hform y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact absurd h (hv0 _ (φ.map_target hy))
      · exact ⟨i, hi, (pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi))).1 h⟩
    · rintro ⟨i, hi, h⟩
      refine Or.inr ⟨i, hi, ?_⟩
      rw [h]
      exact zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))
  refine ⟨hzero, ?_⟩

  have hcont : ContinuousOn (fun y => -2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) φ.target := by
    intro y hy
    have hp := φ.map_target hy
    have cs : ContinuousAt φ.symm y := φ.continuousAt_symm hy
    have c1 : ContinuousAt (fun y => v (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm) (continuousAt_of_holoOn A hv hp) cs
    have c2 : ContinuousAt (fun y => L.φ x (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm)
        (continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (hsrc hp)) cs
    have c3 : ContinuousAt (fun y => Real.log ‖v (φ.symm y)‖) y :=
      c1.norm.log (norm_ne_zero_iff.2 (hv0 _ hp))
    exact ((continuousAt_const.mul c3).add (continuousAt_const.mul c2)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin e → ℂ) 2).exists_bound_of_continuousOn
    (hcont.mono hball)
  refine ⟨C + |(∑ i ∈ S, (μ i : ℝ)) * Real.log 4|, fun y hy hnb => ?_⟩
  have hyt := hball hy
  have hnz : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 => hnb ((hzero y hyt).2 ⟨i, hi, h0⟩)
  have hs0 : s (φ.symm y) (φ.symm y) ≠ 0 := hnb
  have hvn : ‖v (φ.symm y)‖ ≠ 0 := norm_ne_zero_iff.2 (hv0 _ (φ.map_target hyt))
  have hlogS : Real.log (∏ i ∈ S, ‖y i‖ ^ μ i) = ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    rw [Real.log_prod (fun i hi => pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))]
    exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _
  have hlog : logNormSec L s (φ.symm y) = Real.log ‖v (φ.symm y)‖ +
      ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x (φ.symm y) := by
    unfold logNormSec
    rw [← glue y hyt, hform y hyt, norm_mul, norm_prod]
    simp only [norm_pow]
    rw [Real.log_mul (mul_ne_zero hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))) (Real.exp_ne_zero _),
      Real.log_mul hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi))), hlogS, Real.log_exp]
    ring
  have hloc : rLoc S μ y = Real.exp 1 + (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 -
      2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    unfold rLoc
    rw [Finset.sum_mul, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn : ‖y i‖ ≠ 0 := norm_ne_zero_iff.2 (hnz i hi)
    rw [Real.log_div (by norm_num) (pow_ne_zero _ hn), Real.log_pow]
    push_cast
    ring
  have hdiff : rW L s (φ.symm y) - rLoc S μ y =
      (-2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) -
        (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 := by
    unfold rW
    rw [hlog, hloc]
    ring
  rw [hdiff]
  have hb := hC y hy
  rw [Real.norm_eq_abs] at hb
  exact (abs_sub _ _).trans (add_le_add hb le_rfl)

end GlobalTheory.CompanionTheory.Ar.PB.LocalModel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionFormStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_adapted_chart_section_form : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ (x : X) (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ → Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target → φ.source ⊆ L.U x → (∀ i ∈ S, 1 ≤ μ i) → A.HoloOn φ.source v → (∀ y ∈ φ.source, v y ≠ 0) → (∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i) → (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧ ∃ M : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s → |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.LocalModel.zero_set_and_bound | exact GlobalTheory.CompanionTheory.Ar.PB.LocalModel.zero_set_and_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.LocalModel.zero_set_and_bound <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjection
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

variable {e n : ℕ}

theorem continuous_comp_emb (σ : Fin n ↪ Fin e) :
    Continuous (fun w : Fin e → ℂ => w ∘ σ) :=
  continuous_pi fun j => continuous_apply (σ j)

theorem analyticAt_comp_emb (σ : Fin n ↪ Fin e) (w : Fin e → ℂ) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => v ∘ σ) w := by
  rw [analyticAt_pi_iff]
  intro j
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) (σ j)).analyticAt w

theorem extend_comp_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ g w ∘ σ = g :=
  funext fun j => σ.injective.extend_apply g w j

theorem extend_extend_emb (σ : Fin n ↪ Fin e) (g : Fin n → ℂ) (w : Fin e → ℂ) :
    Function.extend σ (w ∘ σ) (Function.extend σ g w) = w := by
  funext i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    exact σ.injective.extend_apply _ _ j
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]

theorem analyticAt_extend_emb (σ : Fin n ↪ Fin e) {f : (Fin n → ℂ) → Fin n → ℂ} {w : Fin e → ℂ}
    (hf : AnalyticAt ℂ f (w ∘ σ)) :
    AnalyticAt ℂ (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v) w := by
  rw [analyticAt_pi_iff]
  intro i
  by_cases h : ∃ j, σ j = i
  · obtain ⟨j, rfl⟩ := h
    have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v (σ j)) =
        (fun y : Fin n → ℂ => f y j) ∘ (fun v : Fin e → ℂ => v ∘ σ) := by
      funext v
      exact σ.injective.extend_apply _ _ j
    rw [hfun]
    exact AnalyticAt.comp (analyticAt_pi_iff.1 hf j) (analyticAt_comp_emb σ w)
  · have hfun : (fun v : Fin e → ℂ => Function.extend σ (f (v ∘ σ)) v i) = fun v => v i := by
      funext v
      exact Function.extend_apply' _ _ _ h
    rw [hfun]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt w

noncomputable def extendHomeo (σ : Fin n ↪ Fin e)
    (τ : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
    (h₁ : AnalyticOnNhd ℂ τ τ.source) (h₂ : AnalyticOnNhd ℂ τ.symm τ.target) :
    OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) where
  toFun w := Function.extend σ (τ (w ∘ σ)) w
  invFun w := Function.extend σ (τ.symm (w ∘ σ)) w
  source := {w | w ∘ σ ∈ τ.source}
  target := {w | w ∘ σ ∈ τ.target}
  map_source' w hw := by
    show Function.extend σ (τ (w ∘ σ)) w ∘ σ ∈ τ.target
    rw [extend_comp_emb]
    exact τ.map_source hw
  map_target' w hw := by
    show Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ ∈ τ.source
    rw [extend_comp_emb]
    exact τ.map_target hw
  left_inv' w hw := by
    show Function.extend σ (τ.symm (Function.extend σ (τ (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.left_inv hw, extend_extend_emb]
  right_inv' w hw := by
    show Function.extend σ (τ (Function.extend σ (τ.symm (w ∘ σ)) w ∘ σ))
      (Function.extend σ (τ.symm (w ∘ σ)) w) = w
    rw [extend_comp_emb, τ.right_inv hw, extend_extend_emb]
  open_source := τ.open_source.preimage (continuous_comp_emb σ)
  open_target := τ.open_target.preimage (continuous_comp_emb σ)
  continuousOn_toFun := fun w hw =>
    (analyticAt_extend_emb σ (h₁ _ hw)).continuousAt.continuousWithinAt
  continuousOn_invFun := fun w hw =>
    (analyticAt_extend_emb σ (h₂ _ hw)).continuousAt.continuousWithinAt

theorem chart_swap :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ ∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i := by
  intro e n X Z _ _ A Ab pr ψ kb σ ψb hψ hb hpr
  have h₁ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb)
      ((Ab.chart kb).symm.trans ψb).source := by
    intro y hy
    exact (hb kb).1 y hy
  have h₂ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb).symm
      ((Ab.chart kb).symm.trans ψb).target := by
    intro y hy
    exact (hb kb).2 y hy
  have hcomp : ∀ y ∈ ψ.source, ψ y ∘ σ = Ab.chart kb (pr y) := fun y hy =>
    funext fun i => ((hpr y hy).2 i).symm
  let T := extendHomeo σ ((Ab.chart kb).symm.trans ψb) h₁ h₂
  have hTan : ∀ w ∈ T.source, AnalyticAt ℂ T w := fun w hw =>
    analyticAt_extend_emb σ (h₁ _ hw)
  have hTsan : ∀ w ∈ T.target, AnalyticAt ℂ T.symm w := fun w hw =>
    analyticAt_extend_emb σ (h₂ _ hw)
  have hsrc : (ψ.trans T).source = ψ.source ∩ pr ⁻¹' ψb.source := by
    ext y
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      have h3 : ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source := hy'
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source] at h3
      have h4 := h3.2
      simp only [Set.mem_preimage] at h4
      rwa [(Ab.chart kb).left_inv (hpr y hy).1] at h4
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      show ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source]
      refine ⟨(Ab.chart kb).map_source (hpr y hy).1, ?_⟩
      simp only [Set.mem_preimage]
      rwa [(Ab.chart kb).left_inv (hpr y hy).1]
  refine ⟨ψ.trans T, ?_, hsrc, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hy2
      have h := (hψ j).1 y ⟨hy1, hy2.1⟩
      exact AnalyticAt.comp (g := T) (f := ψ ∘ (A.chart j).symm) (hTan _ hy2.2) h
    · rintro z ⟨hz1, hz2⟩
      rw [OpenPartialHomeomorph.trans_target] at hz1
      have h := (hψ j).2 (T.symm z) ⟨hz1.2, hz2⟩
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := T.symm) h (hTsan z hz1.1)
  · intro y hy i
    rw [hsrc] at hy
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) (σ i) = ψb (pr y) i
    rw [σ.injective.extend_apply, hcomp y hy.1]
    show ψb ((Ab.chart kb).symm (Ab.chart kb (pr y))) i = ψb (pr y) i
    rw [(Ab.chart kb).left_inv (hpr y hy.1).1]

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_chart_product_projection : ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ ∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap | exact GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.ChartSwap.chart_swap <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedAtlasSmoothPotentialLocal
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCGradAtlas
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace PositivityTheory.Xgp.c_grad_atlas

theorem mono_bd {r a c C t : ℝ} (hr : 1 ≤ r) (ha : 0 ≤ a) (ht : t ≤ c * r ^ c)
    (h1 : a * |c| ≤ C) (h2 : |c| ≤ C) : a * t ≤ C * r ^ C := by
  have hC : 0 ≤ C := le_trans (abs_nonneg c) h2
  have hr0 : 0 < r := by linarith
  have hrC : 0 < r ^ C := Real.rpow_pos_of_pos hr0 C
  have hrc0 : 0 < r ^ c := Real.rpow_pos_of_pos hr0 c
  have h3 : a * t ≤ a * (c * r ^ c) := mul_le_mul_of_nonneg_left ht ha
  rcases le_or_gt 0 c with hc | hc
  · have hcC : c ≤ C := le_trans (le_abs_self c) h2
    have hrc : r ^ c ≤ r ^ C := Real.rpow_le_rpow_of_exponent_le hr hcC
    have hac : a * c ≤ C := by
      rw [abs_of_nonneg hc] at h1
      exact h1
    calc a * t ≤ a * (c * r ^ c) := h3
      _ = (a * c) * r ^ c := by ring
      _ ≤ C * r ^ c := mul_le_mul_of_nonneg_right hac hrc0.le
      _ ≤ C * r ^ C := mul_le_mul_of_nonneg_left hrc hC
  · have h4 : c * r ^ c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc.le hrc0.le
    have h5 : a * (c * r ^ c) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha h4
    nlinarith [mul_nonneg hC hrC.le]

theorem isOpen_compl_bdry {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (hs : IsSection A L s) : IsOpen (bdry s)ᶜ := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : s x x ≠ 0 := hx
  obtain ⟨j, hj⟩ := A.cover x
  have hf := hs.1 x j
  have hmem : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (L.U x) := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, (A.chart j).left_inv hj]
    exact L.mem_U x
  have hc1 : ContinuousAt (s x ∘ (A.chart j).symm) ((A.chart j) x) := (hf _ hmem).continuousAt
  have hc2 : ContinuousAt ((s x ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    hc1.comp ((A.chart j).continuousAt hj)
  have heq : ((s x ∘ (A.chart j).symm) ∘ (A.chart j)) =ᶠ[𝓝 x] s x := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
    simp [(A.chart j).left_inv hy]
  have hc : ContinuousAt (s x) x := hc2.congr heq
  have hne : ∀ᶠ y in 𝓝 x, s x y ≠ 0 := hc.eventually_ne hx'
  filter_upwards [hne, (L.isOpen_U x).mem_nhds (L.mem_U x)] with y hy hyU
  show s y y ≠ 0
  intro h0
  have key := hs.2 x y y ⟨hyU, L.mem_U y⟩
  rw [h0, norm_zero, zero_mul] at key
  have : 0 < ‖s x y‖ * Real.exp (-L.φ x y) := mul_pos (norm_pos_iff.mpr hy) (Real.exp_pos _)
  linarith

theorem local_bd {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (hs : IsSection A L s) (hn : ∀ y, logNormSec L s y ≤ 0) (hAB : A.Compatible B)
    (ph : X → ℝ) (hph : A.SmoothOn (bdry s)ᶜ ph) (j : Fin B.n) (y₀ : Fin e → ℂ) (hy₀ : y₀ ∈ (B.chart j).target)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (V : Set X) (c : ℝ) (hψ : IsCompatChart A ψ) (hV : IsOpen V)
    (hx : (B.chart j).symm y₀ ∈ V) (hVs : V ⊆ ψ.source)
    (hb : ∀ x' ∈ V, x' ∉ bdry s →
      ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2)) :
    ∃ C₅, ∀ᶠ y in 𝓝 y₀, ∀ C, C₅ ≤ C → (B.chart j).symm y ∉ bdry s →
      ‖fderiv ℝ (ph ∘ (B.chart j).symm) y‖ ≤
        C * rW L s ((B.chart j).symm y) ^ C * Real.exp (rW L s ((B.chart j).symm y) / 2) := by
  set φ := B.chart j with hφ
  set τ : (Fin e → ℂ) → (Fin e → ℂ) := ψ ∘ φ.symm with hτ
  have hx₀ψ : φ.symm y₀ ∈ ψ.source := hVs hx
  obtain ⟨k, hk⟩ := A.cover (φ.symm y₀)
  have hτan : AnalyticAt ℂ τ y₀ := by
    have h1 : AnalyticAt ℂ (A.chart k ∘ φ.symm) y₀ := hAB.2 j k y₀ ⟨hy₀, hk⟩
    have h2 : AnalyticAt ℂ (ψ ∘ (A.chart k).symm) ((A.chart k ∘ φ.symm) y₀) := by
      apply (hψ k).1
      refine ⟨(A.chart k).map_source hk, ?_⟩
      simp only [Set.mem_preimage, Function.comp_apply, (A.chart k).left_inv hk]
      exact hx₀ψ
    have h3 := h2.comp h1
    apply h3.congr
    have hnb : φ.symm ⁻¹' (A.chart k).source ∈ 𝓝 y₀ :=
      (φ.continuousAt_symm hy₀).preimage_mem_nhds ((A.chart k).open_source.mem_nhds hk)
    filter_upwards [hnb] with y hy
    simp [hτ, (A.chart k).left_inv hy]
  have hev := hτan.eventually_analyticAt
  have hdc : ContinuousAt (fderiv ℂ τ) y₀ := hτan.fderiv.continuousAt
  set K := ‖fderiv ℂ τ y₀‖ + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  have hKev : ∀ᶠ y in 𝓝 y₀, ‖fderiv ℂ τ y‖ < K :=
    hdc.norm.eventually (Iio_mem_nhds (by linarith))
  have hW : ∀ᶠ y in 𝓝 y₀, y ∈ φ.target ∧ φ.symm y ∈ V := by
    have h1 : φ.target ∈ 𝓝 y₀ := φ.open_target.mem_nhds hy₀
    have h2 : φ.symm ⁻¹' V ∈ 𝓝 y₀ := (φ.continuousAt_symm hy₀).preimage_mem_nhds (hV.mem_nhds hx)
    filter_upwards [h1, h2] with y a b
    exact ⟨a, b⟩
  refine ⟨max (K * |c|) |c|, ?_⟩
  have hWnhds : ∀ᶠ y in 𝓝 y₀, ∀ᶠ y' in 𝓝 y, y' ∈ φ.target ∧ φ.symm y' ∈ V := hW.eventually_nhds
  filter_upwards [hev, hKev, hW, hWnhds] with y hyan hyK hyW hyW'
  intro C hC hyb
  have hx'V : φ.symm y ∈ V := hyW.2
  have hx'ψ : φ.symm y ∈ ψ.source := hVs hx'V
  have hτy : τ y = ψ (φ.symm y) := rfl
  have hψt : τ y ∈ ψ.target := by
    rw [hτy]
    exact ψ.map_source hx'ψ
  have hψl : ψ.symm (τ y) = φ.symm y := by
    rw [hτy]
    exact ψ.left_inv hx'ψ
  have hgd : DifferentiableAt ℝ (ph ∘ ψ.symm) (τ y) := by
    obtain ⟨k', hk'⟩ := A.cover (φ.symm y)
    have hopen : IsOpen ((A.chart k').target ∩ (A.chart k').symm ⁻¹' (bdry s)ᶜ) :=
      (A.chart k').continuousOn_symm.isOpen_inter_preimage (A.chart k').open_target
        (isOpen_compl_bdry A L s hs)
    have hmem : (A.chart k') (φ.symm y) ∈ (A.chart k').target ∩ (A.chart k').symm ⁻¹' (bdry s)ᶜ := by
      refine ⟨(A.chart k').map_source hk', ?_⟩
      simp only [Set.mem_preimage, (A.chart k').left_inv hk']
      exact hyb
    have hd1 : DifferentiableAt ℝ (ph ∘ (A.chart k').symm) ((A.chart k') (φ.symm y)) :=
      ((hph k').differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
    have hd2 : AnalyticAt ℂ ((A.chart k') ∘ ψ.symm) (τ y) := by
      apply (hψ k').2
      refine ⟨hψt, ?_⟩
      simp only [Set.mem_preimage, hψl]
      exact hk'
    have hd3 : DifferentiableAt ℝ ((ph ∘ (A.chart k').symm) ∘ ((A.chart k') ∘ ψ.symm)) (τ y) := by
      apply DifferentiableAt.comp (τ y)
      · rw [Function.comp_apply, hψl]
        exact hd1
      · exact hd2.differentiableAt.restrictScalars ℝ
    apply hd3.congr_of_eventuallyEq
    have hnb : ψ.symm ⁻¹' (A.chart k').source ∈ 𝓝 (τ y) :=
      (ψ.continuousAt_symm hψt).preimage_mem_nhds
        ((A.chart k').open_source.mem_nhds (by rw [hψl]; exact hk'))
    filter_upwards [hnb] with z hz
    simp [(A.chart k').left_inv hz]
  have hτd : DifferentiableAt ℝ τ y := hyan.differentiableAt.restrictScalars ℝ
  have hfeq : fderiv ℝ (ph ∘ φ.symm) y = fderiv ℝ ((ph ∘ ψ.symm) ∘ τ) y := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hyW'] with z hz
    simp [hτ, ψ.left_inv (hVs hz.2)]
  have hchain : fderiv ℝ ((ph ∘ ψ.symm) ∘ τ) y =
      (fderiv ℝ (ph ∘ ψ.symm) (τ y)).comp (fderiv ℝ τ y) := fderiv_comp y hgd hτd
  have hτn : ‖fderiv ℝ τ y‖ ≤ K := by
    rw [(hyan.differentiableAt.hasFDerivAt.restrictScalars ℝ).fderiv]
    rw [ContinuousLinearMap.norm_restrictScalars]
    exact hyK.le
  have hgb : ‖fderiv ℝ (ph ∘ ψ.symm) (τ y)‖ ≤
      c * rW L s (φ.symm y) ^ c * Real.exp (rW L s (φ.symm y) / 2) := hb _ hx'V hyb
  have hr1 : 1 ≤ rW L s (φ.symm y) := by
    have h0 := hn (φ.symm y)
    have he : (1:ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1:ℝ)
      linarith
    show 1 ≤ Real.exp 1 - 2 * logNormSec L s (φ.symm y)
    linarith
  have hm := mono_bd (t := c * rW L s (φ.symm y) ^ c) hr1 hK0 le_rfl
    (le_trans (le_max_left _ _) hC) (le_trans (le_max_right _ _) hC)
  have hE : 0 < Real.exp (rW L s (φ.symm y) / 2) := Real.exp_pos _
  rw [hfeq, hchain]
  calc ‖(fderiv ℝ (ph ∘ ψ.symm) (τ y)).comp (fderiv ℝ τ y)‖
      ≤ ‖fderiv ℝ (ph ∘ ψ.symm) (τ y)‖ * ‖fderiv ℝ τ y‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (c * rW L s (φ.symm y) ^ c * Real.exp (rW L s (φ.symm y) / 2)) * K :=
      mul_le_mul hgb hτn (norm_nonneg _) (le_trans (norm_nonneg _) hgb)
    _ = (K * (c * rW L s (φ.symm y) ^ c)) * Real.exp (rW L s (φ.symm y) / 2) := by ring
    _ ≤ (C * rW L s (φ.symm y) ^ C) * Real.exp (rW L s (φ.symm y) / 2) :=
      mul_le_mul_of_nonneg_right hm hE.le

end PositivityTheory.Xgp.c_grad_atlas


open PositivityTheory.Xgp.c_grad_atlas in
theorem PositivityTheory.Xgp.t_c_grad_atlas : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → ∀ ph : X → ℝ, A.SmoothOn (bdry s)ᶜ ph → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (V : Set X) (c : ℝ), IsCompatChart A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry s → ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2)) → ∃ C₅, ∀ C, C₅ ≤ C → IsGradBound B L s ph C := by
  intro e X _ _ _ A B L s nb m W hpot hsec hsnc hn had ph hph hloc
  have hj : ∀ j : Fin B.n, ∃ D : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) (3 / 2), ∀ C, D ≤ C →
      (B.chart j).symm y ∉ bdry s →
      ‖fderiv ℝ (ph ∘ (B.chart j).symm) y‖ ≤
        C * rW L s ((B.chart j).symm y) ^ C * Real.exp (rW L s ((B.chart j).symm y) / 2) := by
    intro j
    have hl : ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) (3 / 2), ∃ D : ℝ, ∀ᶠ z in 𝓝 y, ∀ C, D ≤ C →
        (B.chart j).symm z ∉ bdry s →
        ‖fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤
          C * rW L s ((B.chart j).symm z) ^ C * Real.exp (rW L s ((B.chart j).symm z) / 2) := by
      intro y hy
      have hyt : y ∈ (B.chart j).target :=
        had.2.1 j (Metric.closedBall_subset_closedBall (by norm_num) hy)
      obtain ⟨ψ, V, c, hψ, hV, hxV, hVs, hb⟩ := hloc ((B.chart j).symm y)
      exact local_bd A B L s hsec hn had.1 ph hph j y hyt ψ V c hψ hV hxV hVs hb
    choose! D hD using hl
    obtain ⟨t, -, hcov⟩ := (isCompact_closedBall (0 : Fin e → ℂ) (3 / 2)).elim_nhds_subcover
      (fun y => {z | ∀ C, D y ≤ C → (B.chart j).symm z ∉ bdry s →
        ‖fderiv ℝ (ph ∘ (B.chart j).symm) z‖ ≤
          C * rW L s ((B.chart j).symm z) ^ C * Real.exp (rW L s ((B.chart j).symm z) / 2)})
      (fun y hy => hD y hy)
    refine ⟨∑ y ∈ t, |D y|, ?_⟩
    intro z hz C hC hzb
    obtain ⟨y, hyt, hzU⟩ := Set.mem_iUnion₂.1 (hcov hz)
    have h1 : D y ≤ ∑ y ∈ t, |D y| :=
      le_trans (le_abs_self _) (Finset.single_le_sum (f := fun y => |D y|) (fun i _ => abs_nonneg _) hyt)
    exact hzU C (le_trans h1 hC) hzb
  choose Dj hDj using hj
  refine ⟨∑ j, |Dj j|, ?_⟩
  intro C hC j y hy hyb
  have h1 : Dj j ≤ ∑ j, |Dj j| :=
    le_trans (le_abs_self _) (Finset.single_le_sum (f := fun j => |Dj j|) (fun i _ => abs_nonneg _) (Finset.mem_univ j))
  exact hDj j y (Metric.ball_subset_closedBall hy) C (le_trans h1 hC) hyb
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedAtlasSmoothPotentialLocal
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gradBound_of_local_bounds : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → ∀ ph : X → ℝ, A.SmoothOn (bdry s)ᶜ ph → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (V : Set X) (c : ℝ), IsCompatChart A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry s → ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2)) → ∃ C₅, ∀ C, C₅ ≤ C → IsGradBound B L s ph C :=
  @PositivityTheory.Xgp.t_c_grad_atlas

end GlobalTheory.CompanionTheory.Ar.PB
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedAtlasSmoothPotentialLocalStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_atlas_smooth_potential_local : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → ∀ ph : X → ℝ, A.SmoothOn (bdry s)ᶜ ph → (∀ x, ∃ (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (V : Set X) (c : ℝ), IsCompatChart A ψ ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ ∀ x' ∈ V, x' ∉ bdry s → ‖fderiv ℝ (ph ∘ ψ.symm) (ψ x')‖ ≤ c * rW L s x' ^ c * Real.exp (rW L s x' / 2)) → ∃ C₅, ∀ C, C₅ ≤ C → IsGradBound B L s ph C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gradBound_of_local_bounds | exact GlobalTheory.CompanionTheory.Ar.PB.gradBound_of_local_bounds | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gradBound_of_local_bounds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeFullRankSublattice
section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeFullRankSubmoduleBounds
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

private theorem card_quotient_span_eq_relIndex {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (G : Submodule R M) {ι : Type*} (s : ι → G) :
    Nat.card (G ⧸ Submodule.span R (Set.range s)) =
      (Submodule.span R (Set.range fun i => (s i : M))).toAddSubgroup.relIndex G.toAddSubgroup := by
  have h : Submodule.span R (Set.range s) =
      (Submodule.span R (Set.range fun i => (s i : M))).comap G.subtype := by
    have hr : (Set.range fun i => (s i : M)) = G.subtype '' Set.range s := by
      rw [← Set.range_comp]
      rfl
    rw [hr, ← Submodule.map_span, Submodule.comap_map_eq_of_injective G.injective_subtype]
  rw [h]
  rfl

private theorem index_span_ne_zero_of_linearIndependent {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    {n : ℕ} (hn : Module.finrank (𝓞 K) E.carrier = n) (v : Fin n → E.carrier)
    (hv : LinearIndependent (𝓞 K) v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.index ≠ 0 := by
  classical
  have hfinZ : Module.Finite ℤ E.carrier := Module.Finite.trans (𝓞 K) E.carrier
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  have key : ∀ y : E.carrier, ∃ a : 𝓞 K, a ≠ 0 ∧ a • y ∈ S := by
    intro y
    have hnot : ¬ LinearIndependent (𝓞 K) (Fin.snoc (α := fun _ => E.carrier) v y) := by
      intro h
      have := h.fintype_card_le_finrank
      rw [hn] at this
      simp at this
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hnot
    rw [Fin.sum_univ_castSucc] at hg
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at hg
    by_cases hl : g (Fin.last n) = 0
    · exfalso
      rw [hl, zero_smul, add_zero] at hg
      have h0 := Fintype.linearIndependent_iff.mp hv (fun j => g j.castSucc) hg
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · exact hi (h0 j)
      · exact hi hl
    · refine ⟨g (Fin.last n), hl, ?_⟩
      rw [eq_neg_of_add_eq_zero_right hg]
      exact S.neg_mem (Submodule.sum_mem _ fun j _ => S.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩))
  have hfg : Module.Finite ℤ (E.carrier ⧸ S.toAddSubgroup) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' S.toAddSubgroup).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  have htor : Module.IsTorsion ℤ (E.carrier ⧸ S.toAddSubgroup) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective S.toAddSubgroup x
    obtain ⟨a, ha0, ha⟩ := key y
    have hN0 : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ha0
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {a}))
    refine ⟨⟨(Ideal.absNorm (Ideal.span {a}) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0)⟩, ?_⟩
    rw [Submonoid.smul_def]
    show ((Ideal.absNorm (Ideal.span {a}) : ℤ)) • (QuotientAddGroup.mk' S.toAddSubgroup y) = 0
    rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    have e : ((Ideal.absNorm (Ideal.span {a}) : ℤ)) • y = b • (a • y) := by
      rw [smul_smul, hb, Nat.cast_smul_eq_nsmul (𝓞 K), natCast_zsmul]
    rw [e]
    exact S.smul_mem b ha
  haveI := Module.finite_of_fg_torsion _ htor
  exact AddSubgroup.index_ne_zero_of_finite

private theorem index_ne_zero_and_le_of_smul_mem {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    (F : Submodule (𝓞 K) E.carrier) {n : ℕ} (v : Fin n → E.carrier)
    (hS : (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.index ≠ 0)
    (d : ℤ) (hd : d ≠ 0) (hdF : ∀ x : E.carrier, d • x ∈ F) :
    F.toAddSubgroup.index ≠ 0 ∧
      (F.toAddSubgroup.index : ℝ) ≤ (|(d : ℝ)| ^ Module.finrank ℚ K) ^ n := by
  classical
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  have hd' : (d : 𝓞 K) ≠ 0 := by exact_mod_cast hd
  set I : Ideal (𝓞 K) := Ideal.span {(d : 𝓞 K)} with hIdef
  have hIidx : I.toAddSubgroup.index = (d ^ Module.finrank ℚ K).natAbs := by
    rw [← Ideal.absNorm_eq_index, hIdef, Ideal.absNorm_span_singleton,
      show (d : 𝓞 K) = algebraMap ℤ (𝓞 K) d by simp, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
  have hIne : I.toAddSubgroup.index ≠ 0 := by
    rw [hIidx]
    exact Int.natAbs_ne_zero.mpr (pow_ne_zero _ hd)
  haveI : I.toAddSubgroup.FiniteIndex := ⟨hIne⟩
  haveI : Finite (𝓞 K ⧸ I) := I.toAddSubgroup.finite_quotient_of_finiteIndex
  haveI : Finite (E.carrier ⧸ (⊤ : Submodule (𝓞 K) E.carrier)) :=
    AddSubgroup.index_ne_zero_iff_finite.mp (by rw [Submodule.top_toAddSubgroup, AddSubgroup.index_top]; exact one_ne_zero)
  have hU : Finite (E.carrier ⧸ I • (⊤ : Submodule (𝓞 K) E.carrier)) :=
    Submodule.finite_quotient_smul I Module.Finite.fg_top
  have hUne : (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index ≠ 0 :=
    AddSubgroup.index_ne_zero_iff_finite.mpr hU
  have hUF : I • (⊤ : Submodule (𝓞 K) E.carrier) ≤ F := by
    rw [Submodule.smul_le]
    intro r hr x _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [mul_smul, Int.cast_smul_eq_zsmul]
    exact F.smul_mem c (hdF x)
  have hTU : I • S ≤ I • (⊤ : Submodule (𝓞 K) E.carrier) := Submodule.smul_mono le_rfl le_top
  set f := DistribSMul.toLinearMap (𝓞 K) E.carrier (d : 𝓞 K) with hfdef
  have hfinj : Function.Injective f := smul_right_injective E.carrier hd'
  have hmapS : (I • S).toAddSubgroup = S.toAddSubgroup.map f.toAddMonoidHom := by
    rw [hIdef, Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_toAddSubgroup]
    rfl
  have hmapT : (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup =
      (⊤ : AddSubgroup E.carrier).map f.toAddMonoidHom := by
    rw [hIdef, Submodule.ideal_span_singleton_smul, Submodule.pointwise_smul_toAddSubgroup,
      Submodule.top_toAddSubgroup]
    rfl
  have hrel : (I • S).toAddSubgroup.relIndex (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup =
      S.toAddSubgroup.index := by
    rw [hmapS, hmapT, AddSubgroup.relIndex_map_map_of_injective _ _ hfinj,
      AddSubgroup.relIndex_top_right]
  have hT := Submodule.index_smul_le I (Finset.univ.image v) (N := S)
    (by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ])
  have hcard : (Finset.univ.image v).card ≤ n := Finset.card_image_le.trans (by simp)
  have hmul2 := AddSubgroup.relIndex_mul_index
    (show (I • S).toAddSubgroup ≤ (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup from hTU)
  rw [hrel] at hmul2
  have hUle : (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index ≤ I.toAddSubgroup.index ^ n := by
    have h1 : S.toAddSubgroup.index * (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index ≤
        S.toAddSubgroup.index * I.toAddSubgroup.index ^ (Finset.univ.image v).card := by
      rw [hmul2, mul_comm]
      exact hT
    have h2 := Nat.le_of_mul_le_mul_left h1 (Nat.pos_of_ne_zero hS)
    exact h2.trans (Nat.pow_le_pow_right (Nat.pos_of_ne_zero hIne) hcard)
  have hFU : F.toAddSubgroup.index ≤ (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hUne) (AddSubgroup.index_dvd_of_le hUF)
  have hFne : F.toAddSubgroup.index ≠ 0 := by
    intro h
    have hdv := AddSubgroup.index_dvd_of_le
      (show (I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup ≤ F.toAddSubgroup from hUF)
    rw [h] at hdv
    exact hUne (Nat.eq_zero_of_zero_dvd hdv)
  refine ⟨hFne, ?_⟩
  have hIr : (I.toAddSubgroup.index : ℝ) = |(d : ℝ)| ^ Module.finrank ℚ K := by
    rw [hIidx, Nat.cast_natAbs, Int.cast_abs, Int.cast_pow, abs_pow]
  calc (F.toAddSubgroup.index : ℝ) ≤ ((I • (⊤ : Submodule (𝓞 K) E.carrier)).toAddSubgroup.index : ℝ) := by
        exact_mod_cast hFU
    _ ≤ (I.toAddSubgroup.index : ℝ) ^ n := by exact_mod_cast hUle
    _ = _ := by rw [hIr]

theorem normDegree_full_rank_submodule_bounds : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  intro K _ _ E F hF
  classical
  have hrF : Module.finrank (𝓞 K) F = Module.finrank (𝓞 K) E.carrier := hF
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := F)
    (n := Module.finrank (𝓞 K) E.carrier) hrF.symm.le
  have hv : LinearIndependent (𝓞 K) (fun i => (s i : E.carrier)) := hs.map' F.subtype F.ker_subtype
  let t : Fin (Module.finrank (𝓞 K) E.carrier) → (⊤ : Submodule (𝓞 K) E.carrier) :=
    fun i => ⟨(s i : E.carrier), Submodule.mem_top⟩
  have ht : LinearIndependent (𝓞 K) t :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 K) E.carrier).subtype hv
  have hSidx := index_span_ne_zero_of_linearIndependent E rfl _ hv
  have hSF : Submodule.span (𝓞 K) (Set.range fun i => (s i : E.carrier)) ≤ F := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (s j).2
  have hcF := card_quotient_span_eq_relIndex F s
  have hcT : Nat.card ((⊤ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range t)) =
      (Submodule.span (𝓞 K) (Set.range fun i => (s i : E.carrier))).toAddSubgroup.index := by
    rw [card_quotient_span_eq_relIndex (⊤ : Submodule (𝓞 K) E.carrier) t, Submodule.top_toAddSubgroup,
      AddSubgroup.relIndex_top_right]
  have hmul := AddSubgroup.relIndex_mul_index
    (show (Submodule.span (𝓞 K) (Set.range fun i => (s i : E.carrier))).toAddSubgroup ≤
      F.toAddSubgroup from hSF)
  have hrelne : (Submodule.span (𝓞 K) (Set.range fun i => (s i : E.carrier))).toAddSubgroup.relIndex
      F.toAddSubgroup ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact hSidx hmul.symm
  have hFne : F.toAddSubgroup.index ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmul
    exact hSidx hmul.symm
  have hdF := E.degree_eq_of_linearIndependent F hs (by rw [Fintype.card_fin]; exact hF.symm)
  have hdT : E.degree ⊤ = Real.log (Nat.card ((⊤ : Submodule (𝓞 K) E.carrier) ⧸
      Submodule.span (𝓞 K) (Set.range t))) -
      1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet E.metric σ fun i => ((s i : F) : E.carrier)) :=
    E.degree_eq_of_linearIndependent (⊤ : Submodule (𝓞 K) E.carrier) ht
      (by rw [Fintype.card_fin]; exact (finrank_top (𝓞 K) E.carrier).symm)
  have hdiff : E.degree ⊤ = E.degree F + Real.log (F.toAddSubgroup.index : ℝ) := by
    rw [hdT, hdF, hcT, hcF, ← hmul, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hrelne) (by exact_mod_cast hFne)]
    ring
  have hq : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hlog0 : 0 ≤ Real.log (F.toAddSubgroup.index : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hFne)
  refine ⟨?_, ?_⟩
  · unfold HermitianBundle.normDegree
    rw [hdiff]
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  · intro d hd hdmem
    obtain ⟨-, hbound⟩ := index_ne_zero_and_le_of_smul_mem E F _ hSidx d hd hdmem
    have hpos : (0 : ℝ) < F.toAddSubgroup.index := by exact_mod_cast Nat.pos_of_ne_zero hFne
    have hlogb : Real.log (F.toAddSubgroup.index : ℝ) ≤
        (Module.finrank (𝓞 K) E.carrier : ℝ) * (Module.finrank ℚ K * Real.log |(d : ℝ)|) := by
      calc Real.log (F.toAddSubgroup.index : ℝ)
          ≤ Real.log ((|(d : ℝ)| ^ Module.finrank ℚ K) ^ Module.finrank (𝓞 K) E.carrier) :=
            Real.log_le_log hpos hbound
        _ = _ := by rw [Real.log_pow, Real.log_pow]
    unfold HermitianBundle.normDegree
    rw [hdiff, add_div, add_le_add_iff_left, div_le_iff₀ hq]
    linarith

end CoverDenseAlt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeFullRankSublattice
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.IndexBound

theorem full_sublattice_normDegree_bounds : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  exact @CoverDenseAlt.normDegree_full_rank_submodule_bounds

end GlobalTheory.CompanionTheory.Ar.IndexBound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeFullRankSublatticeStatement
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_full_rank_sublattice : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds | exact GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds | (intros; apply GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeCommensurableBound
section -- merged from Development.WeilBound.CoreStatements.PlurisubharmonicCones.LabelDegreeCommensurableBound
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights

theorem LevelTowerAlt.label_degree_commensurable_bound : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ) (F : Submodule (𝓞 L) V) (𝔞 : Ideal (𝓞 L)), A.IsAdapted s v q → 𝔞 ≠ ⊥ → 𝔞 • F ≤ A.eig s → 𝔞 • A.eig s ≤ F → |A.labDeg s F v q - A.labDeg s (A.eig s) v q| ≤ (r + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r k v s q F 𝔞 had h𝔞 h1 h2
  obtain ⟨h3, h4⟩ := LevelTowerAlt.sub_eig A had.2
  have h5 := (LevelTowerAlt.Sub.of_smul_le h𝔞 h1).trans h3
  have h6 := h4.trans (LevelTowerAlt.Sub.of_smul_le h𝔞 h2)
  have e1 := LevelTowerAlt.logIdx_sub_le had.1 𝔞 h𝔞 h3 h4 h5 h2
  have e2 := LevelTowerAlt.logIdx_sub_le had.1 𝔞 h𝔞 h5 h6 h3 h1
  have hn : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  push_cast at e1 e2
  rw [LinPt.labDeg, LinPt.labDeg, ← sub_div, abs_div, abs_of_pos hn]
  refine div_le_div_of_nonneg_right (abs_le.2 ⟨?_, ?_⟩) hn.le <;> linarith
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeCommensurableBound
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ) (F : Submodule (𝓞 L) V) (𝔞 : Ideal (𝓞 L)), A.IsAdapted s v q → 𝔞 ≠ ⊥ → 𝔞 • F ≤ A.eig s → 𝔞 • A.eig s ≤ F → |A.labDeg s F v q - A.labDeg s (A.eig s) v q| ≤ (r + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L := by
  first | exact @LevelTowerAlt.label_degree_commensurable_bound | exact LevelTowerAlt.label_degree_commensurable_bound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LabelledDegreeCommensurableBoundStatement
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelled_degree_commensurable_bound : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r k : ℕ) (v : Fin r → V) (s : Ψ ⊕ Ψ) (q : Fin k → A.Λ) (F : Submodule (𝓞 L) V) (𝔞 : Ideal (𝓞 L)), A.IsAdapted s v q → 𝔞 ≠ ⊥ → 𝔞 • F ≤ A.eig s → 𝔞 • A.eig s ≤ F → |A.labDeg s F v q - A.labDeg s (A.eig s) v q| ≤ (r + k) * Real.log (Ideal.absNorm 𝔞) / Module.finrank ℚ L := by
  first | exact @GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound | exact GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound | (intros; apply GlobalTheory.CompanionTheory.Relay.labelled_degree_commensurable_bound <;> assumption)
end
end
