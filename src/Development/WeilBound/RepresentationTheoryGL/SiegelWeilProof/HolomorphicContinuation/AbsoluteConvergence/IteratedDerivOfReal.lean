module

public import Mathlib

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IteratedDerivOfReal
open Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.TSA

theorem iteratedDeriv_ofReal' {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F U)
    {h : ℝ → ℂ} (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) (hFh : ∀ x : ℝ, F x = h x) (p : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv p F) U ∧ ∀ x : ℝ, iteratedDeriv p F x = iteratedDeriv p h x := by
  induction p with
  | zero => simpa using ⟨hF, hFh⟩
  | succ p ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨?_, fun x => ?_⟩
    · rw [iteratedDeriv_succ]
      exact hd.deriv hU
    · rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have h0 : HasDerivAt (iteratedDeriv p F) (deriv (iteratedDeriv p F) x) (x : ℂ) :=
        (hd.differentiableAt (hU.mem_nhds (hmem x))).hasDerivAt
      have h3 : HasDerivAt (fun y : ℝ => iteratedDeriv p F y) (deriv (iteratedDeriv p F) x) x := h0.comp_ofReal
      have h4 : (fun y : ℝ => iteratedDeriv p F y) = iteratedDeriv p h := funext he
      rw [h4] at h3
      exact h3.deriv.symm

theorem eq_of_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) (hmem : ∀ x : ℝ, (x : ℂ) ∈ U) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (h : ∀ r : ℕ, iteratedDeriv r f 0 = iteratedDeriv r g 0) (t : ℝ) : f t = g t := by
  have h0U : (0 : ℂ) ∈ U := by simpa using hmem 0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0U
  have hnear : f =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with z hz
    rw [← Complex.taylorSeries_eq_on_ball' hz (hf.mono hball), ← Complex.taylorSeries_eq_on_ball' hz (hg.mono hball)]
    simp_rw [h]
  set V := connectedComponentIn U (0 : ℂ)
  have hVo : IsOpen V := hU.connectedComponentIn
  have hVc : IsPreconnected V := isPreconnected_connectedComponentIn
  have h0V : (0 : ℂ) ∈ V := mem_connectedComponentIn h0U
  have hRV : range (fun x : ℝ => (x : ℂ)) ⊆ V := by
    apply (isPreconnected_range Complex.continuous_ofReal).subset_connectedComponentIn
    · exact ⟨0, by simp⟩
    · rintro _ ⟨x, rfl⟩; exact hmem x
  have hVU : V ⊆ U := connectedComponentIn_subset _ _
  have hfa : AnalyticOnNhd ℂ f V := (hf.mono hVU).analyticOnNhd hVo
  have hga : AnalyticOnNhd ℂ g V := (hg.mono hVU).analyticOnNhd hVo
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hVc h0V hnear (hRV ⟨t, rfl⟩)

end PositivityTheory.Rg.Sw.AbsSt.TSA
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.IteratedDerivSumOn
noncomputable section

open MeasureTheory Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.TSC

theorem iteratedDeriv_sum_on {ι : Type} (s : Finset ι) {U : Set ℂ} (hU : IsOpen U) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) (r : ℕ) :
    (∀ i ∈ s, DifferentiableOn ℂ (iteratedDeriv r (f i)) U) ∧
    EqOn (iteratedDeriv r (fun w => ∑ i ∈ s, f i w)) (fun w => ∑ i ∈ s, iteratedDeriv r (f i) w) U := by
  induction r with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact ⟨hf, fun _ _ => rfl⟩
  | succ r ih =>
    obtain ⟨hd, he⟩ := ih
    refine ⟨fun i hi => ?_, fun z hz => ?_⟩
    · rw [iteratedDeriv_succ]
      exact (hd i hi).deriv hU
    · simp only [iteratedDeriv_succ]
      have hev : iteratedDeriv r (fun w => ∑ i ∈ s, f i w) =ᶠ[𝓝 z]
          (fun w => ∑ i ∈ s, iteratedDeriv r (f i) w) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hz) he
      rw [hev.deriv_eq]
      first
        | exact deriv_fun_sum (fun i hi => (hd i hi).differentiableAt (hU.mem_nhds hz))
        | exact deriv_sum (fun i hi => (hd i hi).differentiableAt (hU.mem_nhds hz))

theorem exists_int_elem {X : Type} [MeasurableSpace X] (ν : Measure X) {V : Type} [AddCommGroup V] [Module ℂ V]
    (W : Submodule ℂ V) [FiniteDimensional ℂ W] (φ : X → V) (hφ : ∀ x, φ x ∈ W)
    (hint : ∀ l : V →ₗ[ℂ] ℂ, Integrable (fun x => l (φ x)) ν) :
    ∃ Φ ∈ W, ∀ l : V →ₗ[ℂ] ℂ, l Φ = ∫ x, l (φ x) ∂ν := by
  classical
  let b := Module.finBasis ℂ W
  choose cl hcl using fun j => LinearMap.exists_extend (b.coord j)
  have hc : ∀ j x, cl j (φ x) = b.repr ⟨φ x, hφ x⟩ j := by
    intro j x
    have := LinearMap.congr_fun (hcl j) ⟨φ x, hφ x⟩
    simpa using this
  have hrepr : ∀ x, φ x = ∑ j, cl j (φ x) • (b j : V) := by
    intro x
    have h1 := b.sum_repr ⟨φ x, hφ x⟩
    have h2 := congrArg (fun w : W => (w : V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    simp only [hc]
    exact h2.symm
  refine ⟨∑ j, (∫ x, cl j (φ x) ∂ν) • (b j : V), Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2,
    fun l => ?_⟩
  have e1 : ∀ x, l (φ x) = ∑ j, cl j (φ x) * l (b j) := by
    intro x
    conv_lhs => rw [hrepr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [e1]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_mul_const]
  · intro j _
    exact (hint (cl j)).mul_const _

end PositivityTheory.Rg.Sw.AbsSt.TSC
end
end
