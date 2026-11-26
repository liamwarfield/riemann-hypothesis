module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormHolo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas)

theorem continuousOn_of_holoOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) : ContinuousOn g W := by
  intro x hx
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ W
      rw [(A.chart j).left_inv hj]; exact hx⟩
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) := (hg j _ hmem).continuousAt
  have h2 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  have heq : (g ∘ (A.chart j).symm) ∘ A.chart j =ᶠ[nhds x] g := by
    filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
    simp [Function.comp, (A.chart j).left_inv hz]
  exact (h2.congr heq).continuousWithinAt

theorem logNormHolo_of_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {W : Set X} {g : X → ℂ} (hW : IsOpen W) (hg : A.HoloOn W g) (hgc : ContinuousOn g W)
    (hne : ∀ y ∈ W, g y ≠ 0) {y : X} (hy : y ∈ W) : ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      V ⊆ W ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ z ∈ V, Real.log ‖g z‖ = (G z).re := by
  have hc : g y ≠ 0 := hne y hy
  have hcn : 0 < ‖g y‖ := norm_pos_iff.2 hc

  have hslit : ∀ w ∈ Metric.ball (g y) ‖g y‖, w / g y ∈ Complex.slitPlane := by
    intro w hw
    apply Complex.ball_one_subset_slitPlane
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : w / g y - 1 = (w - g y) / g y := by field_simp
    rw [this, norm_div, div_lt_one hcn]
    exact hw
  refine ⟨W ∩ g ⁻¹' Metric.ball (g y) ‖g y‖, hgc.isOpen_inter_preimage hW Metric.isOpen_ball,
    ⟨hy, by simpa using hcn⟩, Set.inter_subset_left,
    fun z => Complex.log (g z / g y) + (Real.log ‖g y‖ : ℂ), ?_, ?_⟩
  · intro j v hv
    have ha : AnalyticAt ℂ (g ∘ (A.chart j).symm) v := hg j v ⟨hv.1, hv.2.1⟩
    have hs : (g ∘ (A.chart j).symm) v / g y ∈ Complex.slitPlane := hslit _ hv.2.2
    exact ((ha.div analyticAt_const hc).clog hs).add analyticAt_const
  · intro z hz
    have hz0 : g z ≠ 0 := hne z hz.1
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re]
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hz0) (norm_ne_zero_iff.2 hc)]
    ring

theorem LogNormHolo.proof (hCC : ChartCont.Statement) : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg ((hCC D A W hW).2 g hg) hne hy

theorem LogNormHolo.full : LogNormHolo.Statement := by
  intro X _ D A W g hW hg hne y hy
  exact logNormHolo_of_continuousOn A hW hg (continuousOn_of_holoOn A hg) hne hy

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PCoordDivDivisible
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.A (coordDiv)
open Filter Topology

theorem cofactor_vanish {D : ℕ} {Ω : Set (Fin D → ℂ)} (hΩ : IsOpen Ω) {F G : (Fin D → ℂ) → ℂ}
    {i k : Fin D} (hik : k ≠ i) (hG : AnalyticOnNhd ℂ G Ω) (hFG : ∀ z ∈ Ω, F z = z i * G z)
    (hF : ∀ z ∈ Ω, z k = 0 → F z = 0) {z : Fin D → ℂ} (hz : z ∈ Ω) (hzk : z k = 0) : G z = 0 := by
  classical
  by_cases hzi : z i = 0
  swap
  · have h := hFG z hz
    rw [hF z hz hzk] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hzi

  set w : ℂ → (Fin D → ℂ) := fun ε => Function.update z i ε with hw
  have hwc : Continuous w := continuous_const.update i continuous_id
  have hw0 : w 0 = z := by rw [← hzi]; simp [hw]
  have hcont : ContinuousAt (fun ε => G (w ε)) 0 := by
    have h := (hG z hz).continuousAt
    rw [← hw0] at h
    exact h.comp hwc.continuousAt
  have hmem : ∀ᶠ ε in 𝓝 (0 : ℂ), w ε ∈ Ω := by
    exact hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact hΩ.mem_nhds hz)

  have hzero : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), G (w ε) = 0 := by
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with ε hε hne
    have hwk : w ε k = 0 := by simp [hw, hik, hzk]
    have hwi : w ε i = ε := by simp [hw]
    have h := hFG _ hε
    rw [hF _ hε hwk, hwi] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  have ht1 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (G (w 0))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun ε => G (w ε)) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.mono fun _ h => h.symm)
  have h := tendsto_nhds_unique ht1 ht2
  rwa [hw0] at h

theorem CoordDivDivisible.proof (hH : HyperplaneDivisible.Statement) : CoordDivDivisible.Statement := by
  classical
  intro D Ω F S hΩ hFa hF
  induction S using Finset.induction_on generalizing F with
  | empty => exact ⟨F, hFa, fun z _ => by simp⟩
  | insert i S hi ih =>
    obtain ⟨G₁, hG₁a, hG₁⟩ := hH D Ω F i hΩ hFa fun z hz hzi =>
      hF z hz ⟨i, Finset.mem_insert_self i S, hzi⟩
    have hG₁0 : ∀ z ∈ Ω, z ∈ coordDiv S → G₁ z = 0 := by
      rintro z hz ⟨k, hk, hzk⟩
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      exact cofactor_vanish hΩ hki hG₁a hG₁
        (fun y hy hyk => hF y hy ⟨k, Finset.mem_insert_of_mem hk, hyk⟩) hz hzk
    obtain ⟨G, hGa, hG⟩ := ih G₁ hG₁a hG₁0
    refine ⟨G, hGa, fun z hz => ?_⟩
    rw [hG₁ z hz, hG z hz, Finset.prod_insert hi, mul_assoc]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end
