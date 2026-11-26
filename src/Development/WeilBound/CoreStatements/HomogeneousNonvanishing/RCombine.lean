module

public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.JPull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FderivAffCoordZero
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularization

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.REnlarge
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem r_enlarge : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ L L' : LocPot X) (s s' : X → X → ℂ) (th : LocPot X) (ph : X → ℝ) (phT : ℝ → X → ℝ) (C₅ C t₀ : ℝ), 0 ≤ C₅ → 0 ≤ C → t₀ ≤ Real.exp (-1) → (∀ y, logNormSec L s y ≤ 0) → bdry s ⊆ bdry s' → (∀ y, y ∉ bdry s' → rW L s y ≤ rW L' s' y) → IsSingWeight A L s th ph C₅ → IsRegFamily A Θ L s th ph phT C t₀ → IsRegFamilyC2 A s ph phT → IsSingWeight A L' s' th ph C₅ ∧ IsRegFamily A Θ L' s' th ph phT C t₀ ∧ IsRegFamilyC2 A s' ph phT := by
  intro e X _ _ _ A Θ L L' s s' th ph phT C₅ C t₀ hC5 hC ht0 hL hsub hrw hS hR hC2
  have hnb : ∀ y, y ∉ bdry s' → y ∉ bdry s := fun y hy h => hy (hsub h)
  have hpos : ∀ y, 0 < rW L s y := by
    intro y
    unfold rW
    have h1 := hL y
    have h2 := Real.exp_pos 1
    linarith
  obtain ⟨hpot, hsm, hpsh, hb⟩ := hS
  obtain ⟨h0, h1, hf⟩ := hR
  refine ⟨⟨hpot, ?_, ?_, ?_⟩, ⟨h0, h1, ?_⟩, ?_⟩
  · intro j
    exact (hsm j).mono (fun z hz => ⟨hz.1, hnb _ hz.2⟩)
  · intro x j y hy w
    exact hpsh x j y ⟨hy.1, hy.2.1, hnb _ hy.2.2⟩ w
  · intro y hy
    obtain ⟨hlo, hhi⟩ := hb y (hnb y hy)
    refine ⟨?_, hhi⟩
    have hlog : Real.log (rW L s y) ≤ Real.log (rW L' s' y) := Real.log_le_log (hpos y) (hrw y hy)
    nlinarith [mul_le_mul_of_nonneg_left hlog hC5]
  · intro t ht htt
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hf t ht htt
    have hte : t ≤ Real.exp (-1) := le_trans htt ht0
    have h1t : Real.exp 1 ≤ 1 / t := by
      rw [le_div_iff₀ ht]
      calc Real.exp 1 * t ≤ Real.exp 1 * Real.exp (-1) := by gcongr
        _ = 1 := by rw [← Real.exp_add]; simp
    have hL1 : 1 ≤ Real.log (1 / t) := by
      have h := Real.log_le_log (Real.exp_pos 1) h1t
      rwa [Real.log_exp] at h
    have heps : 0 ≤ epsT C t := by
      unfold epsT
      exact div_nonneg (mul_nonneg hC (Real.log_nonneg hL1)) (by linarith)
    refine ⟨a1, a2, fun y hy => a3 y (hnb y hy), a4, a5, ?_, ?_, a8⟩
    · intro y hy hle
      exact a6 y (hnb y hy) (le_trans (hrw y hy) hle)
    · intro y hy
      have h7 := a7 y (hnb y hy)
      nlinarith [mul_le_mul_of_nonneg_left (hrw y hy) heps]
  · intro j K hK hKc
    exact hC2 j K (fun z hz => ⟨(hK hz).1, hnb _ (hK hz).2⟩) hKc

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RSnc
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.SmoothContinuousAt
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.GMonomial
namespace PositivityTheory.UnitarySelfGeneration

open Metric Filter Topology Set

namespace GMon

variable {e : ℕ}

theorem update_mem {r : ℝ} {z : Fin e → ℂ} (hz : z ∈ ball (0 : Fin e → ℂ) r) (i : Fin e) {t : ℂ}
    (ht : ‖t‖ < r) : Function.update z i t ∈ ball (0 : Fin e → ℂ) r := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg _) ht
  rw [mem_ball_zero_iff, pi_norm_lt_iff hr] at hz ⊢
  intro j
  by_cases h : j = i
  · subst h; simpa using ht
  · simpa [Function.update_of_ne h] using hz j

theorem analyticAt_update_left (i : Fin e) (t : ℂ) (z : Fin e → ℂ) :
    AnalyticAt ℂ (fun w : Fin e → ℂ => Function.update w i t) z := by
  refine analyticAt_pi_iff.mpr fun j => ?_
  by_cases h : j = i
  · subst h; simpa using analyticAt_const
  · simp only [Function.update_of_ne h]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) j).analyticAt z

theorem analyticAt_update_right (i : Fin e) (z : Fin e → ℂ) (t : ℂ) :
    AnalyticAt ℂ (fun s : ℂ => Function.update z i s) t := by
  refine analyticAt_pi_iff.mpr fun j => ?_
  by_cases h : j = i
  · subst h; simp only [Function.update_self]; exact analyticAt_id
  · simp only [Function.update_of_ne h]
    exact analyticAt_const

theorem norm_sub_update (z : Fin e → ℂ) (i : Fin e) : ‖z - Function.update z i 0‖ ≤ ‖z i‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem isBigO_coord {G : (Fin e → ℂ) → ℂ} {b : Fin e → ℂ} (i : Fin e) (hG : AnalyticAt ℂ G b) (hb : b i = 0)
    (h0 : ∀ᶠ z in 𝓝 b, z i = 0 → G z = 0) : ∃ C : ℝ, ∀ᶠ z in 𝓝 b, ‖G z‖ ≤ C * ‖z i‖ := by
  obtain ⟨C, t, ht, hL⟩ := (hG.contDiffAt (n := 1)).exists_lipschitzOnWith
  have hu : Tendsto (fun w : Fin e → ℂ => Function.update w i 0) (𝓝 b) (𝓝 b) := by
    have := (analyticAt_update_left i 0 b).continuousAt
    rw [ContinuousAt] at this
    rwa [← hb, Function.update_eq_self, hb] at this
  refine ⟨C, ?_⟩
  filter_upwards [ht, hu.eventually ht, hu.eventually h0] with z h1 h2 h3
  have h4 := hL.norm_sub_le h1 h2
  rw [h3 (by simp), sub_zero] at h4
  exact h4.trans (mul_le_mul_of_nonneg_left (norm_sub_update z i) C.2)

theorem divide {G : (Fin e → ℂ) → ℂ} {r : ℝ} (i : Fin e) (hG : AnalyticOnNhd ℂ G (ball 0 r))
    (h0 : ∀ z ∈ ball (0 : Fin e → ℂ) r, z i = 0 → G z = 0) :
    ∃ G' : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ G' (ball 0 r) ∧ ∀ z ∈ ball (0 : Fin e → ℂ) r, G z = z i * G' z := by
  have hi : Differentiable ℂ (fun z : Fin e → ℂ => z i) := by fun_prop
  obtain ⟨F, hF, hE⟩ := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.proof e (ball 0 r)
    (fun z => z i) (fun z => G z / z i) isOpen_ball hi.differentiableOn
    (by
      rintro V hV - ⟨z, hz⟩
      have hd : Dense ((fun z : Fin e → ℂ => z i) ⁻¹' ({0}ᶜ)) :=
        (dense_compl_singleton (0 : ℂ)).preimage (isOpenMap_eval i)
      obtain ⟨w, hw1, hw2⟩ := hd.inter_open_nonempty V hV ⟨z, hz⟩
      exact ⟨w, hw1, hw2⟩)
    (fun z hz => ((hG z hz.1).div ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticAt z)
      hz.2).differentiableAt.differentiableWithinAt)
    (by
      intro τ hτ
      by_cases hτi : τ i = 0
      · obtain ⟨C, hC⟩ := isBigO_coord i (hG τ hτ) hτi
          (by filter_upwards [isOpen_ball.mem_nhds hτ] with z hz using h0 z hz)
        refine ⟨_, hC, (isBounded_closedBall (x := (0 : ℂ)) (r := C)).subset ?_⟩
        rintro _ ⟨z, ⟨⟨h1, -⟩, h2⟩, rfl⟩
        have h3 : 0 < ‖z i‖ := norm_pos_iff.mpr h2
        simp only [mem_closedBall, dist_zero_right, norm_div]
        rw [div_le_iff₀ h3]
        exact h1
      · have hc : ContinuousAt (fun z => G z / z i) τ :=
          (hG τ hτ).continuousAt.div hi.continuous.continuousAt hτi
        refine ⟨_, hc (ball_mem_nhds _ one_pos), (isBounded_ball (x := G τ / τ i) (r := 1)).subset ?_⟩
        rintro _ ⟨z, ⟨⟨h1, -⟩, -⟩, rfl⟩
        exact h1)
  refine ⟨F, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn
    isOpen_ball hF, fun z hz => ?_⟩
  by_cases hzi : z i = 0
  · rw [h0 z hz hzi, hzi, zero_mul]
  · rw [hE ⟨hz, hzi⟩]
    field_simp

theorem spread {G : (Fin e → ℂ) → ℂ} {r : ℝ} (S : Finset (Fin e)) (i : Fin e) (hG : AnalyticOnNhd ℂ G (ball 0 r))
    (hne : ∀ z ∈ ball (0 : Fin e → ℂ) r, z i ≠ 0 → (∀ j ∈ S, j ≠ i → z j ≠ 0) → G z ≠ 0)
    {b : Fin e → ℂ} (hb : b ∈ ball (0 : Fin e → ℂ) r) (hbS : ∀ j ∈ S, j ≠ i → b j ≠ 0) (hb0 : G b = 0) :
    ∀ z ∈ ball (0 : Fin e → ℂ) r, z i = 0 → G z = 0 := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hb
  have hbi : b i = 0 := by
    by_contra h
    exact hne b hb h hbS hb0
  set ρ : ℝ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r := by linarith

  have hcont : ∀ t ∈ sphere (0 : ℂ) ρ,
      ContinuousAt (fun p : (Fin e → ℂ) × ℂ => G (Function.update p.1 i p.2)) (b, t) := by
    intro t ht
    have h1 : ‖t‖ < r := by rw [mem_sphere_zero_iff_norm.mp ht]; exact hρr
    refine ContinuousAt.comp (hG _ (update_mem hb i h1)).continuousAt ?_
    exact (continuous_fst.update i continuous_snd).continuousAt
  have hpos : ∀ t ∈ sphere (0 : ℂ) ρ, G (Function.update b i t) ≠ 0 := by
    intro t ht
    have h0 : ‖t‖ = ρ := mem_sphere_zero_iff_norm.mp ht
    refine hne _ (update_mem hb i (h0 ▸ hρr)) ?_ fun j hj hji => ?_
    · simp only [Function.update_self]
      rintro rfl
      simp at h0
      linarith
    · rw [Function.update_of_ne hji]; exact hbS j hj hji
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_sphere (0 : ℂ) ρ).exists_isMinOn
    (f := fun t => ‖G (Function.update b i t)‖) (NormedSpace.sphere_nonempty.mpr hρ0.le)
    (fun t ht => ((hcont t ht).comp (f := fun t => (b, t))
      (by fun_prop)).norm.continuousWithinAt)
  set δ : ℝ := ‖G (Function.update b i t₀)‖ / 2 with hδ
  have hδ0 : 0 < δ := half_pos (norm_pos_iff.mpr (hpos t₀ ht₀))
  have hev : ∀ᶠ w in 𝓝 b, ∀ t ∈ sphere (0 : ℂ) ρ, δ < ‖G (Function.update w i t)‖ := by
    refine (isCompact_sphere (0 : ℂ) ρ).eventually_forall_of_forall_eventually fun t ht => ?_
    refine (hcont t ht).norm.eventually (lt_mem_nhds ?_)
    have : ‖G (Function.update b i t₀)‖ ≤ ‖G (Function.update b i t)‖ := hmin ht
    simp only
    linarith
  have hU := analyticAt_update_left i 0 b
  have hbb : Function.update b i 0 = b := by rw [← hbi, Function.update_eq_self]
  have hsmall : ∀ᶠ w in 𝓝 b, ‖G (Function.update w i 0)‖ < δ := by
    have : ContinuousAt (fun w => G (Function.update w i 0)) b :=
      ContinuousAt.comp (by rw [hbb]; exact (hG b hb).continuousAt) hU.continuousAt
    refine this.norm.eventually (gt_mem_nhds ?_)
    simp only [hbb, hb0, norm_zero]
    exact hδ0
  have hSev : ∀ᶠ w in 𝓝 b, ∀ j ∈ S, j ≠ i → w j ≠ 0 := by
    refine (S.eventually_all).mpr fun j hj => ?_
    by_cases hji : j = i
    · exact Eventually.of_forall fun w h => absurd hji h
    · filter_upwards [(continuous_apply j).continuousAt.eventually_ne (hbS j hj hji)] with w hw _ using hw
  have hzero : ∀ᶠ w in 𝓝 b, G (Function.update w i 0) = 0 := by
    filter_upwards [hev, hsmall, hSev, isOpen_ball.mem_nhds hb] with w h1 h2 h3 h4
    by_contra hw
    have hnz : ∀ t ∈ closedBall (0 : ℂ) ρ, G (Function.update w i t) ≠ 0 := by
      intro t ht
      by_cases ht0 : t = 0
      · rw [ht0]; exact hw
      · refine hne _ (update_mem h4 i (lt_of_le_of_lt (mem_closedBall_zero_iff.mp ht) hρr))
          (by simpa using ht0) fun j hj hji => ?_
        rw [Function.update_of_ne hji]; exact h3 j hj hji
    have hd : DifferentiableOn ℂ (fun t => (G (Function.update w i t))⁻¹) (closedBall (0 : ℂ) ρ) := by
      intro t ht
      refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.inv ?_ (hnz t ht))
      exact (AnalyticAt.comp (hG _ (update_mem h4 i (lt_of_le_of_lt (mem_closedBall_zero_iff.mp ht) hρr)))
        (analyticAt_update_right i w t)).differentiableAt
    have hdc : DiffContOnCl ℂ (fun t => (G (Function.update w i t))⁻¹) (ball (0 : ℂ) ρ) := by
      apply DifferentiableOn.diffContOnCl
      rwa [closure_ball _ hρ0.ne']
    have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc (C := δ⁻¹)
      (fun t ht => by
        rw [frontier_ball _ hρ0.ne'] at ht
        rw [norm_inv]
        exact inv_anti₀ hδ0 (h1 t ht).le) (z := 0) (subset_closure (mem_ball_self hρ0))
    rw [norm_inv] at hle
    have := inv_strictAnti₀ (norm_pos_iff.mpr hw) h2
    linarith
  have han : AnalyticOnNhd ℂ (fun w => G (Function.update w i 0)) (ball 0 r) := fun w hw =>
    AnalyticAt.comp (hG _ (update_mem hw i (by simpa using hr))) (analyticAt_update_left i 0 w)
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball _ _).isPreconnected hb hzero
  intro z hz hzi
  have := hall hz
  simp only [Pi.zero_apply] at this
  rwa [show Function.update z i 0 = z by rw [← hzi, Function.update_eq_self]] at this

theorem step {F : (Fin e → ℂ) → ℂ} {r : ℝ} (hr : 0 < r) (S : Finset (Fin e)) (i : Fin e)
    (hF : AnalyticOnNhd ℂ F (ball 0 r))
    (hne : ∀ z ∈ ball (0 : Fin e → ℂ) r, z i ≠ 0 → (∀ j ∈ S, j ≠ i → z j ≠ 0) → F z ≠ 0) :
    ∃ (k : ℕ) (G : (Fin e → ℂ) → ℂ), AnalyticOnNhd ℂ G (ball 0 r) ∧
      (∀ z ∈ ball (0 : Fin e → ℂ) r, (∀ j ∈ S, j ≠ i → z j ≠ 0) → G z ≠ 0) ∧
      ∀ z ∈ ball (0 : Fin e → ℂ) r, F z = z i ^ k * G z := by
  by_contra hcon
  push Not at hcon
  have hall : ∀ k : ℕ, ∃ G : (Fin e → ℂ) → ℂ, AnalyticOnNhd ℂ G (ball 0 r) ∧
      ∀ z ∈ ball (0 : Fin e → ℂ) r, F z = z i ^ k * G z := by
    intro k
    induction k with
    | zero => exact ⟨F, hF, fun z _ => by simp⟩
    | succ k ih =>
      obtain ⟨G, hG, hFG⟩ := ih
      have h1 : ∃ b ∈ ball (0 : Fin e → ℂ) r, (∀ j ∈ S, j ≠ i → b j ≠ 0) ∧ G b = 0 := by
        by_contra h
        push Not at h
        obtain ⟨z, hz, hz'⟩ := hcon k G hG h
        exact hz' (hFG z hz)
      obtain ⟨b, hb, hbS, hb0⟩ := h1
      have h2 := spread S i hG (fun z hz hzi hzS hG0 => hne z hz hzi hzS (by rw [hFG z hz, hG0, mul_zero]))
        hb hbS hb0
      obtain ⟨G', hG', hE⟩ := divide i hG h2
      exact ⟨G', hG', fun z hz => by rw [hFG z hz, hE z hz]; ring⟩
  set b : Fin e → ℂ := fun _ => ((r / 2 : ℝ) : ℂ) with hbdef
  have hb : b ∈ ball (0 : Fin e → ℂ) r := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    intro j
    simp only [hbdef, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity)]
    linarith
  have hm : ∀ᶠ t in 𝓝 (0 : ℂ), Function.update b i t ∈ ball (0 : Fin e → ℂ) r := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with t ht using update_mem hb i (mem_ball_zero_iff.mp ht)
  have hφ : AnalyticAt ℂ (fun t => F (Function.update b i t)) 0 :=
    AnalyticAt.comp (hF _ hm.self_of_nhds) (analyticAt_update_right i b 0)
  have htop : analyticOrderAt (fun t => F (Function.update b i t)) 0 = ⊤ := by
    refine ENat.eq_top_iff_forall_ge.mpr fun k => ?_
    obtain ⟨G, hG, hFG⟩ := hall k
    refine (natCast_le_analyticOrderAt hφ).mpr ⟨fun t => G (Function.update b i t),
      AnalyticAt.comp (hG _ hm.self_of_nhds) (analyticAt_update_right i b 0), ?_⟩
    filter_upwards [hm] with t ht
    rw [hFG _ ht]
    simp
  rw [analyticOrderAt_eq_top] at htop
  have h3 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), False := by
    filter_upwards [nhdsWithin_le_nhds htop, nhdsWithin_le_nhds hm, self_mem_nhdsWithin] with t h1 h2 h3
    refine hne _ h2 (by simpa using h3) (fun j _ hji => ?_) h1
    rw [Function.update_of_ne hji]
    simp only [hbdef]
    exact_mod_cast (half_pos hr).ne'
  obtain ⟨_, h⟩ := h3.exists
  exact h

end GMon

theorem g_monomial : ∀ (e : ℕ) (S : Finset (Fin e)) (F : (Fin e → ℂ) → ℂ) (r : ℝ), 0 < r → AnalyticOnNhd ℂ F (Metric.ball 0 r) → (∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, (∀ i ∈ S, z i ≠ 0) → F z ≠ 0) → ∃ (m : Fin e → ℕ) (u : (Fin e → ℂ) → ℂ), (∀ i, i ∉ S → m i = 0) ∧ AnalyticOnNhd ℂ u (Metric.ball 0 r) ∧ (∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, u z ≠ 0) ∧ ∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, F z = u z * ∏ i, z i ^ m i := by
  intro e S F r hr
  induction S using Finset.induction_on generalizing F with
  | empty =>
    intro hF hne
    exact ⟨fun _ => 0, F, fun _ _ => rfl, hF, fun z hz => hne z hz (by simp), fun z _ => by simp⟩
  | insert i S hi ih =>
    intro hF hne
    obtain ⟨k, G, hG, hGne, hFG⟩ := GMon.step hr S i hF fun z hz hzi hzS => hne z hz fun j hj => by
      rcases Finset.mem_insert.mp hj with hj | hj
      · rw [hj]; exact hzi
      · exact hzS j hj fun h => hi (h ▸ hj)
    obtain ⟨m, u, hm, hu, hu0, hE⟩ := ih G hG fun z hz hzS => hGne z hz fun j hj _ => hzS j hj
    refine ⟨m + Pi.single i k, u, fun j hj => ?_, hu, hu0, fun z hz => ?_⟩
    · rw [Finset.mem_insert, not_or] at hj
      simp [hm j hj.2, Pi.single_eq_of_ne hj.1]
    · rw [hFG z hz, hE z hz]
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      have : ∏ j, z j ^ (Pi.single i k : Fin e → ℕ) j = z i ^ k := by
        rw [Finset.prod_eq_single i]
        · simp
        · intro j _ hj; simp [Pi.single_eq_of_ne hj]
        · simp
      rw [this]
      ring

end PositivityTheory.UnitarySelfGeneration
end

namespace PositivityTheory.UnitarySelfGeneration.CSnc

open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology Set Asymptotics HolomorphicMinorCharts

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem smooth_continuousAt {A : FinHolAtlas e X} {U : Set X} (hU : IsOpen U) {g : X → ℝ} (hg : A.SmoothOn U g)
    {x : X} (hx : x ∈ U) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have hc := ((hg j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds
    (x := A.chart j x) ⟨(A.chart j).map_source hj, by rwa [Set.mem_preimage, (A.chart j).left_inv hj]⟩)).continuousAt
  exact ((A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := g) (x := x) (by simpa using hj)).mpr (by simpa using hc)

theorem section_zero {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} (hs : IsSection A L s) {x x' y : X}
    (h : y ∈ L.U x) (h' : y ∈ L.U x') (h0 : s x y = 0) : s x' y = 0 := by
  have := hs.2 x x' y ⟨h, h'⟩
  rw [h0, norm_zero, zero_mul, eq_comm, mul_eq_zero] at this
  exact norm_eq_zero.mp (this.resolve_right (Real.exp_pos _).ne')

def Loc (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (W : Fin n → Set X) (x : X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (σ : Fin n → Option (Fin e)) (mm : Fin e → ℕ) : Prop :=
  IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ψ.source ⊆ L.U x ∧ (∀ k k' i, σ k = some i → σ k' = some i → k = k') ∧
    (∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0}) ∧
    (∀ i, mm i ≠ 0 → ψ x i = 0 ∧ ∃ k, σ k = some i) ∧
    ∃ u : X → ℂ, A.HoloOn ψ.source u ∧ (∀ y ∈ ψ.source, u y ≠ 0) ∧ ∀ y ∈ ψ.source, s x y = u y * ∏ i, ψ y i ^ mm i

theorem exists_loc {A : FinHolAtlas e X} {L₀ L : LocPot X} {s₀ s : X → X → ℂ} {n : ℕ} {m₀ : Fin n → ℕ}
    {W : Fin n → Set X} (h₀ : IsSNC A L₀ s₀ m₀ W) (hs : IsSection A L s) (hb : bdry s ⊆ {x | s₀ x x = 0})
    (hz : ∀ x x', ∀ y ∈ L₀.U x ∩ L₀.U x', (s₀ x y = 0 ↔ s₀ x' y = 0)) (x : X) :
    ∃ ψ σ mm, Loc A L s W x ψ σ mm := by
  classical
  obtain ⟨ψ, hψ, hx, hU, σ, hσ, hW, u₀, -, hu₀, hE⟩ := h₀ x
  set c := ψ x with hc
  have hO : ψ.target ∩ ψ.symm ⁻¹' L.U x ∩ {v | ∀ i, c i ≠ 0 → v i ≠ 0} ∈ 𝓝 c := by
    refine inter_mem ((ψ.isOpen_inter_preimage_symm (L.isOpen_U x)).mem_nhds
      ⟨ψ.map_source hx, by rw [Set.mem_preimage, hc, ψ.left_inv hx]; exact L.mem_U x⟩) ?_
    refine eventually_all.mpr fun i => ?_
    by_cases hi : c i = 0
    · exact Eventually.of_forall fun v h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with v hv _ using hv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hO
  have hsh : ∀ z ∈ Metric.ball (0 : Fin e → ℂ) r, z + c ∈ Metric.ball c r := fun z hz => by
    simpa using hz
  obtain ⟨mm, u, hm, hu, hu0, hF⟩ := g_monomial e (Finset.univ.filter fun i => c i = 0 ∧ ∃ k, σ k = some i)
    (fun z => s x (ψ.symm (z + c))) r hr
    (fun z hz => AnalyticAt.comp (g := s x ∘ ψ.symm) (f := fun z => z + c)
      (holo_compat hψ (hs.1 x) (hball (hsh z hz)).1.1 (hball (hsh z hz)).1.2) (analyticAt_id.add analyticAt_const))
    (by
      intro z hzb hS h0
      obtain ⟨⟨h1, h2⟩, h3⟩ := hball (hsh z hzb)
      have h4 := ψ.map_target h1
      have h5 : s₀ x (ψ.symm (z + c)) = 0 :=
        (hz x _ _ ⟨hU h4, L₀.mem_U _⟩).mpr (hb (section_zero hs h2 (L.mem_U _) h0))
      rw [hE _ h4, mul_eq_zero, Finset.prod_eq_zero_iff] at h5
      obtain ⟨k, -, hk⟩ := h5.resolve_left (hu₀ _ h4)
      rcases h : σ k with _ | i
      · simp [h] at hk
      · simp only [h, ψ.right_inv h1] at hk
        have h6 := eq_zero_of_pow_eq_zero hk
        by_cases hi : c i = 0
        · exact hS i (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hi, k, h⟩)
            (by simpa [hi] using h6)
        · exact h3 i hi h6)
  have hop : IsOpen (ψ.source ∩ ψ ⁻¹' Metric.ball c r) := ψ.isOpen_inter_preimage Metric.isOpen_ball
  have hsub : ∀ y, ψ y ∈ Metric.ball c r → ψ y - c ∈ Metric.ball (0 : Fin e → ℂ) r := fun y hy => by
    simpa [dist_eq_norm] using hy
  have hm' : ∀ i, mm i ≠ 0 → c i = 0 ∧ ∃ k, σ k = some i := fun i hi => by
    by_contra h
    exact hi (hm i (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using h))
  refine ⟨ψ.restrOpen _ hop, σ, mm, fun j => ⟨(hψ j).1.mono fun v hv => ⟨hv.1, hv.2.1⟩,
    (hψ j).2.mono fun v hv => ⟨hv.1.1, hv.2⟩⟩, ⟨hx, hx, Metric.mem_ball_self hr⟩, fun y hy => ?_, hσ, fun k => ?_, hm',
    fun y => u (ψ y - c), ?_, fun y hy => hu0 _ (hsub y hy.2.2), fun y hy => ?_⟩
  · have := (hball hy.2.2).1.2
    rwa [Set.mem_preimage, ψ.left_inv hy.1] at this
  · ext y
    constructor
    · rintro ⟨h1, h2⟩
      have : y ∈ W k ∩ ψ.source := ⟨h1, h2.1⟩
      rw [hW] at this
      exact ⟨h2, this.2⟩
    · rintro ⟨h1, h2⟩
      have : y ∈ W k ∩ ψ.source := by rw [hW]; exact ⟨h1.1, h2⟩
      exact ⟨this.1, h1⟩
  · exact holoOn_of_compat hψ (U := (ψ.restrOpen (ψ.source ∩ ψ ⁻¹' Metric.ball c r) hop).source) (G := fun v => u (v - c)) (fun y hy => hy.1) fun y hy =>
      AnalyticAt.comp (g := u) (f := fun v => v - c) (hu _ (hsub y hy.2.2)) (analyticAt_id.sub analyticAt_const)
  · have := hF _ (hsub y hy.2.2)
    simp only [sub_add_cancel, ψ.left_inv hy.1] at this
    rw [this]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : mm i = 0
    · simp [hi]
    · rw [Pi.sub_apply, (hm' i hi).1, sub_zero]
      rfl

theorem theta_mul {𝕜 : Type} [NormedField 𝕜] {l : Filter X} {v f : X → 𝕜} {c : 𝕜} (hc : c ≠ 0)
    (hv : Tendsto v l (𝓝 c)) : (fun w => v w * f w) =Θ[l] f :=
  (((isEquivalent_const_iff_tendsto hc).mpr hv).mul (IsEquivalent.refl (u := f))).isTheta.trans
    ((isTheta_const_mul_left hc).mpr isTheta_rfl)

variable {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} {n : ℕ} {W : Fin n → Set X}

theorem Loc.mem_iff {x : X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {σ : Fin n → Option (Fin e)} {mm : Fin e → ℕ}
    (h : Loc A L s W x ψ σ mm) {y : X} (hy : y ∈ ψ.source) (k : Fin n) :
    y ∈ W k ↔ ∃ i, σ k = some i ∧ ψ y i = 0 := by
  constructor
  · intro h1
    have : y ∈ W k ∩ ψ.source := ⟨h1, hy⟩
    rw [h.2.2.2.2.1] at this
    exact this.2
  · intro h1
    have : y ∈ W k ∩ ψ.source := by rw [h.2.2.2.2.1]; exact ⟨hy, h1⟩
    exact this.1

theorem Loc.theta {x : X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {σ : Fin n → Option (Fin e)} {mm : Fin e → ℕ}
    (h : Loc A L s W x ψ σ mm) {y : X} (hy : y ∈ ψ.source) {k : Fin n} {i : Fin e} (hk : σ k = some i)
    (hg : ∀ k', k' ≠ k → y ∉ W k') : s x =Θ[𝓝 y] fun w => ψ w i ^ mm i := by
  classical
  obtain ⟨u, hu, hu0, hE⟩ := h.2.2.2.2.2.2
  have h1 : s x =ᶠ[𝓝 y] fun w => (u w * ∏ j ∈ Finset.univ.erase i, ψ w j ^ mm j) * ψ w i ^ mm i := by
    filter_upwards [ψ.open_source.mem_nhds hy] with w hw
    rw [hE w hw, mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  refine h1.isTheta.trans (theta_mul (c := u y * ∏ j ∈ Finset.univ.erase i, ψ y j ^ mm j) ?_ ?_)
  · refine mul_ne_zero (hu0 y hy) (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
    by_cases hj0 : mm j = 0
    · simp [hj0]
    · obtain ⟨-, k', hk'⟩ := h.2.2.2.2.2.1 j hj0
      refine pow_ne_zero _ fun h0 => hg k' ?_ ((h.mem_iff hy k').mpr ⟨j, hk', h0⟩)
      rintro rfl
      rw [hk] at hk'
      exact Finset.ne_of_mem_erase hj (Option.some.inj hk').symm
  · exact (holo_continuousAt hu hy).tendsto.mul (tendsto_finsetProd _ fun j _ =>
      (((continuous_apply j).continuousAt.comp (ψ.continuousAt hy)).pow _).tendsto)

theorem le_of_isBigO (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) {y : X} (hy : y ∈ ψ.source) {i : Fin e}
    (hi : ψ y i = 0) {a b : ℕ} (h : (fun w => ψ w i ^ a) =O[𝓝 y] fun w => ψ w i ^ b) : b ≤ a := by
  by_contra hab
  push Not at hab
  have t1 : Tendsto (fun t : ℂ => Function.update (ψ y) i t) (𝓝 0) (𝓝 (ψ y)) := by
    have := (GMon.analyticAt_update_right i (ψ y) 0).continuousAt.tendsto
    rwa [show Function.update (ψ y) i 0 = ψ y by rw [← hi, Function.update_eq_self]] at this
  have h1 := h.comp_tendsto ((tendsto_symm ψ hy).comp t1)
  have h2 : ∀ c : ℕ, ((fun w => ψ w i ^ c) ∘ ψ.symm ∘ fun t : ℂ => Function.update (ψ y) i t) =ᶠ[𝓝 0]
      fun t => t ^ c := fun c => by
    filter_upwards [t1 (ψ.open_target.mem_nhds (ψ.map_source hy))] with t ht
    simp only [Function.comp_apply]
    rw [ψ.right_inv ht]
    simp only [Function.update_self]
  have h3 := (h1.congr' (h2 a) (h2 b)).trans_isLittleO (isLittleO_pow_pow hab)
  refine isLittleO_irrefl ?_ h3
  refine Frequently.filter_mono (Eventually.frequently (f := 𝓝[≠] (0 : ℂ)) ?_) nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht using pow_ne_zero _ ht

theorem Loc.le_generic (hL : IsPotential A L) (hs : IsSection A L s) {x x' : X}
    {ψ ψ' : OpenPartialHomeomorph X (Fin e → ℂ)} {σ σ' : Fin n → Option (Fin e)} {mm mm' : Fin e → ℕ}
    (h : Loc A L s W x ψ σ mm) (h' : Loc A L s W x' ψ' σ' mm') {y : X} (hy : y ∈ ψ.source) (hy' : y ∈ ψ'.source)
    {k : Fin n} {i i' : Fin e} (hk : σ k = some i) (hk' : σ' k = some i') (hyW : y ∈ W k)
    (hg : ∀ k', k' ≠ k → y ∉ W k') : mm' i' ≤ mm i := by
  have hi : ψ y i = 0 := by
    obtain ⟨j, hj, h0⟩ := (h.mem_iff hy k).mp hyW
    rw [hk] at hj
    rwa [Option.some.inj hj]
  refine le_of_isBigO ψ hy hi ?_
  have h1 : s x =Θ[𝓝 y] s x' := by
    have e1 : (fun w => ‖s x w‖) =ᶠ[𝓝 y] fun w => Real.exp (L.φ x w - L.φ x' w) * ‖s x' w‖ := by
      filter_upwards [ψ.open_source.mem_nhds hy, ψ'.open_source.mem_nhds hy'] with w h1 h2
      have := hs.2 x x' w ⟨h.2.2.1 h1, h'.2.2.1 h2⟩
      rw [Real.exp_neg, Real.exp_neg] at this
      rw [Real.exp_sub]
      have p1 := (Real.exp_pos (L.φ x w)).ne'
      have p2 := (Real.exp_pos (L.φ x' w)).ne'
      field_simp at this ⊢
      linarith
    have e2 := e1.isTheta.trans (theta_mul (Real.exp_pos _).ne'
      ((smooth_continuousAt (L.isOpen_U x) (hL.1 x) (h.2.2.1 hy)).sub
        (smooth_continuousAt (L.isOpen_U x') (hL.1 x') (h'.2.2.1 hy'))).rexp.tendsto)
    exact isTheta_norm_left.mp (isTheta_norm_right.mp e2)
  have h2 : (fun w => ψ' w i') =O[𝓝 y] fun w => ψ w i := by
    have ha : AnalyticAt ℂ ((fun w => ψ' w i') ∘ ψ.symm) (ψ y) :=
      holo_compat h.1 (holoOn_of_compat h'.1 (G := fun v => v i') subset_rfl fun _ _ =>
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i').analyticAt _) (ψ.map_source hy)
        (by rwa [ψ.left_inv hy])
    obtain ⟨C, hC⟩ := GMon.isBigO_coord i ha hi (by
      filter_upwards [ψ.open_target.mem_nhds (ψ.map_source hy),
        tendsto_symm ψ hy (ψ'.open_source.mem_nhds hy')] with v h1 h2 h3
      obtain ⟨j, hj, h0⟩ := (h'.mem_iff h2 k).mp ((h.mem_iff (ψ.map_target h1) k).mpr
        ⟨i, hk, by rwa [ψ.right_inv h1]⟩)
      rw [hk'] at hj
      rwa [← Option.some.inj hj] at h0)
    refine IsBigO.of_bound C ?_
    filter_upwards [(ψ.continuousAt hy).eventually hC, ψ.open_source.mem_nhds hy] with w h1 h2
    simpa only [Function.comp_apply, ψ.left_inv h2] using h1
  exact (((h.theta hy hk hg).symm.trans h1).trans (h'.theta hy' hk' hg)).isBigO.trans (h2.pow _)

theorem Loc.order_eq (hL : IsPotential A L) (hs : IsSection A L s) {x x' : X}
    {ψ ψ' : OpenPartialHomeomorph X (Fin e → ℂ)} {σ σ' : Fin n → Option (Fin e)} {mm mm' : Fin e → ℕ}
    (h : Loc A L s W x ψ σ mm) (h' : Loc A L s W x' ψ' σ' mm') {y : X} (hy : y ∈ ψ.source) (hy' : y ∈ ψ'.source)
    {k : Fin n} {i i' : Fin e} (hk : σ k = some i) (hk' : σ' k = some i') (hyW : y ∈ W k) : mm i = mm' i' := by
  classical
  have hi : ψ y i = 0 := by
    obtain ⟨j, hj, h0⟩ := (h.mem_iff hy k).mp hyW
    rw [hk] at hj
    rwa [Option.some.inj hj]
  let v : ℂ → Fin e → ℂ := fun t => Function.update (fun j => ψ y j + t) i 0
  have t1 : Tendsto v (𝓝[≠] 0) (𝓝 (ψ y)) := by
    have hc : Continuous v := Continuous.update (by fun_prop) i continuous_const
    have h0 : v 0 = ψ y := by
      simp only [v, add_zero]
      rw [← hi, Function.update_eq_self]
    exact (h0 ▸ hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have t2 : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ∀ j, ψ y j + t ≠ 0 := eventually_all.mpr fun j => by
    by_cases hj : ψ y j = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hj, zero_add]
      exact ht
    · exact nhdsWithin_le_nhds (ContinuousAt.eventually_ne (g := fun t : ℂ => ψ y j + t) (by fun_prop)
        (by simpa using hj))
  obtain ⟨t, h1, h2, h3⟩ := (t2.and ((t1.eventually (ψ.open_target.mem_nhds (ψ.map_source hy))).and
    (((tendsto_symm ψ hy).comp t1).eventually (ψ'.open_source.mem_nhds hy')))).exists
  have h4 := ψ.map_target h2
  have h5 : ψ.symm (v t) ∈ W k := (h.mem_iff h4 k).mpr ⟨i, hk, by rw [ψ.right_inv h2]; simp [v]⟩
  have h6 : ∀ k', k' ≠ k → ψ.symm (v t) ∉ W k' := by
    intro k' hne hm
    obtain ⟨j, hj, h0⟩ := (h.mem_iff h4 k').mp hm
    rw [ψ.right_inv h2] at h0
    by_cases hji : j = i
    · exact hne (h.2.2.2.1 k' k i (hji ▸ hj) hk)
    · simp only [v, Function.update_of_ne hji] at h0
      exact h1 j h0
  exact le_antisymm (h'.le_generic hL hs h h3 h4 hk' hk h5 h6) (h.le_generic hL hs h' h4 h3 hk hk' h5 h6)

theorem prod_opt {σ : Fin n → Option (Fin e)} (hσ : ∀ k k' i, σ k = some i → σ k' = some i → k = k')
    (f : Fin e → ℂ) (hf : ∀ i, f i ≠ 1 → ∃ k, σ k = some i) : ∏ k, (σ k).elim 1 f = ∏ i, f i := by
  classical
  have h1 : ∀ k, (σ k).elim 1 f = ∏ i, if σ k = some i then f i else 1 := fun k => by
    rcases σ k with _ | j
    · simp
    · simp
  simp only [h1]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : f i = 1
  · simp [hi]
  · obtain ⟨k, hk⟩ := hf i hi
    rw [Finset.prod_eq_single k, if_pos hk]
    · intro k' _ hne
      exact if_neg fun h => hne (hσ k' k i h hk)
    · simp

theorem snc_of_loc [CompactSpace X] (hL : IsPotential A L) (hs : IsSection A L s)
    (hloc : ∀ x, ∃ ψ σ mm, Loc A L s W x ψ σ mm) :
    ∃ (n' : ℕ) (m : Fin n' → ℕ) (W' : Fin n' → Set X), IsSNC A L s m W' := by
  classical
  choose ψ σ mm h using hloc
  let ord : Fin n → X → ℕ := fun k y => (σ y k).elim 0 (mm y)
  have hord : ∀ x y k i, y ∈ (ψ x).source → y ∈ W k → σ x k = some i → ord k y = mm x i := by
    intro x y k i hy hW hk
    obtain ⟨j, hj, -⟩ := ((h y).mem_iff (h y).2.1 k).mp hW
    simp only [ord, hj, Option.elim_some]
    exact (h y).order_eq hL hs (h x) (h y).2.1 hy hj hk hW
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ y i, mm y i < N := by
    obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover (fun x => (ψ x).source) (fun x => (ψ x).open_source)
      fun x _ => mem_iUnion.mpr ⟨x, (h x).2.1⟩
    refine ⟨∑ x ∈ T, ∑ i, mm x i + 1, fun y i => Nat.lt_succ_of_le ?_⟩
    by_cases h0 : mm y i = 0
    · rw [h0]; exact Nat.zero_le _
    obtain ⟨h1, k, hk⟩ := (h y).2.2.2.2.2.1 i h0
    have hW : y ∈ W k := ((h y).mem_iff (h y).2.1 k).mpr ⟨i, hk, h1⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (hT (mem_univ y))
    obtain ⟨j, hj, -⟩ := ((h x).mem_iff hyx k).mp hW
    rw [← hord y y k i (h y).2.1 hW hk, hord x y k j hyx hW hj]
    exact (Finset.single_le_sum (f := mm x) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun x => ∑ i, mm x i) (fun _ _ => Nat.zero_le _) hx)
  let E : Fin (n * N) ≃ Fin n × Fin N := finProdFinEquiv.symm
  refine ⟨n * N, fun q => (E q).2, fun q => {y | y ∈ W (E q).1 ∧ ord (E q).1 y = (E q).2}, fun x => ?_⟩
  let τ : Fin (n * N) → Option (Fin e) := fun q => (σ x (E q).1).filter fun i => mm x i = (E q).2
  have hτ : ∀ q i, τ q = some i ↔ σ x (E q).1 = some i ∧ mm x i = (E q).2 := fun q i => by
    simp [τ, Option.filter_eq_some_iff]
  have hinj : ∀ q q' i, τ q = some i → τ q' = some i → q = q' := by
    intro q q' i h1 h2
    rw [hτ] at h1 h2
    exact E.injective (Prod.ext ((h x).2.2.2.1 _ _ i h1.1 h2.1) (Fin.ext (h1.2.symm.trans h2.2)))
  obtain ⟨u, hu, hu0, hE⟩ := (h x).2.2.2.2.2.2
  refine ⟨ψ x, (h x).1, (h x).2.1, (h x).2.2.1, τ, hinj, fun q => ?_, u, hu, hu0, fun y hy => ?_⟩
  · ext y
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      obtain ⟨i, hi, h0⟩ := ((h x).mem_iff h3 _).mp h1
      exact ⟨h3, i, (hτ q i).mpr ⟨hi, (hord x y _ i h3 h1 hi).symm.trans h2⟩, h0⟩
    · rintro ⟨h3, i, hi, h0⟩
      rw [hτ] at hi
      have h1 := ((h x).mem_iff h3 _).mpr ⟨i, hi.1, h0⟩
      exact ⟨⟨h1, (hord x y _ i h3 h1 hi.1).trans hi.2⟩, h3⟩
  · rw [hE y hy, ← prod_opt hinj (fun i => ψ x y i ^ mm x i) fun i hi => ?_]
    · congr 1
      refine Finset.prod_congr rfl fun q _ => ?_
      rcases hq : τ q with _ | i
      · rfl
      · simp only [Option.elim_some]
        rw [((hτ q i).mp hq).2]
    · obtain ⟨-, k, hk⟩ := (h x).2.2.2.2.2.1 i fun h0 => hi (by rw [h0, pow_zero])
      exact ⟨E.symm (k, ⟨mm x i, hN x i⟩), (hτ _ i).mpr (by rw [E.apply_symm_apply]; exact ⟨hk, rfl⟩)⟩

end PositivityTheory.UnitarySelfGeneration.CSnc
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

theorem r_snc : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L₀ : LocPot X) (s₀ : X → X → ℂ) (n₀ : ℕ) (m₀ : Fin n₀ → ℕ) (W₀ : Fin n₀ → Set X) (L : LocPot X) (s : X → X → ℂ), IsSNC A L₀ s₀ m₀ W₀ → IsPotential A L → IsSection A L s → bdry s ⊆ {x | s₀ x x = 0} → (∀ x x', ∀ y ∈ L₀.U x ∩ L₀.U x', (s₀ x y = 0 ↔ s₀ x' y = 0)) → ∃ (n : ℕ) (m : Fin n → ℕ) (W : Fin n → Set X), IsSNC A L s m W := by
  intro e X _ _ _ A L₀ s₀ n₀ m₀ W₀ L s h₀ hL hs hb hz
  exact CSnc.snc_of_loc hL hs (CSnc.exists_loc h₀ hs hb hz)

end PositivityTheory.UnitarySelfGeneration
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

namespace RC

open HolomorphicMinorCharts

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem section_pull {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {π : Y → X} (h : HoloMap B A π) {L : LocPot X}
    {s : X → X → ℂ} (hs : IsSection A L s) : IsSection B (L.pullback π h.1) fun x y => s (π x) (π y) :=
  ⟨fun x => holo_comp_map h (hs.1 (π x)), fun x x' y hy => hs.2 (π x) (π x') (π y) hy⟩

theorem nrm_mul (L L' : LocPot X) (s s' : X → X → ℂ) (x y : X) :
    ‖s x y * s' x y‖ * Real.exp (-(L + L').φ x y) =
      (‖s x y‖ * Real.exp (-L.φ x y)) * (‖s' x y‖ * Real.exp (-L'.φ x y)) := by
  rw [add_φ, norm_mul, neg_add, Real.exp_add]
  ring

theorem section_mul {A : FinHolAtlas e X} {L L' : LocPot X} {s s' : X → X → ℂ} (hs : IsSection A L s)
    (hs' : IsSection A L' s') : IsSection A (L + L') fun x y => s x y * s' x y := by
  refine ⟨fun x j w hw => (hs.1 x j w ⟨hw.1, hw.2.1⟩).mul (hs'.1 x j w ⟨hw.1, hw.2.2⟩), fun x x' y hy => ?_⟩
  rw [nrm_mul, nrm_mul, hs.2 x x' y ⟨hy.1.1, hy.2.1⟩, hs'.2 x x' y ⟨hy.1.2, hy.2.2⟩]

theorem log_mul_le {L L' : LocPot X} {s s' : X → X → ℂ} (h : ∀ y, logNormSec L s y ≤ 0)
    (h' : ∀ y, logNormSec L' s' y ≤ 0) (y : X) : logNormSec (L + L') (fun x y => s x y * s' x y) y ≤ 0 := by
  have h1 := h y
  have h2 := h' y
  unfold logNormSec at *
  rw [Real.log_nonpos_iff (by positivity)] at *
  rw [nrm_mul]
  exact mul_le_one₀ h1 (by positivity) h2

theorem log_mul_eq {L L' : LocPot X} {s s' : X → X → ℂ} {y : X} (hy : y ∉ bdry fun x y => s x y * s' x y) :
    logNormSec (L + L') (fun x y => s x y * s' x y) y = logNormSec L s y + logNormSec L' s' y := by
  have h1 : s y y * s' y y ≠ 0 := hy
  unfold logNormSec
  rw [nrm_mul, Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr (left_ne_zero_of_mul h1)) (Real.exp_pos _).ne')
    (mul_ne_zero (norm_ne_zero_iff.mpr (right_ne_zero_of_mul h1)) (Real.exp_pos _).ne')]

theorem exists_scale [CompactSpace X] {A : FinHolAtlas e X} {L : LocPot X} {s : X → X → ℂ} (hL : IsPotential A L)
    (hs : IsSection A L s) : ∃ L' : LocPot X, IsPotential A L' ∧ IsSection A L' s ∧ ∀ y, logNormSec L' s y ≤ 0 := by
  have hc : Continuous fun y => ‖s y y‖ * Real.exp (-L.φ y y) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    refine ContinuousAt.congr (((holo_continuousAt (hs.1 x) (L.mem_U x)).norm).mul
      (CSnc.smooth_continuousAt (L.isOpen_U x) (hL.1 x) (L.mem_U x)).neg.rexp) ?_
    filter_upwards [(L.isOpen_U x).mem_nhds (L.mem_U x)] with y hy
    exact hs.2 x y y ⟨hy, L.mem_U y⟩
  obtain ⟨M, hM⟩ := (isCompact_range hc).bddAbove
  have hsm : A.Smooth fun _ => M := fun j => contDiffOn_const
  have key : ∀ x y, ‖s x y‖ * Real.exp (-(L + LocPot.ofFun fun _ => M).φ x y) =
      ‖s x y‖ * Real.exp (-L.φ x y) * Real.exp (-M) := fun x y => by
    rw [add_φ, neg_add, Real.exp_add, mul_assoc]
    rfl
  refine ⟨L + LocPot.ofFun fun _ => M, isPotentialAdd A _ _ hL (isPotential_ofFun A _ hsm),
    ⟨fun x => holo_mono (hs.1 x) fun y hy => hy.1, fun x x' y hy => ?_⟩, fun y => ?_⟩
  · rw [key, key, hs.2 x x' y ⟨hy.1.1, hy.2.1⟩]
  · unfold logNormSec
    rw [Real.log_nonpos_iff (by positivity), key, Real.exp_neg M, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    have h1 : ‖s y y‖ * Real.exp (-L.φ y y) ≤ M := hM ⟨y, rfl⟩
    have := Real.add_one_le_exp M
    linarith

theorem exists_line {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (b : K → ℤ) :
    ∃ L : HermLine ι, IsSmoothHerm L ∧ L.a = b := by
  refine ⟨HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) b, ?_, rfl⟩
  change ContDiffOn ℝ _ (fun z => ∏ k, (fsMetric (ι := ι k)).ρ (GP.blk (ι := ι) k z) ^ b k) _
  refine contDiffOn_prod fun k _ z hz => ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (fsMetric (ι := ι k)).ρ (GP.blk (ι := ι) k z)) z :=
    ContDiffAt.comp (g := (fsMetric (ι := ι k)).ρ) z (GP.contDiffAt_fs (GP.blk_ne hz k))
      ((GP.blk (ι := ι) k).contDiff.restrict_scalars ℝ).contDiffAt
  have h2 := ((fsMetric (ι := ι k)).pos _ (GP.blk_ne hz k)).ne'
  rcases b k with n | n
  · simpa using h1.pow n
  · simp only [zpow_negSucc]
    exact (h1.pow (n + 1)).inv (pow_ne_zero _ h2)

theorem one (hPull : PullbackStatement) {D : ℕ} [CompactSpace Y] [T2Space Y] {B : FinHolAtlas D Y} {Θ : LocPot Y}
    (hΘ : IsPotential B Θ) (hΘ' : IsPosPot B Θ) {σ : Type} (S : AnSys D σ) {π : Y → S.X} (h : HoloMap B S.A π)
    {n : ℕ} {m : Fin n → ℕ} {W : Fin n → Set Y}
    (hsnc : IsSNC B (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) m W) {L : LocPot Y} {s : Y → Y → ℂ}
    (hb : bdry (fun x y => S.s (π x) (π y)) ⊆ bdry s)
    (hr : ∀ y, y ∉ bdry s → rW (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) y ≤ rW L s y) (a : σ) :
    ∃ C' t' : ℝ, 0 < t' ∧ ∀ C₅ C t₀ : ℝ, 0 ≤ C₅ → S.C₅ ≤ C₅ → |C'| ≤ C → 0 < t₀ → t₀ ≤ t' → t₀ ≤ Real.exp (-1) →
      IsSingWeight B L s ((S.th a).pullback π h.1) (S.ph a ∘ π) C₅ ∧
      IsRegFamily B Θ L s ((S.th a).pullback π h.1) (S.ph a ∘ π) (fun t => S.phT a t ∘ π) C t₀ ∧
      IsRegFamilyC2 B s (S.ph a ∘ π) (fun t => S.phT a t ∘ π) := by
  obtain ⟨C', t', h1, h2, h3⟩ := hPull S.A B π h S.Θ S.L Θ S.s S.m S.W m W S.potΘ S.posΘ hΘ hΘ' S.potL S.sec S.snc
    S.norm_le hsnc (S.th a) (S.ph a) (S.phT a) S.C₅ S.C S.t₀ (S.sing a) (S.reg a) (S.c2 a)
  have hn : ∀ y, logNormSec (S.L.pullback π h.1) (fun x y => S.s (π x) (π y)) y ≤ 0 := fun y => S.norm_le (π y)
  obtain ⟨m1, m2, -⟩ := GlobalTheory.T.singular_weight_monotone_regularization D Y B Θ _ _ n m W (isPotentialPullback S.A B π h _ S.potL)
    (section_pull h S.sec) hsnc hn hΘ hΘ'
  refine ⟨C', t', h2.1, fun C₅ C t₀ a1 a2 a3 a4 a5 a6 => ?_⟩
  exact r_enlarge D Y B Θ _ L _ s _ _ _ C₅ C t₀ a1 ((abs_nonneg _).trans a3) a6 hn hb hr (m1 _ _ _ _ a2 h1)
    (m2 _ _ _ _ _ _ _ a3 a4 a5 a6 h2 h1.1) h3

end RC

open RC HolomorphicMinorCharts in
theorem r_combine : PullbackStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (Amp : HermLine ι) (β : MRing ι) (b : K → ℕ) (σ : Type) [Fintype σ] (S₁ S₂ : AnSys D σ) (π₁ : R.X → S₁.X) (π₂ : R.X → S₂.X) (h₁ : HoloMap R.A S₁.A π₁) (h₂ : HoloMap R.A S₂.A π₂), IsPotential R.A (potOf R Amp) → IsPosPot R.A (potOf R Amp) → IsMultiHomog β b → β ∉ P → (∀ z ∈ mcPts P, evC z β = 0 → z ∈ mcPts J) → (∀ x, π₁ x ∈ bdry S₁.s → evC (R.lift x x) β = 0) → (∀ x, π₂ x ∈ bdry S₂.s → evC (R.lift x x) β = 0) → ∃ (L : LocPot R.X) (s : R.X → R.X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (C₅ C t₀ : ℝ), IsPotential R.A L ∧ IsSection R.A L s ∧ IsSNC R.A L s m W ∧ (∀ y, logNormSec L s y ≤ 0) ∧ (∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0) ∧ t₀ ≤ S₁.t₀ ∧ t₀ ≤ S₂.t₀ ∧ (∀ a, IsSingWeight R.A L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₁.th a).pullback π₁ h₁.1) (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁) C t₀ ∧ IsRegFamilyC2 R.A s (S₁.ph a ∘ π₁) (fun t => S₁.phT a t ∘ π₁)) ∧ ∀ a, IsSingWeight R.A L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) C₅ ∧ IsRegFamily R.A (potOf R Amp) L s ((S₂.th a).pullback π₂ h₂.1) (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) C t₀ ∧ IsRegFamilyC2 R.A s (S₂.ph a ∘ π₂) (fun t => S₂.phT a t ∘ π₂) := by
  intro hPull K _ ι _ P J D R Amp β b σ _ S₁ S₂ π₁ π₂ h₁ h₂ hΘ hΘ' hβ hβP hβJ hb₁ hb₂
  obtain ⟨n₀, m₀, W₀, hsnc₀⟩ := R.snc β b hβP hβ hβJ
  have hsnc : ∀ (L : LocPot R.X) (s : R.X → R.X → ℂ), IsPotential R.A L → IsSection R.A L s →
      (∀ x ∈ bdry s, evC (R.lift x x) β = 0) → ∃ (n : ℕ) (m : Fin n → ℕ) (W : Fin n → Set R.X), IsSNC R.A L s m W :=
    fun L s hL hs hb => r_snc D R.X R.A _ _ n₀ m₀ W₀ L s hsnc₀ hL hs hb
      fun x x' y hy => eval_ne_so hβ (R.compat x x' y hy)
  obtain ⟨Lb, hLb, hLa⟩ := exists_line (ι := ι) fun k => (b k : ℤ)
  obtain ⟨L₃, p₃, s₃, l₃⟩ := exists_scale (isPotential_potOf R hLb)
    (isSection_lift R (A := Lb) (s := β) ⟨b, fun k => congrFun hLa k, hβ, hβP⟩)
  have p₁ := isPotentialPullback S₁.A R.A π₁ h₁ _ S₁.potL
  have p₂ := isPotentialPullback S₂.A R.A π₂ h₂ _ S₂.potL
  have s₁ := section_pull h₁ S₁.sec
  have s₂ := section_pull h₂ S₂.sec
  have l₁ : ∀ y, logNormSec (S₁.L.pullback π₁ h₁.1) (fun x y => S₁.s (π₁ x) (π₁ y)) y ≤ 0 :=
    fun y => S₁.norm_le (π₁ y)
  have l₂ : ∀ y, logNormSec (S₂.L.pullback π₂ h₂.1) (fun x y => S₂.s (π₂ x) (π₂ y)) y ≤ 0 :=
    fun y => S₂.norm_le (π₂ y)
  obtain ⟨n₁, m₁, W₁, c₁⟩ := hsnc _ _ p₁ s₁ hb₁
  obtain ⟨n₂, m₂, W₂, c₂⟩ := hsnc _ _ p₂ s₂ hb₂
  have p := isPotentialAdd R.A _ _ (isPotentialAdd R.A _ _ p₁ p₂) p₃
  have sec := section_mul (section_mul s₁ s₂) s₃
  set L := S₁.L.pullback π₁ h₁.1 + S₂.L.pullback π₂ h₂.1 + L₃ with hL
  set s : R.X → R.X → ℂ := fun x y => S₁.s (π₁ x) (π₁ y) * S₂.s (π₂ x) (π₂ y) *
    eval (R.lift x y) (map (Int.castRingHom ℂ) β) with hs
  have hbd : ∀ x, x ∈ bdry s ↔ evC (R.lift x x) β = 0 := fun x => by
    refine ⟨fun h => ?_, fun h => mul_eq_zero_of_right _ h⟩
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact hb₁ x h
      · exact hb₂ x h
    · exact h
  obtain ⟨n, m, W, c⟩ := hsnc L s p sec fun x => (hbd x).mp
  have hlog : ∀ y, y ∉ bdry s → logNormSec L s y =
      logNormSec (S₁.L.pullback π₁ h₁.1) (fun x y => S₁.s (π₁ x) (π₁ y)) y +
      logNormSec (S₂.L.pullback π₂ h₂.1) (fun x y => S₂.s (π₂ x) (π₂ y)) y +
      logNormSec L₃ (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) β)) y := fun y hy => by
    have h0 : S₁.s (π₁ y) (π₁ y) * S₂.s (π₂ y) (π₂ y) * eval (R.lift y y) (map (Int.castRingHom ℂ) β) ≠ 0 := hy
    rw [← log_mul_eq (s := fun x y => S₁.s (π₁ x) (π₁ y)) (s' := fun x y => S₂.s (π₂ x) (π₂ y))
      (left_ne_zero_of_mul h0)]
    exact log_mul_eq (s := fun x y => S₁.s (π₁ x) (π₁ y) * S₂.s (π₂ x) (π₂ y))
      (s' := fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) β)) hy
  choose C₁ t₁ ht₁ H₁ using one hPull hΘ hΘ' S₁ h₁ c₁ (L := L) (s := s) (fun x hx => (hbd x).mpr (hb₁ x hx))
    fun y hy => by
      have := hlog y hy
      have := l₂ y
      have := l₃ y
      unfold rW
      linarith
  choose C₂ t₂ ht₂ H₂ using one hPull hΘ hΘ' S₂ h₂ c₂ (L := L) (s := s) (fun x hx => (hbd x).mpr (hb₂ x hx))
    fun y hy => by
      have := hlog y hy
      have := l₁ y
      have := l₃ y
      unfold rW
      linarith
  obtain ⟨δ, hδ, hδe, hδ₁, hδ₂⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ Real.exp (-1) ∧ (∀ a, δ ≤ t₁ a) ∧ ∀ a, δ ≤ t₂ a := by
    have e0 : ∀ t : ℝ, 0 < t → ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ t := fun t ht => by
      filter_upwards [Ioc_mem_nhdsGT ht] with δ h using h.2
    exact ((eventually_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)).and ((e0 _ (Real.exp_pos _)).and
      ((eventually_all.mpr fun a => e0 _ (ht₁ a)).and (eventually_all.mpr fun a => e0 _ (ht₂ a))))).exists
  have hpos : σ → 0 < min (min S₁.t₀ S₂.t₀) δ := fun a => lt_min (lt_min (S₁.reg a).1 (S₂.reg a).1) hδ
  have n1 : 0 ≤ ∑ a, |C₁ a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have n2 : 0 ≤ ∑ a, |C₂ a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨L, s, n, m, W, max (max S₁.C₅ S₂.C₅) 0, ∑ a, |C₁ a| + ∑ a, |C₂ a|, min (min S₁.t₀ S₂.t₀) δ, p, sec, c,
    log_mul_le (log_mul_le l₁ l₂) l₃, hbd, (min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _), fun a => H₁ a _ _ _ (le_max_right _ _)
      ((le_max_left _ _).trans (le_max_left _ _)) ?_ (hpos a) ((min_le_right _ _).trans (hδ₁ a))
      ((min_le_right _ _).trans hδe), fun a => H₂ a _ _ _ (le_max_right _ _)
      ((le_max_right _ _).trans (le_max_left _ _)) ?_ (hpos a) ((min_le_right _ _).trans (hδ₂ a))
      ((min_le_right _ _).trans hδe)⟩
  · have := Finset.single_le_sum (f := fun a => |C₁ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith
  · have := Finset.single_le_sum (f := fun a => |C₂ a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith

end PositivityTheory.UnitarySelfGeneration
