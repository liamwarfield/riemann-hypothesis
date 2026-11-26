module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicDescentPunctPolydiscLogCover

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplane
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtCoordinateCauchyIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtCoordinateCauchyIntegral
open Metric Filter Topology Set

noncomputable section

namespace GlobalTheory

def updCLM (n : ℕ) (k : Fin n) : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = k then ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ
    else (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)

theorem updCLM_apply (n : ℕ) (k : Fin n) (p : (Fin n → ℂ) × ℂ) :
    updCLM n k p = Function.update p.1 k p.2 := by
  funext i
  simp only [updCLM, ContinuousLinearMap.pi_apply, Function.update_apply]
  split_ifs <;> simp

theorem cauchyCoord_differentiableAt :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ),
      0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U →
      DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} →
      DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  intro n U k f z₀ r hr hz₀ hU hball hf
  set V : Set (Fin n → ℂ) := {z | z ∈ U ∧ z k ≠ 0} with hVdef
  have hV : IsOpen V := hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  have hfa : AnalyticOnNhd ℂ f V := ReciprocityTheory.AnForm.Osgood.osgood n V f hV hf
  set Φ : (Fin n → ℂ) × ℂ → ℂ := fun p => (p.2 - p.1 k)⁻¹ • f (Function.update p.1 k p.2) with hΦdef
  set Wd : Set ((Fin n → ℂ) × ℂ) := {p | Function.update p.1 k p.2 ∈ V ∧ p.2 - p.1 k ≠ 0} with hWdef
  have hupd : Continuous fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2 :=
    continuous_fst.update k continuous_snd
  have hWo : IsOpen Wd :=
    (hV.preimage hupd).inter (isOpen_ne_fun (continuous_snd.sub ((continuous_apply k).comp continuous_fst))
      continuous_const)
  have hΦa : AnalyticOnNhd ℂ Φ Wd := by
    intro p hp
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) p := by
      have he : (fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) = updCLM n k :=
        funext fun p => (updCLM_apply n k p).symm
      rw [he]; exact (updCLM n k).analyticAt p
    have h2 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => f (Function.update p.1 k p.2)) p :=
      AnalyticAt.comp (g := f) (f := fun p : (Fin n → ℂ) × ℂ => Function.update p.1 k p.2) (hfa _ hp.1) h1
    have h3 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ => p.2 - p.1 k) p :=
      analyticAt_snd.sub (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt _).comp
        analyticAt_fst)
    exact (h3.inv hp.2).smul h2
  have hΦc : ContinuousOn Φ Wd := hΦa.continuousOn
  have hD : ContinuousOn (fun p => fderiv ℂ Φ p) Wd :=
    (hΦa.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen hWo le_rfl

  set K : Set ((Fin n → ℂ) × ℂ) := closedBall z₀ (r / 2) ×ˢ sphere (0 : ℂ) r
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hKW : K ⊆ Wd := by
    rintro ⟨z, t⟩ ⟨hz, ht⟩
    simp only [mem_closedBall, mem_sphere_iff_norm, sub_zero] at hz ht
    have hzk : ‖z k‖ ≤ r / 2 := by
      have := dist_le_pi_dist z z₀ k
      rw [hz₀, dist_zero_right] at this
      linarith [this]
    refine ⟨⟨hball ?_, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_pi_le_iff hr.le]
      intro i
      by_cases hi : i = k
      · subst hi; simp [hz₀, ht]
      · rw [Function.update_of_ne hi]
        exact (dist_le_pi_dist z z₀ i).trans (by linarith)
    · simp only [Function.update_self]
      intro h; rw [h, norm_zero] at ht; linarith
    · intro h
      have : t = z k := sub_eq_zero.mp h
      rw [this] at ht; linarith
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hD.mono hKW)
  have hcirc : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ => circleMap_mem_sphere 0 hr.le θ
  have hmemW : ∀ z ∈ closedBall z₀ (r / 2), ∀ θ : ℝ, (z, circleMap 0 r θ) ∈ Wd := fun z hz θ =>
    hKW ⟨hz, hcirc θ⟩
  have hderc : Continuous fun θ => deriv (circleMap 0 r) θ := by
    have : (fun θ => deriv (circleMap 0 r) θ) = fun θ => circleMap 0 r θ * Complex.I :=
      funext fun θ => deriv_circleMap 0 r θ
    rw [this]; exact (continuous_circleMap 0 r).mul continuous_const
  have hpath : ∀ z : Fin n → ℂ, Continuous fun θ : ℝ => (z, circleMap 0 r θ) := fun z =>
    continuous_const.prodMk (continuous_circleMap 0 r)
  have hr2 : 0 < r / 2 := half_pos hr
  set F : (Fin n → ℂ) → ℝ → ℂ := fun z θ => deriv (circleMap 0 r) θ • Φ (z, circleMap 0 r θ)
  set F' : (Fin n → ℂ) → ℝ → (Fin n → ℂ) →L[ℂ] ℂ := fun z θ =>
    deriv (circleMap 0 r) θ • (fderiv ℂ Φ (z, circleMap 0 r θ)).comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ)
  have hFc : ∀ z ∈ closedBall z₀ (r / 2), Continuous (F z) := fun z hz =>
    hderc.smul (hΦc.comp_continuous (hpath z) (hmemW z hz))
  have hF'c : Continuous (F' z₀) :=
    hderc.smul ((hD.comp_continuous (hpath z₀) (hmemW z₀ (mem_closedBall_self hr2.le))).clm_comp
      continuous_const)
  have key := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := MeasureTheory.volume)
    (a := 0) (b := 2 * Real.pi) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun _ => r * (B * ‖ContinuousLinearMap.inl ℂ (Fin n → ℂ) ℂ‖)) (ball_mem_nhds z₀ hr2)
    (eventually_of_mem (ball_mem_nhds z₀ hr2) fun z hz =>
      (hFc z (ball_subset_closedBall hz)).aestronglyMeasurable)
    ((hFc z₀ (mem_closedBall_self hr2.le)).intervalIntegrable _ _)
    hF'c.aestronglyMeasurable
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      simp only [F', norm_smul]
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, norm_circleMap_zero, abs_of_pos hr]
      exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hB _ ⟨ball_subset_closedBall hz, hcirc θ⟩) (norm_nonneg _))) hr.le)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ z hz => by
      have hd : DifferentiableAt ℂ Φ (z, circleMap 0 r θ) :=
        (hΦa _ (hmemW z (ball_subset_closedBall hz) θ)).differentiableAt
      exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left (𝕜 := ℂ) z (circleMap 0 r θ))).const_smul
        (deriv (circleMap 0 r) θ))
  exact key.differentiableAt

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtCoordinateCauchyIntegralStatement
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentiableAt_coordinate_cauchy_integral : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.closedBall z₀ r ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → DifferentiableAt ℂ (fun z => ∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) z₀ := by
  first | exact @GlobalTheory.cauchyCoord_differentiableAt | exact GlobalTheory.cauchyCoord_differentiableAt | (intros; apply GlobalTheory.cauchyCoord_differentiableAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchySliceEqRemovableExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchySliceEqRemovableExtension
open Metric Filter Topology Set

namespace GlobalTheory

theorem cauchy_slice_removable_extension :
    ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by
  intro n U k f z₀ r M hr hz₀ _hU hball hd hM z hz
  set s : ℂ → ℂ := fun t => f (Function.update z k t) with hs_def

  have hupd : Differentiable ℂ (fun t : ℂ => Function.update z k t) :=
    (contDiff_update (𝕜 := ℂ) 1 z k).differentiable (by norm_num)
  have hzdist : ∀ j, ‖z j - z₀ j‖ < r := by
    intro j
    have h1 : dist z z₀ < r := hz
    rw [dist_pi_lt_iff hr] at h1
    simpa [dist_eq_norm] using h1 j
  have hzk : ‖z k‖ < r := by simpa [hz₀] using hzdist k
  have hmem : ∀ t : ℂ, ‖t‖ < 2 * r → Function.update z k t ∈ Metric.ball z₀ (2 * r) := by
    intro t ht
    rw [Metric.mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj
      simpa [dist_eq_norm, hz₀] using ht
    · rw [Function.update_of_ne hj, dist_eq_norm]
      linarith [hzdist j]
  have hsd : DifferentiableOn ℂ s (Metric.ball (0 : ℂ) (2 * r) \ {0}) := by
    refine hd.comp hupd.differentiableOn ?_
    intro t ht
    have ht1 : ‖t‖ < 2 * r := by simpa using ht.1
    have ht2 : t ≠ 0 := ht.2
    exact ⟨hball (hmem t ht1), by simpa using ht2⟩
  have hsb : BddAbove (norm ∘ s '' (Metric.ball (0 : ℂ) (2 * r) \ {0})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have ht1 : ‖t‖ < 2 * r := by simpa using ht.1
    have ht2 : t ≠ 0 := ht.2
    exact hM _ (hmem t ht1) (by simpa using ht2)
  have hg := Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds (0 : ℂ) (by linarith)) hsd hsb
  set g := Function.update s 0 (limUnder (𝓝[≠] (0 : ℂ)) s) with hg_def
  have hgc : DifferentiableOn ℂ g (Metric.closedBall 0 r) :=
    hg.mono (Metric.closedBall_subset_ball (by linarith))
  have hw : z k ∈ Metric.ball (0 : ℂ) r := by simpa using hzk
  have hcauchy := (hgc.mono closure_ball_subset_closedBall).diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  have hcongr : (∮ t in C(0, r), (t - z k)⁻¹ • g t) = (∮ t in C(0, r), (t - z k)⁻¹ • s t) := by
    refine circleIntegral.integral_congr hr.le ?_
    intro t ht
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, mem_sphere_zero_iff_norm, norm_zero] at ht
      linarith
    simp only [hg_def, Function.update_of_ne ht0]
  rw [hcongr] at hcauchy
  rw [hcauchy]
  by_cases h0 : z k = 0
  · rw [if_pos h0, h0, hg_def, Function.update_self]
  · rw [if_neg h0, hg_def, Function.update_of_ne h0, hs_def]
    simp only [Function.update_eq_self]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchySliceEqRemovableExtensionStatement
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchy_slice_eq_removable_extension : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ) (z₀ : Fin n → ℂ) (r M : ℝ), 0 < r → z₀ k = 0 → IsOpen U → Metric.ball z₀ (2 * r) ⊆ U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z ∈ Metric.ball z₀ (2 * r), z k ≠ 0 → ‖f z‖ ≤ M) → ∀ z ∈ Metric.ball z₀ r, (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • (∮ t in C(0, r), (t - z k)⁻¹ • f (Function.update z k t)) = (if z k = 0 then limUnder (nhdsWithin (0 : ℂ) {0}ᶜ) (fun t => f (Function.update z k t)) else f z) := by
  first | exact @GlobalTheory.cauchy_slice_removable_extension | exact GlobalTheory.cauchy_slice_removable_extension | (intros; apply GlobalTheory.cauchy_slice_removable_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplane
open Metric Filter Topology Set

namespace GlobalTheory

theorem riemann_extension_coordinate_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  intro n U k f hU hd hb
  refine ⟨fun z => if z k = 0 then limUnder (𝓝[≠] (0 : ℂ)) (fun t => f (Function.update z k t)) else f z,
    ?_, fun z _ hz => by simp [hz]⟩
  have hO : IsOpen {z : Fin n → ℂ | z ∈ U ∧ z k ≠ 0} :=
    hU.inter (isOpen_ne_fun (continuous_apply k) continuous_const)
  intro z₀ hz₀
  refine DifferentiableAt.differentiableWithinAt ?_
  by_cases h0 : z₀ k = 0
  · obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hz₀) hV)
    have hr : 0 < ε / 3 := by positivity
    have h2 : ball z₀ (2 * (ε / 3)) ⊆ U ∩ V := (ball_subset_ball (by linarith)).trans hball
    have hG := ((GlobalTheory.T.differentiableAt_coordinate_cauchy_integral n U k f z₀ (ε / 3) hr h0 hU
      ((closedBall_subset_ball (by linarith)).trans (hball.trans inter_subset_left)) hd).const_smul
      ((2 * (Real.pi : ℂ) * Complex.I)⁻¹))
    refine hG.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz
    exact (GlobalTheory.T.cauchy_slice_eq_removable_extension n U k f z₀ (ε / 3) M hr h0 hU (h2.trans inter_subset_left) hd
      (fun z hz hzk => hM z (h2 hz).2 (h2 hz).1 hzk) z hz).symm
  · have hf : DifferentiableAt ℂ f z₀ := hd.differentiableAt (hO.mem_nhds ⟨hz₀, h0⟩)
    refine hf.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds ⟨hz₀, h0⟩] with z hz
    simp [hz.2]
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RiemannExtensionCoordinateHyperplaneStatement
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z := by
  first | exact @GlobalTheory.riemann_extension_coordinate_hyperplane | exact GlobalTheory.riemann_extension_coordinate_hyperplane | (intros; apply GlobalTheory.riemann_extension_coordinate_hyperplane <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossZeroOfExpTwoPiIBound
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossZeroOfExpTwoPiIBound
open Metric Filter Topology Set

namespace GlobalTheory.PuncturedDiscExtension

theorem analyticAt_update_of_bdd {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    (hb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B) :
    AnalyticAt ℂ (Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F)) 0 := by
  obtain ⟨B, hB⟩ := hb
  have ht : Tendsto F (𝓝[≠] (0:ℂ)) (𝓝 (limUnder (𝓝[≠] (0:ℂ)) F)) := by
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd
    refine isBoundedUnder_of_eventually_le (a := B + ‖F 0‖) ?_
    filter_upwards [hB] with z hz
    exact (norm_sub_le _ _).trans (by linarith)
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · rw [eventually_nhdsWithin_iff] at hd ⊢
    filter_upwards [hd] with z hz hz0
    have heq : Function.update F 0 (limUnder (𝓝[≠] (0:ℂ)) F) =ᶠ[𝓝 z] F := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hz hz0).congr_of_eventuallyEq heq
  · exact continuousAt_update_same.2 ht

theorem bdd_of_re_le {F : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ F z)
    {M : ℝ} (hM : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z).re ≤ M) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖F z‖ ≤ B := by
  set g : ℂ → ℂ := fun z => (F z - ((M:ℂ) + 1))⁻¹ with hg
  have hre : ∀ᶠ z in 𝓝[≠] (0:ℂ), (F z - ((M:ℂ)+1)).re ≤ -1 := by
    filter_upwards [hM] with z hz
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
    linarith
  have hne : ∀ᶠ z in 𝓝[≠] (0:ℂ), F z - ((M:ℂ)+1) ≠ 0 := by
    filter_upwards [hre] with z hz h
    rw [h, Complex.zero_re] at hz
    linarith
  have hnorm : ∀ᶠ z in 𝓝[≠] (0:ℂ), 1 ≤ ‖F z - ((M:ℂ)+1)‖ := by
    filter_upwards [hre] with z hz
    have h1 := Complex.abs_re_le_norm (F z - ((M:ℂ)+1))
    have h2 : 1 ≤ |(F z - ((M:ℂ)+1)).re| := by
      rw [abs_of_neg (by linarith)]; linarith
    linarith
  have hgd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ g z := by
    filter_upwards [hd, hne] with z h1 h2
    exact (h1.sub_const _).inv h2
  have hgb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖g z‖ ≤ B := ⟨1, by
    filter_upwards [hnorm] with z hz
    simp only [hg, norm_inv]
    exact inv_le_one_of_one_le₀ hz⟩
  have ha := analyticAt_update_of_bdd hgd hgb
  set g' := Function.update g 0 (limUnder (𝓝[≠] (0:ℂ)) g) with hg'
  have hg'eq : ∀ z, z ≠ 0 → g' z = g z := fun z hz => Function.update_of_ne hz _ _
  by_cases hL : g' 0 = 0
  · exfalso
    rcases ha.eventually_constant_or_nhds_le_map_nhds with h | h
    · have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, hne, self_mem_nhdsWithin] with z h1 h2 h3
        rw [hg'eq z h3, hL] at h1
        exact inv_ne_zero h2 h1
      exact hF.exists.elim fun _ h => h
    · have hS : ∀ᶠ z in 𝓝 (0:ℂ), g' z = 0 ∨ ((g' z)⁻¹).re ≤ -1 := by
        have h0 := eventually_nhdsWithin_iff.1 hre
        filter_upwards [h0] with z hz
        by_cases hz0 : z = 0
        · left; rw [hz0]; exact hL
        · right; rw [hg'eq z hz0]; simp only [hg, inv_inv]; exact hz hz0
      have hS' : {w : ℂ | w = 0 ∨ (w⁻¹).re ≤ -1} ∈ 𝓝 (g' 0) := h hS
      rw [hL] at hS'
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hS'
      have hmem : ((ε/2 : ℝ) : ℂ) ∈ ball (0:ℂ) ε := by
        rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        linarith
      rcases hball hmem with h1 | h1
      · have : (ε/2 : ℝ) = 0 := by exact_mod_cast h1
        linarith
      · rw [← Complex.ofReal_inv, Complex.ofReal_re] at h1
        have : 0 < (ε/2)⁻¹ := inv_pos.2 (by linarith)
        linarith
  · have hpos : 0 < ‖g' 0‖ := norm_pos_iff.2 hL
    have hc : ContinuousAt g' 0 := ha.continuousAt
    have hev : ∀ᶠ z in 𝓝 (0:ℂ), ‖g' 0‖ / 2 < ‖g' z‖ :=
      hc.norm.eventually (lt_mem_nhds (by linarith))
    refine ⟨‖(M:ℂ)+1‖ + 2 / ‖g' 0‖, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin, hne] with z h1 h2 h3
    rw [hg'eq z h2] at h1
    have hq : 0 < ‖F z - ((M:ℂ)+1)‖ := norm_pos_iff.2 h3
    have hgz : ‖g z‖ = ‖F z - ((M:ℂ)+1)‖⁻¹ := by simp only [hg, norm_inv]
    rw [hgz] at h1
    have key : ‖F z - ((M:ℂ)+1)‖ ≤ 2 / ‖g' 0‖ := by
      have h4 := mul_lt_mul_of_pos_right h1 hq
      rw [inv_mul_cancel₀ hq.ne'] at h4
      rw [le_div_iff₀ hpos]
      nlinarith
    have h5 := norm_sub_norm_le (F z) ((M:ℂ)+1)
    linarith

end GlobalTheory.PuncturedDiscExtension

namespace GlobalTheory


open GlobalTheory.PuncturedDiscExtension in
theorem holomorphic_extension_of_exp_two_pi_I_bound :
    ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r →
      DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) →
      (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 →
        ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧
        ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t := by
  intro H r C N hr hH hC
  have hball : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∈ ball (0:ℂ) r ∧ z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0:ℂ) hr), self_mem_nhdsWithin]
      with z h1 h2
    exact ⟨h1, h2⟩
  have hHd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ H z := by
    filter_upwards [hball] with z hz
    exact hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz.1, hz.2⟩)
  set f : ℂ → ℂ := fun z => 2 * (Real.pi:ℂ) * Complex.I * H z with hf
  have hfd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z := by
    filter_upwards [hHd] with z hz
    exact hz.const_mul _
  have hfb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖f z‖ ≤ B := by
    set Gf : ℂ → ℂ := fun z => z ^ N * Complex.exp (f z) with hGf
    have hGd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ Gf z := by
      filter_upwards [hfd] with z hz
      exact (differentiableAt_id.pow N).mul hz.cexp
    have hGb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖Gf z‖ ≤ B := ⟨C, by
      filter_upwards [hball] with z hz
      have h := hC z hz.1 hz.2
      show ‖z ^ N * Complex.exp (f z)‖ ≤ C
      rw [norm_mul, norm_pow, mul_comm]
      exact h⟩
    have ha := analyticAt_update_of_bdd hGd hGb
    set G' := Function.update Gf 0 (limUnder (𝓝[≠] (0:ℂ)) Gf) with hG'
    have hG'eq : ∀ z, z ≠ 0 → G' z = Gf z := fun z hz => Function.update_of_ne hz _ _
    have hnz : ¬ ∀ᶠ z in 𝓝 (0:ℂ), G' z = 0 := by
      intro h
      have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z h1 h2
        rw [hG'eq z h2] at h1
        exact mul_ne_zero (pow_ne_zero _ h2) (Complex.exp_ne_zero _) h1
      exact hF.exists.elim fun _ h => h
    obtain ⟨k, u, hu, hu0, hGu⟩ := (ha.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnz
    have hpos : 0 < ‖u 0‖ := norm_pos_iff.2 hu0
    have huc : ContinuousAt u 0 := hu.continuousAt
    have hup : ∀ᶠ z in 𝓝 (0:ℂ), ‖u z‖ < ‖u 0‖ + 1 :=
      huc.norm.eventually (gt_mem_nhds (by linarith))
    have hlo : ∀ᶠ z in 𝓝 (0:ℂ), ‖u 0‖ / 2 < ‖u z‖ :=
      huc.norm.eventually (lt_mem_nhds (by linarith))
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖z‖ < 1 := by
      filter_upwards [ball_mem_nhds (0:ℂ) one_pos] with z hz
      simpa using hz
    have hrel : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ≠ 0 ∧ ‖z‖ < 1 ∧ ‖u z‖ < ‖u 0‖ + 1 ∧
        ‖u 0‖ / 2 < ‖u z‖ ∧ z ^ N * Complex.exp (f z) = z ^ k * u z := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h1.and (hup.and (hlo.and hGu)))]
        with z hz hh
      obtain ⟨ha1, ha2, ha3, ha4⟩ := hh
      refine ⟨hz, ha1, ha2, ha3, ?_⟩
      have := hG'eq z hz
      rw [ha4, sub_zero, smul_eq_mul] at this
      exact this.symm
    rcases le_or_gt N k with hk | hk
    · refine bdd_of_re_le hfd (M := Real.log (‖u 0‖ + 1)) ?_
      filter_upwards [hrel] with z hh
      obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
      have hk' : z ^ k = z ^ N * z ^ (k - N) := by rw [← pow_add, Nat.add_sub_cancel' hk]
      rw [hk', mul_assoc] at he
      have he2 : Complex.exp (f z) = z ^ (k - N) * u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
      have hn : ‖Complex.exp (f z)‖ ≤ ‖u 0‖ + 1 := by
        rw [he2, norm_mul, norm_pow]
        have : ‖z‖ ^ (k - N) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
        nlinarith [norm_nonneg (u z)]
      rw [Complex.norm_exp] at hn
      have := Real.log_le_log (Real.exp_pos _) hn
      rwa [Real.log_exp] at this
    · obtain ⟨B, hB⟩ := bdd_of_re_le (F := fun z => -f z)
        (by filter_upwards [hfd] with z hz; exact hz.neg) (M := -Real.log (‖u 0‖ / 2)) (by
        filter_upwards [hrel] with z hh
        obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
        have hN : z ^ N = z ^ k * z ^ (N - k) := by rw [← pow_add, Nat.add_sub_cancel' hk.le]
        rw [hN, mul_assoc] at he
        have he2 : z ^ (N - k) * Complex.exp (f z) = u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
        have hn : ‖u 0‖ / 2 ≤ ‖Complex.exp (f z)‖ := by
          have : ‖u z‖ ≤ ‖Complex.exp (f z)‖ := by
            rw [← he2, norm_mul, norm_pow]
            have : ‖z‖ ^ (N - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
            nlinarith [norm_nonneg (Complex.exp (f z))]
          linarith
        rw [Complex.norm_exp] at hn
        have := Real.log_le_log (by positivity) hn
        rw [Real.log_exp] at this
        simp only [Complex.neg_re]
        linarith)
      exact ⟨B, by filter_upwards [hB] with z hz; simpa only [norm_neg] using hz⟩
  obtain ⟨B, hB⟩ := hfb
  have hHb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖H z‖ ≤ B := ⟨B / (2 * Real.pi), by
    filter_upwards [hB] with z hz
    have hf' : ‖f z‖ = 2 * Real.pi * ‖H z‖ := by
      simp only [hf, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [hf'] at hz
    rw [le_div_iff₀ (by positivity)]
    linarith⟩
  have haH := analyticAt_update_of_bdd hHd hHb
  refine ⟨Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H), ?_,
    fun t _ ht => Function.update_of_ne ht _ _⟩
  intro z hz
  by_cases h0 : z = 0
  · subst h0
    exact haH.differentiableAt.differentiableWithinAt
  · have hzd : DifferentiableAt ℂ H z :=
      hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, h0⟩)
    have heq : Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H) =ᶠ[𝓝 z] H := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hzd.congr_of_eventuallyEq heq).differentiableWithinAt

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossZeroOfExpTwoPiIBoundStatement
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extension_across_zero_of_exp_two_pi_I_bound : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t := by
  first | exact @GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound | exact GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound | (intros; apply GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyBoundedOffCoordinateHyperplanes
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyBoundedOffCoordinateHyperplanes
open Metric Filter Topology Set

namespace GlobalTheory.HyperplaneLocBound

lemma isOpen_offHyperplanes (n a : ℕ) (ρ : ℝ) :
    IsOpen {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
  have : {z : Fin n → ℂ | z ∈ ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} =
      ball 0 ρ ∩ ⋂ k ∈ (Finset.univ.filter fun k : Fin n => (k : ℕ) < a),
        (fun z : Fin n → ℂ => z k) ⁻¹' {0}ᶜ := by
    ext z; simp
  rw [this]
  exact isOpen_ball.inter (isOpen_biInter_finset fun k _ =>
    (continuous_apply k).isOpen_preimage _ isOpen_compl_singleton)

lemma prod_update_eq {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℕ) (k : Fin n) (t : ℂ) :
    ∏ j, ‖Function.update z k t j‖ ^ m j =
      ‖t‖ ^ m k * ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma norm_le_of_circle {n a : ℕ} {ρ r : ℝ} {Φ : (Fin n → ℂ) → ℂ} {m : Fin n → ℕ}
    (hext : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t)
    (hΦ : DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0})
    (hgr : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1)
    {z₀ z : Fin n → ℂ} (hr : 0 < r) (hsub : ball z₀ (2 * r) ⊆ ball 0 ρ)
    (hz : z ∈ closedBall z₀ r) (hgen : ∀ j, z j ≠ 0) {k : Fin n} (hk0 : z₀ k = 0)
    {B : ℝ} (hB : ∀ t : ℂ, ‖t‖ = r → ‖Φ (Function.update z k t)‖ ≤ B) : ‖Φ z‖ ≤ B := by
  set H : ℂ → ℂ := fun t => Φ (Function.update z k t) with hH
  have hmem : ∀ t ∈ ball (0 : ℂ) (2 * r), Function.update z k t ∈ ball z₀ (2 * r) := by
    intro t ht
    rw [mem_ball, dist_pi_lt_iff (by linarith)]
    intro j
    by_cases hj : j = k
    · subst hj; simpa [hk0] using ht
    · rw [Function.update_of_ne hj]
      exact lt_of_le_of_lt ((dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)) (by linarith)
  have hU : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 → Function.update z k t ∈
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    intro t ht ht0
    refine ⟨hsub (hmem t ht), fun j _ => ?_⟩
    by_cases hj : j = k
    · subst hj; simpa using ht0
    · rw [Function.update_of_ne hj]; exact hgen j
  have hHd : DifferentiableOn ℂ H (ball (0 : ℂ) (2 * r) \ {0}) := by
    intro t ht
    have hd := (hΦ _ (hU t ht.1 ht.2)).differentiableAt
      ((isOpen_offHyperplanes n a ρ).mem_nhds (hU t ht.1 ht.2))
    exact (hd.comp t (hasFDerivAt_update z t).differentiableAt).differentiableWithinAt
  set P := ∏ j ∈ Finset.univ.erase k, ‖z j‖ ^ m j with hPdef
  have hP : 0 < P := Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (hgen j)) _
  have hHg : ∀ t ∈ ball (0 : ℂ) (2 * r), t ≠ 0 →
      ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ m k ≤ 1 / P := by
    intro t ht ht0
    have h1 := hgr _ (hU t ht ht0).1 (hU t ht ht0).2
    rw [prod_update_eq, ← mul_assoc] at h1
    exact (le_div_iff₀ hP).2 h1
  obtain ⟨G, hGd, hGH⟩ := hext H (2 * r) (1 / P) (m k) (by linarith) hHd hHg
  have hcl : closedBall (0 : ℂ) r ⊆ ball 0 (2 * r) := closedBall_subset_ball (by linarith)
  have hzk : z k ∈ closedBall (0 : ℂ) r := by
    rw [mem_closedBall]
    have := dist_le_pi_dist z z₀ k
    rw [hk0] at this
    exact this.trans (mem_closedBall.1 hz)
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    (hGd.diffContOnCl_ball hcl) (C := B) ?_ (by rw [closure_ball 0 hr.ne']; exact hzk)
  · rw [hGH _ (hcl hzk) (hgen k)] at key
    simpa [H] using key
  · intro t ht
    rw [frontier_ball 0 hr.ne', mem_sphere, dist_zero_right] at ht
    have ht0 : t ≠ 0 := by rintro rfl; simp at ht; linarith
    have htb : t ∈ ball (0 : ℂ) (2 * r) := by rw [mem_ball, dist_zero_right]; linarith
    rw [hGH t htb ht0]
    exact hB t ht

theorem locally_bounded : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  intro hext n a ρ Φ m hρ hΦ hgr z₀ hz₀
  have hUo := isOpen_offHyperplanes n a ρ
  have hδ : 0 < ρ - ‖z₀‖ := by rw [mem_ball, dist_zero_right] at hz₀; linarith
  obtain ⟨r, hr0, hrδ, hrk⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r < ρ - ‖z₀‖ ∧ ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
    have h2 : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2 * r < ρ - ‖z₀‖ := by
      apply nhdsWithin_le_nhds
      have : Tendsto (fun r : ℝ => 2 * r) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_const_mul (2 : ℝ)).tendsto 0
      exact this.eventually (gt_mem_nhds hδ)
    have h3 : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ k, z₀ k ≠ 0 → r < ‖z₀ k‖ := by
      rw [eventually_all]; intro k
      by_cases hk : z₀ k = 0
      · exact Eventually.of_forall fun _ h => absurd hk h
      · exact (show ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ‖z₀ k‖ from
          nhdsWithin_le_nhds (gt_mem_nhds (norm_pos_iff.2 hk))).mono fun r hr _ => hr
    exact (h1.and (h2.and h3)).exists
  have hsub : ball z₀ (2 * r) ⊆ ball 0 ρ := ball_subset_ball' (by rw [dist_zero_right]; linarith)
  set K := closedBall z₀ r ∩ {ζ : Fin n → ℂ | ∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → ‖ζ k‖ = r}
    with hK
  have hKc : IsCompact K := (isCompact_closedBall z₀ r).inter_right (by
    simp only [setOf_forall]
    exact isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_eq (continuous_norm.comp (continuous_apply k)) continuous_const)
  have hKU : K ⊆ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} := by
    rintro ζ ⟨hζ, hζc⟩
    refine ⟨hsub (closedBall_subset_ball (by linarith) hζ), fun k hk => ?_⟩
    by_cases h0 : z₀ k = 0
    · intro h; have := hζc k hk h0; rw [h, norm_zero] at this; linarith
    · intro h
      have h1 := dist_le_pi_dist ζ z₀ k
      rw [h, dist_comm, dist_zero_right] at h1
      have := hrk k h0
      linarith [mem_closedBall.1 hζ]
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hΦ.continuousOn.mono hKU)
  have hind : ∀ S : Finset (Fin n), ∀ z : Fin n → ℂ, (∀ j, z j ≠ 0) → z ∈ closedBall z₀ r →
      (∀ k : Fin n, (k : ℕ) < a → z₀ k = 0 → k ∉ S → ‖z k‖ = r) → ‖Φ z‖ ≤ M := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro z _ hz hc
      exact hM z ⟨hz, fun k hk h0 => hc k hk h0 (by simp)⟩
    · intro k S hkS ih z hgen hz hc
      by_cases hk : (k : ℕ) < a ∧ z₀ k = 0
      · refine norm_le_of_circle hext hΦ hgr hr0 hsub hz hgen hk.2 fun t ht => ?_
        apply ih
        · intro j
          by_cases hj : j = k
          · subst hj; simp only [Function.update_self]; rintro rfl; simp at ht; linarith
          · rw [Function.update_of_ne hj]; exact hgen j
        · rw [mem_closedBall, dist_pi_le_iff hr0.le]
          intro j
          by_cases hj : j = k
          · subst hj; simp [hk.2, ht]
          · rw [Function.update_of_ne hj]
            exact (dist_le_pi_dist z z₀ j).trans (mem_closedBall.1 hz)
        · intro j hj h0 hjS
          by_cases hjk : j = k
          · subst hjk; simpa using ht
          · rw [Function.update_of_ne hjk]; exact hc j hj h0 (by simp [hjk, hjS])
      · apply ih z hgen hz
        intro j hj h0 hjS
        by_cases hjk : j = k
        · subst hjk; exact absurd ⟨hj, h0⟩ hk
        · exact hc j hj h0 (by simp [hjk, hjS])
  refine ⟨ball z₀ r, ball_mem_nhds z₀ hr0, M, fun z hzV hzρ hza => ?_⟩
  have hzU : z ∈ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} :=
    ⟨hzρ, hza⟩
  let w : ℂ → Fin n → ℂ := fun s j => if z j = 0 then s else z j
  have hwc : Continuous w := continuous_pi fun j => by
    by_cases h : z j = 0
    · simp only [w, h, if_true]; exact continuous_id
    · simp only [w, h, if_false]; exact continuous_const
  have hw0 : w 0 = z := funext fun j => by by_cases h : z j = 0 <;> simp [w, h]
  have hΦz : ContinuousAt Φ z := (hΦ.differentiableAt (hUo.mem_nhds hzU)).continuousAt
  have hT : Tendsto (fun s => Φ (w s)) (𝓝[≠] (0 : ℂ)) (𝓝 (Φ z)) := by
    have hc : ContinuousAt (Φ ∘ w) 0 :=
      ContinuousAt.comp (x := 0) (by rw [hw0]; exact hΦz) hwc.continuousAt
    have h := hc.tendsto
    rw [Function.comp_apply, hw0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖Φ (w s)‖ ≤ M := by
    have h1 : ∀ᶠ s in 𝓝 (0 : ℂ), w s ∈ ball z₀ r :=
      hwc.continuousAt.preimage_mem_nhds (by rw [hw0]; exact isOpen_ball.mem_nhds hzV)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with s hs hs0
    apply hind Finset.univ (w s)
    · intro j
      simp only [w]
      split_ifs with h
      · exact hs0
      · exact h
    · exact ball_subset_closedBall hs
    · intro k _ _ hk; exact absurd (Finset.mem_univ k) hk
  exact le_of_tendsto hT.norm hev

end GlobalTheory.HyperplaneLocBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyBoundedOffCoordinateHyperplanesStatement
open Metric Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_bounded_off_coordinate_hyperplanes : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  first | exact @GlobalTheory.HyperplaneLocBound.locally_bounded | exact GlobalTheory.HyperplaneLocBound.locally_bounded | (intros; apply GlobalTheory.HyperplaneLocBound.locally_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanes
open Metric Filter Topology Set

namespace GlobalTheory.HyperplaneExt

theorem norm_le_of_off_hyperplane {n : ℕ} {U V : Set (Fin n → ℂ)} {k : Fin n} {F : (Fin n → ℂ) → ℂ} {M : ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContinuousOn F U)
    (hb : ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖F z‖ ≤ M) : ∀ z ∈ V, z ∈ U → ‖F z‖ ≤ M := by
  intro z hzV hzU
  by_cases hz : z k = 0
  · have hc : ContinuousAt F z := hF.continuousAt (hU.mem_nhds hzU)
    have hupd : Continuous (fun ε : ℂ => Function.update z k ε) := continuous_const.update k continuous_id
    have h0 : Function.update z k 0 = z := by rw [← hz]; exact Function.update_eq_self k z
    have ht : Tendsto (fun ε : ℂ => Function.update z k ε) (𝓝[≠] (0 : ℂ)) (𝓝 z) := by
      have := hupd.tendsto 0
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hT : Tendsto (fun ε : ℂ => F (Function.update z k ε)) (𝓝[≠] (0 : ℂ)) (𝓝 (F z)) :=
      hc.tendsto.comp ht
    refine le_of_tendsto hT.norm ?_
    have hm : ∀ᶠ ε in 𝓝[≠] (0 : ℂ), Function.update z k ε ∈ V ∩ U :=
      ht (inter_mem (hV.mem_nhds hzV) (hU.mem_nhds hzU))
    filter_upwards [hm, self_mem_nhdsWithin] with ε hε hne
    exact hb _ hε.1 hε.2 (by simpa using hne)
  · exact hb z hzV hzU hz

theorem extend_finset (hR : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n : ℕ) (s : Finset (Fin n)) (W : Set (Fin n → ℂ)) (Φ : (Fin n → ℂ) → ℂ), IsOpen W →
      DifferentiableOn ℂ Φ {z | z ∈ W ∧ ∀ k ∈ s, z k ≠ 0} →
      (∀ z₀ ∈ W, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ W → (∀ k ∈ s, z k ≠ 0) → ‖Φ z‖ ≤ M) →
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ ∀ z ∈ W, (∀ k ∈ s, z k ≠ 0) → F z = Φ z := by
  intro n s
  induction s using Finset.induction_on with
  | empty =>
    intro W Φ _ hd _
    refine ⟨Φ, ?_, fun _ _ _ => rfl⟩
    simpa using hd
  | insert j t _ ih =>
    intro W Φ hW hd hb
    have hUeq : {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} = W ∩ ⋂ k ∈ t, {z | z k ≠ 0} := by
      ext z; simp
    have hU : IsOpen {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} := by
      rw [hUeq]
      exact hW.inter (isOpen_biInter_finset fun k _ => isOpen_ne_fun (continuous_apply k) continuous_const)
    have hd1 : DifferentiableOn ℂ Φ {z | z ∈ {z : Fin n → ℂ | z ∈ W ∧ ∀ k ∈ t, z k ≠ 0} ∧ z j ≠ 0} := by
      refine hd.mono fun z hz => ⟨hz.1.1, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hz.2
      · exact hz.1.2 k hk
    obtain ⟨F1, hF1d, hF1e⟩ := hR n _ j Φ hU hd1 (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀.1
      refine ⟨V, hV, M, fun z hzV hzU hzj => hM z hzV hzU.1 ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hzj
      · exact hzU.2 k hk)
    have hall : ∀ z : Fin n → ℂ, (∀ k ∈ insert j t, z k ≠ 0) ↔ z j ≠ 0 ∧ ∀ k ∈ t, z k ≠ 0 := by
      intro z; simp
    obtain ⟨F, hFd, hFe⟩ := ih W F1 hW hF1d (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := hb z₀ hz₀
      refine ⟨interior V, interior_mem_nhds.mpr hV, M, ?_⟩
      intro z hzV hzW ht
      refine norm_le_of_off_hyperplane (k := j) hU isOpen_interior hF1d.continuousOn
        (fun w hwV hwU hwj => ?_) z hzV ⟨hzW, ht⟩
      rw [hF1e w hwU hwj]
      exact hM w (interior_subset hwV) hwU.1 ((hall w).2 ⟨hwj, hwU.2⟩))
    refine ⟨F, hFd, fun z hz hk => ?_⟩
    have hk' := (hall z).1 hk
    rw [hFe z hz hk'.2, hF1e z ⟨hz, hk'.2⟩ hk'.1]

theorem extension_of_parts
    (h1 : ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) (h2 : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M) (h3 : ∀ (n : ℕ) (U : Set (Fin n → ℂ)) (k : Fin n) (f : (Fin n → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ f {z | z ∈ U ∧ z k ≠ 0} → (∀ z₀ ∈ U, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ U → z k ≠ 0 → ‖f z‖ ≤ M) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, z k ≠ 0 → F z = f z) :
    ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  intro n a ρ Φ m hρ hd hb
  have hset : {z : Fin n → ℂ | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} =
      {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k ≠ 0} := by
    ext z; simp
  have hmem : ∀ z : Fin n → ℂ, (∀ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k ≠ 0) ↔
      ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0 := by
    intro z; simp
  obtain ⟨F, hFd, hFe⟩ := extend_finset h3 n (Finset.univ.filter (fun k : Fin n => (k : ℕ) < a))
    (Metric.ball 0 ρ) Φ isOpen_ball (hset ▸ hd) (by
      intro z₀ hz₀
      obtain ⟨V, hV, M, hM⟩ := h2 h1 n a ρ Φ m hρ hd hb z₀ hz₀
      exact ⟨V, hV, M, fun z hzV hz hk => hM z hzV hz ((hmem z).1 hk)⟩)
  exact ⟨F, hFd, fun z hz hk => hFe z hz ((hmem z).2 hk)⟩

theorem extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z :=
  extension_of_parts GlobalTheory.T.extension_across_zero_of_exp_two_pi_I_bound GlobalTheory.T.locally_bounded_off_coordinate_hyperplanes GlobalTheory.T.exists_differentiableOn_ext_of_bounded_off_hyperplane

end GlobalTheory.HyperplaneExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanesStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  first | exact @GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | exact GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | (intros; apply GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydisc
open GlobalTheory.ShFam.Hor

namespace GlobalTheory

theorem periodVec_im_dot {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) :
    (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im
      = dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
  simp [dotProduct, Matrix.mulVec, Complex.im_sum, Finset.mul_sum, Complex.mul_im]

theorem periodVec_norm_exp_le {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (hM : (M.map Complex.im).PosDef)
    (v : Fin g → ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ))))‖ ≤ 1 := by
  have h1 : 0 ≤ dotProduct (fun i => (v i : ℝ)) ((M.map Complex.im).mulVec (fun i => (v i : ℝ))) := by
    have := hM.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i : ℝ))
    simpa using this
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have : (2 * Real.pi * Complex.I *
      dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).re
      = -(2 * Real.pi) * (dotProduct (fun i => (v i : ℂ)) (M.mulVec (fun i => (v i : ℂ)))).im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, periodVec_im_dot]
  have := Real.pi_pos
  nlinarith

end GlobalTheory

namespace GlobalTheory

theorem periodVec_extends : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, 0 ≤ dotProduct v ((B k).mulVec v)) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = F (logExp a s) := by
  intro n a g ha ρ₁ τ B v hρ0 hρ1 hdiff hpos hmono hm
  let vC : Fin g → ℂ := fun i => (v i : ℂ)
  let m : Fin a → ℤ := fun k => dotProduct v ((B k).mulVec v)
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcd : ∀ x : ℂ, 2 * Real.pi * Complex.I * (x / (2 * Real.pi * Complex.I)) = x := fun x => by
    field_simp
  let h : (Fin n → ℂ) → ℂ := fun s => dotProduct vC ((τ s).mulVec vC) -
    ∑ k, s (Fin.castLE ha k) * ((m k : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
  have hdh : DifferentiableOn ℂ h
      {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁} := by
    apply DifferentiableOn.sub
    · simp only [dotProduct, Matrix.mulVec]
      apply DifferentiableOn.fun_sum; intro i _
      apply DifferentiableOn.mul (differentiableOn_const _)
      apply DifferentiableOn.fun_sum; intro j _
      exact (hdiff i j).mul (differentiableOn_const _)
    · apply DifferentiableOn.fun_sum; intro k _
      simp only [div_eq_mul_inv]
      apply DifferentiableOn.mul_const
      apply DifferentiableOn.mul_const
      exact differentiableOn_pi.mp differentiableOn_id (Fin.castLE ha k)
  have hQ : ∀ k : Fin a, dotProduct vC (((B k).map (Int.cast : ℤ → ℂ)).mulVec vC) = ((m k : ℤ) : ℂ) := by
    intro k
    simp [vC, m, dotProduct, Matrix.mulVec, Int.cast_sum, Int.cast_mul]
  have hinv : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
      ∀ k : Fin n, (k : ℕ) < a → h (s + Pi.single k (2 * Real.pi * Complex.I)) = h s := by
    intro s hs hb k hk
    obtain ⟨k', rfl⟩ : ∃ k' : Fin a, Fin.castLE ha k' = k := ⟨⟨k, hk⟩, Fin.ext rfl⟩
    have hτ := hmono s hs hb k'
    simp only [h]
    rw [hτ, Matrix.add_mulVec, dotProduct_add, hQ k']
    have hsum : ∑ j, (s + Pi.single (Fin.castLE ha k') (2 * Real.pi * Complex.I) : Fin n → ℂ) (Fin.castLE ha j)
        * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I)
        = ∑ j, s (Fin.castLE ha j) * ((m j : ℤ) : ℂ) / (2 * Real.pi * Complex.I) + ((m k' : ℤ) : ℂ) := by
      simp only [Pi.add_apply, add_mul, add_div, Finset.sum_add_distrib]
      congr 1
      simp only [Pi.single_apply, (Fin.castLE_injective ha).eq_iff, ite_mul, zero_mul, ite_div, zero_div,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp
    rw [hsum]; ring
  obtain ⟨H, hHd, hHe⟩ := GlobalTheory.T.exists_holomorphic_descent_punctPolydisc_logCover n a ρ₁ h hρ0 hρ1 hdh hinv
  let m' : Fin n → ℕ := fun j => if hj : (j : ℕ) < a then (m ⟨j, hj⟩).toNat else 0
  have hm0 : ∀ k, (((m k).toNat : ℕ) : ℂ) = ((m k : ℤ) : ℂ) := fun k => by
    have := Int.toNat_of_nonneg (hm k)
    exact_mod_cast this
  have hbound : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) →
      ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k ≤ 1 := by
    intro z hz hz0
    let s : Fin n → ℂ := fun j => if (j : ℕ) < a then Complex.log (z j) else z j
    have hzj : ∀ j, ‖z j‖ < ρ₁ := fun j =>
      lt_of_le_of_lt (norm_le_pi_norm z j) (by simpa using hz)
    have hls : logExp a s = z := by
      funext j; simp only [logExp, s]; split_ifs with hj
      · exact Complex.exp_log (hz0 j hj)
      · rfl
    have hsD : s ∈ logDom n a := by
      simp only [logDom, Set.mem_setOf_eq]
      intro j; simp only [s]; split_ifs with hj
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.2 (hz0 j hj)) (lt_of_lt_of_le (hzj j) hρ1)
      · exact lt_of_lt_of_le (hzj j) hρ1
    have hb' : logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by rw [hls]; exact hz
    have hHz : h s = H z := by rw [hHe s hsD hb', hls]
    have hprod : ∏ j, (z j) ^ m' j = ∏ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat := by
      symm
      apply Finset.prod_of_injOn (Fin.castLE ha)
      · intro x _ y _ hxy; exact Fin.castLE_injective ha hxy
      · intro x _; simp
      · intro j _ hj
        have : ¬ (j : ℕ) < a := by
          intro hlt; apply hj; exact ⟨⟨j, hlt⟩, by simp, Fin.ext rfl⟩
        simp [m', this]
      · intro k _; simp [m', Fin.coe_castLE, k.isLt]
    have hexp : ∀ k : Fin a, (z (Fin.castLE ha k)) ^ (m k).toNat
        = Complex.exp (s (Fin.castLE ha k) * ((m k : ℤ) : ℂ)) := by
      intro k
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
      rw [mul_comm, ← hm0 k, Complex.exp_nat_mul]
      congr 1
      simp only [s, if_pos hk]; exact (Complex.exp_log (hz0 _ hk)).symm
    calc ‖Complex.exp (2 * Real.pi * Complex.I * H z)‖ * ∏ k, ‖z k‖ ^ m' k
        = ‖Complex.exp (2 * Real.pi * Complex.I * h s) * ∏ k, z k ^ m' k‖ := by
          rw [norm_mul, norm_prod, hHz]; simp only [norm_pow]
      _ = ‖Complex.exp (2 * Real.pi * Complex.I * dotProduct vC ((τ s).mulVec vC))‖ := by
          rw [hprod, Finset.prod_congr rfl (fun k _ => hexp k), ← Complex.exp_sum, ← Complex.exp_add]
          congr 2
          simp only [h]
          rw [mul_sub, Finset.mul_sum, Finset.sum_congr rfl (fun k _ => hcd _)]
          ring
      _ ≤ 1 := periodVec_norm_exp_le _ (hpos s hsD hb').2 v
  obtain ⟨F, hFd, hFe⟩ := GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes n a ρ₁ H m' hρ0 hHd hbound
  refine ⟨F, hFd, fun s hs hb => ?_⟩
  rw [hFe _ hb (fun k hk => by simp [logExp, hk, Complex.exp_ne_zero])]
  exact hHe s hs hb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodQuadFormExtendsHolomorphicPunctPolydiscStatement
open GlobalTheory.ShFam.Hor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodQuadForm_extends_holomorphic_punctPolydisc : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, 0 ≤ dotProduct v ((B k).mulVec v)) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) - ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) = F (logExp a s) := by
  first | exact @GlobalTheory.periodVec_extends | exact GlobalTheory.periodVec_extends | (intros; apply GlobalTheory.periodVec_extends <;> assumption)
end
