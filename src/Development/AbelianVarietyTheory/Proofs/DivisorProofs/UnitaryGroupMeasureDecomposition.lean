module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureDetOneFactorNearIdentityLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieHaarLeTwoMulTangentNormalizedHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieHaarLeTwoMulTangentNormalizedHaar
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowDens

open Filter Topology Metric Set GlobalTheory.SUVol.DensOne
open scoped NNReal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lam_le_two_mul_tangentHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → lam s ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
  intro E _ _ _ r Ψ G hG lam _
  obtain ⟨hH, hD⟩ := tangentHaar_realSU_of_det Ψ G hG lam
  generalize tangentHaar (realSU Ψ G) (lam.map Subtype.val) = μ at hH hD ⊢
  let ι : realLie Ψ G →ₗᵢ[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    ⟨(incl Ψ G).toLinearMap, fun X => norm_incl Ψ G X⟩
  let L₀ : (Ψ → Matrix (Fin r) (Fin r) ℂ) →ₗ[ℝ]
      ((Ψ → Matrix (Fin r) (Fin r) ℂ) →L[ℝ] (Ψ → Matrix (Fin r) (Fin r) ℂ)) :=
    LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ LinearMap.mul ℝ _
  have hL₀ : Continuous L₀ := L₀.continuous_of_finiteDimensional
  have he : Continuous (chartExp Ψ G hG) := continuous_chartExp Ψ G hG
  have he0 : chartExp Ψ G hG 0 = 1 := chartExp_zero Ψ G hG
  have hd : HasStrictFDerivAt (fun x => matR Ψ G (chartExp Ψ G hG x)) ι.toContinuousLinearMap 0 :=
    hasStrictFDerivAt_chart Ψ G hG
  have hL : ContinuousAt (fun g => L₀ (matR Ψ G g)) 1 := (hL₀.comp (continuous_matR Ψ G)).continuousAt
  have hL1 : (fun g => L₀ (matR Ψ G g)) 1 = ContinuousLinearMap.id ℝ _ := by ext1 A; exact one_mul A
  have hm : ∀ g h, matR Ψ G (g * h) = (fun g => L₀ (matR Ψ G g)) g (matR Ψ G h) := fun g h => rfl
  have hn : ∀ ρ : ℝ, 0 < ρ → chartExp Ψ G hG '' ball 0 ρ ∈ 𝓝 (1 : realSU Ψ G) := fun ε hε =>
    (tendsto_iff_comap.1 ((continuous_matR Ψ G).tendsto 1))
      (eventually_mem_image Ψ G hG (ball_mem_nhds 0 hε))

  haveI : ProperSpace (realLie Ψ G) := FiniteDimensional.proper_real _
  obtain ⟨δ₀, hδ₀, hinj⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ InjOn (chartExp Ψ G hG) (closedBall 0 δ₀) := by
    obtain ⟨s, hs, ha⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))
    obtain ⟨δ, hδ, hsub⟩ := nhds_basis_closedBall.mem_iff.1 hs
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    have h1 := ha x (hsub hx) y (hsub hy)
    simp only [hxy, sub_self, zero_sub, norm_neg, LinearIsometry.coe_toContinuousLinearMap,
      LinearIsometry.norm_map] at h1
    have h2 : ‖x - y‖ ≤ 0 := by
      have h3 : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
      rw [h3] at h1
      linarith
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h2)
  have hK : MeasurableSet (closedBall (0 : realLie Ψ G) δ₀) := measurableSet_closedBall
  have hemb := ContinuousOn.measurableEmbedding hK he.continuousOn hinj
  set ν : Measure (realLie Ψ G) :=
    (μ.comap ((closedBall (0 : realLie Ψ G) δ₀).domRestrict (chartExp Ψ G hG))).map Subtype.val with hν
  have hνS : ∀ S : Set (realLie Ψ G), MeasurableSet S →
      ν S = μ (chartExp Ψ G hG '' (S ∩ closedBall 0 δ₀)) := by
    intro S hS
    rw [hν, Measure.map_apply measurable_subtype_coe hS, hemb.comap_apply]
    congr 1
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, ⟨hx, x.2⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
  have hνsub : ∀ S : Set (realLie Ψ G), MeasurableSet S → S ⊆ closedBall 0 δ₀ →
      ν S = μ (chartExp Ψ G hG '' S) := fun S hS h => by rw [hνS S hS, inter_eq_left.2 h]
  haveI : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνS _ MeasurableSet.univ, univ_inter]
    exact ((isCompact_closedBall _ _).image he).measure_lt_top
  have hball : ∀ (X : realLie Ψ G) (ρ : ℝ), ‖X‖ + ρ ≤ δ₀ → ball X ρ ⊆ closedBall 0 δ₀ := by
    intro X ρ h y hy
    rw [mem_ball_iff_norm] at hy
    rw [mem_closedBall_zero_iff]
    have := norm_le_norm_add_norm_sub' y X
    linarith
  have hpos : ∀ ρ > 0, 0 < ν (closedBall (0 : realLie Ψ G) ρ) := by
    intro ρ hρ
    have h1 : ν (ball 0 (min ρ δ₀)) ≠ 0 := by
      rw [hνsub _ measurableSet_ball (hball 0 _ (by simp))]
      exact (μ.measure_pos_of_mem_nhds (hn _ (lt_min hρ hδ₀))).ne'
    exact pos_iff_ne_zero.2 fun h => h1 (measure_mono_null
      ((ball_subset_closedBall).trans (closedBall_subset_closedBall (min_le_left _ _))) h)

  have himg : ∀ (g : realSU Ψ G) (S : Set (realSU Ψ G)), μ ((fun h => g * h) '' S) = μ S := fun g S => by
    rw [image_mul_left, measure_preimage_mul]
  have hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, Formalism.BasicNotions.Examples₂.CD.QInv ν ε δ := by
    intro ε hε0 hε1
    obtain ⟨δ, hδ, H⟩ := GlobalTheory.translate_chart_ball_distortion _ _ _ (chartExp Ψ G hG) (matR Ψ G) ι
      (fun g => L₀ (matR Ψ G g)) he he0 hd hL hL1 hm hn (1 + ε / 3) (by linarith)
    refine ⟨min (δ / 2) (δ₀ / 4), by positivity, fun X hX ρ hρ0 hρ => ?_⟩
    have hXδ : ‖X‖ < δ / 2 := lt_of_lt_of_le hX (min_le_left _ _)
    have hX4 : ‖X‖ < δ₀ / 4 := lt_of_lt_of_le hX (min_le_right _ _)
    have hρδ : ρ < δ / 2 := lt_of_lt_of_le hρ (min_le_left _ _)
    have hρ4 : ρ < δ₀ / 4 := lt_of_lt_of_le hρ (min_le_right _ _)
    have hXb : X ∈ ball (0 : realLie Ψ G) δ := mem_ball_zero_iff.2 (by linarith)
    have hκ0 : 0 < 1 + ε / 3 := by linarith
    have hκ2 : 1 + ε / 3 < 2 := by linarith
    have hcl0 : closedBall (0 : realLie Ψ G) ρ ⊆ closedBall 0 δ₀ :=
      closedBall_subset_closedBall (by linarith)
    constructor
    · have hr1 : 0 < ρ / (1 + ε / 3) := div_pos hρ0 hκ0
      have hr2 : ρ / (1 + ε / 3) < ρ := div_lt_self hρ0 (by linarith)
      have hr3 : (1 - ε) * ρ < ρ / (1 + ε / 3) := by
        rw [lt_div_iff₀ hκ0]; nlinarith [mul_pos hρ0 hε0, mul_pos (mul_pos hρ0 hε0) hε0]
      have H2 := (H X hXb (ρ / (1 + ε / 3)) ⟨hr1, by linarith⟩).2
      rw [mul_div_cancel₀ _ hκ0.ne'] at H2
      calc ν (closedBall X ((1 - ε) * ρ)) ≤ ν (ball X (ρ / (1 + ε / 3))) :=
            measure_mono (closedBall_subset_ball hr3)
        _ = μ (chartExp Ψ G hG '' ball X (ρ / (1 + ε / 3))) :=
            hνsub _ measurableSet_ball (hball X _ (by linarith))
        _ ≤ μ ((fun h => chartExp Ψ G hG X * h) '' (chartExp Ψ G hG '' ball 0 ρ)) := measure_mono H2
        _ = μ (chartExp Ψ G hG '' ball 0 ρ) := himg _ _
        _ ≤ μ (chartExp Ψ G hG '' closedBall 0 ρ) := measure_mono (image_mono ball_subset_closedBall)
        _ = ν (closedBall 0 ρ) := (hνsub _ measurableSet_closedBall hcl0).symm
    · have hr1 : 0 < (1 + ε / 3) * ρ := by positivity
      have hr2 : (1 + ε / 3) * ρ < δ := by nlinarith
      have H1 := (H X hXb ((1 + ε / 3) * ρ) ⟨hr1, hr2⟩).1
      have hsq : (1 + ε / 3) * ((1 + ε / 3) * ρ) ≤ (1 + ε) * ρ := by
        nlinarith [mul_pos (mul_pos hρ0 hε0) (by linarith : (0:ℝ) < 3 - ε)]
      calc ν (closedBall 0 ρ) ≤ ν (ball 0 ((1 + ε / 3) * ρ)) :=
            measure_mono (closedBall_subset_ball (by nlinarith))
        _ = μ (chartExp Ψ G hG '' ball 0 ((1 + ε / 3) * ρ)) :=
            hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; nlinarith))
        _ = μ ((fun h => chartExp Ψ G hG X * h) '' (chartExp Ψ G hG '' ball 0 ((1 + ε / 3) * ρ))) :=
            (himg _ _).symm
        _ ≤ μ (chartExp Ψ G hG '' ball X ((1 + ε / 3) * ((1 + ε / 3) * ρ))) := measure_mono H1
        _ = ν (ball X ((1 + ε / 3) * ((1 + ε / 3) * ρ))) :=
            (hνsub _ measurableSet_ball (hball X _ (by nlinarith))).symm
        _ ≤ ν (closedBall X ((1 + ε) * ρ)) :=
            measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hsq))
  obtain ⟨c, hc0, hct, hup, hdown⟩ := Formalism.BasicNotions.Examples₂.CD.exists_density lam ν hq hpos

  have hνt : ∀ ε : ℝ, 0 < ε → (lam.map Subtype.val) (tanBall Ψ r ε) = lam (ball 0 ε) := by
    intro ε hε
    rw [Measure.map_apply measurable_subtype_coe, preimage_tanBall Ψ G hε]
    rw [show tanBall Ψ r ε = ball (0 : Ψ → Fin r → Fin r → ℂ) ε by
      ext X; rw [mem_ball_zero_iff, pi_norm_lt_iff hε]; simp only [pi_norm_lt_iff hε]; rfl]
    exact measurableSet_ball
  have hc : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) < c := by
    by_contra hcon
    rw [not_lt] at hcon
    have h34 : c < ((3 / 4 : ℝ≥0) : ℝ≥0∞) :=
      lt_of_le_of_lt hcon (by rw [ENNReal.coe_lt_coe]; norm_num)
    obtain ⟨δ₁, hδ₁, H1⟩ := hup (3 / 4) h34
    obtain ⟨t, ht1, htn⟩ : ∃ t : ℝ, 1 < t ∧ t ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 := by
      have h := ((continuous_pow (Module.finrank ℝ (realLie Ψ G))).tendsto (1 : ℝ)).eventually
        (gt_mem_nhds (show (1 : ℝ) ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 by norm_num))
      have h' : ∀ᶠ x in 𝓝[>] (1 : ℝ), x ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 :=
        h.filter_mono nhdsWithin_le_nhds
      obtain ⟨t, h1, h2⟩ := (h'.and self_mem_nhdsWithin).exists
      exact ⟨t, h2, h1⟩
    have ht0 : 0 < t := by linarith
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ (grpBall (realSU Ψ G) ε) / (lam.map Subtype.val) (tanBall Ψ r ε) ≤
        ((3 / 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t ^ Module.finrank ℝ (realLie Ψ G)) := by
      filter_upwards [chart_squeeze Ψ G hG ht1,
        Ioo_mem_nhdsGT (show 0 < min δ₁ δ₀ / t by positivity)] with ε hsq hε
      obtain ⟨hε0, hε1⟩ := hε
      have hte : t * ε < min δ₁ δ₀ := by rw [mul_comm]; exact (lt_div_iff₀ ht0).1 hε1
      rw [lt_min_iff] at hte
      rw [hνt ε hε0]
      refine ENNReal.div_le_of_le_mul ?_
      calc μ (grpBall (realSU Ψ G) ε) ≤ μ (chartExp Ψ G hG '' ball 0 (t * ε)) := measure_mono hsq.2
        _ = ν (ball 0 (t * ε)) :=
            (hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; linarith))).symm
        _ ≤ ((3 / 4 : ℝ≥0) : ℝ≥0∞) * lam (ball 0 (t * ε)) := H1 _ (ball_subset_ball hte.1.le)
        _ = _ := by rw [Measure.addHaar_ball_mul_of_pos lam 0 ht0 ε, mul_assoc]
    have h1 := le_of_tendsto hD hev
    have h2 : ((3 / 4 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t ^ Module.finrank ℝ (realLie Ψ G)) < 1 := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_lt_one]
      push_cast
      linarith
    exact absurd h1 (not_le.2 h2)
  obtain ⟨δ₂, hδ₂, H2⟩ := hdown 2⁻¹ hc
  refine ⟨min δ₂ δ₀, lt_min hδ₂ hδ₀, fun s hs hsub => ?_⟩
  have h1 := H2 s (hsub.trans (ball_subset_ball (min_le_left _ _)))
  have h2 : ν s = μ (chartExp Ψ G hG '' s) :=
    hνsub s hs (hsub.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall))
  rw [← h2]
  have h22 : (2 : ℝ≥0∞) * ((2⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
    rw [ENNReal.coe_inv two_ne_zero]
    exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  calc lam s = 2 * (((2⁻¹ : ℝ≥0) : ℝ≥0∞) * lam s) := by rw [← mul_assoc, h22, one_mul]
    _ ≤ 2 * ν s := by gcongr

end GlobalTheory.CovTop.VolUp.LowDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieHaarLeTwoMulTangentNormalizedHaarStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → lam s ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
  first | exact @GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar | exact GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar | (intros; apply GlobalTheory.CovTop.VolUp.LowDens.lam_le_two_mul_tangentHaar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLowerBound
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.LowBall

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := _root_.GlobalTheory.CovTop.VolUp.UpBall.exists_lam Ψ G x hx

theorem exists_conj_bound (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (X : Ψ → Fin r → Fin r → ℂ), 0 ≤ t →
      (∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ ≤ t) → ‖X‖ ≤ C * t := by
  let L : (Ψ → Fin r → Fin r → ℂ) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) :=
    { toFun := fun Y τ => (mat x τ * Matrix.of (Y τ) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
      map_add' := fun Y Z => by
        funext τ
        change mat x τ * (Matrix.of (Y τ) + Matrix.of (Z τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_add, Matrix.add_mul]; rfl
      map_smul' := fun c Y => by
        funext τ
        change mat x τ * ((c : ℂ) • Matrix.of (Y τ)) * (mat x τ)⁻¹ = _
        rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  let Lc := LinearMap.toContinuousLinearMap L
  refine ⟨‖Lc‖ + 1, by positivity, fun t X ht hX => ?_⟩
  let Y : Ψ → Fin r → Fin r → ℂ := fun τ => ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
  have hLY : Lc Y = X := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) * (mat x τ)⁻¹ = Matrix.of (X τ)
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hY : ‖Y‖ ≤ t := by
    refine (pi_norm_le_iff_of_nonneg ht).2 fun τ => (pi_norm_le_iff_of_nonneg ht).2 fun a =>
      (pi_norm_le_iff_of_nonneg ht).2 fun b => hX τ a b
  calc ‖X‖ = ‖Lc Y‖ := by rw [hLY]
    _ ≤ ‖Lc‖ * ‖Y‖ := Lc.le_opNorm Y
    _ ≤ ‖Lc‖ * t := by gcongr
    _ ≤ (‖Lc‖ + 1) * t := by nlinarith

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_exp_bound (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < δ → ‖NormedSpace.exp Y - 1‖ ≤ 2 * ‖Y‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (zero_lt_one' ℝ)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero, one_mul] at this
  have this : ‖NormedSpace.exp Y - 1 - Y‖ ≤ ‖Y‖ := this
  calc ‖NormedSpace.exp Y - 1‖ = ‖Y + (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
    _ ≤ ‖Y‖ + ‖NormedSpace.exp Y - 1 - Y‖ := norm_add_le _ _
    _ ≤ 2 * ‖Y‖ := by linarith

theorem exists_exp_entry (n : Type) [Fintype n] [DecidableEq n] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ) (Y : Matrix n n ℂ), 0 < ε → ε < δ → (∀ a b, ‖Y a b‖ < ε / 2) →
      ∀ a b, ‖(NormedSpace.exp Y - 1) a b‖ < ε := by
  obtain ⟨δ, hδ, h⟩ := exists_exp_bound n
  refine ⟨δ, hδ, fun ε Y hε hεδ hY a b => ?_⟩
  have hYn : ‖Y‖ < ε / 2 := (Matrix.norm_lt_iff (by positivity)).2 hY
  calc ‖(NormedSpace.exp Y - 1) a b‖ ≤ ‖NormedSpace.exp Y - 1‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖Y‖ := h Y (by linarith)
    _ < ε := by linarith

end Exp

theorem riemHaar_frBall_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ENNReal.ofReal ((ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2) ≤
        riemHaar Ψ G x (frBall Ψ G x ε) := by
  intro E _ _ _ r Ψ G x hr hG hx
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hlow⟩ := GlobalTheory.T.lieHaar_le_two_mul_tangentNormalizedHaar E r Ψ G hG lam
  obtain ⟨C, hC, hconj⟩ := exists_conj_bound Ψ x hx
  obtain ⟨δ', hδ', hexp⟩ := exists_exp_entry (Fin r)
  refine ⟨min 2 (min δ' (δ / C)), lt_min two_pos (lt_min hδ' (div_pos hδ hC)), fun ε hε hε₀ => ?_⟩
  have hε2 : ε < 2 := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεδ' : ε < δ' := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε < δ / C := lt_of_lt_of_le hε₀ ((min_le_right _ _).trans (min_le_right _ _))
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε / 2} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := Subtype.val ⁻¹' S with hs
  have hsm : MeasurableSet s := measurable_subtype_coe hSm
  have h1 : ENNReal.ofReal ((ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ lam s := by
    have := GlobalTheory.T.riemannianLieMeasure_frameBox_ge E r Ψ G x hr hG hx (ε / 2) (by positivity) (by linarith)
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm] at this
    exact this
  have hball : s ⊆ Metric.ball 0 δ := by
    intro X hX
    rw [mem_ball_zero_iff]
    have h := hconj (ε / 2) X.1 (by positivity) fun τ a b => (hX τ a b).le
    have hCε : C * ε < δ := by rw [lt_div_iff₀ hC] at hεC; linarith
    calc ‖X‖ = ‖X.1‖ := rfl
      _ ≤ C * (ε / 2) := h
      _ < δ := by nlinarith
  have himg : GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s ⊆ frBall Ψ G x ε := by
    rintro _ ⟨X, hX, rfl⟩ τ a b
    change ‖((mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1) a b‖ < ε
    rw [← Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
    exact hexp ε _ hε hεδ' (hX τ) a b
  have h2 := hlow s hsm hball
  have h3 : tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤
      riemHaar Ψ G x (frBall Ψ G x ε) := by
    rw [hmap]; exact measure_mono himg
  have e : ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) = ε / 2 / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) := by rw [div_div]
  rw [e, ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  refine ENNReal.div_le_of_le_mul ?_
  calc _ ≤ lam s := h1
    _ ≤ 2 * tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := h2
    _ ≤ 2 * riemHaar Ψ G x (frBall Ψ G x ε) := by gcongr
    _ = riemHaar Ψ G x (frBall Ψ G x ε) * 2 := mul_comm _ _

end GlobalTheory.CovTop.VolUp.LowBall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLowerBoundStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_frameBall_lower_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ENNReal.ofReal ((ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2) ≤ riemHaar Ψ G x (frBall Ψ G x ε) := by
  first | exact @GlobalTheory.CovTop.VolUp.LowBall.riemHaar_frBall_ge | exact GlobalTheory.CovTop.VolUp.LowBall.riemHaar_frBall_ge | (intros; apply GlobalTheory.CovTop.VolUp.LowBall.riemHaar_frBall_ge <;> assumption)
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.MassUp

theorem inv_facts {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) :
    (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1 ∧ mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1 ∧
    A ρ * (mat x (σ ρ) * (permM (e ρ))ᵀ) = 1 ∧ mat x (σ ρ) * (permM (e ρ))ᵀ * A ρ = 1 := by
  have h0 := (hI ρ).2
  have h1 : (permM (e ρ))ᵀ * A ρ * mat x (σ ρ) = 1 := by rw [Matrix.mul_assoc, h0, transpose_mul_permM]
  have h2 : mat x (σ ρ) * ((permM (e ρ))ᵀ * A ρ) = 1 := mul_eq_one_comm.1 h1
  refine ⟨h1, h2, ?_, by rw [Matrix.mul_assoc, h2]⟩
  rw [← Matrix.mul_assoc, h0, permM_mul_transpose]

theorem det_ne {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (hI : IsIdent p q Ψ G x σ A e) (ρ : κ) : G.det ≠ 0 := by
  obtain ⟨-, -, h3, h4⟩ := inv_facts hI ρ
  set B := mat x (σ ρ) * (permM (e ρ))ᵀ
  have hJ := GlobalTheory.UpqTopology.jpq_sq (P := p ρ) (Q := q ρ)
  have key : (-(G.map (σ ρ).1)ᵀ) * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ) = 1 := by
    rw [← (hI ρ).1]
    calc (A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ * (B * Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ)
        = (A ρ)ᴴ * (Formalism.UG.Jpq (p ρ) (q ρ) * ((A ρ * B) * (Formalism.UG.Jpq (p ρ) (q ρ) * Bᴴ))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [h3, Matrix.one_mul, ← Matrix.mul_assoc (Formalism.UG.Jpq (p ρ) (q ρ)), hJ, Matrix.one_mul,
            ← Matrix.conjTranspose_mul, h4, Matrix.conjTranspose_one]
  have hd := Matrix.det_ne_zero_of_right_inverse key
  rw [Matrix.det_neg, Matrix.det_transpose] at hd
  have hd' : (G.map (σ ρ).1).det ≠ 0 := fun h => hd (by rw [h, mul_zero])
  intro h0
  apply hd'
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem perm_conj {ι : Type} [Fintype ι] [DecidableEq ι] {r : ℕ} (e : ι ≃ Fin r) (M : Matrix ι ι ℂ) (a b : Fin r) :
    ((permM e)ᵀ * M * permM e) a b = M (e.symm a) (e.symm b) := by
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply]

theorem preimage_frBall : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G), IsIdent p q Ψ G x σ A e → IsProj p q Ψ G σ A a₀ π → ∀ ε : ℝ, π ⁻¹' frBall Ψ G x ε = Set.univ.pi (fun ρ => {u : UpqT (p ρ) (q ρ) | ∀ a b, ‖(sMat (a₀ ρ) u - 1) a b‖ < ε}) := by
  intro E _ _ _ r κ p q Ψ G x σ A e a₀ π hI hP ε
  ext b
  simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_setOf_eq, frBall]
  have key : ∀ ρ, (mat x (σ ρ))⁻¹ * (((π b).1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x (σ ρ) - 1
      = (permM (e ρ))ᵀ * (sMat (a₀ ρ) (b ρ) - 1) * permM (e ρ) := by
    intro ρ
    obtain ⟨h1, -, -, -⟩ := inv_facts hI ρ
    have hinv : (mat x (σ ρ))⁻¹ = (permM (e ρ))ᵀ * A ρ := Matrix.inv_eq_left_inv h1
    rw [hinv, Matrix.mul_assoc (permM (e ρ))ᵀ (A ρ), hP b ρ]
    simp only [Matrix.mul_assoc, (hI ρ).2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
      transpose_mul_permM]
  constructor
  · intro h ρ i j
    have := h (σ ρ) (e ρ i) (e ρ j)
    rwa [key ρ, perm_conj, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
  · intro h τ i j
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    rw [key ρ, perm_conj]
    exact h ρ _ _
theorem exists_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), IsIdent p q Ψ G x σ A e → ∀ s : realSU Ψ G, ∃ b₀ : ∀ ρ, UpqT (p ρ) (q ρ), ∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI s
  have key : ∀ ρ, ∃ b : UpqT (p ρ) (q ρ), UpqT.mat b =
      A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * (mat x (σ ρ) * (permM (e ρ))ᵀ) := by
    intro ρ
    rw [← Set.mem_range, GlobalTheory.UpqTopology.range_mat]
    show _ = _
    set Sm := ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)
    set Bm := mat x (σ ρ) * (permM (e ρ))ᵀ
    have hmem := ((GlobalTheory.SUVol.DensOne.mem_realSU_iff Ψ G s.1).1 s.2 (σ ρ)).1
    have h2 : Smᴴ * (G.map (σ ρ).1)ᵀ * Sm = (G.map (σ ρ).1)ᵀ := by
      have := congrArg Matrix.transpose hmem
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at this
      rw [Matrix.mul_assoc]
      exact this
    calc (A ρ * Sm * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Sm * Bm)
        = Bmᴴ * (Smᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Sm) * Bm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Bmᴴ * ((A ρ)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * A ρ) * Bm := by
          rw [(hI ρ).1, Matrix.mul_neg, Matrix.neg_mul, h2]
      _ = (A ρ * Bm)ᴴ * Formalism.UG.Jpq (p ρ) (q ρ) * (A ρ * Bm) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.UG.Jpq (p ρ) (q ρ) := by
          rw [(inv_facts hI ρ).2.2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  choose b hb using key
  refine ⟨b, fun ρ => ?_⟩
  rw [hb ρ, Matrix.mul_assoc (A ρ * _), (inv_facts hI ρ).2.2.2, Matrix.mul_one]
theorem constant_bound : ∀ (f r : ℕ) (ε : ℝ), 1 ≤ f → 1 ≤ r → 0 < ε → ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ (f * r ^ 2) * ((ε / (2 * ((f : ℝ) * (r : ℝ) ^ 2))) ^ (f * (r ^ 2 - 1)) / 2) := by
  intro f r ε hf hr hε
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN : 1 ≤ f * r ^ 2 := by have := Nat.one_le_pow 2 r hr; nlinarith
  have hnN : f * (r ^ 2 - 1) ≤ f * r ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hL : ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ f =
      (200 * (r : ℝ)) ^ (f * r ^ 2) * ε ^ (f * (r ^ 2 - 1)) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (r ^ 2) f, mul_comm (r ^ 2 - 1) f]
  rw [hL, div_pow]
  generalize hN' : f * r ^ 2 = N at hN hnN
  generalize hn' : f * (r ^ 2 - 1) = n at hnN
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ hr'
  have ha1 : (1 : ℝ) ≤ 2 * ((f : ℝ) * (r : ℝ) ^ 2) := by nlinarith
  generalize ha : 2 * ((f : ℝ) * (r : ℝ) ^ 2) = a at ha1
  have ha0 : 0 < a := by linarith
  have e1 : 1000 * (f : ℝ) * (r : ℝ) ^ 3 = (5 / 2) * (200 * (r : ℝ) * a) := by rw [← ha]; ring
  have han : a ^ n ≤ a ^ N := pow_le_pow_right₀ ha1 hnN
  have hq : 0 ≤ 200 * (r : ℝ) * a := mul_nonneg (by positivity) ha0.le
  have h52 : (2 : ℝ) ≤ (5 / 2) ^ N := by
    calc (2 : ℝ) ≤ 5 / 2 := by norm_num
      _ = (5 / 2) ^ 1 := (pow_one _).symm
      _ ≤ (5 / 2) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have key : (200 * (r : ℝ)) ^ N * a ^ N * 2 ≤ (1000 * (f : ℝ) * (r : ℝ) ^ 3) ^ N := by
    rw [e1, mul_pow (5 / 2 : ℝ), ← mul_pow (200 * (r : ℝ)) a N]
    have hp : 0 ≤ (200 * (r : ℝ) * a) ^ N := pow_nonneg hq _
    nlinarith
  have hεn : 0 < ε ^ n := pow_pos hε _
  have han0 : 0 < a ^ n := pow_pos ha0 _
  have hw : 0 ≤ ε ^ n / a ^ n / 2 := by positivity
  calc (200 * (r : ℝ)) ^ N * ε ^ n = ((200 * (r : ℝ)) ^ N * a ^ n * 2) * (ε ^ n / a ^ n / 2) := by
        field_simp
    _ ≤ ((200 * (r : ℝ)) ^ N * a ^ N * 2) * (ε ^ n / a ^ n / 2) := by
        gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right key hw

theorem massUp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) [Fintype κ] (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r) (a₀ : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ)) (π : (∀ ρ, UpqT (p ρ) (q ρ)) → realSU Ψ G) (m : ∀ ρ, Measure (UpqT (p ρ) (q ρ))), 1 ≤ r → 1 ≤ Ψ.card → IsIdent p q Ψ G x σ A e → Continuous π → IsProj p q Ψ G σ A a₀ π → (∀ (s : realSU Ψ G) (b₀ : ∀ ρ, UpqT (p ρ) (q ρ)), (∀ ρ, UpqT.mat (b₀ ρ) * A ρ = A ρ * ((s.1 (σ ρ) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → ∀ b, π (b₀ * b) = s * π b) → (∀ ρ, IsMinf (m ρ)) → ∀ S : Set (realSU Ψ G), MeasurableSet S → Measure.pi m (π ⁻¹' S) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) * riemHaar Ψ G x S := by
  intro E _ _ _ r κ _ p q Ψ G x σ A e a₀ π m hr hΨ hI hπc hP hT hm S hS
  classical
  haveI : ∀ ρ, IsTopologicalGroup (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  haveI : ∀ ρ, LocallyCompactSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.1
  haveI : ∀ ρ, SecondCountableTopology (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.1
  haveI : ∀ ρ, BorelSpace (UpqT (p ρ) (q ρ)) := fun ρ => (GlobalTheory.UpqTopology.upq_lcsc _ _).2.2.2.2.1
  haveI : ∀ ρ, (m ρ).IsHaarMeasure := fun ρ => (hm ρ).1

  have hcard : Fintype.card κ = Ψ.card := by
    rw [Fintype.card_congr σ]; simp
  have hne : Nonempty κ := by
    rw [← Fintype.card_pos_iff, hcard]; omega
  obtain ⟨ρ₀⟩ := hne
  have hG : G.det ≠ 0 := det_ne hI ρ₀
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ
    obtain ⟨ρ, rfl⟩ := σ.surjective τ
    exact Matrix.det_ne_zero_of_right_inverse (inv_facts hI ρ).2.1
  have hpq : ∀ ρ, p ρ + q ρ = r := by
    intro ρ; simpa using Fintype.card_congr (e ρ)
  have hπm : Measurable π := hπc.measurable
  set μ := Measure.pi m with hμ
  set ν := μ.map π with hν

  haveI hinv : ν.IsMulLeftInvariant := by
    constructor
    intro s
    obtain ⟨b₀, hb₀⟩ := exists_lift E r κ p q Ψ G x σ A e hI s
    rw [hν, Measure.map_map (measurable_const_mul s) hπm]
    have h : (fun y => s * y) ∘ π = π ∘ (fun b => b₀ * b) := funext fun b => (hT s b₀ hb₀ b).symm
    rw [h, ← Measure.map_map hπm (measurable_const_mul b₀), map_mul_left_eq_self]

  have hopen : ∀ ε, IsOpen (frBall Ψ G x ε) := by
    intro ε
    have hc : ∀ τ a b, Continuous fun s : realSU Ψ G =>
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ := by
      intro τ a b
      have h1 : Continuous fun s : realSU Ψ G => ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) :=
        Units.continuous_val.comp ((continuous_apply τ).comp continuous_subtype_val)
      exact ((((continuous_const.matrix_mul h1).matrix_mul continuous_const).sub continuous_const).matrix_elem a b).norm
    have : frBall Ψ G x ε = ⋂ τ, ⋂ a, ⋂ b, {s : realSU Ψ G |
        ‖((mat x τ)⁻¹ * ((s.1 τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) * mat x τ - 1) a b‖ < ε} := by
      ext s; simp [frBall]
    rw [this]
    exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a =>
      isOpen_iInter_of_finite fun b => isOpen_lt (hc τ a b) continuous_const
  have h1mem : ∀ ε, 0 < ε → (1 : realSU Ψ G) ∈ frBall Ψ G x ε := by
    intro ε hε τ a b
    have : (mat x τ)⁻¹ * ((((1 : realSU Ψ G).1 τ : GL (Fin r) ℂ)) : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 1 := by
      simp [Matrix.nonsing_inv_mul _ (hx τ).isUnit]
    rw [this, sub_self]; simpa using hε
  have hplace := fun ρ => GlobalTheory.T.measure_detOneFactor_nearIdentity_le (p ρ) (q ρ) (a₀ ρ) (m ρ) (hm ρ)
  choose εp hεp hbp using hplace
  obtain ⟨εl, hεl, hbl⟩ := GlobalTheory.T.riemannianHaar_frameBall_lower_bound E r Ψ G x hr hG hx
  set δ := Finset.univ.inf' ⟨ρ₀, Finset.mem_univ _⟩ εp with hδdef
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun ρ _ => hεp ρ
  set ε := min δ εl / 2 with hεdef
  have hεm : ε < min δ εl := half_lt_self (lt_min hδ hεl)
  have hε : 0 < ε := half_pos (lt_min hδ hεl)
  have hεδ : ∀ ρ, ε < εp ρ := fun ρ =>
    lt_of_lt_of_le (lt_of_lt_of_le hεm (min_le_left _ _)) (Finset.inf'_le _ (Finset.mem_univ ρ))
  have hεl' : ε < εl := lt_of_lt_of_le hεm (min_le_right _ _)
  set U := ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) ^ Ψ.card with hU
  have hνB : ν (frBall Ψ G x ε) ≤ ENNReal.ofReal U := by
    rw [hν, Measure.map_apply hπm (hopen ε).measurableSet,
      preimage_frBall E r κ p q Ψ G x σ A e a₀ π hI hP ε, hμ, Measure.pi_pi]
    calc _ ≤ ∏ _ρ : κ, ENNReal.ofReal ((200 * (r : ℝ)) ^ (r ^ 2) * ε ^ (r ^ 2 - 1)) :=
          Finset.prod_le_prod' fun ρ _ => by
            have := hbp ρ ε hε (hεδ ρ)
            rw [hpq ρ] at this
            exact this
      _ = ENNReal.ofReal U := by
          rw [Finset.prod_const, Finset.card_univ, hcard, ← ENNReal.ofReal_pow (by positivity)]
  have hfinB : ν (frBall Ψ G x ε) < ∞ := lt_of_le_of_lt hνB ENNReal.ofReal_lt_top
  haveI : IsLocallyFiniteMeasure ν := ⟨fun g => ⟨(fun h => g⁻¹ * h) ⁻¹' frBall Ψ G x ε,
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by
      show frBall Ψ G x ε ∈ nhds (g⁻¹ * g)
      rw [inv_mul_cancel]; exact (hopen ε).mem_nhds (h1mem ε hε)),
    by rw [measure_preimage_mul]; exact hfinB⟩⟩
  haveI hH : (riemHaar Ψ G x).IsHaarMeasure :=
    (GlobalTheory.SUVol.DensOne.tangentHaar_riemLie (Ψ := Ψ) (G := G) (hG := hG) (x := x) (hx := hx)).1
  have hc := Measure.isMulLeftInvariant_eq_smul ν (riemHaar Ψ G x)
  set c := ν.haarScalarFactor (riemHaar Ψ G x) with hcdef
  have hL := hbl ε hε hεl'
  have hf : (0 : ℝ) < Ψ.card := by exact_mod_cast hΨ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  set L := (ε / (2 * ((Ψ.card : ℝ) * (r : ℝ) ^ 2))) ^ (Ψ.card * (r ^ 2 - 1)) / 2 with hLdef
  have hLpos : 0 < L := div_pos (pow_pos (div_pos hε (mul_pos two_pos (mul_pos hf (pow_pos hr' 2)))) _) two_pos
  have hcL : (c : ℝ) * L ≤ U := by
    have h1 : (c : ℝ≥0∞) * ENNReal.ofReal L ≤ ENNReal.ofReal U := by
      calc (c : ℝ≥0∞) * ENNReal.ofReal L ≤ c * riemHaar Ψ G x (frBall Ψ G x ε) := mul_le_mul_of_nonneg_left hL (zero_le)
        _ = ν (frBall Ψ G x ε) := by
          conv_rhs => rw [hc]
          rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        _ ≤ _ := hνB
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (mul_nonneg (by positivity) (pow_nonneg hε.le _)) _)).1 h1
  have hUC := constant_bound Ψ.card r ε hΨ hr hε
  have hcC : (c : ℝ) ≤ (1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2) :=
    le_of_mul_le_mul_right (hcL.trans hUC) hLpos
  rw [← Measure.map_apply hπm hS, ← hν, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcC' : (c : ℝ≥0∞) ≤ ENNReal.ofReal ((1000 * (Ψ.card : ℝ) * (r : ℝ) ^ 3) ^ (Ψ.card * r ^ 2)) := by
    rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_le_ofReal hcC
  exact mul_le_mul_of_nonneg_right hcC' (zero_le)

end GlobalTheory.CovTop.VolUp.MassUp
