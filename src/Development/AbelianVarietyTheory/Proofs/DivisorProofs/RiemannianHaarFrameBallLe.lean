module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentNormalizedHaarLeTwoMulLieHaar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentNormalizedHaarLeTwoMulLieHaar
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.UpDens

open Filter Topology Metric Set GlobalTheory.SUVol.DensOne
open scoped NNReal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem tangentHaar_le_two_mul_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤ 2 * lam s := by
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
  have hc : c < ((2 : ℝ≥0) : ℝ≥0∞) := by
    by_contra hcon
    rw [not_lt] at hcon
    have h32 : (((3 / 2 : ℝ≥0)) : ℝ≥0∞) < c :=
      lt_of_lt_of_le (by rw [ENNReal.coe_lt_coe]; norm_num) hcon
    obtain ⟨δ₁, hδ₁, H1⟩ := hdown (3 / 2) h32
    obtain ⟨t, ht1, htn⟩ : ∃ t : ℝ, 1 < t ∧ t ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 := by
      have h := ((continuous_pow (Module.finrank ℝ (realLie Ψ G))).tendsto (1 : ℝ)).eventually
        (gt_mem_nhds (show (1 : ℝ) ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 by norm_num))
      have h' : ∀ᶠ x in 𝓝[>] (1 : ℝ), x ^ Module.finrank ℝ (realLie Ψ G) < 4 / 3 :=
        h.filter_mono nhdsWithin_le_nhds
      obtain ⟨t, h1, h2⟩ := (h'.and self_mem_nhdsWithin).exists
      exact ⟨t, h2, h1⟩
    have ht0 : 0 < t := by linarith
    have hti0 : 0 < t⁻¹ := inv_pos.2 ht0
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((3 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t⁻¹ ^ Module.finrank ℝ (realLie Ψ G)) ≤
        μ (grpBall (realSU Ψ G) ε) / (lam.map Subtype.val) (tanBall Ψ r ε) := by
      filter_upwards [chart_squeeze Ψ G hG ht1,
        Ioo_mem_nhdsGT (show 0 < min δ₁ δ₀ * t by positivity)] with ε hsq hε
      obtain ⟨hε0, hε1⟩ := hε
      have hte : t⁻¹ * ε < min δ₁ δ₀ := by
        rw [inv_mul_lt_iff₀ ht0, mul_comm]; exact hε1
      rw [lt_min_iff] at hte
      rw [hνt ε hε0]
      rw [ENNReal.le_div_iff_mul_le (Or.inl (measure_ball_pos lam 0 hε0).ne')
        (Or.inl measure_ball_lt_top.ne)]
      calc ((3 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t⁻¹ ^ Module.finrank ℝ (realLie Ψ G)) * lam (ball 0 ε)
          = ((3 / 2 : ℝ≥0) : ℝ≥0∞) * lam (ball 0 (t⁻¹ * ε)) := by
            rw [Measure.addHaar_ball_mul_of_pos lam 0 hti0 ε, mul_assoc]
        _ ≤ ν (ball 0 (t⁻¹ * ε)) := H1 _ (ball_subset_ball hte.1.le)
        _ = μ (chartExp Ψ G hG '' ball 0 (t⁻¹ * ε)) :=
            hνsub _ measurableSet_ball (hball 0 _ (by rw [norm_zero]; linarith))
        _ ≤ μ (grpBall (realSU Ψ G) ε) := measure_mono hsq.1
    have h1 := ge_of_tendsto hD hev
    have h2 : 1 < ((3 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (t⁻¹ ^ Module.finrank ℝ (realLie Ψ G)) := by
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
        ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      have hp : 0 < t ^ Module.finrank ℝ (realLie Ψ G) := by positivity
      rw [inv_pow]
      push_cast
      rw [← div_eq_mul_inv, lt_div_iff₀ hp]
      linarith
    exact absurd h1 (not_le.2 h2)
  obtain ⟨δ₂, hδ₂, H2⟩ := hup 2 hc
  refine ⟨min δ₂ δ₀, lt_min hδ₂ hδ₀, fun s hs hsub => ?_⟩
  have h1 := H2 s (hsub.trans (ball_subset_ball (min_le_left _ _)))
  have h2 : ν s = μ (chartExp Ψ G hG '' s) :=
    hνsub s hs (hsub.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall))
  rw [← h2]
  calc ν s ≤ ((2 : ℝ≥0) : ℝ≥0∞) * lam s := h1
    _ = 2 * lam s := by norm_num

end GlobalTheory.CovTop.VolUp.UpDens
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentNormalizedHaarLeTwoMulLieHaarStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentNormalizedHaar_le_two_mul_lieHaar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (lam : Measure (realLie Ψ G)) [lam.IsAddHaarMeasure], ∃ δ : ℝ, 0 < δ ∧ ∀ s : Set (realLie Ψ G), MeasurableSet s → s ⊆ Metric.ball 0 δ → tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) ≤ 2 * lam s := by
  first | exact @GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam | exact GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam | (intros; apply GlobalTheory.CovTop.VolUp.UpDens.tangentHaar_le_two_mul_lam <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarLeOneOfDimZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarLeOneOfDimZero
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SUVol.Degenerate

theorem realSU_subsingleton {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (h : Ψ.card = 0 ∨ r = 1) :
    Subsingleton (realSU Ψ G) := by
  refine ⟨fun g g' => ?_⟩
  have key : ∀ g : realSU Ψ G, g = 1 := by
    intro g
    apply Subtype.ext
    funext τ
    rcases h with h | h
    · exact absurd (Finset.card_pos.2 ⟨τ.1, τ.2⟩) (by omega)
    · subst h
      apply Units.ext
      have hd := (g.2 τ).1
      rw [Matrix.det_unique] at hd
      ext a b
      rw [Subsingleton.elim a default, Subsingleton.elim b default]
      simpa using hd
  rw [key g, key g']

theorem realLie_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (h : Ψ.card = 0 ∨ r = 1)
    (X : Ψ → Fin r → Fin r → ℂ) (hX : X ∈ realLie Ψ G) : X = 0 := by
  funext τ
  rcases h with h | h
  · exact absurd (Finset.card_pos.2 ⟨τ.1, τ.2⟩) (by omega)
  · subst h
    have ht := (hX τ).1
    rw [Matrix.trace_fin_one] at ht
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simpa using ht

theorem fromFrame_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (hdet : ∀ τ, (mat x τ).det ≠ 0)
    (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (hY : fromFrame x Y = 0) : Y = 0 := by
  ext ⟨τ, a, b⟩
  have h1 := congrFun hY τ
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (hdet τ)
  have h2 : Matrix.of (fun a b => Y (τ, a, b)) = 0 := by
    have e : (mat x τ)⁻¹ * (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹) * mat x τ =
        Matrix.of (fun a b => Y (τ, a, b)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    rw [← e]
    have h1' : (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = 0 := h1
    rw [h1', Matrix.mul_zero, Matrix.zero_mul]
  have := congrFun (congrFun h2 a) b
  simpa using this

end GlobalTheory.SUVol.Degenerate


open GlobalTheory.SUVol.Degenerate in
theorem GlobalTheory.SUVol.Degenerate.riemHaar_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → (∀ τ, (mat x τ).det ≠ 0) → Ψ.card * (r ^ 2 - 1) = 0 → ∀ S : Set (realSU Ψ G), riemHaar Ψ G x S ≤ 1 := by
  intro E _ _ _ r Ψ G x hr hdet hc S
  have h : Ψ.card = 0 ∨ r = 1 := by
    rcases Nat.mul_eq_zero.1 hc with h | h
    · exact Or.inl h
    · right
      have : r ^ 2 ≤ 1 := by omega
      nlinarith
  haveI := realSU_subsingleton Ψ G h
  haveI : CompactSpace (realSU Ψ G) := Finite.compactSpace
  set K := (realLie Ψ G).comap (fromFrame x) with hK
  haveI hKs : Subsingleton K := by
    refine ⟨fun Y Y' => ?_⟩
    have hz : ∀ Y : K, Y = 0 := fun Y => by
      apply Subtype.ext
      exact fromFrame_eq_zero x hdet Y.1 (realLie_eq_zero Ψ G h _ Y.2)
    rw [hz Y, hz Y']

  have hν : ∀ s, riemLie Ψ G x s ≤ 1 := by
    intro s
    set b := (stdOrthonormalBasis ℝ K).toBasis
    have hb : b.addHaar Set.univ = 1 := by
      rw [← Set.Nonempty.eq_univ (b.parallelepiped).nonempty]
      exact b.addHaar_self
    calc riemLie Ψ G x s ≤ riemLie Ψ G x Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := by
        unfold riemLie
        by_cases hm : AEMeasurable (fun Y : K => fromFrame x Y.1) b.addHaar
        · rw [Measure.map_apply_of_aemeasurable hm MeasurableSet.univ, Set.preimage_univ, hb]
        · have hne : b.addHaar ≠ 0 := by
            intro he
            simp [he] at hb
          rw [Measure.map_of_not_aemeasurable_of_ne_zero hm hne]
          simp
  set μ := (Measure.haar : Measure (realSU Ψ G))
  have hu0 : μ Set.univ ≠ 0 := (isOpen_univ.measure_ne_zero μ Set.univ_nonempty)
  have hut : μ Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  have hball : ∀ ε : ℝ, 0 < ε → grpBall (realSU Ψ G) ε = Set.univ := by
    intro ε hε
    ext g
    simp only [Set.mem_univ, iff_true]
    rw [Subsingleton.elim g 1]
    intro τ a b
    simpa using hε
  have hlim : Filter.limsup (fun ε : ℝ => riemLie Ψ G x (tanBall Ψ r ε) / μ (grpBall (realSU Ψ G) ε))
      (nhdsWithin 0 (Set.Ioi 0)) ≤ 1 / μ Set.univ := by
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hball ε hε]
    exact ENNReal.div_le_div_right (hν _) _
  show riemHaar Ψ G x S ≤ 1
  unfold riemHaar tangentHaar
  rw [Measure.smul_apply, smul_eq_mul]
  calc _ ≤ (1 / μ Set.univ) * μ Set.univ :=
        mul_le_mul' hlim (measure_mono (Set.subset_univ S))
    _ = 1 := ENNReal.div_mul_cancel hu0 hut
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarLeOneOfDimZeroStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_le_one_of_dim_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → (∀ τ, (mat x τ).det ≠ 0) → Ψ.card * (r ^ 2 - 1) = 0 → ∀ S : Set (realSU Ψ G), riemHaar Ψ G x S ≤ 1 := by
  first | exact @GlobalTheory.SUVol.Degenerate.riemHaar_le_one | exact GlobalTheory.SUVol.Degenerate.riemHaar_le_one | (intros; apply GlobalTheory.SUVol.Degenerate.riemHaar_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameBallSubsetExpChartImageFrameBox
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameBallSubsetExpChartImageFrameBox
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.BallCover

section Exp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exists_exp_lower (n : Type) [Fintype n] [DecidableEq n] :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ Y : Matrix n n ℂ, ‖Y‖ < ρ → ‖Y‖ ≤ 2 * ‖NormedSpace.exp Y - 1‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1
    (GlobalTheory.CompactDualExists.exp_strict (n := n)).hasFDerivAt).def (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun Y hY => ?_⟩
  have := hh (y := Y) (by rwa [dist_zero_right])
  simp only [zero_add, NormedSpace.exp_zero] at this
  have h1 : ‖NormedSpace.exp Y - 1 - Y‖ ≤ 1 / 2 * ‖Y‖ := this
  have h2 : ‖Y‖ ≤ ‖NormedSpace.exp Y - 1‖ + ‖NormedSpace.exp Y - 1 - Y‖ := by
    calc ‖Y‖ = ‖(NormedSpace.exp Y - 1) - (NormedSpace.exp Y - 1 - Y)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  linarith

end Exp

section Main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem frBall_subset_chartExp_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (hG : G.det ≠ 0), (∀ τ, (mat x τ).det ≠ 0) → ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → frBall Ψ G x ε ⊆ GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} := by
  intro E _ _ _ r Ψ G x hG hx δ hδ
  obtain ⟨ρ, hρ, hexp⟩ := exists_exp_lower (Fin r)
  let cj : (Ψ → Fin r → Fin r → ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    fun X τ => (mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ
  have hcj : Continuous cj :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const
  let U : Set (realLie Ψ G) := {X | ‖X‖ < δ ∧ ∀ τ, ‖cj X.1 τ‖ < ρ}
  have hU : U ∈ nhds 0 := by
    refine IsOpen.mem_nhds ?_ ?_
    · change IsOpen ({X : realLie Ψ G | ‖X‖ < δ} ∩
        {X : realLie Ψ G | ∀ τ, ‖cj X.1 τ‖ < ρ})
      refine (isOpen_lt continuous_norm continuous_const).inter ?_
      change IsOpen {X : realLie Ψ G | ∀ τ, ‖cj X.1 τ‖ < ρ}
      rw [Set.setOf_forall]
      exact isOpen_iInter_of_finite fun τ =>
        isOpen_lt ((continuous_apply τ).comp (hcj.comp continuous_subtype_val)).norm continuous_const
    · refine ⟨by simpa using hδ, fun τ => ?_⟩
      have e : cj (0 : realLie Ψ G).1 τ = 0 := by
        change (mat x τ)⁻¹ * (0 : Matrix (Fin r) (Fin r) ℂ) * mat x τ = 0
        simp
      rw [e, norm_zero]; exact hρ
  have hev := GlobalTheory.SUVol.DensOne.eventually_mem_image Ψ G hG hU
  rw [Filter.eventually_comap] at hev
  obtain ⟨η, hη, hh⟩ := Metric.eventually_nhds_iff.1 hev
  let bk : (Ψ → Matrix (Fin r) (Fin r) ℂ) → (Ψ → Matrix (Fin r) (Fin r) ℂ) :=
    fun A τ => mat x τ * A τ * (mat x τ)⁻¹
  have hbk : Continuous bk :=
    continuous_pi fun τ => (continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const
  have hbk0 : bk 0 = 0 := by funext τ; simp [bk]
  obtain ⟨ε₁, hε₁, hbkε⟩ := Metric.continuous_iff.1 hbk 0 η hη
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ g hg => ?_⟩
  let A : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => (mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1
  have hA : ‖A‖ < ε := (pi_norm_lt_iff hε).2 fun τ => (Matrix.norm_lt_iff hε).2 fun a b => hg τ a b
  have hbkA : bk A = GlobalTheory.SUVol.DensOne.matR Ψ G g - 1 := by
    funext τ
    change mat x τ * ((mat x τ)⁻¹ * GlobalTheory.SUVol.DensOne.matR Ψ G g τ * mat x τ - 1) * (mat x τ)⁻¹ =
      GlobalTheory.SUVol.DensOne.matR Ψ G g τ - 1
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hx τ).isUnit,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hdist : dist (GlobalTheory.SUVol.DensOne.matR Ψ G g) 1 < η := by
    have := hbkε A (by rw [dist_zero_right]; linarith)
    rw [hbk0, dist_zero_right, hbkA] at this
    rwa [dist_eq_norm]
  obtain ⟨X, ⟨hXδ, hXρ⟩, rfl⟩ := hh hdist g rfl
  refine ⟨X, ⟨hXδ, fun τ a b => ?_⟩, rfl⟩
  have hY := hexp (cj X.1 τ) (hXρ τ)
  have he : NormedSpace.exp (cj X.1 τ) - 1 = A τ := by
    change NormedSpace.exp ((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) - 1 =
      (mat x τ)⁻¹ * NormedSpace.exp (Matrix.of (X.1 τ)) * mat x τ - 1
    rw [Matrix.exp_conj' _ _ ((Matrix.isUnit_iff_isUnit_det _).2 (hx τ).isUnit)]
  have hAτ : ‖A τ‖ < ε := lt_of_le_of_lt (norm_le_pi_norm A τ) hA
  rw [he] at hY
  calc ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ = ‖cj X.1 τ a b‖ := rfl
    _ ≤ ‖cj X.1 τ‖ := Matrix.norm_entry_le_entrywise_sup_norm _
    _ ≤ 2 * ‖A τ‖ := hY
    _ < 2 * ε := by linarith

end Main

end GlobalTheory.CovTop.VolUp.BallCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameBallSubsetExpChartImageFrameBoxStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameBall_subset_expChart_image_frameBox : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (hG : G.det ≠ 0), (∀ τ, (mat x τ).det ≠ 0) → ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → frBall Ψ G x ε ⊆ GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} := by
  first | exact @GlobalTheory.CovTop.VolUp.BallCover.frBall_subset_chartExp_image | exact GlobalTheory.CovTop.VolUp.BallCover.frBall_subset_chartExp_image | (intros; apply GlobalTheory.CovTop.VolUp.BallCover.frBall_subset_chartExp_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLe
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovTop.VolUp.UpBall

theorem isIdent_det {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {κ : Type} {p q : κ → ℕ}
    {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {x : Frame Ψ r} {σ : κ ≃ Ψ}
    {A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ} {e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r}
    (h : IsIdent p q Ψ G x σ A e) (τ : Ψ) : (mat x τ).det ≠ 0 ∧ G.det ≠ 0 := by
  obtain ⟨h1, h2⟩ := h (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ))
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ))
  set N := Pᵀ * A (σ.symm τ)
  have hN : N * mat x τ = 1 := by rw [Matrix.mul_assoc, h2, transpose_mul_permM]
  have hN' : mat x τ * N = 1 := mul_eq_one_comm.1 hN
  refine ⟨Matrix.det_ne_zero_of_left_inverse hN, ?_⟩
  have hA : A (σ.symm τ) = P * N := by
    calc A (σ.symm τ) = A (σ.symm τ) * (mat x τ * N) := by rw [hN', Matrix.mul_one]
      _ = P * N := by rw [← Matrix.mul_assoc, h2]
  have hJ : J * J = 1 := by
    simp [J, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [P, permM, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.of_apply]
    split_ifs <;> simp
  set D := Pᵀ * J * P
  have hD : D * D = 1 := by
    calc D * D = Pᵀ * J * (P * Pᵀ) * J * P := by simp only [D, Matrix.mul_assoc]
      _ = Pᵀ * (J * J) * P := by rw [permM_mul_transpose]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hJ, Matrix.mul_one, transpose_mul_permM]
  have hDdet : D.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hD
  have hNdet : N.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse hN'
  have key : -(G.map τ.1)ᵀ = Nᴴ * D * N := by
    rw [← h1, hA, Matrix.conjTranspose_mul, hPc]
    simp only [D, Matrix.mul_assoc]
  have hdet : (-(G.map τ.1)ᵀ).det ≠ 0 := by
    rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 hNdet) hDdet) hNdet
  intro hG
  apply hdet
  rw [Matrix.det_neg, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hG, map_zero, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_lam (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hx : ∀ τ, (mat x τ).det ≠ 0) :
    ∃ lam : Measure (realLie Ψ G), lam.IsAddHaarMeasure ∧ lam.map Subtype.val = riemLie Ψ G x := by
  set W := (realLie Ψ G).comap (fromFrame x)
  let Φ : W →ₗ[ℝ] realLie Ψ G :=
    ((fromFrame x).comp W.subtype).codRestrict (realLie Ψ G) (fun v => v.2)
  have key2 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      mat x τ * ((mat x τ)⁻¹ * A * mat x τ) * (mat x τ)⁻¹ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hsurj : Function.Surjective Φ := by
    intro X
    let Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r) := WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      ((mat x p.1)⁻¹ * Matrix.of (X.1 p.1) * mat x p.1) p.2.1 p.2.2)
    have hY : fromFrame x Y = X.1 := by
      funext τ
      have e : Matrix.of (fun a b => Y (τ, a, b)) = (mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ := by
        ext a b; simp [Y]
      change (mat x τ * Matrix.of _ * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = X.1 τ
      rw [e, key2]; rfl
    exact ⟨⟨Y, show fromFrame x Y ∈ realLie Ψ G by rw [hY]; exact X.2⟩, Subtype.ext hY⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hinj : Function.Injective Φ := by
    intro Y Z h
    have h' : fromFrame x Y.1 = fromFrame x Z.1 := congrArg Subtype.val h
    have hτ : ∀ τ, Matrix.of (fun a b => Y.1 (τ, a, b)) = Matrix.of (fun a b => Z.1 (τ, a, b)) := by
      intro τ
      have h1 : mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ =
          mat x τ * Matrix.of (fun a b => Z.1 (τ, a, b)) * (mat x τ)⁻¹ := congrFun h' τ
      rw [← key1 τ (Matrix.of (fun a b => Y.1 (τ, a, b))), h1, key1]
    refine Subtype.ext (PiLp.ext fun p => ?_)
    obtain ⟨τ, a, b⟩ := p
    exact congrFun (congrFun (hτ τ) a) b
  let φ : W ≃L[ℝ] realLie Ψ G := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  refine ⟨(stdOrthonormalBasis ℝ W).toBasis.addHaar.map φ, φ.isAddHaarMeasure_map _, ?_⟩
  rw [Measure.map_map measurable_subtype_coe φ.continuous.measurable]
  rfl

theorem riemHaar_frBall_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → riemHaar Ψ G x (frBall Ψ G x ε) ≤ ENNReal.ofReal ((8 * ε) ^ (Ψ.card * (r ^ 2 - 1))) := by
  intro E _ _ _ r κ p q Ψ G x σ A e hr hI
  have hx : ∀ τ, (mat x τ).det ≠ 0 := fun τ => (isIdent_det hI τ).1
  by_cases hd : Ψ.card * (r ^ 2 - 1) = 0
  · refine ⟨1, one_pos, fun ε _ _ => ?_⟩
    rw [hd, pow_zero, ENNReal.ofReal_one]
    exact GlobalTheory.T.riemannianHaar_le_one_of_dim_zero E r Ψ G x hr hx hd _
  have hΨ : 0 < Ψ.card := Nat.pos_of_ne_zero fun h => hd (by rw [h, zero_mul])
  obtain ⟨τ₀, hτ₀⟩ := Finset.card_pos.1 hΨ
  have hG : G.det ≠ 0 := (isIdent_det hI ⟨τ₀, hτ₀⟩).2
  have hr2 : 3 ≤ r ^ 2 - 1 := by
    have : r ≠ 1 := fun h => hd (by rw [h]; simp)
    have : 2 ≤ r := by omega
    have : 4 ≤ r ^ 2 := by nlinarith
    omega
  have hd3 : 3 ≤ Ψ.card * (r ^ 2 - 1) := le_trans hr2 (Nat.le_mul_of_pos_left _ hΨ)
  obtain ⟨lam, hlam, hmap⟩ := exists_lam Ψ G x hx
  obtain ⟨δ, hδ, hup⟩ := GlobalTheory.T.tangentNormalizedHaar_le_two_mul_lieHaar E r Ψ G hG lam
  obtain ⟨ε₀, hε₀, hcov⟩ := GlobalTheory.T.frameBall_subset_expChart_image_frameBox E r Ψ G x hG hx δ hδ
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  set S : Set (Ψ → Fin r → Fin r → ℂ) :=
    {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < 2 * ε} with hS
  have hcont : ∀ τ a b, Continuous (fun X : Ψ → Fin r → Fin r → ℂ =>
      ((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b) := by
    intro τ a b
    exact ((continuous_const.matrix_mul (continuous_apply τ)).matrix_mul continuous_const).matrix_elem a b
  have hSm : MeasurableSet S := by
    simp only [hS, Set.setOf_forall]
    exact MeasurableSet.iInter fun τ => MeasurableSet.iInter fun a => MeasurableSet.iInter fun b =>
      measurableSet_lt (hcont τ a b).norm.measurable measurable_const
  set s : Set (realLie Ψ G) := {X : realLie Ψ G | ‖X‖ < δ ∧ ∀ τ a b,
    ‖((mat x τ)⁻¹ * Matrix.of (X.1 τ) * mat x τ) a b‖ < 2 * ε} with hs
  have hs' : s = Metric.ball 0 δ ∩ Subtype.val ⁻¹' S := by
    ext X; simp [hs, hS, mem_ball_zero_iff]
  have hsm : MeasurableSet s := by
    rw [hs']; exact measurableSet_ball.inter (measurable_subtype_coe hSm)
  have hsb : s ⊆ Metric.ball 0 δ := by rw [hs']; exact Set.inter_subset_left
  have h1 : riemHaar Ψ G x (frBall Ψ G x ε) ≤ 2 * lam s := by
    calc riemHaar Ψ G x (frBall Ψ G x ε)
        ≤ tangentHaar (realSU Ψ G) (lam.map Subtype.val) (GlobalTheory.SUVol.DensOne.chartExp Ψ G hG '' s) := by
          unfold riemHaar; rw [← hmap]; exact measure_mono (hcov ε hε hεε)
      _ ≤ 2 * lam s := hup s hsm hsb
  have h2 : lam s ≤ riemLie Ψ G x S := by
    rw [← hmap, Measure.map_apply measurable_subtype_coe hSm, hs']
    exact measure_mono Set.inter_subset_right
  have h3 := GlobalTheory.T.riemannianLieMeasure_frameBox_le E r κ p q Ψ G x σ A e hr hI (2 * ε) (by positivity)
  have h4 : 2 * lam s ≤ 2 * ENNReal.ofReal ((3 * (2 * ε)) ^ (Ψ.card * (r ^ 2 - 1))) := by
    gcongr; exact h2.trans h3
  refine h1.trans (h4.trans ?_)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  set d := Ψ.card * (r ^ 2 - 1)
  have e1 : (8 * ε) ^ d = (4 / 3 : ℝ) ^ d * (3 * (2 * ε)) ^ d := by rw [← mul_pow]; ring_nf
  have e2 : (2 : ℝ) ≤ (4 / 3 : ℝ) ^ d := by
    calc (2 : ℝ) ≤ (4 / 3) ^ 3 := by norm_num
      _ ≤ (4 / 3) ^ d := pow_le_pow_right₀ (by norm_num) hd3
  rw [e1]
  exact mul_le_mul_of_nonneg_right e2 (by positivity)

end GlobalTheory.CovTop.VolUp.UpBall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarFrameBallLeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianHaar_frameBall_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → riemHaar Ψ G x (frBall Ψ G x ε) ≤ ENNReal.ofReal ((8 * ε) ^ (Ψ.card * (r ^ 2 - 1))) := by
  first | exact @GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le | exact GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le | (intros; apply GlobalTheory.CovTop.VolUp.UpBall.riemHaar_frBall_le <;> assumption)
end
