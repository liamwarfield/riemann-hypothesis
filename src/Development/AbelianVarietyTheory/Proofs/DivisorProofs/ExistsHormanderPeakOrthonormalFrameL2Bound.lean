module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakCutoffSingularWeightsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicDecreasingLimitExtensionStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlurisubharmonicDecreasingLimitExtension
open ReciprocityTheory.L2DbarEstimates MeasureTheory Metric Set Filter
open scoped ENNReal ContDiff Topology

namespace GlobalTheory.HormanderLimit

theorem exists_tendstoLocallyUniformlyOn_ultrafilter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {U : Set E} {F : ℕ → E → ℂ} (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ c ∈ U, ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ k, ∀ z ∈ ball c r, ‖F k z‖ ≤ M)
    (𝒰 : Ultrafilter ℕ) : ∃ f : E → ℂ, TendstoLocallyUniformlyOn F f (𝒰 : Filter ℕ) U := by
  have hpt : ∀ c, ∃ a : ℂ, c ∈ U → Tendsto (fun k => F k c) (𝒰 : Filter ℕ) (𝓝 a) := by
    intro c
    by_cases hc : c ∈ U
    · obtain ⟨r, hr, M, -, hM⟩ := hb c hc
      obtain ⟨a, -, ha⟩ := (isCompact_closedBall (0 : ℂ) M).ultrafilter_le_nhds
        (𝒰.map fun k => F k c) (by
          rw [le_principal_iff, Ultrafilter.coe_map, mem_map]
          exact Eventually.of_forall fun k => by
            simpa using hM k c (mem_ball_self hr))
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose f hf using hpt
  refine ⟨f, Metric.tendstoLocallyUniformlyOn_iff.2 fun ε hε c hc => ?_⟩
  obtain ⟨r, hr, M, hrU, hM⟩ := hb c hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 c (mem_ball_self hr))
  set L : ℝ := (2 * M + 1) / r with hL
  have hL0 : 0 < L := by positivity
  have hlip : ∀ k, ∀ z ∈ ball c r, dist (F k z) (F k c) ≤ L * dist z c := by
    intro k z hz
    refine Complex.dist_le_div_mul_dist_of_mapsTo_ball ((hF k).mono hrU) (fun w hw => ?_) hz
    have := norm_sub_le (F k w) (F k c)
    have h2 : dist (F k w) (F k c) < 2 * M + 1 := by
      rw [dist_eq_norm]
      linarith [hM k w hw, hM k c (mem_ball_self hr)]
    first
      | exact mem_ball.2 h2
      | exact mem_closedBall.2 h2.le
  have hlipf : ∀ z ∈ ball c r, dist (f z) (f c) ≤ L * dist z c := fun z hz =>
    le_of_tendsto ((hf z (hrU hz)).dist (hf c hc)) (Eventually.of_forall fun k => hlip k z hz)
  refine ⟨ball c (min r (ε / (3 * L))), nhdsWithin_le_nhds (ball_mem_nhds c (by positivity)), ?_⟩
  filter_upwards [(Metric.tendsto_nhds.1 (hf c hc)) (ε / 3) (by positivity)] with k hk y hy
  have hy1 : y ∈ ball c r := ball_subset_ball (min_le_left _ _) hy
  have hy2 : dist y c < ε / (3 * L) := (mem_ball.1 hy).trans_le (min_le_right _ _)
  have hy3 : L * dist y c < ε / 3 := by
    rw [lt_div_iff₀ (by positivity)] at hy2
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have h1 := hlipf y hy1
  have h2 := hlip k y hy1
  have h3 := dist_triangle4 (f y) (f c) (F k c) (F k y)
  rw [dist_comm (F k y)] at h2
  rw [dist_comm] at hk
  linarith

theorem enorm_sq_le_lintegral {n : ℕ} {g : V n → ℂ} {c : V n} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball c r)) :
    ‖g c‖ₑ ^ 2 ≤ (volume (closedBall (0 : V n) r))⁻¹ * ∫⁻ z in closedBall c r, ‖g z‖ₑ ^ 2 := by
  have hd : DifferentiableOn ℂ (fun z => g (c + z)) (ball 0 r) :=
    hg.comp (by fun_prop) fun z hz => by simpa [mem_ball_iff_norm] using hz
  obtain ⟨-, h1, -⟩ := GlobalTheory.submean_sq_closedBall hr hd
  have h2 := (measurePreserving_add_left (volume : Measure (V n)) c).setLIntegral_comp_preimage_emb
    (MeasurableEquiv.addLeft c).measurableEmbedding (fun z => ‖g z‖ₑ ^ 2) (closedBall c r)
  have h3 : (fun z => c + z) ⁻¹' closedBall c r = closedBall 0 r := by
    ext z
    simp [mem_closedBall_iff_norm]
  rw [h3] at h2
  rw [← h2]
  simpa using h1

theorem locally_bounded_of_lintegral {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {F : ℕ → V n → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z in K, ‖F k z‖ₑ ^ 2 ≤ C) :
    ∀ c ∈ U, ∃ r > 0, ∃ M : ℝ, ball c r ⊆ U ∧ ∀ k, ∀ z ∈ ball c r, ‖F k z‖ ≤ M := by
  intro c hc
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU c hc
  set r := R / 4 with hr
  have hr0 : 0 < r := by positivity
  have hK : closedBall c (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  obtain ⟨C, hC, hCk⟩ := hb _ hK (isCompact_closedBall _ _)
  set B : ℝ≥0∞ := (volume (closedBall (0 : V n) r))⁻¹ * C with hB
  have hBt : B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 (measure_closedBall_pos _ _ hr0).ne') hC
  refine ⟨r, hr0, Real.sqrt B.toReal, (ball_subset_ball (by linarith)).trans hRU,
    fun k z hz => ?_⟩
  have hsub : closedBall z r ⊆ closedBall c (2 * r) :=
    closedBall_subset_closedBall' (by linarith [mem_ball.1 hz])
  have h1 := enorm_sq_le_lintegral hr0
    ((hF k).mono (ball_subset_closedBall.trans (hsub.trans hK)))
  have h2 : ‖F k z‖ₑ ^ 2 ≤ B :=
    h1.trans (by
      rw [hB]
      gcongr
      exact (lintegral_mono_set hsub).trans (hCk k))
  refine Real.le_sqrt_of_sq_le ?_
  have h3 := ENNReal.toReal_mono hBt h2
  simpa using h3

theorem exists_limit {n : ℕ} {U : Set (V n)} (hU : IsOpen U) (K : ℕ → Set (V n))
    (hKc : ∀ j, IsCompact (K j)) (hKU : ∀ j, K j ⊆ U) (hK : ∀ y ∈ U, ∀ᶠ j in atTop, y ∈ K j)
    {φ : ℕ → V n → ℝ} (hφ : ∀ k, ContinuousOn (φ k) U) (hdec : ∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y)
    {F0 : V n → ℂ} (hF0 : ContinuousOn F0 U) {A : ℝ≥0∞} (hA : A ≠ ⊤) {F : ℕ → V n → ℂ}
    (hF : ∀ k, DifferentiableOn ℂ (F k) U)
    (hest : ∀ k, ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F k y‖ ^ 2 * Real.exp (-φ k y)) ≤ A) :
    ∃ f : V n → ℂ, DifferentiableOn ℂ f U ∧
      ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  have hanti : ∀ y ∈ U, Antitone fun k => φ k y := fun y hy =>
    antitone_nat_of_succ_le fun k => hdec k y hy
  have hloc : ∀ S ⊆ U, IsCompact S → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k, ∫⁻ z in S, ‖F k z‖ₑ ^ 2 ≤ C := by
    intro S hSU hS
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn ((hφ 0).mono hSU)
    obtain ⟨N, hN⟩ := hS.exists_bound_of_continuousOn (hF0.mono hSU)
    refine ⟨ENNReal.ofReal (2 * N ^ 2) * volume S + ENNReal.ofReal (2 * Real.exp M) * A,
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA⟩, fun k => ?_⟩
    calc ∫⁻ z in S, ‖F k z‖ₑ ^ 2
        ≤ ∫⁻ z in S, (ENNReal.ofReal (2 * N ^ 2) + ENNReal.ofReal (2 * Real.exp M) *
            ENNReal.ofReal (‖F0 z - F k z‖ ^ 2 * Real.exp (-φ k z))) := by
          refine setLIntegral_mono' hS.measurableSet fun z hz => ?_
          rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : φ k z ≤ M :=
            (hanti z (hSU hz) (Nat.zero_le k)).trans ((le_abs_self _).trans (hM z hz))
          have h2 : 1 ≤ Real.exp M * Real.exp (-φ k z) := by
            rw [← Real.exp_add]
            exact Real.one_le_exp (by linarith)
          have h3 : ‖F k z‖ ≤ N + ‖F0 z - F k z‖ := by
            have := norm_sub_le (F0 z) (F0 z - F k z)
            rw [sub_sub_cancel] at this
            linarith [hN z hz]
          have h4 : ‖F k z‖ ^ 2 ≤ (N + ‖F0 z - F k z‖) ^ 2 := by gcongr
          have h5 : ‖F0 z - F k z‖ ^ 2 * 1 ≤
              ‖F0 z - F k z‖ ^ 2 * (Real.exp M * Real.exp (-φ k z)) := by gcongr
          nlinarith [sq_nonneg (N - ‖F0 z - F k z‖)]
      _ ≤ _ := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          exact (lintegral_mono_set hSU).trans (hest k)
  obtain ⟨f, hf⟩ := exists_tendstoLocallyUniformlyOn_ultrafilter hF
    (locally_bounded_of_lintegral hU hF hloc) (hyperfilter ℕ)
  have hfd : DifferentiableOn ℂ f U :=
    GlobalTheory.SCV.differentiableOn_of_tendstoLocallyUniformlyOn hU hf (Eventually.of_forall hF)
  have hsel : ∀ j : ℕ, ∃ k, j ≤ k ∧ ∀ y ∈ K j, dist (f y) (F k y) < 1 / ((j : ℝ) + 1) := by
    intro j
    have h1 := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hf (K j) (hKU j) (hKc j))
      (1 / ((j : ℝ) + 1)) (by positivity)
    have h2 : ∀ᶠ k in (hyperfilter ℕ : Filter ℕ), j ≤ k :=
      Nat.hyperfilter_le_atTop (eventually_ge_atTop j)
    exact (h2.and h1).exists
  choose σ hσ hσK using hsel
  have hlim : ∀ y ∈ U, Tendsto (fun j => F (σ j) y) atTop (𝓝 (f y)) := by
    intro y hy
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hK y hy] with j hj
    rw [dist_comm]
    exact (hσK j y hj).le
  have hmeas : ∀ {g : V n → ℂ}, ContinuousOn g U → ∀ m, AEMeasurable
      (fun y => ENNReal.ofReal (‖F0 y - g y‖ ^ 2 * Real.exp (-φ m y))) (volume.restrict U) := by
    intro g hg m
    exact (ContinuousOn.aemeasurable ((((hF0.sub hg).norm).pow 2).mul (hφ m).neg.rexp)
      hU.measurableSet).ennreal_ofReal
  have hm : ∀ m, ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ m y)) ≤ A := by
    intro m
    calc ∫⁻ y in U, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ m y))
        = ∫⁻ y in U, liminf (fun j =>
            ENNReal.ofReal (‖F0 y - F (σ j) y‖ ^ 2 * Real.exp (-φ m y))) atTop := by
          refine setLIntegral_congr_fun hU.measurableSet fun y hy => ?_
          refine (Tendsto.liminf_eq ?_).symm
          exact ENNReal.tendsto_ofReal
            (((tendsto_const_nhds.sub (hlim y hy)).norm.pow 2).mul_const _)
      _ ≤ liminf (fun j => ∫⁻ y in U,
            ENNReal.ofReal (‖F0 y - F (σ j) y‖ ^ 2 * Real.exp (-φ m y))) atTop :=
          lintegral_liminf_le' fun j => hmeas (hF _).continuousOn m
      _ ≤ A := by
          refine liminf_le_of_frequently_le' (Eventually.frequently ?_)
          filter_upwards [eventually_ge_atTop m] with j hj
          refine le_trans (setLIntegral_mono' hU.measurableSet fun y hy => ?_) (hest (σ j))
          refine ENNReal.ofReal_le_ofReal ?_
          have := hanti y hy (hj.trans (hσ j))
          gcongr
  refine ⟨f, hfd, ?_⟩
  have e : ∀ y, ENNReal.ofReal (‖F0 y - f y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) =
      ⨆ k, ENNReal.ofReal (‖F0 y - f y‖ ^ 2 * Real.exp (-φ k y)) := by
    intro y
    rw [ENNReal.mul_iSup]
    exact iSup_congr fun k => (ENNReal.ofReal_mul (by positivity)).symm
  simp_rw [e]
  rw [lintegral_iSup' (hmeas hfd.continuousOn)]
  · exact iSup_le hm
  · filter_upwards [ae_restrict_mem hU.measurableSet] with y hy a b hab
    refine ENNReal.ofReal_le_ofReal ?_
    have := hanti y hy hab
    gcongr

theorem hormander_limit : ∀ {n : ℕ} {U : Set (V n)}, IsOpen U → ∀ (e : V n → ℝ), ContDiffOn ℝ ∞ e U → (∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re) → (∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a}) → ∀ (φ : ℕ → V n → ℝ), (∀ k, ContDiffOn ℝ ∞ (φ k) U) → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → (∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y) → ∀ (F0 : V n → ℂ), ContDiffOn ℝ ∞ F0 U → ∀ (h : V n → ℝ≥0∞), Measurable h → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → ∀ A : ℝ≥0∞, (∀ k, ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ k y)) ≤ A) → ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧ ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  intro n U hU e he hel hec φ hφ hφl hdec F0 hF0 h hh hb A hA
  by_cases hAt : A = ⊤
  · exact ⟨0, differentiableOn_const 0, hAt ▸ le_top⟩
  choose F hF hest using fun k => ReciprocityTheory.ChartRestriction.G.AR.Up.HE.hormander_open hU e he hel hec (φ k)
    (hφ k) (hφl k) F0 hF0 h hh (hb k)
  refine exists_limit hU (fun j => {y | y ∈ U ∧ e y ≤ (j : ℝ)}) (fun j => hec j)
    (fun j y hy => hy.1) (fun y hy => ?_) (fun k => (hφ k).continuousOn) hdec hF0.continuousOn hAt
    hF fun k => (hest k).trans (hA k)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (e y)] with j hj
  exact ⟨hy, hj⟩

end GlobalTheory.HormanderLimit
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plurisubharmonic_decreasing_limit_extension : ∀ {n : ℕ} {U : Set (V n)}, IsOpen U → ∀ (e : V n → ℝ), ContDiffOn ℝ ∞ e U → (∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (e w : ℂ)) y ξ).re) → (∀ a : ℝ, IsCompact {y | y ∈ U ∧ e y ≤ a}) → ∀ (φ : ℕ → V n → ℝ), (∀ k, ContDiffOn ℝ ∞ (φ k) U) → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → (∀ k, ∀ y ∈ U, φ (k + 1) y ≤ φ k y) → ∀ (F0 : V n → ℂ), ContDiffOn ℝ ∞ F0 U → ∀ (h : V n → ℝ≥0∞), Measurable h → (∀ k, ∀ y ∈ U, ∀ ξ : Fin n → ℂ, ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤ h y * ENNReal.ofReal (leviV n (fun w => (φ k w : ℂ)) y ξ).re) → ∀ A : ℝ≥0∞, (∀ k, ∫⁻ y in U, h y * ENNReal.ofReal (Real.exp (-φ k y)) ≤ A) → ∃ F : V n → ℂ, DifferentiableOn ℂ F U ∧ ∫⁻ y in U, ENNReal.ofReal (‖F0 y - F y‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k y)) ≤ A := by
  first | exact @GlobalTheory.HormanderLimit.hormander_limit | exact GlobalTheory.HormanderLimit.hormander_limit | (intros; apply GlobalTheory.HormanderLimit.hormander_limit <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicWeightedSquareIntegrableVanishes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicWeightedSquareIntegrableVanishes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

namespace GlobalTheory

theorem holo_vanish_of_critical_integrable : ∀ {n : ℕ}, 0 < n → ∀ (u : V n → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) < ⊤ → u 0 = 0 := by
  intro n hn u ρ hρ hu hint
  by_contra hne
  have hb : Metric.ball (0 : V n) ρ ∈ nhds (0 : V n) := Metric.ball_mem_nhds 0 hρ
  set a := ‖u 0‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hne
  have hc : ContinuousAt u 0 := hu.continuousOn.continuousAt hb
  have ev1 : ∀ᶠ z in nhds (0 : V n), a / 2 < ‖u z‖ :=
    hc.norm.eventually (Ioi_mem_nhds (by show a / 2 < a; linarith))
  obtain ⟨δ0, hδ0, hall⟩ := Metric.eventually_nhds_iff.mp (ev1.and (Filter.eventually_of_mem hb fun z hz => hz))
  set δ := min δ0 ρ with hδ
  have hδpos : 0 < δ := lt_min hδ0 hρ
  have hsub : Metric.ball (0 : V n) δ ⊆ Metric.ball (0 : V n) ρ := Metric.ball_subset_ball (min_le_right _ _)
  have hpt : ∀ z ∈ Metric.ball (0 : V n) δ,
      ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ))) ≤
        ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    intro z hz
    have hz0 : dist z 0 < δ0 := by
      rw [Metric.mem_ball] at hz; exact lt_of_lt_of_le hz (min_le_left _ _)
    have h1 := (hall hz0).1
    rw [← ENNReal.ofReal_mul (by positivity), neg_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have hr : 0 ≤ ‖z‖ ^ (-(2 * (n : ℝ))) := Real.rpow_nonneg (norm_nonneg _) _
    have h2 : (a / 2) ^ 2 ≤ ‖u z‖ ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
    exact mul_le_mul_of_nonneg_right h2 hr
  have hlow : ENNReal.ofReal ((a / 2) ^ 2) * ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal ((a / 2) ^ 2) * ENNReal.ofReal (‖z‖ ^ (-2 * (n : ℝ)))
        ≤ ∫⁻ z in Metric.ball (0 : V n) δ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
      _ ≤ _ := lintegral_mono_set hsub
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.VanishPf.crit_div hn hδpos,
    ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le]; positivity)] at hlow
  exact absurd (lt_of_le_of_lt hlow hint) (lt_irrefl _)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicWeightedSquareIntegrableVanishesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_weighted_square_integrable_vanishes : ∀ {n : ℕ}, 0 < n → ∀ (u : V n → ℂ) (ρ : ℝ), 0 < ρ → DifferentiableOn ℂ u (Metric.ball 0 ρ) → ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (‖u z‖ ^ 2 * ‖z‖ ^ (-(2 * (n : ℝ)))) < ⊤ → u 0 = 0 := by
  first | exact @GlobalTheory.holo_vanish_of_critical_integrable | exact GlobalTheory.holo_vanish_of_critical_integrable | (intros; apply GlobalTheory.holo_vanish_of_critical_integrable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakExtensionVanishOtherOrbitPointsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakExtensionVanishOtherOrbitPoints
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
  Topology Filter Metric
open scoped ENNReal

noncomputable section

namespace GlobalTheory.PeakOrbit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem rank_pos (X : Data E r) (hn : 0 < nd X) : 0 < r := by
  obtain ⟨e⟩ : Nonempty (Ent X) := Fintype.card_pos_iff.1 hn
  exact Fin.pos e.2.1.1

theorem isOrth_translate (X : Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (ho : IsOrth X x) : IsOrth X (lact γ x) := fun τ => by
  rw [OntoS.gram_lact X hγ]; exact ho τ

def testFn (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (Ψ : Frame X.Ψ r → ℝ≥0∞)
    (y : Frame X.Ψ r) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (‖X.dom.piecewise P 0 y‖ ^ 2 * Real.exp (-(X.dom.piecewise (phla X la) 0 y))) * Ψ y

theorem testFn_dom (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (Ψ : Frame X.Ψ r → ℝ≥0∞)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    testFn X la P Ψ y = ENNReal.ofReal (‖P y‖ ^ 2 * Real.exp (-phla X la y)) * Ψ y := by
  classical
  simp only [testFn, Set.piecewise_eq_of_mem _ _ _ hy]

theorem testFn_meas (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} (hP : ContinuousOn P X.dom)
    {Ψ : Frame X.Ψ r → ℝ≥0∞} (hΨ : Measurable Ψ) : Measurable (testFn X la P Ψ) := by
  classical
  have hm := (IW.isOpen_dom X).measurableSet
  have h1 : Measurable (X.dom.piecewise P 0) := hP.measurable_piecewise continuousOn_const hm
  have h2 : Measurable (X.dom.piecewise (phla X la) 0) :=
    (IW.phla_contOn X la).measurable_piecewise continuousOn_const hm
  unfold testFn
  exact ((h1.norm.pow_const 2).mul (h2.neg.exp)).ennreal_ofReal.mul hΨ

theorem testFn_rmul (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : IsBEq X la P)
    {Ψ : Frame X.Ψ r → ℝ≥0∞} (hΨ : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    testFn X la P Ψ (rmul y b) = testFn X la P Ψ y := by
  rw [testFn_dom X la P Ψ (OntoS.dom_rmul X hy hb), testFn_dom X la P Ψ hy,
    IW.exp_neg_phla_rmul X GlobalTheory.NormFactor.nfacRmul_holds la hy hb, hP.2 y hy b hb, hΨ y hy b hb]
  congr 2
  have : ‖bchar la b‖ ≠ 0 := norm_ne_zero_iff.2 (IW.bchar_ne_zero X hb la)
  rw [norm_mul]
  field_simp

theorem vanish_translate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → 0 < nd X →
    ∀ (Ψ : Frame X.Ψ r → ℝ≥0∞), Measurable Ψ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y) →
    (∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψ (lact γ y) = Ψ y) → ∀ (c ρ' : ℝ), 0 < c → 0 < ρ' →
    (∀ w ∈ Metric.ball (0 : V (nd X)) ρ',
      ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ Ψ (cpt X x w)) →
    (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) →
      ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) →
    ∀ (F0 F : V (nd X) → ℂ), (∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0) →
    DifferentiableOn ℂ F (OmF X x) →
    ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) * Ψ (cpt X x z)
      ∂muF X x < ⊤ →
    ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → (∀ z ∈ OmF X x, P (cpt X x z) = F z) →
    ∀ γ ∈ X.Γ, γ ≠ 1 → P (lact γ x) = 0 := by
  intro E _ _ _ r X la x ho hn Ψ hΨm hΨB hΨΓ c ρ' hc hρ' hlow hinj F0 F hF0 _ hI P hP hPF γ hγ hγ1
  by_contra hne
  have hr : (0 : ℝ) < r := Nat.cast_pos.2 (rank_pos X hn)
  have hR : (0 : ℝ) < 1 / (100 * (r : ℝ) ^ 2) := by positivity
  set x1 := lact γ x with hx1def
  have ho1 : IsOrth X x1 := isOrth_translate X hγ ho
  have h01 := IW.zero_mem_OmF X x1 ho1
  have hO1 := (ExF.isOpen_OmF X x1).mem_nhds h01
  have hO := (ExF.isOpen_OmF X x).mem_nhds (IW.zero_mem_OmF X x ho)

  set h : V (nd X) → ℝ := fun w => Real.exp (Real.log (densF X x1 w) - phla X la (cpt X x1 w)) *
    ‖P (cpt X x1 w)‖ ^ 2 with hh
  have hcont : ContinuousAt h 0 :=
    (Real.continuous_exp.continuousAt.comp (((IW.logDens_cdAt X x1 h01).sub
      (IW.phla_cpt_cdAt X x1 h01 la)).continuousAt)).mul
      (((IW.comp_cpt_diffOn X hP.1 x1).continuousOn.continuousAt hO1).norm.pow 2)
  have hh0 : 0 < h 0 := by
    simp only [hh, IW.cpt_zero]
    exact mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.2 hne) 2)
  have hev : ∀ᶠ w in 𝓝 (0 : V (nd X)), h 0 / 2 < h w :=
    hcont.eventually (lt_mem_nhds (by linarith))
  have hall : ∀ᶠ w in 𝓝 (0 : V (nd X)), h 0 / 2 < h w ∧ w ∈ OmF X x1 ∧ w ∈ OmF X x ∧
      w ∈ ball (0 : V (nd X)) ρ' ∧ w ∈ ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) := by
    filter_upwards [hev, hO1, hO, ball_mem_nhds 0 hρ', ball_mem_nhds 0 hR] with w a b c d e
    exact ⟨a, b, c, d, e⟩
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 hall
  obtain ⟨Δ, zOf, bOf, hΔd, -, hzOf, -, hdec, hlast⟩ := lu_holds (E := E) r X x1 ho1
  have hG : IsOpen {y | y ∈ X.dom ∧ Δ y ≠ 0} :=
    hΔd.continuous.continuousOn.isOpen_inter_preimage (IW.isOpen_dom X) isOpen_compl_singleton
  have hNo : IsOpen (IW.Nset X Δ zOf ρ) := hzOf.continuousOn.isOpen_inter_preimage hG isOpen_ball
  have hN1 : ∀ w ∈ ball (0 : V (nd X)) ρ, cpt X x1 w ∈ IW.Nset X Δ zOf ρ := by
    intro w hw
    have hwO := (hsub hw).2.1
    obtain ⟨h1, h2, -⟩ := hlast w hwO (IW.idF X) (IW.idF_mem X)
    rw [IW.rmul_idF] at h1 h2
    exact ⟨⟨hwO, h1⟩, by simp only [Set.mem_preimage]; rw [h2]; exact hw⟩
  have hN2 : ∀ z, cpt X x z ∈ IW.Nset X Δ zOf ρ → z ∈ OmF X x ∧ F0 z = 0 := by
    intro z hzN
    obtain ⟨⟨hzd, hΔz⟩, hzb⟩ := hzN
    refine ⟨hzd, hF0 z (lt_of_not_ge fun hz => hγ1 ?_)⟩
    obtain ⟨-, hbO, hd⟩ := hdec _ hzd hΔz
    have e := IW.rmul_binv X (cpt X x1 (zOf (cpt X x z))) hbO
    rw [← hd, hx1def, IW.cpt_lact] at e
    have hw := (hsub hzb).2.2.2.2
    rw [mem_ball, dist_zero_right] at hw
    exact hinj γ hγ _ z hw.le hz _ (IW.binv_mem X hbO) e.symm
  have hφm : Measurable ((IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ)) :=
    (testFn_meas X la hP.1.continuousOn hΨm).indicator hNo.measurableSet
  have hφinv : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (rmul y b) =
        (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) y := by
    intro y hy b hb
    by_cases hyN : y ∈ IW.Nset X Δ zOf ρ
    · rw [Set.indicator_of_mem hyN,
        Set.indicator_of_mem ((IW.Nset_sat X x1 hdec hlast ρ hy hb).2 hyN),
        testFn_rmul X hP hΨB hy hb]
    · rw [Set.indicator_of_notMem hyN, Set.indicator_of_notMem
        (fun h => hyN ((IW.Nset_sat X x1 hdec hlast ρ hy hb).1 h))]
  have hMI := measInv_holds (E := E) r X x x1 ho ho1 _ hφm hφinv
  have hL : ∫⁻ z, (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x z) ∂muF X x < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hI
    by_cases hzN : cpt X x z ∈ IW.Nset X Δ zOf ρ
    · obtain ⟨hz, hz0⟩ := hN2 z hzN
      have hzd : cpt X x z ∈ X.dom := hz
      rw [Set.indicator_of_mem hzN, testFn_dom X la P Ψ hzd, hPF z hz, hz0, zero_sub, norm_neg]
    · rw [Set.indicator_of_notMem hzN]; exact zero_le
  have hk : 0 < h 0 / 2 * c := by positivity
  have hpt : ∀ w ∈ ball (0 : V (nd X)) ρ, ENNReal.ofReal (h 0 / 2 * c) *
      ENNReal.ofReal (‖w‖ ^ (-2 * (nd X : ℝ))) ≤
      ENNReal.ofReal (densF X x1 w) * (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x1 w) := by
    intro w hw
    obtain ⟨h1, hw1, hw0, hwρ, -⟩ := hsub hw
    have hd := IW.densF_pos X x1 hw1
    have hwd : cpt X x1 w ∈ X.dom := hw1
    have hΨw : Ψ (cpt X x1 w) = Ψ (cpt X x w) := by
      rw [hx1def, IW.cpt_lact]; exact hΨΓ γ hγ _ hw0
    have hval : h w = densF X x1 w * (‖P (cpt X x1 w)‖ ^ 2 * Real.exp (-phla X la (cpt X x1 w))) := by
      simp only [hh]
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hd]
      ring
    rw [Set.indicator_of_mem (hN1 w hw), testFn_dom X la P Ψ hwd, hΨw, ← mul_assoc,
      ← ENNReal.ofReal_mul hd.le, ← hval, ← ENNReal.ofReal_mul hk.le, mul_assoc,
      ENNReal.ofReal_mul (by positivity), neg_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h1.le) (hlow w hwρ)
  have hR1 : ENNReal.ofReal (h 0 / 2 * c) *
      ∫⁻ w in ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖w‖ ^ (-2 * (nd X : ℝ))) ≤
      ∫⁻ w, (IW.Nset X Δ zOf ρ).indicator (testFn X la P Ψ) (cpt X x1 w) ∂muF X x1 := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, IW.muF_lintegral]
    exact (setLIntegral_mono' measurableSet_ball hpt).trans
      (lintegral_mono_set fun w hw => (hsub hw).2.1)
  rw [VanishPf.crit_div hn hρ, ENNReal.mul_top (ENNReal.ofReal_pos.2 hk).ne', ← hMI] at hR1
  exact absurd (hR1.trans_lt hL) (lt_irrefl _)

end GlobalTheory.PeakOrbit

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peakExtension_vanish_other_orbit_points : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), IsOrth X x → 0 < nd X → ∀ (Ψ : Frame X.Ψ r → ℝ≥0∞), Measurable Ψ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψ (rmul y b) = Ψ y) → (∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψ (lact γ y) = Ψ y) → ∀ (c ρ' : ℝ), 0 < c → 0 < ρ' → (∀ w ∈ Metric.ball (0 : V (nd X)) ρ', ENNReal.ofReal (c * ‖w‖ ^ (-(2 * (nd X : ℝ)))) ≤ Ψ (cpt X x w)) → (∀ γ ∈ X.Γ, ∀ z z' : V (nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (cpt X x z) = rmul (cpt X x z') b → γ = 1) → ∀ (F0 F : V (nd X) → ℂ), (∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0) → DifferentiableOn ℂ F (OmF X x) → ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) * Ψ (cpt X x z) ∂muF X x < ⊤ → ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → (∀ z ∈ OmF X x, P (cpt X x z) = F z) → ∀ γ ∈ X.Γ, γ ≠ 1 → P (lact γ x) = 0 := by
  first | exact @GlobalTheory.PeakOrbit.vanish_translate | exact GlobalTheory.PeakOrbit.vanish_translate | (intros; apply GlobalTheory.PeakOrbit.vanish_translate <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakOrthonormalFrameL2Bound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
open scoped ContDiff

namespace GlobalTheory.HormanderPeak

open scoped ENNReal

theorem hormander_peak : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∃ (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) ∧ ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 ∧ (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) ∧ P0 x = 1 ∧ (∀ γ ∈ X.Γ, γ ≠ 1 → P0 (lact γ x) = 0) ∧ ReciprocityTheory.ChartRestriction.G.AR.Up.InAt X x (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0)) (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) F ∧ ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) ≤ ENNReal.ofReal (Real.exp (C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by

  classical
  obtain ⟨C1, hC1, hW⟩ := GlobalTheory.T.exists_hormanderPeak_cutoff_singularWeights
  refine ⟨C1 + 2, by linarith, ?_⟩
  intro E _ _ _ r X la x hp0 hp0r ho hgap hbar hinj
  have hr2 : 2 ≤ r := by omega
  obtain ⟨t0⟩ : Nonempty X.Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ ∈ X.Ψ
    · exact ⟨⟨τ, h⟩⟩
    · by_cases h' : ComplexEmbedding.conjugate τ ∈ X.Ψ
      · exact ⟨⟨_, h'⟩⟩
      · exact absurd ((X.cmType τ).2 h') h
  have hnd : 0 < nd X :=
    Fintype.card_pos_iff.2 ⟨⟨t0, ⟨(⟨1, by omega⟩, ⟨0, by omega⟩), by simp [Fin.lt_def]⟩⟩⟩
  have hcard : (1 : ℝ) ≤ X.Ψ.card := by
    have : 0 < X.Ψ.card := Finset.card_pos.2 ⟨t0.1, t0.2⟩
    exact_mod_cast this
  have hfr : 1 ≤ (X.Ψ.card : ℝ) * r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    nlinarith
  set S : ℝ := (∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8 with hSdef
  have hf8 : 1 ≤ ((X.Ψ.card : ℝ) * r) ^ 8 := one_le_pow₀ hfr
  have hS1 : 1 ≤ S := by
    have h2 : 0 ≤ ∑ τ, ∑ a, |(la τ a : ℝ)| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hgap' : ∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 →
      C1 * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b :=
    fun τ a b h1 h2 => le_trans (by nlinarith) (hgap τ a b h1 h2)
  have hbar' : ∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 →
      C1 * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a :=
    fun τ a b h1 h2 => le_trans (by nlinarith) (hbar τ a b h1 h2)
  obtain ⟨ρ, c, F0, ψ, φ, h, hρ, hρR, hc, hcb, hfin, hF0s, hF01, hF00, hF0n, hψm, hψB, hψΓ, hψ0,
    hφeq, hφs, hφl, hφmono, hhm, hdb, hhint, hsup, hpoleψ, hpoleφ⟩ :=
    hW E r X la x hp0 hp0r ho hgap' hbar' hinj
  set bb : ℝ := 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 with hbbdef
  have hbb0 : 0 ≤ bb := by positivity
  have hO := ExF.isOpen_OmF X x
  have hOm : MeasurableSet (OmF X x) := hO.measurableSet
  set A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (C1 * S)) * muF X x (Metric.ball 0 ρ ∩ OmF X x) with hAdef
  have hμρ : muF X x (Metric.ball 0 ρ ∩ OmF X x) ≤
      muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) :=
    measure_mono (Set.inter_subset_inter_left _ (Metric.ball_subset_ball hρR))
  have hA : A < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμρ.trans_lt hfin)
  obtain ⟨F, hFd, hFI⟩ := GlobalTheory.T.plurisubharmonic_decreasing_limit_extension hO (eF X x) (IW.eF_smooth X x ho) (IW.eF_levi X x ho)
    (IW.eF_compact X x ho) φ hφs hφl hφmono F0 hF0s h hhm hdb A hhint

  have hexpφ : ∀ k, ∀ z ∈ OmF X x, Real.exp (-φ k z) = Real.exp (-phla X la (cpt X x z)) *
      Real.exp (bb * rhF X x z) * densF X x z * Real.exp (-ψ k (cpt X x z)) := by
    intro k z hz
    rw [hφeq k z hz]
    have hd := IW.densF_pos X x hz
    rw [show -(phla X la (cpt X x z) - bb * rhF X x z - Real.log (densF X x z) + ψ k (cpt X x z)) =
      -phla X la (cpt X x z) + bb * rhF X x z + Real.log (densF X x z) + -ψ k (cpt X x z) by ring,
      Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hd]
  have hE0 : ∀ z ∈ OmF X x, Real.exp (-phla X la (cpt X x z)) * Real.exp (bb * rhF X x z) *
      densF X x z ≤ Real.exp (-φ 0 z) := by
    intro z hz
    rw [hexpφ 0 z hz]
    have h1 : 1 ≤ Real.exp (-ψ 0 (cpt X x z)) := Real.one_le_exp (by linarith [hψ0 0 (cpt X x z)])
    have h0 : 0 ≤ Real.exp (-phla X la (cpt X x z)) * Real.exp (bb * rhF X x z) * densF X x z :=
      mul_nonneg (by positivity) (IW.densF_pos X x hz).le
    nlinarith

  have hball2 : Metric.ball (0 : V (nd X)) (ρ / 2) ⊆ OmF X x := fun z hz =>
    hcb (Metric.mem_closedBall.2 (le_trans (Metric.mem_ball.1 hz).le (by linarith)))
  have hu : DifferentiableOn ℂ (fun z => F0 z - F z) (Metric.ball 0 (ρ / 2)) := by
    have e : Set.EqOn (fun z => 1 - F z) (fun z => F0 z - F z) (Metric.ball 0 (ρ / 2)) := by
      intro z hz
      have hz' : ‖z‖ ≤ ρ / 2 := by
        have := (Metric.mem_ball.1 hz).le
        rwa [dist_zero_right] at this
      show 1 - F z = F0 z - F z
      rw [hF01 z hz']
    exact ((differentiableOn_const (1 : ℂ)).sub (hFd.mono hball2)).congr e.symm
  have hint0 : ∫⁻ z in Metric.ball (0 : V (nd X)) (ρ / 2),
      ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * ‖z‖ ^ (-(2 * (nd X : ℝ)))) < ⊤ := by
    have hpt : ∀ z ∈ Metric.ball (0 : V (nd X)) (ρ / 2),
        ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * ‖z‖ ^ (-(2 * (nd X : ℝ)))) ≤
          ENNReal.ofReal c⁻¹ * (ENNReal.ofReal (‖F0 z - F z‖ ^ 2) *
            ⨆ k, ENNReal.ofReal (Real.exp (-φ k z))) := by
      intro z hz
      have hp := hpoleφ z hz
      rw [ENNReal.ofReal_mul hc.le] at hp
      have hcc : ENNReal.ofReal c⁻¹ * ENNReal.ofReal c = 1 := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
      have ht : ENNReal.ofReal (‖z‖ ^ (-(2 * (nd X : ℝ)))) ≤
          ENNReal.ofReal c⁻¹ * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z)) := by
        calc ENNReal.ofReal (‖z‖ ^ (-(2 * (nd X : ℝ))))
            = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c * ENNReal.ofReal (‖z‖ ^ (-(2 * (nd X : ℝ))))) := by
              rw [← mul_assoc, hcc, one_mul]
          _ ≤ _ := by gcongr
      rw [ENNReal.ofReal_mul (sq_nonneg _)]
      calc ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ENNReal.ofReal (‖z‖ ^ (-(2 * (nd X : ℝ))))
          ≤ ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * (ENNReal.ofReal c⁻¹ *
              ⨆ k, ENNReal.ofReal (Real.exp (-φ k z))) := by gcongr
        _ = _ := by ring
    calc ∫⁻ z in Metric.ball (0 : V (nd X)) (ρ / 2),
          ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * ‖z‖ ^ (-(2 * (nd X : ℝ))))
        ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) (ρ / 2), ENNReal.ofReal c⁻¹ *
            (ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
      _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in Metric.ball (0 : V (nd X)) (ρ / 2),
            ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z)) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c⁻¹ * A := by
          gcongr
          exact (lintegral_mono_set hball2).trans hFI
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA
  have hF0val : F 0 = 1 := by
    have h0 := GlobalTheory.T.holomorphic_weighted_square_integrable_vanishes hnd (fun z => F0 z - F z) (ρ / 2) (by linarith) hu hint0
    have h1 := hF01 0 (by rw [norm_zero]; linarith)
    rw [h1] at h0
    exact (sub_eq_zero.1 h0).symm

  have hmuF : muF X x = (volume.restrict (OmF X x)).withDensity
      (fun z => ENNReal.ofReal (densF X x z)) := rfl
  have hdm : Measurable fun z => ENNReal.ofReal (densF X x z) :=
    ENNReal.measurable_ofReal.comp (IW.densF_meas X x)
  have hrw : ∀ g : V (nd X) → ℝ≥0∞, ∫⁻ z, g z ∂muF X x =
      ∫⁻ z in OmF X x, ENNReal.ofReal (densF X x z) * g z := by
    intro g
    rw [hmuF, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hdm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rfl
  have hWdom : ∀ z ∈ OmF X x, IW.Wpsi X la (fun _ => 0) (cpt X x z) =
      ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) := by
    intro z hz
    have hz' : cpt X x z ∈ X.dom := hz
    simp [IW.Wpsi, hz']
  have hka : ∀ z, ‖F z‖ ^ 2 / kaF X x bb z = ‖F z‖ ^ 2 * Real.exp (bb * rhF X x z) := by
    intro z
    rw [kaF, div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  have hval : ∀ z ∈ OmF X x, ENNReal.ofReal (densF X x z) *
      (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * IW.Wpsi X la (fun _ => 0) (cpt X x z)) =
      ENNReal.ofReal (‖F z‖ ^ 2 * (Real.exp (-phla X la (cpt X x z)) * Real.exp (bb * rhF X x z) *
        densF X x z)) := by
    intro z hz
    have hd := (IW.densF_pos X x hz).le
    rw [hWdom z hz, hka z, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd]
    congr 1
    ring

  have hmain : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) *
      IW.Wpsi X la (fun _ => 0) (cpt X x z) ∂muF X x ≤
      ENNReal.ofReal (Real.exp ((C1 + 2) * S)) *
        muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x) := by
    rw [hrw]
    have hpt : ∀ z ∈ OmF X x, ENNReal.ofReal (densF X x z) *
        (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * IW.Wpsi X la (fun _ => 0) (cpt X x z)) ≤
        (Metric.ball (0 : V (nd X)) ρ).indicator
          (fun z => ENNReal.ofReal (2 * Real.exp (C1 * S)) * ENNReal.ofReal (densF X x z)) z +
        2 * (ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z))) := by
      intro z hz
      rw [hval z hz]
      set E0 := Real.exp (-phla X la (cpt X x z)) * Real.exp (bb * rhF X x z) * densF X x z
        with hE0def
      have hE0n : 0 ≤ E0 := mul_nonneg (by positivity) (IW.densF_pos X x hz).le
      have hsq := HE.sq_le_two (F0 z) (F z)
      calc ENNReal.ofReal (‖F z‖ ^ 2 * E0)
          ≤ ENNReal.ofReal (2 * ‖F0 z‖ ^ 2 * E0 + 2 * (‖F0 z - F z‖ ^ 2 * E0)) := by
            apply ENNReal.ofReal_le_ofReal
            nlinarith
        _ = ENNReal.ofReal (2 * ‖F0 z‖ ^ 2 * E0) + 2 * ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * E0) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := (2 : ℝ)) (q := ‖F0 z - F z‖ ^ 2 * E0) (by norm_num), ENNReal.ofReal_ofNat]
        _ ≤ _ := by
            gcongr
            · by_cases hzb : z ∈ Metric.ball (0 : V (nd X)) ρ
              · rw [Set.indicator_of_mem hzb, ← ENNReal.ofReal_mul (by positivity)]
                apply ENNReal.ofReal_le_ofReal
                have h1 : ‖F0 z‖ ^ 2 ≤ 1 := by
                  have := hF0n z
                  nlinarith [norm_nonneg (F0 z)]
                have h2 : E0 ≤ Real.exp (C1 * S) * densF X x z := by
                  rw [hE0def]
                  exact mul_le_mul_of_nonneg_right (hsup z hzb) (IW.densF_pos X x hz).le
                have h3 : 0 ≤ Real.exp (C1 * S) * densF X x z :=
                  mul_nonneg (Real.exp_pos _).le (IW.densF_pos X x hz).le
                nlinarith [sq_nonneg ‖F0 z‖]
              · have hz0 : F0 z = 0 := hF00 z (by
                  rw [Metric.mem_ball, dist_zero_right, not_lt] at hzb
                  exact hzb)
                simp [hz0]
            · rw [ENNReal.ofReal_mul (sq_nonneg _)]
              gcongr
              refine le_trans ?_ (le_iSup _ 0)
              exact ENNReal.ofReal_le_ofReal (hE0 z hz)
    calc ∫⁻ z in OmF X x, ENNReal.ofReal (densF X x z) *
          (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * IW.Wpsi X la (fun _ => 0) (cpt X x z))
        ≤ ∫⁻ z in OmF X x, ((Metric.ball (0 : V (nd X)) ρ).indicator
            (fun z => ENNReal.ofReal (2 * Real.exp (C1 * S)) * ENNReal.ofReal (densF X x z)) z +
          2 * (ENNReal.ofReal (‖F0 z - F z‖ ^ 2) * ⨆ k, ENNReal.ofReal (Real.exp (-φ k z)))) :=
          setLIntegral_mono' hOm hpt
      _ = (∫⁻ z in OmF X x, (Metric.ball (0 : V (nd X)) ρ).indicator
            (fun z => ENNReal.ofReal (2 * Real.exp (C1 * S)) * ENNReal.ofReal (densF X x z)) z) +
          2 * ∫⁻ z in OmF X x, ENNReal.ofReal (‖F0 z - F z‖ ^ 2) *
            ⨆ k, ENNReal.ofReal (Real.exp (-φ k z)) := by
          rw [lintegral_add_left ((Measurable.const_mul hdm _).indicator Metric.isOpen_ball.measurableSet),
            lintegral_const_mul' _ _ (by norm_num)]
      _ ≤ ENNReal.ofReal (2 * Real.exp (C1 * S)) * muF X x (Metric.ball 0 ρ ∩ OmF X x) + 2 * A := by
          gcongr
          rw [lintegral_indicator Metric.isOpen_ball.measurableSet,
            lintegral_const_mul _ hdm, hmuF, withDensity_apply _
              (Metric.isOpen_ball.measurableSet.inter hOm),
            Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
            Measure.restrict_restrict (Metric.isOpen_ball.measurableSet.inter hOm),
            Set.inter_assoc, Set.inter_self]
      _ = ENNReal.ofReal (4 * Real.exp (C1 * S)) * muF X x (Metric.ball 0 ρ ∩ OmF X x) := by
          rw [hAdef, show (4 : ℝ) * Real.exp (C1 * S) = 2 * Real.exp (C1 * S) + 2 * Real.exp (C1 * S)
            by ring, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
          ring
      _ ≤ _ := by
          gcongr
          have hS' : 2 ≤ S + 1 := by linarith
          have h4 : (4 : ℝ) ≤ Real.exp (2 * S) := by
            have h1 : S + 1 ≤ Real.exp S := Real.add_one_le_exp S
            have h2 : Real.exp (2 * S) = Real.exp S * Real.exp S := by
              rw [← Real.exp_add]; ring_nf
            nlinarith
          rw [show (C1 + 2) * S = C1 * S + 2 * S by ring, Real.exp_add]
          nlinarith [Real.exp_pos (C1 * S)]
  have hfinI : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) *
      IW.Wpsi X la (fun _ => 0) (cpt X x z) ∂muF X x < ⊤ :=
    hmain.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

  have hac : muF X x ≪ volume.restrict (OmF X x) := by
    rw [hmuF]; exact withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ z ∂muF X x, z ∈ OmF X x := hac.ae_le (ae_restrict_mem hOm)
  have hext : ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) ∂muF X x < ⊤ := by
    intro C _ _
    refine lt_of_le_of_lt (setLIntegral_le_lintegral _ _) (lt_of_le_of_lt ?_ hfinI)
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with z hz
    rw [hWdom z hz, hka z, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : 1 ≤ Real.exp (bb * rhF X x z) :=
      Real.one_le_exp (mul_nonneg hbb0 (ExF.rhF_nonneg X x ho hz))
    have h2 : 0 ≤ ‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z)) := by positivity
    nlinarith
  obtain ⟨P0, hBE, hPF⟩ := extFStatement_holds r X x ho la F hFd hext

  set Ψw : Frame X.Ψ r → ℝ≥0∞ := fun y => ⨆ k, ENNReal.ofReal (Real.exp (-ψ k y)) with hΨdef
  have hΨm : Measurable Ψw :=
    Measurable.iSup fun k => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hψm k).neg)
  have hΨB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, Ψw (rmul y b) = Ψw y := by
    intro y hy b hb
    simp only [hΨdef, hψB _ y hy b hb]
  have hΨΓ : ∀ γ ∈ X.Γ, ∀ y ∈ X.dom, Ψw (lact γ y) = Ψw y := by
    intro γ hγ y hy
    simp only [hΨdef, hψΓ _ γ hγ y hy]
  have hF0R : ∀ z, 1 / (100 * (r : ℝ) ^ 2) < ‖z‖ → F0 z = 0 := fun z hz =>
    hF00 z (hρR.trans hz.le)
  have hintT : ∫⁻ z, ENNReal.ofReal (‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z))) *
      Ψw (cpt X x z) ∂muF X x < ⊤ := by
    rw [hrw]
    refine lt_of_le_of_lt ?_ hA
    refine le_trans (setLIntegral_mono' hOm fun z hz => ?_) hFI
    have hd := (IW.densF_pos X x hz).le
    simp only [hΨdef]
    rw [ENNReal.mul_iSup, ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_mono fun k => ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hd,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hexpφ k z hz]
    have h1 : 1 ≤ Real.exp (bb * rhF X x z) :=
      Real.one_le_exp (mul_nonneg hbb0 (ExF.rhF_nonneg X x ho hz))
    have h2 : 0 ≤ ‖F0 z - F z‖ ^ 2 * Real.exp (-phla X la (cpt X x z)) * densF X x z *
      Real.exp (-ψ k (cpt X x z)) := by positivity
    nlinarith
  refine ⟨F, P0, hFd, hBE, hPF, ?_, ?_, hfinI, hmain⟩
  · have h0 := hPF 0 (IW.zero_mem_OmF X x ho)
    rw [IW.cpt_zero] at h0
    rw [h0, hF0val]
  · intro γ hγ hne
    exact GlobalTheory.T.peakExtension_vanish_other_orbit_points X la x ho hnd Ψw hΨm hΨB hΨΓ c (ρ / 2) hc (by linarith) hpoleψ hinj F0 F hF0R hFd
      hintT P0 hBE hPF γ hγ hne

end GlobalTheory.HormanderPeak
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHormanderPeakOrthonormalFrameL2BoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hormanderPeak_orthonormalFrame_l2Bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x : Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → C * ((X.Ψ.card : ℝ) * r) ^ 8 ≤ (la τ b : ℝ) - la τ a) → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∃ (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) ∧ ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 ∧ (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) ∧ P0 x = 1 ∧ (∀ γ ∈ X.Γ, γ ≠ 1 → P0 (lact γ x) = 0) ∧ ReciprocityTheory.ChartRestriction.G.AR.Up.InAt X x (ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0)) (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) F ∧ ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) ≤ ENNReal.ofReal (Real.exp (C * ((∑ τ, ∑ a, |(la τ a : ℝ)|) + ((X.Ψ.card : ℝ) * r) ^ 8))) * ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball 0 (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) := by
  first | exact @GlobalTheory.HormanderPeak.hormander_peak | exact GlobalTheory.HormanderPeak.hormander_peak | (intros; apply GlobalTheory.HormanderPeak.hormander_peak <;> assumption)
end
