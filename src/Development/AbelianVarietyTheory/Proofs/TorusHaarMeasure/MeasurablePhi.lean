module

public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLtTopOfCutoff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralBallLtTopOfLocalInverse
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ChartChange

open Filter

theorem lintegral_ball_lt_top_of_localInverse {n : ℕ} (η θ : V n → V n) {U : Set (V n)} (hU : IsOpen U)
    (h0 : (0 : V n) ∈ U) (hη : DifferentiableOn ℂ η U) (hθ : ContinuousAt θ 0) (hθ0 : θ 0 = 0)
    (hηθ : ∀ᶠ z in 𝓝 (0 : V n), η (θ z) = z) (hθη : ∀ᶠ w in 𝓝 (0 : V n), θ (η w) = w)
    (g h : V n → ℝ≥0∞) (hgh : ∀ w ∈ U, g (η w) = h w) {ρ : ℝ} (hρ : 0 < ρ)
    (hint : ∫⁻ w in Metric.ball (0 : V n) ρ, h w < ⊤) :
    ∃ S ∈ 𝓝 (0 : V n), ∫⁻ z in S, g z < ⊤ := by
  have hcd : ContDiffOn ℝ ∞ η U := by
    refine (contDiffOn_piLp 2).2 fun i => ?_
    have hi : DifferentiableOn ℂ (fun z => η z i) U := (differentiableOn_piLp 2).1 hη i
    exact (contDiffOn_of_differentiableOn n _ U hU hi).restrict_scalars ℝ
  have hfc : ContinuousAt (fun w => |(fderiv ℝ η w).det|) 0 := by
    have h1 : ContinuousOn (fderiv ℝ η) U := hcd.continuousOn_fderiv_of_isOpen hU (by simp)
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp (h1.continuousAt (hU.mem_nhds h0))).abs
  set C : ℝ := |(fderiv ℝ η 0).det| + 1 with hC
  have hb : ∀ᶠ w in 𝓝 (0 : V n), |(fderiv ℝ η w).det| < C := hfc.eventually_lt continuousAt_const (by simp [hC])
  have hall : ∀ᶠ w in 𝓝 (0 : V n), w ∈ U ∧ w ∈ Metric.ball (0 : V n) ρ ∧ θ (η w) = w ∧
      |(fderiv ℝ η w).det| < C := by
    filter_upwards [hU.mem_nhds h0, Metric.ball_mem_nhds (0 : V n) hρ, hθη, hb] with w a b c d
    exact ⟨a, b, c, d⟩
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨η '' Metric.ball 0 δ, ?_, ?_⟩
  · have h1 : ∀ᶠ z in 𝓝 (0 : V n), θ z ∈ Metric.ball (0 : V n) δ :=
      hθ.eventually (by rw [hθ0]; exact Metric.ball_mem_nhds _ hδ)
    filter_upwards [h1, hηθ] with z hz1 hz2
    exact ⟨θ z, hz1, hz2⟩
  · have hd : ∀ w ∈ Metric.ball (0 : V n) δ,
        HasFDerivWithinAt η (fderiv ℝ η w) (Metric.ball (0 : V n) δ) w := fun w hw =>
      (((hcd.differentiableOn (by simp)).differentiableAt
        (hU.mem_nhds (hB w hw).1)).hasFDerivAt).hasFDerivWithinAt
    have hinj : Set.InjOn η (Metric.ball (0 : V n) δ) := fun w hw w' hw' e => by
      rw [← (hB w hw).2.2.1, e, (hB w' hw').2.2.1]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball hd hinj]
    calc ∫⁻ w in Metric.ball (0 : V n) δ, ENNReal.ofReal |(fderiv ℝ η w).det| * g (η w)
        ≤ ∫⁻ w in Metric.ball (0 : V n) δ, ENNReal.ofReal C * h w := by
          refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
          rw [hgh w (hB w hw).1]
          gcongr
          exact (hB w hw).2.2.2.le
      _ = ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) δ, h w :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ∫⁻ w in Metric.ball (0 : V n) ρ, h w := by
          exact mul_le_mul_right (lintegral_mono_set fun w hw => (hB w hw).2.1) _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open ExtFPf in
theorem zOf_zOf {r : ℕ} {X : Data E r} {x1 b c : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hbc : ∀ τ, mat b τ * mat c τ = 1) {z : V (nd X)} (hz : z ∈ OmF X x1)
    (hcz : cpt X (rmul x1 c) z ∈ cell D) :
    D.zOf (cpt X (rmul x1 b) (D.zOf (cpt X (rmul x1 c) z))) = z := by
  obtain ⟨-, hβ, he⟩ := D.split _ hcz.1 hcz.2
  set w := D.zOf (cpt X (rmul x1 c) z)
  set β := D.bOf (cpt X (rmul x1 c) z)
  have hx1 := IW.orth_mem_dom X x1 ho
  have key : cpt X (rmul x1 b) w = rmul (cpt X x1 z) (invF X β) := by
    funext τ
    have e : mat x1 τ * mat c τ * mat (nmat X z) τ = mat x1 τ * mat (nmat X w) τ * mat β τ := congrFun he τ
    have hu : IsUnit (mat x1 τ).det := isUnit_iff_ne_zero.mpr (hx1 τ).1
    have huβ : IsUnit (mat β τ).det := isUnit_iff_ne_zero.mpr (hβ τ).1
    have e2 : mat c τ * mat (nmat X z) τ = mat (nmat X w) τ * mat β τ := by
      have := congrArg (fun M => (mat x1 τ)⁻¹ * M) e
      simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu] using this
    have e3 : mat (nmat X z) τ = mat b τ * mat (nmat X w) τ * mat β τ := by
      rw [Matrix.mul_assoc, ← e2, ← Matrix.mul_assoc, hbc τ, Matrix.one_mul]
    show mat x1 τ * mat b τ * mat (nmat X w) τ = mat x1 τ * mat (nmat X z) τ * (mat β τ)⁻¹
    rw [e3]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ huβ, Matrix.mul_one]
  rw [key]
  exact (D.uniq z hz _ (invF_mem X hβ)).2.1

open ExtFPf in
theorem cpt_zero_cell {r : ℕ} {X : Data E r} {x1 b : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hb : b ∈ Bor X.Ψ r) :
    cpt X (rmul x1 b) 0 ∈ cell D ∧ D.zOf (cpt X (rmul x1 b) 0) = 0 := by
  have h := D.uniq 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero] at h
  rw [IW.cpt_zero]
  exact ⟨⟨OrthogonalFrameDomain.rmul_mem_dom X (IW.orth_mem_dom X x1 ho) hb, h.1⟩, h.2.1⟩


open ExtFPf in
theorem chart_change : ∀ (r : ℕ) (X : Data E r) (x1 b : Frame X.Ψ r), IsOrth X x1 → b ∈ Bor X.Ψ r →
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∀ ρ : ℝ, 0 < ρ → ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, φ (cpt X (rmul x1 b) z) < ⊤ →
    ∃ ρ' : ℝ, 0 < ρ' ∧ Metric.ball (0 : V (nd X)) ρ' ⊆ OmF X x1 ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) ρ', φ (cpt X x1 z) ∂muF X x1 < ⊤ := by
  intro r X x1 b ho hb φ _ hφ ρ hρ hint
  obtain ⟨D⟩ := luData_of lu_holds X x1 ho
  have hc := invF_mem X hb
  have hop : ∀ y : Frame X.Ψ r, IsOpen (cpt X y ⁻¹' cell D) := fun y =>
    (isOpen_cell D).preimage (OntoB.cd_cpt X y).continuous
  have hdiff : ∀ y : Frame X.Ψ r, DifferentiableOn ℂ (fun z => D.zOf (cpt X y z)) (cpt X y ⁻¹' cell D) :=
    fun y => D.hz.comp ((OntoB.cd_cpt X y).differentiable (by simp)).differentiableOn fun _ hz => hz
  have h0 := IW.zero_mem_OmF X x1 ho
  have hO := (OntoB.isOpen_OmF X x1).mem_nhds h0
  obtain ⟨hb0, -⟩ := cpt_zero_cell D ho hb
  obtain ⟨hc0, hc1⟩ := cpt_zero_cell D ho hc
  obtain ⟨S, hS, hSi⟩ := lintegral_ball_lt_top_of_localInverse
    (fun z => D.zOf (cpt X (rmul x1 b) z)) (fun z => D.zOf (cpt X (rmul x1 (invF X b)) z))
    (hop (rmul x1 b)) hb0 (hdiff _)
    (((hdiff _).differentiableAt ((hop _).mem_nhds hc0)).continuousAt) hc1
    (by
      filter_upwards [hO, (hop _).mem_nhds hc0] with z hz1 hz2
      exact zOf_zOf D ho
        (fun τ => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hb τ).1)) hz1 hz2)
    (by
      filter_upwards [hO, (hop _).mem_nhds hb0] with z hz1 hz2
      exact zOf_zOf D ho
        (fun τ => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hb τ).1)) hz1 hz2)
    (fun z => φ (cpt X x1 z)) (fun z => φ (cpt X (rmul x1 b) z))
    (by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := D.split _ hw.1 hw.2
      show φ (cpt X x1 _) = φ _
      conv_rhs => rw [h3]
      exact (hφ _ h1 _ h2).symm) hρ hint
  have hdc : ContinuousAt (densF X x1) 0 := (OntoB.densF_continuousOn (X := X) (x0 := x1)).continuousAt hO
  set C : ℝ := densF X x1 0 + 1 with hC
  have hbd : ∀ᶠ z in 𝓝 (0 : V (nd X)), densF X x1 z < C := hdc.eventually_lt continuousAt_const (by simp [hC])
  have hall : ∀ᶠ z in 𝓝 (0 : V (nd X)), z ∈ OmF X x1 ∧ z ∈ S ∧ densF X x1 z < C := by
    filter_upwards [hO, hS, hbd] with w a b c
    exact ⟨a, b, c⟩
  obtain ⟨δ, hδ, hB⟩ := Metric.eventually_nhds_iff_ball.1 hall
  refine ⟨δ, hδ, fun z hz => (hB z hz).1, ?_⟩
  have hle : (muF X x1).restrict (Metric.ball 0 δ) ≤ ENNReal.ofReal C • volume.restrict S := by
    unfold muF
    rw [restrict_withDensity measurableSet_ball, Measure.restrict_restrict measurableSet_ball]
    calc (volume.restrict (Metric.ball 0 δ ∩ OmF X x1)).withDensity
          (fun z => ENNReal.ofReal (densF X x1 z))
        ≤ (volume.restrict (Metric.ball 0 δ ∩ OmF X x1)).withDensity (fun _ => ENNReal.ofReal C) := by
          refine withDensity_mono ?_
          filter_upwards [ae_restrict_mem
            (measurableSet_ball.inter (OntoB.isOpen_OmF X x1).measurableSet)] with z hz
          exact ENNReal.ofReal_le_ofReal (hB z hz.1).2.2.le
      _ = ENNReal.ofReal C • volume.restrict (Metric.ball 0 δ ∩ OmF X x1) := withDensity_const _
      _ ≤ ENNReal.ofReal C • volume.restrict S := by
          refine Measure.le_iff'.2 fun s => ?_
          simp only [Measure.smul_apply, smul_eq_mul]
          have hsub : Metric.ball 0 δ ∩ OmF X x1 ⊆ S := fun z hz => (hB z hz.1).2.1
          exact mul_le_mul_right (Measure.le_iff'.1 (Measure.restrict_mono_set _ hsub) s) _
  refine lt_of_le_of_lt (lintegral_mono' hle le_rfl) ?_
  rw [lintegral_smul_measure]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSi

end GlobalTheory.ChartChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsOpenSaturation
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SatOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuous_lact {r : ℕ} {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) :
    Continuous (lact δ : Frame Ψ r → Frame Ψ r) := by
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
  simp only [lact, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem isOpen_cell {r : ℕ} (X : Data E r) {x1 : Frame X.Ψ r} (ho : IsOrth X x1)
    {N : Set (V (nd X))} (hN : IsOpen N) (hNO : N ⊆ OmF X x1) :
    IsOpen {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
  obtain ⟨Δ, zOf, bOf, hΔ, -, hz, -, hsplit, huniq⟩ := lu_holds r X x1 ho
  have hU : IsOpen {x | x ∈ X.dom ∧ Δ x ≠ 0} :=
    (FourierCoefficientDomain.isOpen_dom X).inter (isOpen_ne_fun hΔ.continuous continuous_const)
  have heq : {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} =
      {x | x ∈ X.dom ∧ Δ x ≠ 0} ∩ zOf ⁻¹' N := by
    ext x
    constructor
    · rintro ⟨y, hy, b, hb, rfl⟩
      obtain ⟨h1, h2, -⟩ := huniq y (hNO hy) b hb
      refine ⟨⟨OntoS.dom_rmul X (hNO hy) hb, h1⟩, ?_⟩
      rw [Set.mem_preimage, h2]
      exact hy
    · rintro ⟨⟨hx, hd⟩, hzN⟩
      obtain ⟨-, h2, h3⟩ := hsplit x hx hd
      exact ⟨zOf x, hzN, bOf x, h2, h3⟩
  rw [heq]
  exact hz.continuousOn.isOpen_inter_preimage hU hN

theorem isOpen_saturation : ∀ (r : ℕ) (X : Data E r) (x1 : Frame X.Ψ r), IsOrth X x1 →
    ∀ N : Set (V (nd X)), IsOpen N → N ⊆ OmF X x1 →
    IsOpen {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} := by
  intro r X x1 ho N hN hNO
  have heq : {x | ∃ y ∈ N, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b)} =
      ⋃ γ ∈ X.Γ, lact γ⁻¹ ⁻¹' {x | ∃ y ∈ N, ∃ b ∈ Bor X.Ψ r, x = rmul (cpt X x1 y) b} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨γ, hγ, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
    · rintro ⟨γ, hγ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ, hγ, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
  rw [heq]
  exact isOpen_biUnion fun γ _ => (isOpen_cell X ho hN hNO).preimage (continuous_lact _)

end GlobalTheory.SatOpen
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivInFFPf

open Filter

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem muF_lt_top (hM : MeasInvStatement (E := E)) (hfin : FinMu X) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) : muF X x0 FF < ⊤ := by
  classical
  obtain ⟨x1, ho1, F1, hF1, hlt⟩ := hfin
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 ho ho1 FF hF (fun _ => 1)
    measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1
  simp only [lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] at hle
  let S : Set (Frame X.Ψ r) := ⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1
  have hS : MeasurableSet S := MeasurableSet.iUnion fun γ =>
    (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X ho1 hF1.1 hF1.2.1)
  have hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, x = lact γ (rmul (cpt X x1 y) b) := by
    intro x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
    · rintro ⟨y, hy, γ, hγ, b, hb, rfl⟩
      exact ⟨⟨γ, hγ⟩, y, hy, b, hb, FundSetPf.lact_inv _ _⟩
  have hψ : Measurable (Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞)) := measurable_one.indicator hS.compl
  have hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Sᶜ.indicator 1 x := by
    intro x _ b hb
    have : rmul x b ∈ S ↔ x ∈ S := by
      simp only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul,
        GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]
    simp only [Set.indicator, Set.mem_compl_iff, this, Pi.one_apply]
  have h0 : ∫⁻ z, Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [hM r X x0 x1 ho ho1 _ hψ hB]
    refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
    filter_upwards [hF1.2.2.2] with z hz
    exact Set.indicator_of_notMem (Set.notMem_compl_iff.2 ((hSiff _).2 hz)) _
  have hae := (lintegral_eq_zero_iff (hψ.comp (FundSetPf.cont_cpt X x0).measurable)).1 h0
  refine lt_of_le_of_lt (measure_mono_ae ?_) (hle.trans_lt hlt)
  filter_upwards [hae] with z hz hzF
  refine ⟨hzF, (hSiff _).1 ?_⟩
  by_contra hn
  have : Sᶜ.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) = 0 := hz
  rw [Set.indicator_of_mem (show _ ∈ Sᶜ from hn)] at this
  exact one_ne_zero this

variable (Xa : ArchInM X) (Fl : FlatM X Xa)

theorem ae_exists_ne {x0 : Frame X.Ψ r} (ho : IsOrth X x0) :
    ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 → ∃ k, Fl.s k (cpt X x0 z) ≠ 0 := by
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hn := Xa.n_ge
  have : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have hc : (⋃ j : Fin Fl.δ, ⋃ γ : GL (Fin r) E,
      {z | ∃ b ∈ Bor X.Ψ r, cpt X x0 z = lact γ (rmul (Fl.xs j) b)}).Countable := by
    refine Set.countable_iUnion fun j => Set.countable_iUnion fun γ => Set.Subsingleton.countable ?_
    rintro z ⟨b, hb, h⟩ z' ⟨b', hb', h'⟩
    refine FundSetPf.cpt_uniq X ho (ExtFPf.invF_mem X hb) (ExtFPf.invF_mem X hb') ?_
    rw [h, h', FundSetPf.lact_rmul, FundSetPf.lact_rmul, ExtFPf.rmul_assoc, ExtFPf.rmul_assoc,
      ExtFPf.rmul_invF X hb, ExtFPf.rmul_invF X hb']
  have hac : muF X x0 ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  filter_upwards [hac.ae_le (hc.ae_notMem volume)] with z hz hzO
  by_contra hs
  push Not at hs
  obtain ⟨j, γ, -, b, hb, h⟩ := (Fl.S_eq _ hzO).1 hs
  exact hz (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨γ, b, hb, h⟩⟩)

theorem pnorm_contOn {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom :=
  hP.1.continuousOn.norm.mul (ExtFPf.nfac_contOn X la)

theorem measurable_cut {f : Frame X.Ψ r → ℝ} (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hf continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet

theorem sum_pnorm_pos {N : ℕ} {la : Wt X.Ψ r} {P : Fin N → Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (h : ∃ k, P k x ≠ 0) : 0 < ∑ k, X.pnorm la (P k) x ^ 2 := by
  simp only [pnorm_sq_eq_exp hx, ← Finset.mul_sum]
  exact mul_pos (Real.exp_pos _) (sum_normSq_pos h)

theorem real_bound {e F G w s K C : ℝ} {a b : ℂ} {n : ℕ} (hn : 1 ≤ n) (he : 0 ≤ e) (hF : F = e * ‖a‖ ^ 2)
    (hG : G = e * ‖b‖ ^ 2) (hw : 0 < w) (hs : 0 ≤ s) (hK : w ≤ K * s) (hC : G ≤ C * w ^ n) :
    e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2)) ≤
      2 * |K| ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) + 2 * |K| ^ ((n : ℝ) - 1 / 2) * C := by
  have hn' : 0 ≤ (n : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hKs : 0 < K * s := hw.trans_le hK
  have hs' : 0 < s := lt_of_le_of_ne hs (by rintro rfl; simp at hKs)
  have hK0 : 0 < K := (mul_pos_iff_of_pos_right hs').1 hKs
  rw [abs_of_pos hK0]
  have h1 : s ^ (-((n : ℝ) - 1 / 2)) ≤ K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2)) := by
    have : (K * s) ^ (-((n : ℝ) - 1 / 2)) ≤ w ^ (-((n : ℝ) - 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos hw hK (by linarith)
    rw [Real.mul_rpow hK0.le hs, Real.rpow_neg hK0.le,
      inv_mul_le_iff₀ (Real.rpow_pos_of_pos hK0 _)] at this
    exact this
  have h2 : w ^ (-(1 / 2 : ℝ)) * w ^ (-((n : ℝ) - 1 / 2)) = w ^ (-(n : ℝ)) := by
    rw [← Real.rpow_add hw]; congr 1; ring
  have h3 : e * ‖a - b‖ ^ 2 ≤ 2 * F + 2 * G := by
    have h4 : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
      nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    rw [hF, hG]
    nlinarith [mul_le_mul_of_nonneg_left h4 he]
  have h5 : G * w ^ (-(n : ℝ)) ≤ C := by
    rw [Real.rpow_neg hw.le, Real.rpow_natCast, mul_inv_le_iff₀ (pow_pos hw n)]
    exact hC
  have hKp := Real.rpow_pos_of_pos hK0 ((n : ℝ) - 1 / 2)
  calc e * ‖a - b‖ ^ 2 * w ^ (-(1 / 2 : ℝ)) * s ^ (-((n : ℝ) - 1 / 2))
      ≤ (2 * F + 2 * G) * w ^ (-(1 / 2 : ℝ)) * (K ^ ((n : ℝ) - 1 / 2) * w ^ (-((n : ℝ) - 1 / 2))) := by
        have : 0 ≤ 2 * F + 2 * G := le_trans (by positivity) h3
        gcongr
    _ = 2 * K ^ ((n : ℝ) - 1 / 2) * (F * w ^ (-(n : ℝ))) +
          2 * K ^ ((n : ℝ) - 1 / 2) * (G * w ^ (-(n : ℝ))) := by rw [← h2]; ring
    _ ≤ _ := by gcongr

end GlobalTheory.Up.DivInFFPf
