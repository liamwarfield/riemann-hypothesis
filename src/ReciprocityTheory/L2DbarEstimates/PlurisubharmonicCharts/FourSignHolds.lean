module

public import ReciprocityTheory.L2DbarEstimates.NormFibrations.Hormander
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.LseSmoothRIffReal
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.ImportsAlt
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeLoc
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourIndep
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart

@[expose] public section

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.HyPhi
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Metric
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem hy (n : ℕ) (Y : Type u) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] (hH : HAll.{u} n) (hE : EXTStatement n) (hN : EXTNullStatement n) :
    HYStatement n Y ι La := by
  intro A L la N w w0 s De σ ps F0 h hD hF hσ hps hPos hF0 hh hdb
  classical
  by_cases hfin : ∫⁻ y, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu = ⊤
  · refine ⟨fun _ _ => 0, ⟨fun i => differentiableOn_const 0, fun i j y _ _ _ => by simp⟩, ?_⟩
    rw [hfin]; exact le_top
  set M := A.Mset w0 s De with hMdef
  set X := flatStein A hD hF with hX
  have hMo : IsOpen M := isOpen_Mset A hD
  set Φ := hyPhi A w0 s σ la ps with hΦdef
  set u0 := sectionFrameQuotient A F0 σ with hu0def
  set nσ := A.nsq (A.kap + la) σ with hnσdef
  have hpsc : Continuous ps := hyq_smoothFn_cont A hps
  have hΦs : SmoothR n X.z (fun y : M => Φ y) := smoothR_flat A hD hF Φ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_phi_smooth A hD hF hσ hps hx _ (A.mem_pick x)⟩)
  have hΦl : LeviNonneg n X.z (fun y : M => Φ y) := leviNonneg_flat A hD hF Φ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_phi_smooth A hD hF hσ hps hx _ (A.mem_pick x), fun ξ => by
      rw [hyq_levi_phi A hD hF hσ hps hx _ (A.mem_pick x)]
      exact hPos _ _ (A.mem_pick x) ξ⟩)
  have hu0s : Smooth n X.z (fun y : M => u0 y) := smooth_flat A hD hF u0 (fun x hx =>
    ⟨A.pick x, A.mem_pick x, contDiffAt_sectionFrameQuotient A hD hσ hF0 hx _ (A.mem_pick x)⟩)
  have hnσs : SmoothR n X.z (fun y : M => nσ y) := smoothR_flat A hD hF nσ (fun x hx =>
    ⟨A.pick x, A.mem_pick x, hyq_nsig_smooth A hD hσ hx _ (A.mem_pick x)⟩)
  have hnσc : Continuous (fun y : M => nσ y) := by
    have := Complex.continuous_re.comp (Smooth.continuous n X.z X.isLocalHomeomorph _ hnσs)
    exact this
  have hu0c : Continuous (fun y : M => u0 y) := Smooth.continuous n X.z X.isLocalHomeomorph _ hu0s

  set hHf : M → ℝ≥0∞ := fun x => h x * ENNReal.ofReal (nσ x)⁻¹ with hHfdef
  have hHm : Measurable hHf :=
    (hh.comp measurable_subtype_coe).mul (ENNReal.measurable_ofReal.comp hnσc.measurable.inv)
  have hdbM : ∀ (x : M) (η : Fin n → ℂ), ENNReal.ofReal (‖dbarDot n X.z (fun y : M => u0 y) x η‖ ^ 2) ≤
      hHf x * ENNReal.ofReal (Levi n X.z (fun y : M => Φ y) x η).re := by
    intro x η
    have hi := A.mem_pick (x : Y)
    have hdet := jz_det_ne A hD hF x x.2 (A.pick x) hi
    set J' := (jz A w0 s (A.pick x) x).toContinuousLinearEquivOfDetNeZero hdet
    set ξ : Fin n → ℂ := WithLp.ofLp (J'.symm (WithLp.toLp 2 η)) with hξ
    have hη : (fun k => jz A w0 s (A.pick x) x (WithLp.toLp 2 ξ) k) = η := by
      have h1 : jz A w0 s (A.pick x) x (WithLp.toLp 2 ξ) = WithLp.toLp 2 η := by
        have h2 := ((jz A w0 s (A.pick x) x).toContinuousLinearEquivOfDetNeZero hdet).apply_symm_apply
          (WithLp.toLp 2 η)
        rw [ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply] at h2
        simpa [J', ξ] using h2
      rw [h1]
    rw [← hη, ← dbar_flat_loc A hD hF u0 (A.pick x) x hi (contDiffAt_sectionFrameQuotient A hD hσ hF0 x.2 _ hi) ξ,
      ← levi_flat_loc A hD hF Φ (A.pick x) x hi (hyq_phi_smooth A hD hF hσ hps x.2 _ hi) ξ,
      hyq_levi_phi A hD hF hσ hps x.2 _ hi, dbar_sectionFrameQuotient A hD hσ hF0 x.2 _ hi]
    have key := hdb (A.pick x) x hi ξ
    have hσne := hyq_sigma_ne A hσ x.2 (A.pick x) hi
    have e1 : ‖A.dbarAt (A.pick x) F0 x ξ / σ (A.pick x) x‖ ^ 2 =
        (‖A.dbarAt (A.pick x) F0 x ξ‖ ^ 2 * Real.exp (-A.ph (A.kap + la) (A.pick x) x)) * (nσ x)⁻¹ := by
      simp only [hnσdef, nsq]
      rw [norm_div, div_pow, mul_inv, Real.exp_neg, inv_inv]
      field_simp
    rw [e1, ENNReal.ofReal_mul (by positivity)]
    calc _ ≤ h x * ENNReal.ofReal (A.leviAt (A.pick x) (fun y => A.ph la (A.pick x) y + ps y) x ξ) *
          ENNReal.ofReal (nσ x)⁻¹ := by gcongr
      _ = _ := by simp only [hHfdef]; ring
  obtain ⟨Fu, hFu, hFbd⟩ := hH M X (fun y => Φ y) (fun y => u0 y) hHf hΦs hΦl hu0s hHm hdbM

  set ut : Y → ℂ := fun y => if hy : y ∈ M then Fu ⟨y, hy⟩ else 0 with hutdef
  have hut : (fun y : M => ut y) = Fu := funext fun y => dif_pos y.2
  have hutc : Continuous (fun y : M => ut y) := by
    rw [hut]; exact Smooth.continuous n X.z X.isLocalHomeomorph _ (Holo.smooth n X.z _ hFu)
  set Fs : ι → Y → ℂ := fun i y => σ i y * ut y with hFsdef
  have hFs : A.IsSecOn (A.kap + la) M Fs := by
    refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
    · have h1 := (holo_flat_iff A hD hF ut).1 (by rw [hut]; exact hFu) i
      exact (hσ.1.1 i).mul h1
    · simp only [hFsdef]; rw [hσ.1.2 i j y hy hi hj]; ring

  set ψ0 : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (nσ y * ‖u0 y - ut y‖ ^ 2 * Real.exp (-ps y))
    with hψ0def
  set ψ : Y → ℝ≥0∞ := M.indicator ψ0 with hψdef
  have hψm : Measurable ψ := by
    refine measurable_of_restrict_of_restrict_compl hMo.measurableSet ?_ ?_
    · have hc : Continuous (fun y : M => ψ0 y) :=
        ENNReal.continuous_ofReal.comp ((hnσc.mul ((hu0c.sub hutc).norm.pow 2)).mul
          (Real.continuous_exp.comp (hpsc.comp continuous_subtype_val).neg))
      have : M.domRestrict ψ = fun y : M => ψ0 y := funext fun y => by
        show M.indicator ψ0 y = ψ0 y; exact Set.indicator_of_mem y.2 _
      rw [this]; exact hc.measurable
    · have : Mᶜ.domRestrict ψ = fun _ => 0 := funext fun y => by
        show M.indicator ψ0 y = 0; exact Set.indicator_of_notMem y.2 _
      rw [this]; exact measurable_const
  have hae : ∀ᵐ y ∂A.mu, y ∈ M := by
    rw [ae_iff]; simpa [Set.compl_def] using mu_compl_Mset A hN hD hF
  have hre : ∀ f : Y → ℝ≥0∞, ∫⁻ y, f y ∂A.mu = ∫⁻ y in M, f y ∂A.mu := fun f => by
    rw [Measure.restrict_eq_self_of_ae_mem hae]
  set nJ := A.nsq A.kap (fun i y => (jz A w0 s i y).det) with hnJdef
  have hdens : ∀ x : M, Real.exp (A.ph A.kap (A.pick x) x) / ‖(jz A w0 s (A.pick x) x).det‖ ^ 2 =
      (nJ x)⁻¹ := by
    intro x
    have hJp := hyq_nJ_pos A hD hF x.2
    simp only [hnJdef, nsq] at hJp ⊢
    rw [Real.exp_neg, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  have hexp : ∀ x : M, Real.exp (-Φ x) = nσ x * Real.exp (-ps x) * (nJ x)⁻¹ := by
    intro x
    have hσp := hyq_nsig_pos A hσ x.2
    have hJp := hyq_nJ_pos A hD hF x.2
    have e : -Φ x = Real.log (nσ x) - Real.log (nJ x) + -ps x := by
      simp only [hΦdef, hyPhi, hnσdef, hnJdef]; ring
    rw [e, Real.exp_add, Real.exp_sub, Real.exp_log hσp, Real.exp_log hJp]; ring
  have hI1 : ∫⁻ y, ψ y ∂A.mu = wint n X.z (fun x => u0 x - Fu x) (fun y => Φ y) := by
    rw [hre, lintegral_flat A hD hF ψ hψm, wint]
    refine lintegral_congr fun x => ?_
    have hσp := hyq_nsig_pos A hσ x.2
    rw [hψdef, Set.indicator_of_mem x.2]
    show ENNReal.ofReal (nσ x * ‖u0 x - ut x‖ ^ 2 * Real.exp (-ps x)) * _ = _
    rw [show ut x = Fu x from congrFun hut x, ← ENNReal.ofReal_mul (by positivity), hdens x, hexp x]
    congr 1; ring
  have hI2 : ∫⁻ x, hHf x * ENNReal.ofReal (Real.exp (-(fun y : M => Φ y) x)) ∂vol n X.z =
      ∫⁻ y in M, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu := by
    rw [lintegral_flat A hD hF (fun y => h y * ENNReal.ofReal (Real.exp (-ps y))) (hh.mul
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hpsc.neg).measurable))]
    refine lintegral_congr fun x => ?_
    have hσp := hyq_nsig_pos A hσ x.2
    have hJp := hyq_nJ_pos A hD hF x.2
    rw [hHfdef, mul_assoc, mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hdens x]
    show h x * ENNReal.ofReal ((nσ x)⁻¹ * Real.exp (-Φ x)) = _
    rw [hexp x]
    congr 2
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (show nσ x ≠ 0 from hσp.ne'), one_mul]
  have hint : ∫⁻ y, ψ y ∂A.mu ≤ ∫⁻ y, h y * ENNReal.ofReal (Real.exp (-ps y)) ∂A.mu := by
    rw [hI1]
    exact hFbd.trans (hI2.le.trans (setLIntegral_le_lintegral _ _))
  have hψfin : ∫⁻ y, ψ y ∂A.mu < ⊤ := hint.trans_lt (lt_top_iff_ne_top.2 hfin)

  have hloc : ∀ y, ∃ U ∈ 𝓝 y, ∫⁻ x in U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ∂A.mu < ⊤ := by
    intro y0
    have hi := A.mem_pick y0
    set e := A.chart (A.pick y0) with he
    obtain ⟨r, hr, hrt⟩ := Metric.isOpen_iff.1 e.open_target (e y0) (e.map_source hi)
    have hcb : closedBall (e y0) (r / 2) ⊆ e.target :=
      (closedBall_subset_ball (by linarith)).trans hrt
    have hS : ContinuousOn e.symm (closedBall (e y0) (r / 2)) := e.continuousOn_symm.mono hcb
    obtain ⟨C1, hC1⟩ := hyq_bdd (f := fun v => ‖F0 (A.pick y0) (e.symm v)‖ ^ 2 *
      Real.exp (-A.ph (A.kap + la) (A.pick y0) (e.symm v))) (c := e y0) (r := r / 2) (by
        have h1 := (hF0.1 (A.pick y0)).continuousOn.mono hcb
        have h2 := (A.smooth_ph (A.kap + la) (A.pick y0)).continuousOn.mono hcb
        exact (h1.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn h2.neg))
    obtain ⟨C2, hC2⟩ := hyq_bdd (f := fun v => ps (e.symm v)) (c := e y0) (r := r / 2)
      (hpsc.comp_continuousOn hS)
    obtain ⟨C3, hC3⟩ := hyq_bdd (f := fun v => Real.exp (A.ph A.kap (A.pick y0) (e.symm v)))
      (c := e y0) (r := r / 2) (Real.continuous_exp.comp_continuousOn
        ((A.smooth_ph A.kap (A.pick y0)).continuousOn.mono hcb))
    set U := e.source ∩ e ⁻¹' ball (e y0) (r / 2) with hU
    have hUo : IsOpen U := e.isOpen_inter_preimage isOpen_ball
    have hyU : y0 ∈ U := ⟨hi, by exact Set.mem_preimage.mpr (mem_ball_self (by linarith))⟩
    have hUM : MeasurableSet (U ∩ M) := (hUo.inter hMo).measurableSet
    refine ⟨U, hUo.mem_nhds hyU, ?_⟩
    have hC1n : 0 ≤ C1 := le_trans (by positivity) (hC1 (e y0) (mem_closedBall_self (by linarith)))
    have hpt : ∀ x ∈ U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ≤
        ENNReal.ofReal (2 * C1) + ENNReal.ofReal (2 * Real.exp C2) * ψ x := by
      rintro x ⟨⟨hxs, hxb⟩, hxM⟩
      have hv : e x ∈ closedBall (e y0) (r / 2) := ball_subset_closedBall hxb
      have hSx : e.symm (e x) = x := e.left_inv hxs
      have h1 := hC1 _ hv
      have h2 := hC2 _ hv
      simp only [hSx] at h1 h2
      have hF0x : A.nsq (A.kap + la) F0 x =
          ‖F0 (A.pick y0) x‖ ^ 2 * Real.exp (-A.ph (A.kap + la) (A.pick y0) x) :=
        hyq_nsq_chart A _ F0 _ x hxs (hF0.2 _ _ x hxs (A.mem_pick x))
      have hσne := hyq_sigma_ne A hσ hxM (A.pick x) (A.mem_pick x)
      have hFsx : A.nsq (A.kap + la) Fs x = nσ x * ‖ut x‖ ^ 2 := by
        simp only [nsq, hFsdef, hnσdef, norm_mul, mul_pow]; ring
      have hF0x' : A.nsq (A.kap + la) F0 x = nσ x * ‖u0 x‖ ^ 2 := by
        simp only [nsq, hnσdef, hu0def, sectionFrameQuotient, norm_div, div_pow]; field_simp
      have hσp := hyq_nsig_pos A hσ hxM
      set t := nσ x * ‖u0 x - ut x‖ ^ 2 * Real.exp (-ps x) with ht
      have hψx : ψ x = ENNReal.ofReal t := by rw [hψdef, Set.indicator_of_mem hxM]
      have ht0 : 0 ≤ t := by positivity
      have hpar : ‖ut x‖ ^ 2 ≤ 2 * ‖u0 x‖ ^ 2 + 2 * ‖u0 x - ut x‖ ^ 2 := by
        have h0 : ‖ut x‖ ≤ ‖u0 x‖ + ‖u0 x - ut x‖ := by
          calc ‖ut x‖ = ‖u0 x - (u0 x - ut x)‖ := by rw [sub_sub_cancel]
            _ ≤ _ := norm_sub_le _ _
        have h3 : ‖ut x‖ ^ 2 ≤ (‖u0 x‖ + ‖u0 x - ut x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h0 2
        nlinarith [sq_nonneg (‖u0 x‖ - ‖u0 x - ut x‖)]
      have hte : nσ x * ‖u0 x - ut x‖ ^ 2 = Real.exp (ps x) * t := by
        rw [ht, Real.exp_neg]; field_simp
      have hkey : A.nsq (A.kap + la) Fs x ≤ 2 * C1 + 2 * Real.exp C2 * t := by
        have he2 : Real.exp (ps x) ≤ Real.exp C2 := Real.exp_le_exp.2 h2
        calc A.nsq (A.kap + la) Fs x = nσ x * ‖ut x‖ ^ 2 := hFsx
          _ ≤ nσ x * (2 * ‖u0 x‖ ^ 2 + 2 * ‖u0 x - ut x‖ ^ 2) := by gcongr
          _ = 2 * A.nsq (A.kap + la) F0 x + 2 * (Real.exp (ps x) * t) := by rw [hF0x', ← hte]; ring
          _ ≤ 2 * C1 + 2 * (Real.exp C2 * t) := by
            rw [hF0x]; gcongr
          _ = 2 * C1 + 2 * Real.exp C2 * t := by ring
      rw [hψx, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
        (by positivity)]
      exact ENNReal.ofReal_le_ofReal hkey
    calc ∫⁻ x in U ∩ M, ENNReal.ofReal (A.nsq (A.kap + la) Fs x) ∂A.mu
        ≤ ∫⁻ x in U ∩ M, (ENNReal.ofReal (2 * C1) + ENNReal.ofReal (2 * Real.exp C2) * ψ x) ∂A.mu :=
          setLIntegral_mono' hUM hpt
      _ = ENNReal.ofReal (2 * C1) * A.mu (U ∩ M) +
          ENNReal.ofReal (2 * Real.exp C2) * ∫⁻ x in U ∩ M, ψ x ∂A.mu := by
          rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul _ hψm,
            Measure.restrict_apply_univ]
      _ < ⊤ := by
          have hmu : A.mu (U ∩ M) < ⊤ := by
            calc A.mu (U ∩ M) ≤ A.mu U := measure_mono Set.inter_subset_left
              _ = ∫⁻ v in e '' U, ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y0) (e.symm v))) :=
                  A.mu_chart _ U hUo.measurableSet Set.inter_subset_left
              _ ≤ ∫⁻ v in closedBall (e y0) (r / 2),
                  ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y0) (e.symm v))) :=
                  lintegral_mono_set (by
                    rintro _ ⟨y, ⟨_, hyb⟩, rfl⟩; exact ball_subset_closedBall hyb)
              _ ≤ ∫⁻ v in closedBall (e y0) (r / 2), ENNReal.ofReal C3 :=
                  setLIntegral_mono' measurableSet_closedBall
                    (fun v hv => ENNReal.ofReal_le_ofReal (hC3 v hv))
              _ = ENNReal.ofReal C3 * volume (closedBall (e y0) (r / 2)) := setLIntegral_const _ _
              _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
          have hψU : ∫⁻ x in U ∩ M, ψ x ∂A.mu < ⊤ :=
            (setLIntegral_le_lintegral _ _).trans_lt hψfin
          exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmu,
            ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψU⟩

  obtain ⟨G, hG, hGeq⟩ := ext_Mset A hE hD hF (A.kap + la) Fs hFs hloc
  refine ⟨G, hG, ?_⟩
  calc ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) (F0 - G) y * Real.exp (-ps y)) ∂A.mu
      = ∫⁻ y, ψ y ∂A.mu := by
        refine lintegral_congr_ae (hae.mono fun y hy => ?_)
        rw [hψdef, Set.indicator_of_mem hy]
        show ENNReal.ofReal (A.nsq (A.kap + la) (F0 - G) y * Real.exp (-ps y)) = ψ0 y
        have hσne := hyq_sigma_ne A hσ hy (A.pick y) (A.mem_pick y)
        have hGy := hGeq (A.pick y) y hy (A.mem_pick y)
        have e : A.nsq (A.kap + la) (F0 - G) y = nσ y * ‖u0 y - ut y‖ ^ 2 := by
          simp only [nsq, Pi.sub_apply, hGy, hFsdef, hnσdef, hu0def, sectionFrameQuotient]
          rw [show F0 (A.pick y) y - σ (A.pick y) y * ut y =
            σ (A.pick y) y * (F0 (A.pick y) y / σ (A.pick y) y - ut y) by field_simp, norm_mul,
            mul_pow]
          ring
        rw [e]
    _ ≤ _ := hint

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ImportsAlt
section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.VanishingOrderTransfer
section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DifferentiableAtLocalCoordinates
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem isCoveringMapOn_of_proper {n : ℕ} {E : Type*} [TopologicalSpace E] [T2Space E] (z : E → V n)
    (U : Set (V n)) (hU : IsOpen U) (hz : ∀ x, z x ∈ U) (hl : IsLocalHomeomorph z)
    (hp : ∀ K : Set (V n), IsCompact K → K ⊆ U → IsCompact (z ⁻¹' K)) :
    IsCoveringMapOn z U ∧ ∀ y, (z ⁻¹' {y}).Finite := by
  let g : E → U := fun x => ⟨z x, hz x⟩
  have hgc : Continuous g := hl.continuous.subtype_mk _
  have hgl : IsLocalHomeomorph g :=
    IsLocalHomeomorph.of_comp (g := Subtype.val) (by simpa [Function.comp_def, g] using hl)
      hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph hgc
  have hgp : IsProperMap g := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hgc, fun K hK => ?_⟩
    have h1 := hp (Subtype.val '' K) (hK.image continuous_subtype_val)
      (by rintro _ ⟨y, -, rfl⟩; exact y.2)
    have h2 : g ⁻¹' K = z ⁻¹' (Subtype.val '' K) := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hx; exact ⟨g x, hx, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have : y = g x := Subtype.ext hyx
        rw [← this]; exact hy
    rw [h2]; exact h1
  have hfib : ∀ y (hy : y ∈ U), (z ⁻¹' {y}).Finite := by
    intro y hy
    have h2 : z ⁻¹' {y} = g ⁻¹' {⟨y, hy⟩} := by
      ext x; simp [g, Subtype.ext_iff]
    rw [h2]
    refine (hgp.isCompact_preimage isCompact_singleton).finite ?_
    refine (hgl.isLocalHomeomorphOn.mono (Set.subset_univ _)).isDiscrete_of_image ?_
    refine (Set.subsingleton_singleton.anti (Set.image_preimage_subset _ _)).isDiscrete
  refine ⟨?_, fun y => ?_⟩
  · refine IsCoveringMapOn.of_isCoveringMap_subtype hU hz ?_
    refine isCoveringMap_iff_isCoveringMapOn_univ.2 ?_
    refine hgp.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => ?_)
      hgl.isLocalHomeomorphOn
    have h2 : g ⁻¹' {x} = z ⁻¹' {(x : V n)} := by
      ext x'; simp [g, Subtype.ext_iff]
    rw [h2]; exact hfib x x.2
  · by_cases hy : y ∈ U
    · exact hfib y hy
    · convert Set.finite_empty
      ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h; exact hy (h ▸ hz x)

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem transition_zero_eq_one (A : WeightedAtlas n Y ι La) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) : A.g 0 i j y = 1 := by
  have h := A.g_add 0 0 i j y hi hj
  rw [add_zero] at h
  have hne := A.g_ne 0 i j y hi hj
  exact mul_left_cancel₀ hne ((h.symm).trans (mul_one _).symm)

theorem transition_nsmul_eq_pow (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    A.g (m • la) i j y = A.g la i j y ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, transition_zero_eq_one A i j y hi hj]
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]

theorem weight_zero_eq_zero (A : WeightedAtlas n Y ι La) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph 0 i y = 0 := by
  have h := A.ph_add 0 0 i y hi
  rw [add_zero] at h
  linarith

theorem weight_nsmul_eq_mul (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) : A.ph (m • la) i y = m * A.ph la i y := by
  induction m with
  | zero => rw [zero_nsmul, weight_zero_eq_zero A i y hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring

theorem ratio_pow_chart_independent (A : WeightedAtlas n Y ι La) (la : La) (m : ℕ) (F w0 : ι → Y → ℂ)
    (hF : A.IsSec (m • la) F) (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) :
    F i y / w0 i y ^ m = F j y / w0 j y ^ m := by
  rw [hF.2 i j y (Set.mem_univ y) hi hj, hw.2 i j y (Set.mem_univ y) hi hj,
    transition_nsmul_eq_pow A la m i j y hi hj, mul_pow]
  exact mul_div_mul_left _ _ (pow_ne_zero _ (A.g_ne la i j y hi hj))

theorem ne_zero_of_overlap_ne_zero (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (hw : A.IsSec la w0) (i j : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (hj : y ∈ (A.chart j).source) (h : w0 j y ≠ 0) :
    w0 i y ≠ 0 := by
  rw [hw.2 i j y (Set.mem_univ y) hi hj]
  exact mul_ne_zero (A.g_ne la i j y hi hj) h

theorem localCoordinates_eq_zmap (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) :
    A.zLoc w0 s i (A.chart i y) = A.zmap w0 s y := by
  simp only [zLoc, zmap, (A.chart i).left_inv hi]
  congr 1
  funext k
  have := ratio_pow_chart_independent A la 1 (s k) w0 (by rw [one_nsmul]; exact hs k) hw i (A.pick y) y hi
    (A.mem_pick y)
  simpa using this

end atlas

theorem holo_restrict_open {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n) (u : M → ℂ)
    (hu : Holo n z u) (S : Set M) (hS : IsOpen S) [Nonempty S] :
    Holo n (fun x : S => z x) (fun x : S => u x) := by
  intro e he
  let f := hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : S → M)
  have hc : IsChart n z (f.symm.trans e) := by
    intro x hx
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage, f, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hx
    obtain ⟨⟨x', rfl⟩, hx2⟩ := hx
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, f,
      hS.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv] at hx2 ⊢
    exact he hx2
  have h2 := hu _ hc
  have ht : (f.symm.trans e).target = e.target := by
    simp [f]
  rw [ht] at h2
  refine h2.congr (fun v hv => ?_)
  simp [f, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

theorem sub_isBigO_of_det_ne_zero {n : ℕ} {q : V n → V n} {D : V n →L[ℂ] V n} {a : V n}
    (hq : HasFDerivAt q D a) (hD : LinearMap.det (D : V n →ₗ[ℂ] V n) ≠ 0) :
    (fun x => x - a) =O[𝓝 a] (fun x => q x - q a) := by
  let E : V n ≃L[ℂ] V n :=
    (LinearMap.equivOfDetNeZero (D : V n →ₗ[ℂ] V n) hD).toContinuousLinearEquiv
  have hE : ∀ x, E x = D x := by
    intro x
    rfl
  have h1 : (fun x => x - a) =O[𝓝 a] (fun x => D (x - a)) := by
    simpa [hE] using E.isBigO_sub_rev (𝓝 a) a
  have h3 : (fun x => D (x - a) - (q x - q a)) =o[𝓝 a] (fun x => D (x - a)) := by
    have := (hq.isLittleO.trans_isBigO h1).neg_left
    refine this.congr_left (fun x => ?_)
    abel
  have h4 := h3.right_isBigO_sub
  refine h1.trans (h4.congr_right (fun x => ?_))
  abel

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem differentiableAt_localCoordinates (A : WeightedAtlas n Y ι La) (la : La) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (hw : A.IsSec la w0) (hs : ∀ k, A.IsSec la (s k)) (i : ι) (y : Y)
    (hi : y ∈ (A.chart i).source) (h0 : w0 i y ≠ 0) :
    DifferentiableAt ℂ (A.zLoc w0 s i) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hi)
  have hd : ∀ F : ι → Y → ℂ, A.IsSec la F →
      DifferentiableAt ℂ (fun v => F i ((A.chart i).symm v)) (A.chart i y) := by
    intro F hF
    have := hF.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact (this.differentiableAt hT)
  rw [differentiableAt_euclidean]
  intro k
  simp only [zLoc, PiLp.toLp_apply, div_eq_mul_inv]
  refine (hd (s k) (hs k)).mul ((hd w0 hw).inv ?_)
  simpa [(A.chart i).left_inv hi] using h0

end atlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem vanishing_order_transfer (A : WeightedAtlas n Y ι La) (L : La) (m : ℕ) (w0 : ι → Y → ℂ)
    (s : Fin n → ι → Y → ℂ) (Nsec : ι → Y → ℂ)
    (hw : A.IsSec L w0) (hs : ∀ k, A.IsSec L (s k)) (hN : A.IsSec (m • L) Nsec)
    (y : Y) (hy0 : w0 (A.pick y) y ≠ 0)
    (hdet : (fderiv ℂ (A.zLoc w0 s (A.pick y)) (A.chart (A.pick y) y)).det ≠ 0)
    (hvan : A.VanishOrd Nsec y (m + 1))
    {T : Type*} [TopologicalSpace T] (j : T → Y) (hj : Continuous j)
    (e : OpenPartialHomeomorph T (V n)) (he : Set.EqOn (fun t => A.zmap w0 s (j t)) e e.source)
    (t0 : T) (ht0 : t0 ∈ e.source) (hjt0 : j t0 = y) :
    ∃ C : ℝ, ∀ᶠ v in 𝓝 (e t0),
      ‖(fun t => Nsec (A.pick (j t)) (j t) / w0 (A.pick (j t)) (j t) ^ m) (e.symm v)‖ ≤
        C * ‖v - e t0‖ ^ (m + 1) := by
  set p := A.pick y with hp
  set c := A.chart p with hc
  set v0 := e t0 with hv0def
  have hy : y ∈ c.source := A.mem_pick y
  have hv0 : v0 ∈ e.target := e.map_source ht0
  have hsymm0 : e.symm v0 = t0 := e.left_inv ht0
  have hte : Tendsto (fun v => j (e.symm v)) (𝓝 v0) (𝓝 y) := by
    have h := (hj.continuousAt (x := e.symm v0)).tendsto.comp (e.continuousAt_symm hv0).tendsto
    rw [hsymm0, hjt0] at h
    exact h
  let φ := fun v => c (j (e.symm v))
  have htφ : Tendsto φ (𝓝 v0) (𝓝 (c y)) := (c.continuousAt hy).tendsto.comp hte
  have hev : ∀ᶠ v in 𝓝 v0, v ∈ e.target ∧ j (e.symm v) ∈ c.source :=
    (e.open_target.eventually_mem hv0).and (hte.eventually (c.open_source.eventually_mem hy))
  have hzφ : ∀ᶠ v in 𝓝 v0, A.zLoc w0 s p (φ v) = v := hev.mono fun v hv => by
    rw [localCoordinates_eq_zmap A L w0 s hw hs p _ hv.2]
    have := he (e.map_target hv.1)
    simp only at this
    rw [this, e.right_inv hv.1]
  have hUeq : ∀ᶠ v in 𝓝 v0,
      Nsec p (c.symm (φ v)) * (w0 p (c.symm (φ v)) ^ m)⁻¹ =
      (fun t => Nsec (A.pick (j t)) (j t) / w0 (A.pick (j t)) (j t) ^ m) (e.symm v) :=
    hev.mono fun v hv => by
      simp only [φ, c.left_inv hv.2]
      rw [ratio_pow_chart_independent A L m Nsec w0 hN hw (A.pick (j (e.symm v))) p _ (A.mem_pick _) hv.2,
        div_eq_mul_inv]
  have hN' : (fun w => Nsec p (c.symm w)) =O[𝓝 (c y)] (fun w => ‖w - c y‖ ^ (m + 1)) := by
    obtain ⟨C, hC⟩ := hvan
    exact IsBigO.of_bound C (hC.mono fun w hw => by rw [norm_pow, norm_norm]; exact hw)
  have hw0c : ContinuousAt (fun w => w0 p (c.symm w)) (c y) := by
    have := hw.1 p
    simp only [Set.preimage_univ, Set.inter_univ] at this
    exact (this.differentiableAt (c.open_target.mem_nhds (c.map_source hy))).continuousAt
  have hinv : (fun w => (w0 p (c.symm w) ^ m)⁻¹) =O[𝓝 (c y)] (fun _ => (1 : ℝ)) := by
    have : ContinuousAt (fun w => (w0 p (c.symm w) ^ m)⁻¹) (c y) :=
      (hw0c.pow m).inv₀ (by
        show w0 p (c.symm (c y)) ^ m ≠ 0
        rw [c.left_inv hy]; exact pow_ne_zero _ hy0)
    exact this.tendsto.isBigO_one ℝ
  have hG := (hN'.mul hinv).comp_tendsto htφ
  have hlow : (fun v => φ v - c y) =O[𝓝 v0] (fun v => v - v0) := by
    have hd := differentiableAt_localCoordinates A L w0 s hw hs p y hy hy0
    have h1 := (sub_isBigO_of_det_ne_zero hd.hasFDerivAt hdet).comp_tendsto htφ
    have hq0 : A.zLoc w0 s p (c y) = v0 := by
      rw [localCoordinates_eq_zmap A L w0 s hw hs p y hy, ← hjt0]; exact he ht0
    refine h1.congr' (Eventually.of_forall fun v => rfl) (hzφ.mono fun v hv => ?_)
    simp only [Function.comp_apply, hv]
    exact congrArg (v - ·) hq0
  have hfin : (fun v => Nsec p (c.symm (φ v)) * (w0 p (c.symm (φ v)) ^ m)⁻¹) =O[𝓝 v0]
      (fun v => ‖v - v0‖ ^ (m + 1)) := by
    refine hG.trans ?_
    have := hlow.norm_norm.pow (m + 1)
    exact this.congr_left (fun v => by simp [φ])
  obtain ⟨C, hC⟩ := isBigO_iff.1 (hfin.congr' hUeq EventuallyEq.rfl)
  refine ⟨C, hC.mono fun v hv => ?_⟩
  rwa [norm_pow, norm_norm] at hv

end atlas

section atlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem norm_section_ratio_le {N' : ℕ} (A : WeightedAtlas n Y ι La) (L : La) (m : ℕ)
    (w : Fin N' → ι → Y → ℂ) (w0 : ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (Nsec : ι → Y → ℂ)
    (C1 C2 : ℝ) (h1 : ∀ y, A.nsq (m • L) Nsec y ≤ C1 * A.sqn L w y ^ m)
    (h2 : ∀ y, A.sqn L w y ≤ C2 * (A.nsq L w0 y + A.sqn L s y)) (y : Y)
    (hy0 : w0 (A.pick y) y ≠ 0) :
    ‖Nsec (A.pick y) y / w0 (A.pick y) y ^ m‖ ≤
      Real.sqrt (max C1 0 * |C2| ^ m) * (1 + ‖A.zmap w0 s y‖ ^ 2) ^ ((m : ℝ) / 2) := by
  set p := A.pick y with hp
  set E := Real.exp (-A.ph L p y) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hw0n : 0 < ‖w0 p y‖ := norm_pos_iff.2 hy0
  set a := ‖w0 p y‖ ^ 2 * E with ha
  have ha0 : 0 < a := by positivity
  set t := 1 + ‖A.zmap w0 s y‖ ^ 2 with ht
  have ht0 : 0 < t := by positivity
  set U := Nsec p y / w0 p y ^ m with hU
  have hsq : A.sqn L s y = a * ‖A.zmap w0 s y‖ ^ 2 := by
    simp only [sqn, nsq, zmap, EuclideanSpace.norm_sq_eq, ← hp, ← hE, ha,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [norm_div]
    field_simp
  have hw0sq : A.nsq L w0 y = a := rfl
  have hNsq : A.nsq (m • L) Nsec y = ‖U‖ ^ 2 * a ^ m := by
    simp only [nsq, ← hp]
    rw [weight_nsmul_eq_mul A L m p y (A.mem_pick y), show -(↑m * A.ph L p y) = ↑m * (-A.ph L p y)
      by ring, Real.exp_nat_mul, ← hE, hU, ha, norm_div, norm_pow]
    field_simp
    ring_nf
  have hsqw : 0 ≤ A.sqn L w y :=
    Finset.sum_nonneg (fun k _ => by unfold nsq; positivity)
  have hle : ‖U‖ ^ 2 * a ^ m ≤ (max C1 0 * |C2| ^ m * t ^ m) * a ^ m := by
    rw [← hNsq]
    have hb : A.sqn L w y ≤ |C2| * (a * t) := by
      have := h2 y
      rw [hw0sq, hsq] at this
      calc A.sqn L w y ≤ C2 * (a + a * ‖A.zmap w0 s y‖ ^ 2) := this
        _ = C2 * (a * t) := by rw [ht]; ring
        _ ≤ |C2| * (a * t) := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    calc A.nsq (m • L) Nsec y ≤ C1 * A.sqn L w y ^ m := h1 y
      _ ≤ max C1 0 * A.sqn L w y ^ m :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hsqw m)
      _ ≤ max C1 0 * (|C2| * (a * t)) ^ m :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsqw hb m) (le_max_right _ _)
      _ = (max C1 0 * |C2| ^ m * t ^ m) * a ^ m := by ring
  have hle' : ‖U‖ ^ 2 ≤ max C1 0 * |C2| ^ m * t ^ m :=
    le_of_mul_le_mul_right hle (pow_pos ha0 m)
  have hK : 0 ≤ max C1 0 * |C2| ^ m := by positivity
  calc ‖U‖ = Real.sqrt (‖U‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (max C1 0 * |C2| ^ m * t ^ m) := Real.sqrt_le_sqrt hle'
    _ = Real.sqrt (max C1 0 * |C2| ^ m) * Real.sqrt (t ^ m) :=
        Real.sqrt_mul hK _
    _ = Real.sqrt (max C1 0 * |C2| ^ m) * t ^ ((m : ℝ) / 2) := by
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
        congr 1; ring

end atlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas Asymptotics
open scoped ContDiff ENNReal Pointwise Matrix

noncomputable section

universe u

theorem zero (n : ℕ) (Y : Type u) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La] (hNORM : NORMAll.{u} n) : ZEROStatement n Y ι La := by
  intro A L N w w0 s De m Nsec hconn hD hF hDe hwC hN hNC hvan
  obtain ⟨C2, hC2⟩ := hwC
  obtain ⟨C1, hC1⟩ := hNC
  set MS := A.Mset w0 s De with hMS
  have hw0 : A.IsSec L w0 := hD.isSection_denom
  have hs := hD.sec_s
  let Uf : Y → ℂ := fun y => Nsec (A.pick y) y / w0 (A.pick y) y ^ m

  have hHolo : Holo n (flatStein A hD hF).z (fun y : MS => Uf y) := by
    refine (holo_flat_iff A hD hF Uf).2 (fun i => ?_)
    have hNd := hN.1 i
    have hwd := hw0.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at hNd hwd
    have hne : ∀ v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' MS,
        ((w0 i ∘ (A.chart i).symm) v) ^ m ≠ 0 := fun v hv =>
      pow_ne_zero _ (ne_zero_of_overlap_ne_zero A L w0 hw0 i (A.pick _) _ ((A.chart i).map_target hv.1)
        (A.mem_pick _) hv.2.1)
    refine ((hNd.mono Set.inter_subset_left).mul
      (((hwd.mono Set.inter_subset_left).pow m).inv hne)).congr (fun v hv => ?_)
    simp only [Function.comp_apply, Uf]
    rw [ratio_pow_chart_independent A L m Nsec w0 hN hw0 (A.pick _) i _ (A.mem_pick _)
      ((A.chart i).map_target hv.1), div_eq_mul_inv]
    rfl
  let U : Set (V n) := {v : V n | MvPolynomial.eval (fun i => v i) De ≠ 0}
  have hUo : IsOpen U := isOpen_ne_fun
    ((MvPolynomial.continuous_eval (p := De)).comp (by fun_prop)) continuous_const

  have key : ∀ x0 : MS, Uf x0 = 0 := by
    intro x0
    have hM'o : IsOpen (connectedComponent x0) := by
      rw [isOpen_iff_mem_nhds]
      intro x hx
      obtain ⟨e, hxe, -⟩ := hF.localHomeo x
      have hTo : IsOpen (connectedComponentIn e.target (e x)) :=
        e.open_target.connectedComponentIn
      have hxT : e x ∈ connectedComponentIn e.target (e x) :=
        mem_connectedComponentIn (e.map_source hxe)
      have hTs : connectedComponentIn e.target (e x) ⊆ e.target := connectedComponentIn_subset _ _
      have hW : IsOpen (e.symm '' connectedComponentIn e.target (e x)) := by
        rw [e.symm_image_eq_source_inter_preimage hTs]
        exact e.isOpen_inter_preimage hTo
      have hWc : IsPreconnected (e.symm '' connectedComponentIn e.target (e x)) :=
        isPreconnected_connectedComponentIn.image _ (e.continuousOn_symm.mono hTs)
      have hxW : x ∈ e.symm '' connectedComponentIn e.target (e x) := ⟨e x, hxT, e.left_inv hxe⟩
      have hsub : e.symm '' connectedComponentIn e.target (e x) ⊆ connectedComponent x0 := by
        rw [connectedComponent_eq hx]
        exact hWc.subset_connectedComponent hxW
      exact Filter.mem_of_superset (hW.mem_nhds hxW) hsub
    have : Nonempty (connectedComponent x0) := ⟨⟨x0, mem_connectedComponent⟩⟩
    have : ConnectedSpace (connectedComponent x0) :=
      Subtype.connectedSpace isConnected_connectedComponent
    let z' : connectedComponent x0 → V n := fun x => A.zmap w0 s (x : MS)
    have hzU : ∀ x, z' x ∈ U := fun x => (x : MS).2.2
    have hloc : IsLocalHomeomorph z' :=
      hF.localHomeo.comp hM'o.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    have hprop : ∀ K : Set (V n), IsCompact K → K ⊆ U → IsCompact (z' ⁻¹' K) := by
      intro K hK hKU
      have h1 := hF.proper K hK (fun v hv => hKU hv)
      have h2 : IsCompact (Subtype.val ⁻¹' (A.zmap w0 s ⁻¹' K) : Set MS) := by
        rw [Subtype.isCompact_iff, Subtype.image_preimage_coe]
        exact h1
      have h3 : IsCompact (Subtype.val ⁻¹' (Subtype.val ⁻¹' (A.zmap w0 s ⁻¹' K) : Set MS) :
          Set (connectedComponent x0)) := by
        rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, Set.inter_comm]
        exact h2.inter_right isClosed_connectedComponent
      exact h3
    obtain ⟨hcov, hfin⟩ := isCoveringMapOn_of_proper z' U hUo hzU hloc hprop
    have hH' := holo_restrict_open _ _ hHolo (connectedComponent x0) hM'o
    have hbd : ∀ x : connectedComponent x0, ‖Uf ((x : MS) : Y)‖ ≤
        Real.sqrt (max C1 0 * |C2| ^ m) * (1 + ‖z' x‖ ^ 2) ^ ((m : ℝ) / 2) := fun x =>
      norm_section_ratio_le A L m w w0 s Nsec C1 C2 hC1 hC2 _ (x : MS).2.1
    have hv' : ∀ x : connectedComponent x0, z' x = 0 →
        VanishesBeyond n z' (fun x : connectedComponent x0 => Uf ((x : MS) : Y)) x m := by
      intro x hx e he hxe k hk
      have hyS : ((x : MS) : Y) ∈ A.zeroSet s := by
        intro k'
        have h := congrArg (fun v : V n => v k') hx
        simp only [z', zmap, PiLp.toLp_apply, PiLp.zero_apply] at h
        exact (div_eq_zero_iff.1 h).resolve_right (x : MS).2.1
      obtain ⟨C, hC⟩ := vanishing_order_transfer A L m w0 s Nsec hw0 hs hN ((x : MS) : Y) (x : MS).2.1
        (hF.deriv_ne _ (x : MS).2) (hvan _ hyS)
        (fun t : connectedComponent x0 => ((t : MS) : Y))
        (continuous_subtype_val.comp continuous_subtype_val) e he x hxe rfl
      have hex : z' x = e x := he hxe
      rw [hex]
      exact iteratedFDeriv_eq_zero_of_bound _ e.target (e x) e.open_target (e.map_source hxe)
        (hH' e he) m ⟨C, hC⟩ k hk
    have hzero := hNORM (connectedComponent x0) z' De
      (fun x : connectedComponent x0 => Uf ((x : MS) : Y)) (Real.sqrt (max C1 0 * |C2| ^ m)) m
      hDe hcov hzU hfin ‹_› hH' hbd hv'
    exact congrFun hzero ⟨x0, mem_connectedComponent⟩

  intro i y hy
  have hzM : ∀ y' ∈ (A.chart i).source ∩ MS, Nsec i y' = 0 := by
    intro y' hy'
    have h := key ⟨y', hy'.2⟩
    simp only [Uf] at h
    have h0 : Nsec (A.pick y') y' = 0 :=
      (div_eq_zero_iff.1 h).resolve_right (pow_ne_zero _ hy'.2.1)
    rw [hN.2 i (A.pick y') y' (Set.mem_univ _) hy'.1 (A.mem_pick y'), h0, mul_zero]
  have hcont : ContinuousOn (Nsec i) (A.chart i).source := by
    have hNd := hN.1 i
    simp only [Set.preimage_univ, Set.inter_univ] at hNd
    refine (hNd.continuousOn.comp (A.chart i).continuousOn (fun y hy => (A.chart i).map_source hy)).congr
      (fun y hy => ?_)
    simp [(A.chart i).left_inv hy]
  have hEq := Set.EqOn.of_subset_closure (f := Nsec i) (g := fun _ => (0 : ℂ)) hzM hcont
    continuousOn_const Set.inter_subset_left
    ((dense_Mset A hD hF).open_subset_closure_inter (A.chart i).open_source)
  exact hEq hy

end

end ReciprocityTheory.L2DbarEstimates.Y
end

section -- merged from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxL
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal

noncomputable section

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

theorem aap_continuous_nsq (la : La) (u : ι → Y → ℂ)
    (hcoc : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → u i y = A.g la i j y * u j y)
    (hc : ∀ i, ContinuousOn (u i ∘ (A.chart i).symm) (A.chart i).target) :
    Continuous (A.nsq la u) := by
  have hloc : ∀ i y, y ∈ (A.chart i).source →
      A.nsq la u y = ‖u i y‖ ^ 2 * Real.exp (-A.ph la i y) := by
    intro i y hy
    have hg := A.g_ne la (A.pick y) i y (A.mem_pick y) hy
    have ht := A.ph_trans la (A.pick y) i y (A.mem_pick y) hy
    have hg2 : 0 < ‖A.g la (A.pick y) i y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
    have hp : A.ph la (A.pick y) y = A.ph la i y + Real.log (‖A.g la (A.pick y) i y‖ ^ 2) := by
      linarith
    unfold nsq
    rw [hcoc (A.pick y) i y (A.mem_pick y) hy, hp, norm_mul, mul_pow, neg_add, Real.exp_add,
      Real.exp_neg (Real.log _), Real.exp_log hg2]
    field_simp
  rw [continuous_iff_continuousAt]
  intro y0
  have hy0 : y0 ∈ (A.chart (A.pick y0)).source := A.mem_pick y0
  have hs : (A.chart (A.pick y0)).source ∈ 𝓝 y0 := (A.chart (A.pick y0)).open_source.mem_nhds hy0
  have hu : ContinuousOn (u (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (hc (A.pick y0)).comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hph : ContinuousOn (A.ph la (A.pick y0)) (A.chart (A.pick y0)).source := by
    have h1 := (A.smooth_ph la (A.pick y0)).continuousOn.comp (A.chart (A.pick y0)).continuousOn
      (fun y hy => (A.chart (A.pick y0)).map_source hy)
    exact h1.congr fun y hy => by simp [(A.chart (A.pick y0)).left_inv hy]
  have hf : ContinuousOn (fun y => ‖u (A.pick y0) y‖ ^ 2 * Real.exp (-A.ph la (A.pick y0) y))
      (A.chart (A.pick y0)).source :=
    (hu.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  exact (hf.congr fun y hy => hloc (A.pick y0) y hy).continuousAt hs

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

namespace ReciprocityTheory.L2DbarEstimates.Y

section
variable (n : ℕ) (Y : Type*) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] (ι : Type*) (La : Type*) [AddCommGroup La]

end

theorem four_sign_holds (f : ℕ) : FOURSignStatement f :=
  four_sign f (four_indep f) (four_bound f)

end ReciprocityTheory.L2DbarEstimates.Y
