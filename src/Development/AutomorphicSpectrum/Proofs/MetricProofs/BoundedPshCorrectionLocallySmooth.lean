module

public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshPoisson
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChart
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChart
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_eq_zero_of_compatChart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
    (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ →
    IsOpen U → A.SmoothOn U g →
    (∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, ∀ w,
      levi (g ∘ (A.chart j).symm) y w = 0) →
    ∀ z ∈ ψ.target, ψ.symm z ∈ U → ∀ w, levi (g ∘ ψ.symm) z w = 0 := by
  intro e X _ A ψ U g hψ hU hg hA z hz hzU w
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hzs : z ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source := ⟨hz, hj⟩
  have hopen : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
    ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (A.chart j).open_source
  have hτ : AnalyticAt ℂ (⇑(A.chart j) ∘ ⇑ψ.symm) z := (hψ j).2 z hzs
  have hEq : g ∘ ⇑ψ.symm =ᶠ[𝓝 z] (g ∘ ⇑(A.chart j).symm) ∘ (⇑(A.chart j) ∘ ⇑ψ.symm) := by
    filter_upwards [hopen.mem_nhds hzs] with y hy
    simp only [Function.comp_apply, (A.chart j).left_inv hy.2]
  have hcz : (⇑(A.chart j) ∘ ⇑ψ.symm) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    simp only [Set.mem_preimage, Function.comp_apply, (A.chart j).left_inv hj]
    exact hzU
  have hopen2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hU
  have hsm : ContDiffAt ℝ 2 (g ∘ ⇑(A.chart j).symm) ((⇑(A.chart j) ∘ ⇑ψ.symm) z) :=
    ((hg j).contDiffAt (hopen2.mem_nhds hcz)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | simp | norm_num | exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  rw [levi_congr hEq w, levi_comp w hτ hsm]
  exact hA j _ hcz _

end GlobalTheory.CompanionTheory.LeviChart
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviZeroInCompatibleChartStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_zero_in_compatible_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ → IsOpen U → A.SmoothOn U g → (∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, ∀ w, levi (g ∘ (A.chart j).symm) y w = 0) → ∀ z ∈ ψ.target, ψ.symm z ∈ U → ∀ w, levi (g ∘ ψ.symm) z w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart | exact GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart | (intros; apply GlobalTheory.CompanionTheory.LeviChart.levi_eq_zero_of_compatChart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonic
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PoissonIntegralPuncturedDisc
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrinciple
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrinciple
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem harmonic_eventually_eq_of_ball_le {h : ℂ → ℝ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hh : InnerProductSpace.HarmonicOnNhd h (Metric.ball z₀ r))
    (hle : ∀ z ∈ Metric.ball z₀ r, h z ≤ h z₀) : ∀ᶠ z in 𝓝 z₀, h z = h z₀ := by
  obtain ⟨F, hF, hre⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hh
  have hz₀ : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr
  have hball : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hnorm : ∀ z ∈ Metric.ball z₀ r, ‖Complex.exp (F z)‖ = Real.exp (h z) := fun z hz => by
    rw [Complex.norm_exp]
    exact congrArg Real.exp (hre hz)
  have hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (F z)) z₀ := by
    filter_upwards [hball] with z hz
    simp only [Function.comp_apply]
    rw [hnorm z hz, hnorm z₀ hz₀]
    exact Real.exp_le_exp.2 (hle z hz)
  filter_upwards [Complex.eventually_eq_of_isLocalMax_norm hdiff hmax, hball] with z hz hzb
  have h1 := congrArg norm hz
  rw [hnorm z hzb, hnorm z₀ hz₀] at h1
  exact Real.exp_injective h1

theorem harmonic_annulus_le_zero : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b →
    ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} →
    (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) →
    (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) →
    ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  intro h a b ha hab hc hh hb z hz1 hz2
  by_contra hpos
  push Not at hpos
  set K : Set ℂ := {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} with hK
  have hKclosed : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hKcomp : IsCompact K :=
    (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset hKclosed
      (fun w hw => by simpa using hw.2)
  have hzK : z ∈ K := ⟨hz1, hz2⟩
  obtain ⟨z₁, hz₁K, hz₁⟩ := hKcomp.exists_isMaxOn ⟨z, hzK⟩ hc
  set S : Set ℂ := K ∩ h ⁻¹' {h z₁} with hS
  have hSclosed : IsClosed S :=
    hc.preimage_isClosed_of_isClosed hKclosed isClosed_singleton
  have hScomp : IsCompact S := hKcomp.of_isClosed_subset hSclosed Set.inter_subset_left
  obtain ⟨z₀, hz₀S, hz₀⟩ :=
    hScomp.exists_isMaxOn ⟨z₁, hz₁K, rfl⟩ (continuous_norm.continuousOn (s := S))
  have hz₀K : z₀ ∈ K := hz₀S.1
  have hval : h z₀ = h z₁ := hz₀S.2
  have hMpos : 0 < h z₀ := hval ▸ hpos.trans_le (hz₁ hzK)
  have hlo : a < ‖z₀‖ := lt_of_le_of_ne hz₀K.1 fun e => absurd (hb z₀ (Or.inl e.symm)) (not_le.2 hMpos)
  have hhi : ‖z₀‖ < b := lt_of_le_of_ne hz₀K.2 fun e => absurd (hb z₀ (Or.inr e)) (not_le.2 hMpos)
  have hUopen : IsOpen {w : ℂ | a < ‖w‖ ∧ ‖w‖ < b} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUopen z₀ ⟨hlo, hhi⟩
  have hloc : ∀ᶠ w in 𝓝 z₀, h w = h z₀ := by
    refine harmonic_eventually_eq_of_ball_le hr (fun w hw => hh w (hrU hw).1 (hrU hw).2) ?_
    intro w hw
    rw [hval]
    exact hz₁ ⟨(hrU hw).1.le, (hrU hw).2.le⟩
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1
    (hloc.and (hUopen.mem_nhds ⟨hlo, hhi⟩))
  have hz₀pos : 0 < ‖z₀‖ := ha.trans hlo

  set t : ℝ := ε / (2 * ‖z₀‖) with ht
  have htpos : 0 < t := by positivity
  set w : ℂ := ((1 + t : ℝ) : ℂ) * z₀ with hw
  have hwnorm : ‖w‖ = (1 + t) * ‖z₀‖ := by
    rw [hw, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hdist : dist w z₀ < ε := by
    have e : w - z₀ = (t : ℂ) * z₀ := by
      rw [hw]; push_cast; ring
    rw [dist_eq_norm, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg htpos.le, ht]
    have : ε / (2 * ‖z₀‖) * ‖z₀‖ = ε / 2 := by field_simp
    rw [this]
    linarith
  obtain ⟨hwval, hwU⟩ := hεb w hdist
  have hwS : w ∈ S := ⟨⟨hwU.1.le, hwU.2.le⟩, by simpa [hval] using hwval⟩
  have hle : ‖w‖ ≤ ‖z₀‖ := hz₀ hwS
  rw [hwnorm] at hle
  nlinarith [mul_pos htpos hz₀pos]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.HarmonicAnnulusMaximumPrincipleStatement
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonic_annulus_maximum_principle : ∀ (h : ℂ → ℝ) (a b : ℝ), 0 < a → a < b → ContinuousOn h {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} → (∀ z : ℂ, a < ‖z‖ → ‖z‖ < b → InnerProductSpace.HarmonicAt h z) → (∀ z : ℂ, (‖z‖ = a ∨ ‖z‖ = b) → h z ≤ 0) → ∀ z : ℂ, a ≤ ‖z‖ → ‖z‖ ≤ b → h z ≤ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.harmonic_annulus_le_zero <;> assumption)
end
end

open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PuncturedDisc

theorem le_zero_of_bddAbove_punctured (g : ℂ → ℝ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hc : ContinuousOn g {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ})
    (hh : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt g z)
    (h0 : ∀ z : ℂ, ‖z‖ = ρ → g z ≤ 0)
    (hC : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → g z ≤ C) :
    ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < ρ → g w ≤ 0 := by
  intro w hw0 hwρ
  have hlogw : Real.log ‖w‖ < Real.log ρ := Real.log_lt_log hw0 hwρ
  have hD : 0 < Real.log ρ - Real.log ‖w‖ := sub_pos.mpr hlogw
  have key : ∀ ε : ℝ, 0 < ε → g w ≤ ε * (Real.log ρ - Real.log ‖w‖) := by
    intro ε hε
    have hexp_pos : 0 < Real.exp (-(|C| / ε)) := Real.exp_pos _
    have hexp_le : Real.exp (-(|C| / ε)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ |C| / ε := div_nonneg (abs_nonneg C) hε.le
      linarith
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ‖w‖ * Real.exp (-(|C| / ε)) / 2 := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hr_def]
      exact div_pos (mul_pos hw0 hexp_pos) two_pos
    have hrw : r < ‖w‖ := by
      have := mul_le_mul_of_nonneg_left hexp_le hw0.le
      rw [hr_def]
      linarith
    have hrρ : r < ρ := lt_trans hrw hwρ
    have hlogr : Real.log r = Real.log ‖w‖ - |C| / ε - Real.log 2 := by
      rw [hr_def, Real.log_div (mul_pos hw0 hexp_pos).ne' two_ne_zero,
        Real.log_mul hw0.ne' hexp_pos.ne', Real.log_exp]
      ring
    let h : ℂ → ℝ := fun z => g z - ε * (Real.log ρ - Real.log ‖z‖)
    have hcont : ContinuousOn h {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} := by
      have hsub : {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} :=
        fun z hz => ⟨lt_of_lt_of_le hr0 hz.1, hz.2⟩
      refine (hc.mono hsub).sub (continuousOn_const.mul (continuousOn_const.sub ?_))
      refine ContinuousOn.log continuous_norm.continuousOn ?_
      intro z hz
      exact (lt_of_lt_of_le hr0 hz.1).ne'
    have hharm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < ρ → InnerProductSpace.HarmonicAt h z := by
      intro z hz1 hz2
      have hz0 : 0 < ‖z‖ := lt_trans hr0 hz1
      have hlog : InnerProductSpace.HarmonicAt (fun y : ℂ => Real.log ‖y‖) z :=
        analyticAt_id.harmonicAt_log_norm (norm_pos_iff.mp hz0)
      have hcst : InnerProductSpace.HarmonicAt (fun _ : ℂ => Real.log ρ) z :=
        InnerProductSpace.harmonicAt_const _
      have h2 : InnerProductSpace.HarmonicAt
          (ε • ((fun _ : ℂ => Real.log ρ) - fun y : ℂ => Real.log ‖y‖)) z := by
        apply InnerProductSpace.HarmonicAt.const_smul
        exact hcst.sub hlog
      exact (hh z hz0 hz2).sub h2
    have hbdry : ∀ z : ℂ, ‖z‖ = r ∨ ‖z‖ = ρ → h z ≤ 0 := by
      intro z hz
      rcases hz with hz | hz
      · have hgz : g z ≤ C := hC z (by rw [hz]; exact hr0) (by rw [hz]; exact hrρ.le)
        have hCabs : C ≤ |C| := le_abs_self C
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
        show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, hlogr]
        have e1 : ε * (Real.log ρ - (Real.log ‖w‖ - |C| / ε - Real.log 2)) =
            ε * (Real.log ρ - Real.log ‖w‖) + ε * (|C| / ε) + ε * Real.log 2 := by ring
        have e2 : ε * (|C| / ε) = |C| := by field_simp
        rw [e1, e2]
        linarith [mul_pos hε hD, mul_pos hε hlog2]
      · show g z - ε * (Real.log ρ - Real.log ‖z‖) ≤ 0
        rw [hz, sub_self, mul_zero, sub_zero]
        exact h0 z hz
    have hmax := GlobalTheory.T.harmonic_annulus_maximum_principle h r ρ hr0 hrρ hcont hharm hbdry w hrw.le hwρ.le
    simp only [h] at hmax
    linarith
  by_contra hneg
  have hpos := not_le.mp hneg
  have hk := key (g w / (2 * (Real.log ρ - Real.log ‖w‖))) (div_pos hpos (mul_pos two_pos hD))
  have e3 : g w / (2 * (Real.log ρ - Real.log ‖w‖)) * (Real.log ρ - Real.log ‖w‖) = g w / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hD.ne']
  linarith

theorem poisson_formula_punctured (f : ℂ → ℝ) (ρ R M : ℝ) (hρ : 0 < ρ) (hρR : ρ < R)
    (hH : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → InnerProductSpace.HarmonicAt f z)
    (hB : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → |f z| ≤ M) (w : ℂ) (hw0 : w ≠ 0) (hwρ : ‖w‖ < ρ) :
    ∫ t, pker ρ w t * f (circleMap 0 ρ t) ∂angMeas = f w := by
  have hρabs : |ρ| = ρ := abs_of_pos hρ
  have hfc : ContinuousOn f (Metric.sphere 0 ρ) := by
    intro z hz
    have hz' : ‖z‖ = ρ := by simpa using hz
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz'
      linarith
    exact (hH z hz0 (by rw [hz']; exact hρR)).1.continuousAt.continuousWithinAt
  have hPbd : ∀ z : ℂ, ‖z‖ < ρ → |ReciprocityTheory.AnForm.A.poissonInt f ρ z| ≤ M := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hup := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb M
    have hlo := ReciprocityTheory.AnForm.A.poissonInt_sub hρ hfc hzb (-M)
    have hsph : ∀ x ∈ Metric.sphere (0 : ℂ) |ρ|, |f x| ≤ M ∧ 0 ≤ poissonKernel 0 z x := by
      intro x hx
      rw [hρabs] at hx
      have hx' : ‖x‖ = ρ := by simpa using hx
      have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx'
        linarith
      exact ⟨hB x hx0 (by rw [hx']; exact hρR), ReciprocityTheory.AnForm.A.poissonKernel_zero_nonneg hzb hx⟩
    have h1 : 0 ≤ Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).2
        have : 0 ≤ poissonKernel 0 z x * (M - f x) := mul_nonneg hk (by linarith)
        linarith
    have h1' : Real.circleAverage (fun x => -(poissonKernel 0 z x * (f x - M))) 0 ρ =
        -Real.circleAverage (fun x => poissonKernel 0 z x * (f x - M)) 0 ρ := by
      simp only [Real.circleAverage, intervalIntegral.integral_neg, smul_neg]
    have h2 : 0 ≤ Real.circleAverage (fun x => poissonKernel 0 z x * (f x - -M)) 0 ρ :=
      Real.circleAverage_nonneg_of_nonneg fun x hx => by
        obtain ⟨hb, hk⟩ := hsph x hx
        have := (abs_le.mp hb).1
        exact mul_nonneg hk (by linarith)
    rw [abs_le]
    constructor <;> linarith
  let Φ : ℂ → ℝ := fun z => if ‖z‖ < ρ then ReciprocityTheory.AnForm.A.poissonInt f ρ z else f z
  have hPharm : ∀ z : ℂ, ‖z‖ < ρ → InnerProductSpace.HarmonicAt Φ z := by
    intro z hz
    have hzb : z ∈ Metric.ball (0 : ℂ) ρ := by simpa using hz
    have hev : Φ =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.poissonInt f ρ := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with y hy
      have : ‖y‖ < ρ := by simpa using hy
      simp only [Φ, if_pos this]
    exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr
      (ReciprocityTheory.AnForm.A.poissonInt_harmonicAt hρ hfc hzb)
  have hΦcont : ContinuousOn Φ (Metric.closedBall 0 ρ) := by
    intro z hz
    by_cases hzl : ‖z‖ < ρ
    · exact (hPharm z hzl).1.continuousAt.continuousWithinAt
    · have hzle : ‖z‖ ≤ ρ := by simpa using hz
      have hzeq : ‖z‖ = ρ := le_antisymm hzle (not_lt.mp hzl)
      have hzs : z ∈ Metric.sphere (0 : ℂ) ρ := by simpa using hzeq
      have hΦz : Φ z = f z := by simp only [Φ, if_neg hzl]
      rw [← Metric.ball_union_sphere]
      apply ContinuousWithinAt.union
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (ReciprocityTheory.AnForm.A.poissonInt_tendsto hρ hfc hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have : ‖y‖ < ρ := by simpa using hy
        simp only [Φ, if_pos this]
      · rw [ContinuousWithinAt, hΦz]
        refine Filter.Tendsto.congr' ?_ (hfc z hzs)
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy' : ‖y‖ = ρ := by simpa using hy
        simp only [Φ, if_neg (not_lt.mpr hy'.ge)]
  have hΦb : ∀ z : ℂ, ‖z‖ = ρ → Φ z = f z := by
    intro z hz
    simp only [Φ, if_neg (not_lt.mpr hz.ge)]
  have hS : {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} ⊆ Metric.closedBall 0 ρ := fun z hz => by
    simpa using hz.2
  have hfS : ContinuousOn f {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ ≤ ρ} := fun z hz =>
    (hH z (norm_pos_iff.mp hz.1) (lt_of_le_of_lt hz.2 hρR)).1.continuousAt.continuousWithinAt
  have hΦbd : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ρ → |Φ z| ≤ M := by
    intro z hz0 hzρ
    by_cases hzl : ‖z‖ < ρ
    · simp only [Φ, if_pos hzl]
      exact hPbd z hzl
    · simp only [Φ, if_neg hzl]
      exact hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR)
  have hA := le_zero_of_bddAbove_punctured (fun z => f z - Φ z) ρ (2 * M) hρ
    (hfS.sub (hΦcont.mono hS))
    (fun z hz0 hzρ => (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)).sub (hPharm z hzρ))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hA' := le_zero_of_bddAbove_punctured (fun z => Φ z - f z) ρ (2 * M) hρ
    ((hΦcont.mono hS).sub hfS)
    (fun z hz0 hzρ => (hPharm z hzρ).sub (hH z (norm_pos_iff.mp hz0) (lt_trans hzρ hρR)))
    (fun z hz => by simp only [hΦb z hz, sub_self, le_refl])
    (fun z hz0 hzρ => by
      have h1 := abs_le.mp (hB z (norm_pos_iff.mp hz0) (lt_of_le_of_lt hzρ hρR))
      have h2 := abs_le.mp (hΦbd z hz0 hzρ)
      linarith [h1.1, h1.2, h2.1, h2.2])
    w (norm_pos_iff.mpr hw0) hwρ
  have hΦw : Φ w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by simp only [Φ, if_pos hwρ]
  have hfw : f w = ReciprocityTheory.AnForm.A.poissonInt f ρ w := by linarith
  rw [hfw]
  have hint := GlobalTheory.CompanionTheory.Ar.PB.Flat.integral_angMeas (fun z => poissonKernel 0 w z * f z) ρ
  exact hint

end GlobalTheory.CompanionTheory.Ar.PuncturedDisc
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonic
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem pker_eq {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (t : ℝ) :
    pker ρ w t = (ρ ^ 2 - ‖w‖ ^ 2) / ‖circleMap 0 ρ t - w‖ ^ 2 := by
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  simp only [pker, poissonKernel_def, sub_zero, h]

theorem sub_le_norm_circleMap_sub {ρ : ℝ} (hρ : 0 < ρ) (w : ℂ) (t : ℝ) :
    ρ - ‖w‖ ≤ ‖circleMap 0 ρ t - w‖ := by
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  have h2 := norm_sub_norm_le (circleMap (0 : ℂ) ρ t) w
  rwa [h] at h2

theorem continuous_pker {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ < ρ) :
    Continuous (pker ρ w) := by
  have h : pker ρ w = fun t => (ρ ^ 2 - ‖w‖ ^ 2) / ‖circleMap 0 ρ t - w‖ ^ 2 :=
    funext (pker_eq hρ w)
  rw [h]
  refine continuous_const.div
    (((continuous_circleMap 0 ρ).sub continuous_const).norm.pow 2) ?_
  intro t
  have h1 := sub_le_norm_circleMap_sub hρ w t
  have h2 : 0 < ‖circleMap (0 : ℂ) ρ t - w‖ := by linarith
  positivity

theorem exists_abs_pker_le {ρ : ℝ} (hρ : 0 < ρ) {w : ℂ} (hw : ‖w‖ < ρ) :
    ∃ K : ℝ, ∀ t, |pker ρ w t| ≤ K := by
  refine ⟨(ρ ^ 2 - ‖w‖ ^ 2) / (ρ - ‖w‖) ^ 2, fun t => ?_⟩
  have h1 := sub_le_norm_circleMap_sub hρ w t
  have h0 : 0 < ρ - ‖w‖ := by linarith
  have hn : 0 ≤ ρ ^ 2 - ‖w‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg w) hw.le 2
    linarith
  rw [pker_eq hρ, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left hn (by positivity) (pow_le_pow_left₀ h0.le h1 2)

theorem continuous_torusPt {n : ℕ} (ρ : ℝ) : Continuous (torusPt (n := n) ρ) :=
  continuous_pi fun i => (continuous_circleMap 0 ρ).comp (continuous_apply i)

theorem circleMap_mem {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (t : ℝ) :
    circleMap (0 : ℂ) ρ t ≠ 0 ∧ ‖circleMap (0 : ℂ) ρ t‖ < R := by
  refine ⟨circleMap_ne_center hρ.ne', ?_⟩
  have h : ‖circleMap (0 : ℂ) ρ t‖ = ρ := by simp [abs_of_pos hρ]
  rwa [h]

theorem torusPt_mem_punct {n : ℕ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (θ : Fin n → ℝ) :
    torusPt ρ θ ∈ punct R := fun i => circleMap_mem hρ hρR (θ i)

theorem cons_mem_punct {n : ℕ} {R : ℝ} {c : ℂ} {y : Fin n → ℂ} (hc : c ≠ 0 ∧ ‖c‖ < R)
    (hy : y ∈ punct R) : (Fin.cons c y : Fin (n + 1) → ℂ) ∈ punct R := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hc
  · simpa using hy j

theorem continuous_cons_pair {n : ℕ} {α : Type*} [TopologicalSpace α] :
    Continuous (fun p : α × (Fin n → α) => (Fin.cons p.1 p.2 : Fin (n + 1) → α)) := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using continuous_fst
  · simp only [Fin.cons_succ]
    exact (continuous_apply j).comp continuous_snd

theorem integral_pi_cons {n : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (hF : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
      (angMeas.prod (Measure.pi fun _ : Fin n => angMeas))) :
    ∫ θ, F θ ∂(Measure.pi fun _ : Fin (n + 1) => angMeas) =
      ∫ t, ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) ∂angMeas := by
  have mp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
      (angMeas.prod (Measure.pi fun _ : Fin n => angMeas))
      (Measure.pi fun _ : Fin (n + 1) => angMeas) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => angMeas) 0).symm _
  have he : ∀ p : ℝ × (Fin n → ℝ),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p =
        Fin.cons p.1 p.2 := by
    rintro ⟨a, b⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [MeasurableEquiv.piFinSuccAbove]
  rw [← mp.integral_comp']
  simp only [he]
  exact integral_prod _ hF

theorem polyPoisson_eq_self : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R →
    ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) →
    ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  intro n
  induction n with
  | zero =>
    intro f ρ R M _ _ _ _ _ z _
    have h : ∀ θ : Fin 0 → ℝ, (∏ i, pker ρ (z i) (θ i)) * f (torusPt ρ θ) = f z := by
      intro θ
      simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
      rw [Subsingleton.elim (torusPt ρ θ) z]
    simp only [polyPoisson, h]
    simp
  | succ n ih =>
    intro f ρ R M hρ hρR hc hs hb z hz
    have hz0 := hz 0
    have hzt : Fin.tail z ∈ punct ρ := fun i => hz i.succ
    have hztR : Fin.tail z ∈ punct R := fun i => ⟨(hzt i).1, (hzt i).2.trans hρR⟩
    have hslice : ∀ t, polyPoisson ρ (fun y => f (Fin.cons (circleMap 0 ρ t) y)) (Fin.tail z) =
        f (Fin.cons (circleMap 0 ρ t) (Fin.tail z)) := by
      intro t
      have hcm := circleMap_mem (t := t) hρ hρR
      refine ih _ ρ R M hρ hρR ?_ ?_ ?_ _ hzt
      · have hcont : Continuous (fun y : Fin n → ℂ =>
            (Fin.cons (circleMap 0 ρ t) y : Fin (n + 1) → ℂ)) :=
          continuous_cons_pair.comp (continuous_const.prodMk continuous_id)
        exact hc.comp hcont.continuousOn (fun y hy => cons_mem_punct hcm hy)
      · intro y hy i
        have h := hs _ (cons_mem_punct hcm hy) i.succ
        simp only [Fin.cons_succ] at h
        simpa only [Fin.cons_update] using h
      · exact fun y hy => hb _ (cons_mem_punct hcm hy)
    have hone := GlobalTheory.CompanionTheory.Ar.PuncturedDisc.poisson_formula_punctured (fun w => f (Fin.cons w (Fin.tail z))) ρ R M hρ hρR
      (fun w hw0 hwR => by
        have h := hs _ (cons_mem_punct ⟨hw0, hwR⟩ hztR) 0
        simpa only [Fin.update_cons_zero, Fin.cons_zero] using h)
      (fun w hw0 hwR => hb _ (cons_mem_punct ⟨hw0, hwR⟩ hztR))
      (z 0) hz0.1 hz0.2
    simp only [Fin.cons_self_tail] at hone
    set F : (Fin (n + 1) → ℝ) → ℝ :=
      fun θ => (∏ i, pker ρ (z i) (θ i)) * f (torusPt ρ θ) with hFdef
    have hFc : Continuous F :=
      (continuous_finsetProd _ fun i _ =>
        (continuous_pker hρ (hz i).2).comp (continuous_apply i)).mul
      (hc.comp_continuous (continuous_torusPt ρ) (torusPt_mem_punct hρ hρR))
    have hFb : ∃ K, ∀ θ, |F θ| ≤ K := by
      choose K hK using fun i => exists_abs_pker_le hρ (hz i).2
      refine ⟨(∏ i, K i) * M, fun θ => ?_⟩
      rw [hFdef]
      simp only [abs_mul, Finset.abs_prod]
      have hM : 0 ≤ M := (abs_nonneg _).trans (hb _ (torusPt_mem_punct hρ hρR θ))
      have hK0 : 0 ≤ ∏ i, K i :=
        Finset.prod_nonneg fun i _ => (abs_nonneg _).trans (hK i 0)
      exact mul_le_mul
        (Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hK i _))
        (hb _ (torusPt_mem_punct hρ hρR θ)) (abs_nonneg _) hK0
    obtain ⟨K, hK⟩ := hFb
    have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => F (Fin.cons p.1 p.2))
        (angMeas.prod (Measure.pi fun _ : Fin n => angMeas)) :=
      Integrable.of_bound (hFc.comp continuous_cons_pair).aestronglyMeasurable K
        (ae_of_all _ fun p => hK _)
    have hFcons : ∀ t θ', F (Fin.cons t θ') = pker ρ (z 0) t *
        ((∏ i, pker ρ (Fin.tail z i) (θ' i)) *
          f (Fin.cons (circleMap 0 ρ t) (torusPt ρ θ'))) := by
      intro t θ'
      have ht : torusPt ρ (Fin.cons t θ' : Fin (n + 1) → ℝ) =
          Fin.cons (circleMap 0 ρ t) (torusPt ρ θ') := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusPt]
      simp only [hFdef, ht, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail, mul_assoc]
    calc polyPoisson ρ f z
        = ∫ t, ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) ∂angMeas :=
          integral_pi_cons F hint
      _ = ∫ t, pker ρ (z 0) t * f (Fin.cons (circleMap 0 ρ t) (Fin.tail z)) ∂angMeas := by
          refine integral_congr_ae (ae_of_all _ fun t => ?_)
          have h : ∫ θ', F (Fin.cons t θ') ∂(Measure.pi fun _ : Fin n => angMeas) =
              pker ρ (z 0) t *
                polyPoisson ρ (fun y => f (Fin.cons (circleMap 0 ρ t) y)) (Fin.tail z) := by
            simp only [hFcons]
            rw [integral_const_mul]
            rfl
          simp only [h, hslice t]
      _ = f z := hone

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonReproducesHarmonicStatement
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_poisson_reproduces_harmonic : ∀ (n : ℕ) (f : (Fin n → ℂ) → ℝ) (ρ R M : ℝ), 0 < ρ → ρ < R → ContinuousOn f (punct R) → SepHarm R f → (∀ z ∈ punct R, |f z| ≤ M) → ∀ z ∈ punct ρ, polyPoisson ρ f z = f z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.polyPoisson_eq_self <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmooth
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth

theorem contDiffOn_pker {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffOn ℝ ∞ (fun q : ℂ × ℝ => pker ρ q.1 q.2)
      (Metric.ball (0 : ℂ) ρ ×ˢ (Set.univ : Set ℝ)) := by
  have hc : ContDiff ℝ ∞ (fun q : ℂ × ℝ => circleMap 0 ρ q.2) := (contDiff_circleMap 0 ρ).comp contDiff_snd
  have e : (fun q : ℂ × ℝ => pker ρ q.1 q.2) =
      (fun q : ℂ × ℝ => ‖circleMap 0 ρ q.2 - 0‖ ^ 2 - ‖q.1 - 0‖ ^ 2) /
        (fun q : ℂ × ℝ => ‖circleMap 0 ρ q.2 - 0 - (q.1 - 0)‖ ^ 2) := by
    funext q
    simp only [pker, poissonKernel_def, Pi.div_apply]
  rw [e]
  refine ContDiffOn.div ?_ ?_ ?_
  · exact (((contDiff_norm_sq ℝ).comp (hc.sub contDiff_const)).sub
      ((contDiff_norm_sq ℝ).comp (contDiff_fst.sub contDiff_const))).contDiffOn
  · exact ((contDiff_norm_sq ℝ).comp ((hc.sub contDiff_const).sub (contDiff_fst.sub contDiff_const))).contDiffOn
  · rintro ⟨w, t⟩ ⟨hw, -⟩
    have hw' : ‖w‖ < ρ := mem_ball_zero_iff.mp hw
    have hne : circleMap 0 ρ t - 0 - (w - 0) ≠ 0 := by
      intro h0
      have h1 : circleMap 0 ρ t = w := by simpa [sub_eq_zero] using h0
      have hn := norm_circleMap_zero ρ t
      rw [h1, abs_of_pos hρ] at hn
      linarith
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

theorem contDiffOn_prod_pker {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffOn ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => ∏ i, pker ρ (q.1 i) (q.2 i))
      (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := by
  have hmaps : ∀ i : Fin n, Set.MapsTo (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i))
      (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) (Metric.ball (0 : ℂ) ρ ×ˢ (Set.univ : Set ℝ)) := by
    rintro i ⟨z, θ⟩ ⟨hz, -⟩
    refine Set.mk_mem_prod ?_ (Set.mem_univ _)
    rw [mem_ball_zero_iff] at hz ⊢
    exact lt_of_le_of_lt (norm_le_pi_norm z i) hz
  have hlin : ∀ i : Fin n, ContDiff ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i)) := fun i =>
    ((contDiff_apply ℝ (fun _ => ℂ) i).comp contDiff_fst).prodMk ((contDiff_apply ℝ (fun _ => ℝ) i).comp contDiff_snd)
  have hcomp : ∀ i : Fin n, ContDiffOn ℝ ∞
      ((fun q : ℂ × ℝ => pker ρ q.1 q.2) ∘ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => (q.1 i, q.2 i))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
    fun i => (contDiffOn_pker hρ).comp (hlin i).contDiffOn (hmaps i)
  have hi : ∀ i : Fin n, ContDiffOn ℝ ∞ (fun q : (Fin n → ℂ) × (Fin n → ℝ) => pker ρ (q.1 i) (q.2 i)) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
    hcomp
  exact contDiffOn_prod (fun i _ => hi i)

theorem ae_mem_box (n : ℕ) :
    ∀ᵐ θ ∂(Measure.pi fun _ : Fin n => angMeas), ∀ i, θ i ∈ Set.Ioc 0 (2 * Real.pi) := by
  have h1 : ∀ᵐ t ∂angMeas, t ∈ Set.Ioc 0 (2 * Real.pi) :=
    Measure.smul_absolutelyContinuous.ae_le (ae_restrict_mem measurableSet_Ioc)
  rw [ae_all_iff]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually h1

private theorem contDiffOn_integral_angMeas {n : ℕ} {ρ : ℝ} (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) :
    ∀ (k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (G : (Fin n → ℂ) × (Fin n → ℝ) → E),
      ContDiffOn ℝ ∞ G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) →
      ContDiffOn ℝ k (fun z => ∫ θ, g θ • G (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas)) (Metric.ball (0 : Fin n → ℂ) ρ) := by
  have hopen : IsOpen (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := Metric.isOpen_ball.prod isOpen_univ
  have hK : IsCompact (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hbox : ∀ᵐ θ ∂(Measure.pi fun _ : Fin n => angMeas), θ ∈ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi) := by
    filter_upwards [ae_mem_box n] with θ hθ
    exact fun i _ => Set.Ioc_subset_Icc_self (hθ i)
  obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  have key : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (G : (Fin n → ℂ) × (Fin n → ℝ) → E), ContDiffOn ℝ ∞ G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) →
      ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ,
        HasFDerivAt (fun z => ∫ θ, g θ • G (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas))
          (∫ θ, g θ • (fderiv ℝ G (z₀, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ)) ∂(Measure.pi fun _ : Fin n => angMeas)) z₀ := by
    intro E _ _ _ G hG z₀ hz₀
    have hGd := (contDiffOn_infty_iff_fderiv_of_isOpen hopen).mp hG
    have hz₀' : ‖z₀‖ < ρ := mem_ball_zero_iff.mp hz₀
    obtain ⟨r, hr, hrdef⟩ : ∃ r : ℝ, 0 < r ∧ r = (ρ - ‖z₀‖) / 2 := ⟨_, by linarith, rfl⟩
    have hsub : Metric.closedBall z₀ r ⊆ Metric.ball (0 : Fin n → ℂ) ρ := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball_zero_iff]
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ < ρ := by linarith
    have hSK : IsCompact (Metric.closedBall z₀ r ×ˢ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) :=
      (isCompact_closedBall z₀ r).prod hK
    have hSsub : (Metric.closedBall z₀ r ×ˢ Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) (2 * Real.pi)) ⊆ Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ)) :=
      Set.prod_mono hsub (Set.subset_univ _)
    have hGc : ContinuousOn G (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) := hG.continuousOn
    have hG'c : ContinuousOn (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
      hGd.2.continuousOn.clm_comp continuousOn_const
    obtain ⟨C, hC⟩ := hSK.exists_bound_of_continuousOn (hG'c.mono hSsub)
    obtain ⟨C0, hC0⟩ := hSK.exists_bound_of_continuousOn (hGc.mono hSsub)
    have hslice : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, Continuous fun θ => g θ • G (z, θ) := fun z hz =>
      hg.smul (hGc.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => Set.mk_mem_prod hz (Set.mem_univ θ)))
    have hslice' : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ,
        Continuous fun θ => g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ)) := fun z hz =>
      hg.smul (hG'c.comp_continuous (continuous_const.prodMk continuous_id)
        (fun θ => Set.mk_mem_prod hz (Set.mem_univ θ)))
    have hball : Metric.ball z₀ r ⊆ Metric.ball (0 : Fin n → ℂ) ρ := Metric.ball_subset_closedBall.trans hsub
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z θ => g θ • G (z, θ))
      (F' := fun z θ => g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (bound := fun _ => Cg * C)
      (Metric.ball_mem_nhds z₀ hr) ?_ ?_ ?_ ?_ (integrable_const _) ?_
    · filter_upwards [Metric.isOpen_ball.mem_nhds hz₀] with z hz
      exact (hslice z hz).aestronglyMeasurable
    · refine Integrable.mono' (integrable_const (Cg * C0)) (hslice z₀ hz₀).aestronglyMeasurable ?_
      filter_upwards [hbox] with θ hθ
      show ‖g θ • G (z₀, θ)‖ ≤ Cg * C0
      rw [norm_smul]
      exact mul_le_mul (hCg θ hθ) (hC0 (z₀, θ) (Set.mk_mem_prod (Metric.mem_closedBall_self hr.le) hθ))
        (norm_nonneg _) ((norm_nonneg _).trans (hCg θ hθ))
    · exact (hslice' z₀ hz₀).aestronglyMeasurable
    · filter_upwards [hbox] with θ hθ z hz
      show ‖g θ • (fderiv ℝ G (z, θ)).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))‖ ≤ Cg * C
      rw [norm_smul]
      exact mul_le_mul (hCg θ hθ) (hC (z, θ) (Set.mk_mem_prod (Metric.ball_subset_closedBall hz) hθ))
        (norm_nonneg _) ((norm_nonneg _).trans (hCg θ hθ))
    · filter_upwards with θ z hz
      have hz' : z ∈ Metric.ball (0 : Fin n → ℂ) ρ := hball hz
      have hd : DifferentiableAt ℝ G (z, θ) :=
        hGd.1.differentiableAt (hopen.mem_nhds (Set.mk_mem_prod hz' (Set.mem_univ θ)))
      exact (hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_left z θ)).const_smul (g θ)
  intro k
  induction k with
  | zero =>
    intro E _ _ _ G hG
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun z hz => (key E G hG z hz).continuousAt.continuousWithinAt
  | succ k ih =>
    intro E _ _ _ G hG
    have hGd := (contDiffOn_infty_iff_fderiv_of_isOpen hopen).mp hG
    have hG' : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ (Fin n → ℂ) (Fin n → ℝ))) (Metric.ball (0 : Fin n → ℂ) ρ ×ˢ (Set.univ : Set (Fin n → ℝ))) :=
      hGd.2.clm_comp contDiffOn_const
    rw [Nat.cast_succ]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).mpr
      ⟨fun z hz => (key E G hG z hz).differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
    exact (ih _ _ hG').congr fun z hz => (key E G hG z hz).fderiv

theorem contDiffOn_polyPoisson :
    ∀ (n : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℝ), 0 < ρ →
      Continuous (fun θ : Fin n → ℝ => h (torusPt ρ θ)) →
      ContDiffOn ℝ ∞ (polyPoisson ρ h) (Metric.ball 0 ρ) := by
  intro n ρ h hρ hh
  have e : polyPoisson ρ h = fun z => ∫ θ, h (torusPt ρ θ) •
      (fun q : (Fin n → ℂ) × (Fin n → ℝ) => ∏ i, pker ρ (q.1 i) (q.2 i)) (z, θ) ∂(Measure.pi fun _ : Fin n => angMeas) := by
    funext z
    show (∫ θ, (∏ i, pker ρ (z i) (θ i)) * h (torusPt ρ θ) ∂(Measure.pi fun _ : Fin n => angMeas)) = _
    congr 1
    funext θ
    rw [smul_eq_mul, mul_comm]
  rw [e, contDiffOn_infty]
  intro k
  exact contDiffOn_integral_angMeas _ hh k ℝ _ (contDiffOn_prod_pker hρ)

end GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolydiscPoissonSmoothStatement
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polydisc_poisson_smooth : ∀ (n : ℕ) (ρ : ℝ) (h : (Fin n → ℂ) → ℝ), 0 < ρ → Continuous (fun θ : Fin n → ℝ => h (torusPt ρ θ)) → ContDiffOn ℝ ∞ (polyPoisson ρ h) (Metric.ball 0 ρ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.Smooth.contDiffOn_polyPoisson <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmooth
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

theorem locExt_two_le : (2 : WithTop ℕ∞) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)

theorem locExt_isOpen_punct {n : ℕ} (R : ℝ) : IsOpen (punct (n := n) R) := by
  have h : punct (n := n) R = ⋂ i, ({z | z i ≠ 0} ∩ {z | ‖z i‖ < R}) := by
    ext z; simp [punct]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    (isOpen_ne_fun (continuous_apply i) continuous_const).inter
      (isOpen_lt (continuous_apply i).norm continuous_const)

theorem locExt_isOpen_nz {n : ℕ} (S : Finset (Fin n)) :
    IsOpen {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} := by
  have h : {z : Fin n → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z | z i ≠ 0} := by
    ext z; simp
  rw [h]
  exact isOpen_biInter_finset fun i _ => isOpen_ne_fun (continuous_apply i) continuous_const

theorem locExt_core {n : ℕ} (c : Fin n → ℂ) (r : ℝ) (hr : 0 < r) (Q : Set (Fin n → ℂ))
    (hQ : IsOpen Q) (hcov : ∀ z ∈ Metric.ball c r, (∀ i, z i ≠ c i) → z ∈ Q)
    (F : (Fin n → ℂ) → ℝ) (hsm : ∀ z ∈ Metric.ball c r ∩ Q, ContDiffAt ℝ ∞ F z)
    (hlevi : ∀ z ∈ Metric.ball c r ∩ Q, ∀ w, levi F z w = 0)
    (B : ℝ) (hB : ∀ z ∈ Metric.ball c r ∩ Q, |F z| ≤ B) :
    ∃ G : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ G (Metric.ball c (r / 2)) ∧
      ∀ z ∈ Metric.ball c (r / 2) ∩ Q, G z = F z := by
  set f : (Fin n → ℂ) → ℝ := fun w => F (c + w) with hf
  have hmem : ∀ w ∈ punct (n := n) r, c + w ∈ Metric.ball c r ∩ Q := by
    intro w hw
    have hb : c + w ∈ Metric.ball c r := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (pi_norm_lt_iff hr).2 fun i => (hw i).2
    refine ⟨hb, hcov _ hb fun i => ?_⟩
    simpa using (hw i).1
  have hτ : ∀ w : Fin n → ℂ, ContDiffAt ℝ ∞ (fun w : Fin n → ℂ => c + w) w :=
    fun w => contDiffAt_const.add contDiffAt_id
  have hfsm : ∀ w ∈ punct (n := n) r, ContDiffAt ℝ ∞ f w :=
    fun w hw => ContDiffAt.comp w (hsm _ (hmem w hw)) (hτ w)
  have hharm : SepHarm r f := by
    refine GlobalTheory.T.levi_flat_separately_harmonic n f (punct r) (locExt_isOpen_punct r)
      (fun w hw => (hfsm w hw).contDiffWithinAt) ?_
    intro w hw v
    have hA : AnalyticAt ℂ (fun w : Fin n → ℂ => c + w) w := analyticAt_const.add analyticAt_id
    have h2 : ContDiffAt ℝ 2 F (c + w) := (hsm _ (hmem w hw)).of_le locExt_two_le
    have := levi_comp (φ := F) (τ := fun w : Fin n → ℂ => c + w) (z := w) v hA h2
    calc levi f w v = levi (F ∘ fun w : Fin n → ℂ => c + w) w v := rfl
      _ = 0 := by rw [this]; exact hlevi _ (hmem w hw) _
  have hfc : ContinuousOn f (punct r) :=
    fun w hw => (hfsm w hw).continuousAt.continuousWithinAt
  have hpo := GlobalTheory.T.polydisc_poisson_reproduces_harmonic n f (r / 2) r B (half_pos hr) (half_lt_self hr) hfc hharm
    (fun w hw => hB _ (hmem w hw))
  have htor : ∀ θ : Fin n → ℝ, torusPt (r / 2) θ ∈ punct (n := n) r := by
    intro θ i
    have hn : ‖torusPt (r / 2) θ i‖ = r / 2 := by
      simp only [torusPt]
      rw [norm_circleMap_zero, abs_of_pos (half_pos hr)]
    refine ⟨fun h0 => ?_, by rw [hn]; exact half_lt_self hr⟩
    rw [h0, norm_zero] at hn
    linarith
  have hcont : Continuous fun θ : Fin n → ℝ => f (torusPt (r / 2) θ) :=
    hfc.comp_continuous
      (continuous_pi fun i => (continuous_circleMap 0 _).comp (continuous_apply i)) htor
  have hG := GlobalTheory.T.polydisc_poisson_smooth n (r / 2) f (half_pos hr) hcont
  have hGc : ContDiffOn ℝ ∞ (fun z => polyPoisson (r / 2) f (z - c)) (Metric.ball c (r / 2)) := by
    refine ContDiffOn.comp (g := polyPoisson (r / 2) f) (f := fun z : Fin n → ℂ => z - c)
      (t := Metric.ball 0 (r / 2)) hG (contDiff_id.sub contDiff_const).contDiffOn ?_
    intro z hz
    simpa [dist_eq_norm] using hz
  refine ⟨fun z => polyPoisson (r / 2) f (z - c), hGc, ?_⟩
  have hT : Dense {z : Fin n → ℂ | ∀ i, z i ≠ c i} := by
    have h := (GlobalTheory.T.dense_coordinate_torus n).preimage (Homeomorph.subRight c).isOpenMap
    convert h using 1
    ext z
    simp [sub_ne_zero]
  have hD : IsOpen (Metric.ball c (r / 2) ∩ Q) := Metric.isOpen_ball.inter hQ
  have hsub : Metric.ball c (r / 2) ∩ Q ⊆ Metric.ball c r ∩ Q :=
    Set.inter_subset_inter_left _ (Metric.ball_subset_ball (half_le_self hr.le))
  have heq : Set.EqOn (fun z => polyPoisson (r / 2) f (z - c)) F
      ((Metric.ball c (r / 2) ∩ Q) ∩ {z : Fin n → ℂ | ∀ i, z i ≠ c i}) := by
    intro z hz
    have hw : z - c ∈ punct (n := n) (r / 2) := by
      intro i
      refine ⟨sub_ne_zero.2 (hz.2 i), ?_⟩
      have h1 : ‖z - c‖ < r / 2 := by simpa [dist_eq_norm] using hz.1.1
      exact (norm_le_pi_norm (z - c) i).trans_lt h1
    simp only
    rw [hpo _ hw, hf]
    simp
  exact Set.EqOn.of_subset_closure heq
    (hGc.mono Set.inter_subset_left).continuousOn
    (fun z hz => (hsm z (hsub hz)).continuousAt.continuousWithinAt)
    Set.inter_subset_left (hT.open_subset_closure_inter hD)

theorem locExt : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  intro e X _ A L s nb m W hs hsnc th u M hth hu hP hPn hM x
  obtain ⟨ψ, hψ, hxψ, S, hbd⟩ := GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hsnc x
  obtain ⟨hcl, -⟩ := GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc
  let g₀ : X → ℝ := fun y => th.φ x y + u y
  let U' : Set X := th.U x ∩ (bdry s)ᶜ
  have hU' : IsOpen U' := (th.isOpen_U x).inter hcl.isOpen_compl
  have hsm0 : A.SmoothOn U' g₀ := fun j =>
    ((hth.1 x j).mono (by exact fun y hy => ⟨hy.1, hy.2.1⟩)).add ((hu j).mono fun y hy => ⟨hy.1, hy.2.2⟩)
  have hlz : ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U', ∀ w,
      levi (g₀ ∘ (A.chart j).symm) y w = 0 := by
    intro j y hy w
    have hmemP : y ∈ (A.chart j).target ∩
        (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u).U x ∩ (bdry s)ᶜ) :=
      ⟨hy.1, ⟨hy.2.1, trivial⟩, hy.2.2⟩
    have h1 : 0 ≤ levi (g₀ ∘ (A.chart j).symm) y w := hP x j y hmemP w
    have h2 : 0 ≤ levi (fun z => (-1 : ℝ) * (g₀ ∘ (A.chart j).symm) z) y w :=
      hPn x j y hmemP w
    have hc2 : ContDiffAt ℝ 2 (g₀ ∘ (A.chart j).symm) y :=
      ((hsm0 j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU').mem_nhds hy)).of_le
        locExt_two_le
    have h3 := levi_add_smul (f := fun _ => (0 : ℝ)) (-1) contDiffAt_const hc2 w
    simp only [zero_add] at h3
    rw [h3] at h2
    have h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
    linarith
  have hO₁ : IsOpen (ψ.target ∩ ψ.symm ⁻¹' th.U x) :=
    ψ.isOpen_inter_preimage_symm (th.isOpen_U x)
  have hcO₁ : ψ x ∈ ψ.target ∩ ψ.symm ⁻¹' th.U x :=
    ⟨ψ.map_source hxψ, by rw [Set.mem_preimage, ψ.left_inv hxψ]; exact th.mem_U x⟩
  let Q : Set (Fin e → ℂ) := {z | ∀ i ∈ S, z i ≠ 0}
  have hQ : IsOpen Q := locExt_isOpen_nz S
  let S' : Finset (Fin e) := S.filter fun i => ψ x i ≠ 0
  have hQ₂ : IsOpen {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0} := locExt_isOpen_nz S'
  have hcQ₂ : ψ x ∈ {z : Fin e → ℂ | ∀ i ∈ S', z i ≠ 0} :=
    fun i hi => (Finset.mem_filter.1 hi).2
  obtain ⟨r, hr, hball⟩ :=
    Metric.nhds_basis_closedBall.mem_iff.1 ((hO₁.inter hQ₂).mem_nhds ⟨hcO₁, hcQ₂⟩)
  have hcov : ∀ z ∈ Metric.ball (ψ x) r, (∀ i, z i ≠ ψ x i) → z ∈ Q := by
    intro z hz hne i hi
    by_cases h0 : ψ x i = 0
    · rw [← h0]; exact hne i
    · exact (hball (Metric.ball_subset_closedBall hz)).2 i (Finset.mem_filter.2 ⟨hi, h0⟩)
  have hoff : ∀ z ∈ Metric.ball (ψ x) r ∩ Q, z ∈ ψ.target ∧ ψ.symm z ∈ U' := by
    intro z hz
    have hz1 := (hball (Metric.ball_subset_closedBall hz.1)).1
    refine ⟨hz1.1, hz1.2, fun hb => ?_⟩
    obtain ⟨i, hi, h0⟩ := (hbd _ (ψ.map_target hz1.1)).1 hb
    rw [ψ.right_inv hz1.1] at h0
    exact hz.2 i hi h0
  obtain ⟨C, hC⟩ := (isCompact_closedBall (ψ x) r).exists_bound_of_continuousOn
    (f := th.φ x ∘ ψ.symm) fun z hz =>
      (GlobalTheory.T.smooth_in_compatible_chart e X A ψ (th.U x) (th.φ x) hψ (th.isOpen_U x) (hth.1 x) z (hball hz).1.1
        (hball hz).1.2).continuousAt.continuousWithinAt
  obtain ⟨G, hGs, hGe⟩ := locExt_core (ψ x) r hr Q hQ hcov (g₀ ∘ ψ.symm)
    (fun z hz => GlobalTheory.T.smooth_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 z (hoff z hz).1 (hoff z hz).2)
    (fun z hz => GlobalTheory.T.levi_zero_in_compatible_chart e X A ψ U' g₀ hψ hU' hsm0 hlz z (hoff z hz).1 (hoff z hz).2)
    (C + M) (fun z hz => by
      have h1 := hC z (Metric.ball_subset_closedBall hz.1)
      have h2 := hM _ (hoff z hz).2.2
      rw [Real.norm_eq_abs] at h1
      exact (abs_add_le _ _).trans (add_le_add h1 h2))
  have hhalf : Metric.ball (ψ x) (r / 2) ⊆ Metric.closedBall (ψ x) r :=
    (Metric.ball_subset_ball (half_le_self hr.le)).trans Metric.ball_subset_closedBall
  have hNU : ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2) ⊆ th.U x := by
    intro y hy
    have h := (hball (hhalf hy.2)).1.2
    rwa [Set.mem_preimage, ψ.left_inv hy.1] at h
  refine ⟨ψ.source ∩ ψ ⁻¹' Metric.ball (ψ x) (r / 2), fun y => (G ∘ ψ) y - th.φ x y,
    ψ.isOpen_inter_preimage Metric.isOpen_ball, ⟨hxψ, Metric.mem_ball_self (half_pos hr)⟩, ?_, ?_⟩
  · intro j
    have h1 := GlobalTheory.T.smoothOn_of_chart_composition e X A ψ (Metric.ball (ψ x) (r / 2)) G hψ Metric.isOpen_ball
      (fun z hz => (hball (hhalf hz)).1.1) hGs
    exact (h1 j).sub ((hth.1 x j).mono fun y hy => ⟨hy.1, hNU hy.2⟩)
  · intro y hy hyb
    have hz : ψ y ∈ Metric.ball (ψ x) (r / 2) ∩ Q :=
      ⟨hy.2, fun i hi h0 => hyb ((hbd y hy.1).2 ⟨i, hi, h0⟩)⟩
    have h := hGe _ hz
    simp only [Function.comp_apply] at h ⊢
    rw [h, ψ.left_inv hy.1]
    simp [g₀]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmoothStatement
open MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar.PB.Flat ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_psh_correction_locally_smooth : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → ∀ (th : LocPot X) (u : X → ℝ) (M : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ M) → ∀ x, ∃ (N : Set X) (E : X → ℝ), IsOpen N ∧ x ∈ N ∧ A.SmoothOn N E ∧ ∀ y ∈ N, y ∉ bdry s → E y = u y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | exact GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Flat.locExt <;> assumption)
end
