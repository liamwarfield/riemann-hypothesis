module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicValueDerivativeL2Ball
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFderivLeOfBoundedGen
namespace GlobalTheory.FrechetDerivativeBound

theorem norm_fderiv_le_of_bounded_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} {ρ R M : ℝ} (hρ : 0 < ρ) (hR : ρ < R) (u : E → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ := by
  have hp : p ∈ Metric.ball p R := Metric.mem_ball_self (hρ.trans hR)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p hp)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM0 hρ.le) ?_
  intro v hv
  have hmem : ∀ t ∈ Metric.closedBall (0 : ℂ) ρ, p + t • v ∈ Metric.ball p R := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one]
    exact ht.trans_lt hR
  have hline : ∀ t : ℂ, HasDerivAt (fun s : ℂ => p + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hd : DifferentiableOn ℂ (fun t : ℂ => u (p + t • v)) (Metric.closedBall 0 ρ) :=
    hu.comp (fun t _ => (hline t).differentiableAt.differentiableWithinAt) hmem
  have hdc : DiffContOnCl ℂ (fun t : ℂ => u (p + t • v)) (Metric.ball 0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball _ hρ.ne']
  have hup : DifferentiableAt ℂ u p := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hp)
  have hder : HasDerivAt (fun t : ℂ => u (p + t • v)) (fderiv ℂ u p v) 0 := by
    have h1 : HasFDerivAt u (fderiv ℂ u p) (p + (0 : ℂ) • v) := by
      simpa using hup.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hline 0)
  rw [← hder.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc
    (fun z hz => hM _ (hmem z (Metric.sphere_subset_closedBall hz)))

theorem norm_fderiv_le_of_bounded {n : ℕ} {p : ReciprocityTheory.L2DbarEstimates.V n} {ρ R M : ℝ}
    (hρ : (0 : ℝ) < ρ) (hR : ρ < R) (u : ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ :=
  norm_fderiv_le_of_bounded_gen hρ hR u hu hM

end GlobalTheory.FrechetDerivativeBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicValueDerivativeL2Ball
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem l2ball_sq_mul_vol_le {n : ℕ} {x : V n} {s : ℝ} (u : V n → ℂ)
    (hu : DifferentiableOn ℂ u (ball x s)) :
    ENNReal.ofReal (‖u x‖ ^ 2) * volume (ball (0 : V n) s) ≤
      ∫⁻ v in ball x s, ENNReal.ofReal (‖u v‖ ^ 2) := by
  have hu' : DifferentiableOn ℂ (fun y => u (x + y)) (ball 0 s) := by
    intro y hy
    have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    exact ((hu.differentiableAt (isOpen_ball.mem_nhds hxy)).comp y
      ((differentiable_const x).add differentiable_id y)).differentiableWithinAt
  have hρm : Measurable fun t : ℝ => (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) t :=
    measurable_const.indicator measurableSet_Iio
  have h := ReciprocityTheory.L2DbarEstimates.mv n s _ _ hu' hρm
    (fun t ht => Set.indicator_of_notMem (by simpa using ht) _)
  have e1 : ∀ y : V n, (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) ‖y‖ =
      (ball (0 : V n) s).indicator 1 y := by
    intro y
    by_cases hy : ‖y‖ < s
    · rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using hy)]; rfl
    · rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using hy)]
  simp only [add_zero, e1] at h
  rw [lintegral_indicator_one measurableSet_ball] at h
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self (fun v => (ball x s).indicator (fun v => ENNReal.ofReal (‖u v‖ ^ 2)) v) x]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ ball (0 : V n) s
  · have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hxy]; simp
  · have hxy : x + y ∉ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hxy]; simp

theorem norm_fderiv_le_of_ball {n : ℕ} {p : V n} {ρ R M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (u : V n → ℂ) (hu : DifferentiableOn ℂ u (ball p R)) (hM : ∀ x ∈ ball p R, ‖u x‖ ≤ M) :
    ‖fderiv ℂ u p‖ ≤ M / ρ := by
  first
  | exact @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | (apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded ..)

theorem l2_value_deriv_ball :
    ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ),
      DifferentiableOn ℂ u (ball p r) →
        ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
          ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  intro n r hr
  set β : ℝ := (volume (ball (0 : V n) (r / 2))).toReal with hβdef
  have hβ : 0 < β := ENNReal.toReal_pos (measure_ball_pos volume _ (by linarith)).ne'
    measure_ball_lt_top.ne
  have hV : volume (ball (0 : V n) (r / 2)) = ENNReal.ofReal β :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  refine ⟨(1 + 16 / r ^ 2) / β, by positivity, fun p u hu => ?_⟩
  set I := ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) with hIdef
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact le_top
  set J := I.toReal with hJ
  have hI' : I = ENNReal.ofReal J := (ENNReal.ofReal_toReal hI).symm
  have hx : ∀ x ∈ ball p (r / 2), ‖u x‖ ^ 2 ≤ J / β := by
    intro x hx
    have hsub : ball x (r / 2) ⊆ ball p r := by
      apply ball_subset_ball'
      rw [mem_ball] at hx; linarith
    have h2 := (l2ball_sq_mul_vol_le u (hu.mono hsub)).trans (lintegral_mono_set hsub)
    rw [hV, ← ENNReal.ofReal_mul (sq_nonneg _), ← hIdef, hI'] at h2
    rw [le_div_iff₀ hβ]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
  set M := Real.sqrt (J / β) with hMdef
  have hJβ : 0 ≤ J / β := div_nonneg ENNReal.toReal_nonneg hβ.le
  have hMx : ∀ x ∈ ball p (r / 2), ‖u x‖ ≤ M := by
    intro x hx'
    have := Real.sqrt_le_sqrt (hx x hx')
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hD := norm_fderiv_le_of_ball (ρ := r / 4) (by positivity) (by linarith) u
    (hu.mono (ball_subset_ball (by linarith))) hMx
  have hD2 : ‖fderiv ℂ u p‖ ^ 2 ≤ 16 / r ^ 2 * (J / β) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hD 2
    refine this.trans (le_of_eq ?_)
    rw [div_pow, Real.sq_sqrt hJβ]; field_simp; ring
  have hp := hx p (mem_ball_self (by linarith))
  rw [hI', ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ J / β + 16 / r ^ 2 * (J / β) := add_le_add hp hD2
    _ = (1 + 16 / r ^ 2) / β * J := by ring

end

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicValueDerivativeL2BallStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_value_derivative_l2_ball : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ), DifferentiableOn ℂ u (ball p r) → ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤ ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  first | exact @GlobalTheory.l2_value_deriv_ball | exact GlobalTheory.l2_value_deriv_ball | (intros; apply GlobalTheory.l2_value_deriv_ball <;> assumption)
end
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.JetSmall

theorem ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : La) (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) (k : ℕ) :
    A.ph (k • H) i y = k * A.ph H i y := by
  induction k with
  | zero =>
    rw [zero_nsmul, Nat.cast_zero, zero_mul]
    have := A.ph_add 0 0 i y hy
    rw [add_zero] at this
    linarith
  | succ k ih =>
    rw [succ_nsmul, A.ph_add _ _ i y hy, ih]
    push_cast; ring

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  intro n Y _ _ _ _ _ ι La _ A H G i p r0 c Cq K q hr0 hc hsub hq hH ε hε

  set r : ℝ := min r0 (Real.sqrt (c / (2 * (|Cq| + 1)))) with hr
  have hCq1 : 0 < |Cq| + 1 := by positivity
  have hrpos : 0 < r := lt_min hr0 (Real.sqrt_pos.2 (by positivity))
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hr2 : r ^ 2 ≤ c / (2 * (|Cq| + 1)) := by
    have h1 : r ≤ Real.sqrt (c / (2 * (|Cq| + 1))) := min_le_right _ _
    have h2 := pow_le_pow_left₀ hrpos.le h1 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hsubr : closedBall p r ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall hrr0).trans hsub
  have hball : ball p r ⊆ (A.chart i).target := ball_subset_closedBall.trans hsubr
  have hquad : ∀ v ∈ closedBall p r, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ c / 2 := by
    intro v hv
    have h := hH v (closedBall_subset_closedBall hrr0 hv)
    have hd : ‖v - p‖ ≤ r := by rw [← dist_eq_norm]; exact hv
    have hd2 : ‖v - p‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have h3 : Cq * ‖v - p‖ ^ 2 ≤ |Cq| * ‖v - p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h4 : |Cq| * ‖v - p‖ ^ 2 ≤ |Cq| * (c / (2 * (|Cq| + 1))) :=
      mul_le_mul_of_nonneg_left (hd2.trans hr2) (abs_nonneg _)
    have h5 : |Cq| * (c / (2 * (|Cq| + 1))) ≤ c / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg Cq]
    linarith

  obtain ⟨M, hM⟩ := hyq_bdd (f := fun v => Real.exp (A.ph G i ((A.chart i).symm v))) (c := p) (r := r)
    ((A.smooth_ph G i).continuousOn.rexp.mono hsubr)
  have hM0 : 0 ≤ M := (Real.exp_pos _).le.trans (hM p (mem_closedBall_self hrpos.le))

  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.holomorphic_value_derivative_l2_ball n r hrpos

  have htend : Tendsto (fun k : ℕ => C * M * |K| * Real.exp (-(c / 2) * k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => -(c / 2) * (k : ℝ)) atTop atBot :=
      (tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by linarith)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (C * M * |K|)
    simpa using h2
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ((tendsto_order.1 htend).2 (ε ^ 2) (by positivity))
  refine ⟨k0, fun k hk D hD hDd hn0 => ?_⟩
  set u : V n → ℂ := fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v)) with hu
  have hud : DifferentiableOn ℂ u (ball p r) :=
    (hDd.mono (ball_subset_ball hrr0)).mul
      ((Complex.differentiable_exp.comp ((hq.const_mul (k : ℂ)).neg)).differentiableOn)
  have hest := hC p u hud

  set la : La := G + k • H
  set f : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq _ D hD.2
      (fun j => (hD.1 j).continuousOn)).measurable

  have hpt : ∀ v ∈ ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
        (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) := by
    intro v hv
    set y := (A.chart i).symm v
    have hy : y ∈ (A.chart i).source := (A.chart i).map_target (hball hv)
    have hns := hyq_nsq_chart A (A.kap + la) D i y hy (hD.2 i (A.pick y) y hy (A.mem_pick y))
    have hph : A.ph (A.kap + la) i y = A.ph A.kap i y + (A.ph G i y + k * A.ph H i y) := by
      rw [A.ph_add _ _ i y hy, A.ph_add _ _ i y hy, ph_nsmul A H i y hy]
    simp only [hf]
    rw [hns, hph, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hnu : ‖u v‖ ^ 2 = ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re)) := by
      simp only [hu, norm_mul, Complex.norm_exp, mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      simp [Complex.neg_re, Complex.mul_re]
      ring
    rw [hnu]
    have hq2 := hquad v (ball_subset_closedBall hv)
    have hMv := hM v (ball_subset_closedBall hv)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have key : Real.exp (-(2 * k * (q v).re)) ≤
        M * Real.exp (k * (c / 2)) * (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
          Real.exp (A.ph A.kap i y)) := by
      calc Real.exp (-(2 * k * (q v).re))
          ≤ Real.exp (A.ph G i y) * Real.exp (k * (c / 2)) *
              (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
                Real.exp (A.ph A.kap i y)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith [mul_le_mul_of_nonneg_left hq2 hk0]
        _ ≤ _ := by gcongr
    calc ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re))
        ≤ ‖D i y‖ ^ 2 * (M * Real.exp (k * (c / 2)) *
          (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring
  have hint : ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
    calc ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2)
        ≤ ∫⁻ v in ball p r, ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (M * Real.exp (k * (c / 2))) * ∫⁻ v in ball p r,
            f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
          gcongr
          exact A.aap_lintegral_chart_le i f hfm _ hball

  have hall : ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
      ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
    calc ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            ENNReal.ofReal (|K| * Real.exp (-c * k))) := by
          refine hest.trans ?_
          gcongr
          refine hint.trans ?_
          gcongr
          exact hn0.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le))
      _ = ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
          congr 1
          have : Real.exp (k * (c / 2)) * Real.exp (-c * k) = Real.exp (-(c / 2) * k) := by
            rw [← Real.exp_add]; congr 1; ring
          calc C * (M * Real.exp (k * (c / 2)) * (|K| * Real.exp (-c * k)))
              = C * M * |K| * (Real.exp (k * (c / 2)) * Real.exp (-c * k)) := by ring
            _ = _ := by rw [this]
  have hsq : ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by
    have hb := (hk0 k hk).le
    rcases (ENNReal.ofReal_le_ofReal_iff'.1 hall) with h | h
    · linarith
    · nlinarith [sq_nonneg ε]
  have h1 : ‖u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖fderiv ℂ u p‖]
  have h2 : ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖u p‖]
  exact ⟨by nlinarith [norm_nonneg (u p)], by nlinarith [norm_nonneg (fderiv ℂ u p)]⟩

end GlobalTheory.JetSmall
