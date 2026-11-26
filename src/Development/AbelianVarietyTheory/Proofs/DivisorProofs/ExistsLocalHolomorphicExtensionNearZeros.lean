module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellMassIntegrableNearNondegenerateZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellMass
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

noncomputable section

namespace GlobalTheory.ShellMass

theorem shell_mass : ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O → DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O → ∀ (φ : V n → ℝ) (l τ : ℝ), ContinuousOn φ O → 0 < l → 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ball p ρ ⊆ O ∧ ∀ b : ℝ, ∫⁻ v in ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b}, ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) ≤ ENNReal.ofReal ((1 + τ) * (Real.pi ^ n / ((n - 1).factorial : ℝ) * (l / n)) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) := by
  classical
  intro n hn p O Z lam hO hpO hZ hZp hdet hlam φ l τ hφ hl hτ
  have hZc : ContDiffOn ℂ ∞ Z O := by
    refine contDiffOn_piLp' (p := 2) fun i => ?_
    have hd : DifferentiableOn ℂ (fun x => Z x i) O :=
      (EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hZ
    have ha : AnalyticOnNhd ℂ (fun x => Z x i) O := fun z hz =>
      ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hO hd hz
    exact ha.contDiffOn hO.uniqueDiffOn
  have hZa : ContDiffAt ℂ ∞ Z p := hZc.contDiffAt (hO.mem_nhds hpO)
  set E0 := (fderiv ℂ Z p).toContinuousLinearEquivOfDetNeZero hdet
  have hs : HasStrictFDerivAt Z (E0 : V n →L[ℂ] V n) p := by
    simpa [E0] using hZa.hasStrictFDerivAt_fderiv (by norm_cast)
  set e := hs.toOpenPartialHomeomorph Z
  have he : (e : V n → V n) = Z := rfl
  have hpe : p ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have hdetc : ContinuousOn (fun v => (fderiv ℂ Z v).det) O :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hZc.continuousOn_fderiv_of_isOpen hO (by norm_cast))
  set D : V n → ℝ := fun v => ‖(fderiv ℂ Z v).det‖ ^ 2 with hD
  have hDc : ContinuousAt D p := ((hdetc.continuousAt (hO.mem_nhds hpO)).norm).pow 2
  have hD0 : 0 < D p := pow_pos (norm_pos_iff.2 hdet) 2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set c := l / n with hcdef
  have hc : 0 < c := div_pos hl hnr
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ Real.exp (2 * η) * (c + 2 * η) < (1 + τ) * c := by
    refine Filter.Eventually.and eventually_mem_nhdsWithin (nhdsWithin_le_nhds ?_)
    have ht : Tendsto (fun η : ℝ => Real.exp (2 * η) * (c + 2 * η)) (𝓝 0)
        (𝓝 (Real.exp (2 * 0) * (c + 2 * 0))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_const.add (continuous_const.mul continuous_id))).tendsto 0
    simp only [mul_zero, Real.exp_zero, one_mul, add_zero] at ht
    exact ht.eventually (gt_mem_nhds (by nlinarith))
  obtain ⟨η, hη, hηc⟩ := hev.exists
  have hlamc : ContinuousAt lam p := hlam.continuousAt (hO.mem_nhds hpO)
  have hgc : ContinuousAt (fun v => -φ v + (n : ℝ) * lam v) p :=
    ((hφ.continuousAt (hO.mem_nhds hpO)).neg).add (continuousAt_const.mul hlamc)
  have h1 : ∀ᶠ v in 𝓝 p, v ∈ O := hO.mem_nhds hpO
  have h2 : ∀ᶠ v in 𝓝 p, v ∈ e.source := e.open_source.mem_nhds hpe
  have h3 : ∀ᶠ v in 𝓝 p, lam v ∈ ball (lam p) η := hlamc.eventually (ball_mem_nhds _ hη)
  have h4 : ∀ᶠ v in 𝓝 p, (-φ v + (n : ℝ) * lam v) ∈ ball (-φ p + (n : ℝ) * lam p) η :=
    hgc.eventually (ball_mem_nhds _ hη)
  have h5 : ∀ᶠ v in 𝓝 p, D p * Real.exp (-η) < D v := by
    refine hDc.eventually (lt_mem_nhds ?_)
    have : Real.exp (-η) < 1 := (Real.exp_lt_exp.2 (by linarith : -η < 0)).trans_eq Real.exp_zero
    nlinarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (h3.and (h4.and h5))))
  have hbO : ball p ρ ⊆ O := fun v hv => (hball v hv).1
  have hinj : Set.InjOn Z (ball p ρ) := by
    rw [← he]; exact e.injOn.mono fun v hv => (hball v hv).2.1
  refine ⟨ρ, hρ, hbO, ?_⟩
  intro b
  set a1 := Real.exp ((b - l) / n + lam p - η) with ha1
  set a2 := Real.exp (b / n + lam p + η) with ha2
  have ha1p : 0 < a1 := Real.exp_pos _
  have h21 : a2 / a1 = Real.exp (c + 2 * η) := by
    rw [ha1, ha2, ← Real.exp_sub, hcdef]; congr 1; ring
  have ha12 : a1 ≤ a2 := by
    rw [ha1, ha2]; refine Real.exp_le_exp.2 ?_
    have : (b - l) / n ≤ b / n := div_le_div_of_nonneg_right (by linarith) hnr.le
    linarith
  set Ann := {w : V n | a1 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ a2} with hAnn
  have hAnnm : MeasurableSet Ann :=
    ((isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)).measurableSet
  set K := Real.exp (2 * η) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hfm' : Measurable fun w : V n => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ))) :=
    ((measurable_norm.pow_const 2).pow_const _).ennreal_ofReal
  set f : V n → ℝ≥0∞ := fun w => ENNReal.ofReal K *
      Ann.indicator (fun w => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ)))) w with hfdef
  have hfm : Measurable f := measurable_const.mul (hfm'.indicator hAnnm)
  set Zb : V n → V n := (ball p ρ).piecewise Z (fun _ => 0) with hZb
  have hZbm : Measurable Zb :=
    ContinuousOn.measurable_piecewise (hZ.continuousOn.mono hbO) continuousOn_const measurableSet_ball
  set G : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (D v) * f (Zb v) with hG
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (hfm.comp hZbm)
    refine Measurable.ennreal_ofReal ?_
    exact ((ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℂ Z)).norm).pow_const 2

  have hpt : ∀ v ∈ ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧
      ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b},
      ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) ≤ G v := by
    rintro v ⟨hvb, hv0, hvl, hvu⟩
    obtain ⟨-, -, hv3, hv4, hv5⟩ := hball v hvb
    rw [mem_ball, Real.dist_eq, abs_lt] at hv3 hv4
    set s := ‖Z v‖ ^ 2 with hsdef
    have hsp : 0 < s := pow_pos (norm_pos_iff.2 hv0) 2
    have hlog : Real.log (s * Real.exp (-lam v)) = Real.log s - lam v := by
      rw [Real.log_mul hsp.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    rw [hlog] at hvl hvu ⊢
    have hl1 : (b - l) / n ≤ Real.log s - lam v := by rw [div_le_iff₀ hnr]; linarith
    have hl2 : Real.log s - lam v ≤ b / n := by rw [le_div_iff₀ hnr]; linarith
    have hA : Z v ∈ Ann := by
      refine ⟨?_, ?_⟩
      · exact (Real.exp_le_exp.2 (by linarith)).trans_eq (Real.exp_log hsp)
      · exact (Real.exp_log hsp).symm.trans_le (Real.exp_le_exp.2 (by linarith))
    have hZbv : Zb v = Z v := Set.piecewise_eq_of_mem _ _ _ hvb
    simp only [hG, hfdef, hZbv, Set.indicator_of_mem hA]
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsn : s ^ (-(n : ℝ)) = Real.exp (-(n : ℝ) * Real.log s) := by
      rw [Real.rpow_def_of_pos hsp]; ring_nf
    have heq : Real.exp (-φ v) * Real.exp (-((n : ℝ) * (Real.log s - lam v))) =
        Real.exp (-φ v + (n : ℝ) * lam v) * s ^ (-(n : ℝ)) := by
      rw [hsn, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [heq]
    have hexp : Real.exp (-φ v + (n : ℝ) * lam v) ≤ D v * K := by
      have e1 : Real.exp (-φ v + (n : ℝ) * lam v) ≤ Real.exp (-φ p + n * lam p + η) :=
        Real.exp_le_exp.2 (by linarith)
      have e2 : Real.exp (-φ p + n * lam p + η) = D p * Real.exp (-η) * K := by
        rw [hK, show ‖(fderiv ℂ Z p).det‖ ^ 2 = D p from rfl, div_eq_mul_inv]
        have hDi : D p * (D p)⁻¹ = 1 := mul_inv_cancel₀ hD0.ne'
        have hx : Real.exp (-φ p + n * lam p + η) =
            Real.exp (-η) * Real.exp (2 * η) * Real.exp (-φ p + n * lam p) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [hx]
        linear_combination (-(Real.exp (-η) * Real.exp (2 * η) * Real.exp (-φ p + n * lam p))) * hDi
      rw [e2] at e1
      exact e1.trans (mul_le_mul_of_nonneg_right hv5.le hK0)
    have hsn0 : 0 ≤ s ^ (-(n : ℝ)) := Real.rpow_nonneg hsp.le _
    calc Real.exp (-φ v + (n : ℝ) * lam v) * s ^ (-(n : ℝ)) ≤ D v * K * s ^ (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_right hexp hsn0
      _ = D v * (K * s ^ (-(n : ℝ))) := by ring
  have hcov := ReciprocityTheory.L2DbarEstimates.I.cov n (ball p ρ) Z f isOpen_ball (hZ.mono hbO) hinj hfm
  have hpol := ReciprocityTheory.L2DbarEstimates.I.polar n hn a1 a2 ha1p ha12
  calc _ ≤ ∫⁻ v in ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧
        ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b}, G v := setLIntegral_mono hGm hpt
    _ ≤ ∫⁻ v in ball p ρ, G v := lintegral_mono_set Set.inter_subset_left
    _ = ∫⁻ w in Z '' ball p ρ, f w := by
        rw [hcov]
        refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
        simp only [hG, hD, Set.piecewise_eq_of_mem _ _ _ hv, hZb]
    _ ≤ ∫⁻ w, f w := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal K * ENNReal.ofReal (Real.pi ^ n / ((n - 1).factorial : ℝ) * Real.log (a2 / a1)) := by
        rw [hfdef, lintegral_const_mul _ (hfm'.indicator hAnnm), lintegral_indicator hAnnm, hpol]
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [h21, Real.log_exp, hK]
        have hP : 0 ≤ Real.pi ^ n / ((n - 1).factorial : ℝ) := by positivity
        have hE : 0 ≤ Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2 := by positivity
        calc Real.exp (2 * η) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2) *
              (Real.pi ^ n / ((n - 1).factorial : ℝ) * (c + 2 * η))
            = (Real.pi ^ n / ((n - 1).factorial : ℝ) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) *
              (Real.exp (2 * η) * (c + 2 * η)) := by ring
          _ ≤ (Real.pi ^ n / ((n - 1).factorial : ℝ) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) *
              ((1 + τ) * c) := mul_le_mul_of_nonneg_left hηc.le (mul_nonneg hP hE)
          _ = _ := by rw [hcdef]; ring

end GlobalTheory.ShellMass
end
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.ShellZero

section
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

end

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma lintegral_nsq_transition_eq_chart_lintegral {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (E : La) (i : ι) (c : ℂ) (h : Y → ℝ) (hh : Measurable h)
    (h0 : ∀ y, 0 ≤ h y) (W : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (hW : MeasurableSet W)
    (hWt : W ⊆ (A.chart i).target) :
    ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W,
        ENNReal.ofReal (A.nsq (A.kap + E) (fun j y => A.g (A.kap + E) j i y * c) y * h y) ∂A.mu =
      ∫⁻ v in W, ENNReal.ofReal (‖c‖ ^ 2 * h ((A.chart i).symm v) *
        Real.exp (-A.ph E i ((A.chart i).symm v))) := by
  classical
  set D : ι → Y → ℂ := fun j y => A.g (A.kap + E) j i y * (c * (Real.sqrt (h y) : ℂ)) with hD
  have hsq : ∀ y, (‖(Real.sqrt (h y) : ℂ)‖) ^ 2 = h y := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (h0 y)]
  have hL : ∀ y, A.nsq (A.kap + E) (fun j y => A.g (A.kap + E) j i y * c) y * h y =
      A.nsq (A.kap + E) D y := by
    intro y
    simp only [_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq, hD, norm_mul, mul_pow, hsq]
    ring
  simp_rw [hL]
  rw [_root_.GlobalTheory.OTY.lintegral_nsq_chart_part n Y ι La A E i W D hW hWt]
  · refine setLIntegral_congr_fun hW (fun v hv => ?_)
    have hs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target (hWt hv)
    simp only [hD, A.g_self _ i hs, one_mul, norm_mul, mul_pow, hsq]
  · intro y hy _
    simp only [hD, A.g_self _ i hy, one_mul]
  · have hc : ContinuousOn (A.chart i).symm W :=
      (A.chart i).continuousOn_symm.mono hWt
    have hm : AEMeasurable (fun v => c * (Real.sqrt (h ((A.chart i).symm v)) : ℂ))
        (volume.restrict W) :=
      (aemeasurable_const.mul (Complex.measurable_ofReal.comp_aemeasurable
        ((Real.continuous_sqrt.measurable.comp hh).comp_aemeasurable (hc.aemeasurable hW))))
    refine hm.congr ?_
    filter_upwards [ae_restrict_mem hW] with v hv
    have hs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target (hWt hv)
    simp only [Function.comp, hD, A.g_self _ i hs, one_mul]


open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.ShellZero.shell_near_zero : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ P ∈ A.zeroSet s, _root_.GlobalTheory.Published.L2Extension.jacAt A s P ≠ 0 → ∀ (c : ℂ) (δ : ℝ), 0 < δ → ∃ N : Set Y, IsOpen N ∧ P ∈ N ∧ N ⊆ (A.chart (A.pick P)).source ∧ (∀ T : ℝ, 2 ≤ T → ∫⁻ y in N ∩ {y | -T - 1 ≤ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ∧ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * c) y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu ≤ ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ * _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c)) ∧ ∫⁻ y in N, ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) * A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * c) y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu < ⊤ := by
  intro n Y _ _ _ _ _ ι La _ A hn E L s hs P hP hJ c δ hδ
  set i := A.pick P with hi
  set e := A.chart i with he
  set Z : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.ReciprocityTheory.L2DbarEstimates.V n := A.zLoc (fun _ _ => 1) s i with hZ
  set lam : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => A.ph L i (e.symm v) with hlam
  set φ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => A.ph E i (e.symm v) with hφ
  set ψ : Y → ℝ := _root_.GlobalTheory.Published.L2Extension.psi A L s with hψdef
  have hPs : P ∈ e.source := A.mem_pick P
  have hp : e P ∈ e.target := e.map_source hPs
  have hZd : DifferentiableOn ℂ Z e.target := by
    have hk : ∀ k, DifferentiableOn ℂ (fun v => s k i (e.symm v) / 1) e.target := by
      intro k
      have := ((hs k).1 i)
      simpa [Set.preimage_univ, Set.inter_univ, Function.comp_def] using this
    have : DifferentiableOn ℂ (fun v => (EuclideanSpace.equiv (Fin n) ℂ).symm
        (fun k => s k i (e.symm v) / 1)) e.target :=
      (EuclideanSpace.equiv (Fin n) ℂ).symm.differentiable.comp_differentiableOn
        (differentiableOn_pi.2 hk)
    exact this
  have hZ0 : Z (e P) = 0 := by
    simp only [hZ, _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc, he]
    rw [(A.chart i).left_inv hPs]
    have hPk : ∀ k, s k i P = 0 := hP
    have h0 : (fun k => s k i P / 1) = 0 := funext fun k => by simp [hPk k]
    rw [h0]
    rfl
  have hdet : (fderiv ℂ Z (e P)).det ≠ 0 := hJ
  have hlamc : ContinuousOn lam e.target :=
    (A.continuousOn_ph L i).comp e.continuousOn_symm (fun v hv => e.map_target hv)
  have hφc : ContinuousOn φ e.target :=
    (A.continuousOn_ph E i).comp e.continuousOn_symm (fun v hv => e.map_target hv)
  have hψx : ∀ x ∈ e.source, ψ x = n * Real.log (‖Z (e x)‖ ^ 2 * Real.exp (-lam (e x))) := by
    intro x hx
    have h1 := A.sqn_s_eq (w0 := fun _ _ => (1 : ℂ)) hs hx one_ne_zero
    simp only [hψdef, _root_.GlobalTheory.Published.L2Extension.psi, h1, hlam, e.left_inv hx, hZ]
    rw [norm_one, one_pow, one_mul, mul_comm (Real.exp _)]
  have hψm : Measurable ψ := by
    simp only [hψdef, _root_.GlobalTheory.Published.L2Extension.psi]
    exact measurable_const.mul (Real.measurable_log.comp (A.continuous_sqn hs).measurable)
  obtain ⟨ρ, hρ, hball, hshell⟩ := _root_.GlobalTheory.ShellMass.shell_mass n hn (e P) e.target Z lam e.open_target hp hZd hZ0
    hdet hlamc φ (2 / δ) (1 / 30) hφc (by positivity) (by norm_num)
  set W : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n) := ball (e P) (ρ / 2) with hW
  have hWm : MeasurableSet W := measurableSet_ball
  have hWρ : W ⊆ ball (e P) ρ := ball_subset_ball (by linarith)
  have hWt : W ⊆ e.target := hWρ.trans hball
  set D : ι → Y → ℂ := fun j y => A.g (A.kap + E) j i y * c with hD
  have hψW : ∀ v ∈ W, ψ (e.symm v) = n * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v)) := by
    intro v hv
    rw [hψx _ (e.map_target (hWt hv)), e.right_inv (hWt hv)]
  refine ⟨e.source ∩ e ⁻¹' W, e.isOpen_inter_preimage isOpen_ball, ⟨hPs, mem_ball_self (by positivity)⟩,
    Set.inter_subset_left, ?_⟩
  have hpart1 : ∀ T : ℝ, 2 ≤ T → ∫⁻ y in (e.source ∩ e ⁻¹' W) ∩
      {y | -T - 1 ≤ δ * ψ y ∧ δ * ψ y ≤ -T + 1},
      ENNReal.ofReal (A.nsq (A.kap + E) D y * Real.exp (-ψ y)) ∂A.mu ≤
      ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
        _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c) := by
    intro T hT
    set S : Set Y := {y | -T - 1 ≤ δ * ψ y ∧ δ * ψ y ≤ -T + 1} with hS
    have hSm : MeasurableSet S :=
      (measurableSet_le measurable_const (measurable_const.mul hψm)).inter
        (measurableSet_le (measurable_const.mul hψm) measurable_const)
    set h : Y → ℝ := S.indicator (fun y => Real.exp (-ψ y)) with hh
    have hhm : Measurable h := (Real.measurable_exp.comp hψm.neg).indicator hSm
    have h0 : ∀ y, 0 ≤ h y := fun y => Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) y
    have hLHS : ∫⁻ y in (e.source ∩ e ⁻¹' W) ∩ S,
        ENNReal.ofReal (A.nsq (A.kap + E) D y * Real.exp (-ψ y)) ∂A.mu =
        ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + E) D y * h y) ∂A.mu := by
      rw [Set.inter_comm, ← Measure.restrict_restrict hSm, ← lintegral_indicator hSm]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ S
      · simp only [Set.indicator_of_mem hy, hh]
      · simp only [Set.indicator_of_notMem hy, hh, mul_zero, ENNReal.ofReal_zero]
    rw [hLHS]
    refine (lintegral_nsq_transition_eq_chart_lintegral A E i c h hhm h0 W hWm hWt).trans_le ?_
    set Ψ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => n * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v)) with hΨ
    set b : ℝ := (1 - T) / δ with hb
    set S' : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n) := {v | Z v ≠ 0 ∧ b - 2 / δ ≤ Ψ v ∧ Ψ v ≤ b} with hS'
    set G : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-Ψ v)) with hG
    have hpt : ∀ v ∈ W, ENNReal.ofReal (‖c‖ ^ 2 * h (e.symm v) * Real.exp (-A.ph E i (e.symm v))) ≤
        ENNReal.ofReal (‖c‖ ^ 2) * S'.indicator G v := by
      intro v hv
      by_cases hx : e.symm v ∈ S
      · have hψv := hψW v hv
        have h1 : δ * Ψ v ≤ -T + 1 := by
          have := hx.2
          rw [hψv] at this
          exact this
        have h2 : -T - 1 ≤ δ * Ψ v := by
          have := hx.1
          rw [hψv] at this
          exact this
        have hZv : Z v ≠ 0 := by
          intro hz
          have : Ψ v = 0 := by simp [hΨ, hz]
          rw [this, mul_zero] at h1
          linarith
        have hmem : v ∈ S' := by
          refine ⟨hZv, ?_, ?_⟩
          · rw [hb, div_sub_div_same, div_le_iff₀ hδ]
            linarith
          · rw [hb, le_div_iff₀ hδ]
            linarith
        rw [Set.indicator_of_mem hmem, hG, ← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        simp only [hh, Set.indicator_of_mem hx, hψv, hφ]
        ring
      · simp only [hh, Set.indicator_of_notMem hx, mul_zero, zero_mul, ENNReal.ofReal_zero]
        exact bot_le
    calc _ ≤ ∫⁻ v in W, ENNReal.ofReal (‖c‖ ^ 2) * S'.indicator G v := setLIntegral_mono' hWm hpt
      _ = ENNReal.ofReal (‖c‖ ^ 2) * ∫⁻ v in W, S'.indicator G v :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (‖c‖ ^ 2) * ∫⁻ v in ball (e P) ρ ∩ S', G v := by
          gcongr ENNReal.ofReal (‖c‖ ^ 2) * ?_
          calc ∫⁻ v in W, S'.indicator G v ≤ ∫⁻ v in S', G v ∂(volume.restrict W) :=
                lintegral_indicator_le _ _
            _ = ∫⁻ v in S' ∩ W, G v := by rw [Measure.restrict_restrict' hWm]
            _ ≤ ∫⁻ v in ball (e P) ρ ∩ S', G v :=
                lintegral_mono_set fun v hv => ⟨hWρ hv.2, hv.1⟩
      _ ≤ ENNReal.ofReal (‖c‖ ^ 2) * ENNReal.ofReal ((1 + 1 / 30) *
            (Real.pi ^ n / ((n - 1).factorial : ℝ) * (2 / δ / n)) *
            (Real.exp (-φ (e P) + n * lam (e P)) / ‖(fderiv ℂ Z (e P)).det‖ ^ 2)) := by
          gcongr ENNReal.ofReal (‖c‖ ^ 2) * ?_
          exact hshell b
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hJeq : _root_.GlobalTheory.Published.L2Extension.jacAt A s P = (fderiv ℂ Z (e P)).det := rfl
          have hφP : φ (e P) = A.ph E i P := by simp only [hφ, e.left_inv hPs]
          have hlamP : lam (e P) = A.ph L i P := by simp only [hlam, e.left_inv hPs]
          have hres : _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c = ‖c‖ ^ 2 /
              ‖(fderiv ℂ Z (e P)).det‖ ^ 2 * Real.exp (-A.ph E i P + n * A.ph L i P) := by
            unfold _root_.GlobalTheory.Published.L2Extension.resSq
            rw [hJeq, norm_div, div_pow]
          rw [hres, hφP, hlamP]
          have hJ0 : ‖(fderiv ℂ Z (e P)).det‖ ≠ 0 := norm_ne_zero_iff.mpr hdet
          have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
          set K := Real.pi ^ n / ((n - 1).factorial : ℝ) with hK
          set X := Real.exp (-A.ph E i P + n * A.ph L i P) with hX
          set J := ‖(fderiv ℂ Z (e P)).det‖ with hJdef
          have hK0 : 0 ≤ K := by positivity
          have hX0 : 0 ≤ X := (Real.exp_pos _).le
          have key : ‖c‖ ^ 2 * ((1 + 1 / 30) * (K * (2 / δ / n)) * (X / J ^ 2)) =
              62 / 30 * K / δ * (‖c‖ ^ 2 / J ^ 2 * X) * (1 / n) := by
            field_simp
            ring
          rw [key]
          refine mul_le_of_le_one_right (by positivity) ?_
          rw [div_le_one hnpos]
          exact_mod_cast hn
  refine ⟨hpart1, ?_⟩
  set N : Set Y := e.source ∩ e ⁻¹' W with hN
  have hNm : MeasurableSet N := (e.isOpen_inter_preimage isOpen_ball).measurableSet
  set Kc : ℝ≥0∞ := ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
        _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c) with hKc
  set F : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (1 / (1 + (δ * ψ y) ^ 2) *
      A.nsq (A.kap + E) D y * Real.exp (-ψ y)) with hF
  set w : ℕ → ℝ := fun m => 1 / (1 + ((m : ℝ) + 1) ^ 2) with hw
  set Sh : ℕ → Set Y := fun m => N ∩ {y | -((m : ℝ) + 2) - 1 ≤ δ * ψ y ∧
      δ * ψ y ≤ -((m : ℝ) + 2) + 1} with hSh
  set Hi : Set Y := N ∩ {y | -1 ≤ δ * ψ y} with hHi
  have hnsq : ∀ y, 0 ≤ A.nsq (A.kap + E) D y * Real.exp (-ψ y) :=
    fun y => mul_nonneg (A.nsq_nonneg _ _ _) (Real.exp_pos _).le

  have hshellF : ∀ m : ℕ, ∫⁻ y in Sh m, F y ∂A.mu ≤ ENNReal.ofReal (w m) * Kc := by
    intro m
    have hShm : MeasurableSet (Sh m) := hNm.inter
      ((measurableSet_le measurable_const (measurable_const.mul hψm)).inter
        (measurableSet_le (measurable_const.mul hψm) measurable_const))
    calc ∫⁻ y in Sh m, F y ∂A.mu ≤ ∫⁻ y in Sh m, ENNReal.ofReal (w m) *
          ENNReal.ofReal (A.nsq (A.kap + E) D y * Real.exp (-ψ y)) ∂A.mu := by
          refine setLIntegral_mono' hShm fun y hy => ?_
          have hy2 := hy.2.2
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          have hsq : ((m : ℝ) + 1) ^ 2 ≤ (δ * ψ y) ^ 2 := by nlinarith
          have hwle : 1 / (1 + (δ * ψ y) ^ 2) ≤ w m :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
          rw [hF, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hwle (hnsq y)
      _ = ENNReal.ofReal (w m) * ∫⁻ y in Sh m,
          ENNReal.ofReal (A.nsq (A.kap + E) D y * Real.exp (-ψ y)) ∂A.mu :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (w m) * Kc := by
          gcongr ENNReal.ofReal (w m) * ?_
          exact hpart1 ((m : ℝ) + 2) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)

  have hHiF : ∫⁻ y in Hi, F y ∂A.mu < ⊤ := by
    have hHim : MeasurableSet Hi := hNm.inter (measurableSet_le measurable_const
      (measurable_const.mul hψm))
    obtain ⟨C, hC⟩ := (isCompact_closedBall (e P) (ρ / 2)).exists_bound_of_continuousOn
      (hφc.mono ((closedBall_subset_ball (by linarith)).trans hball))
    calc ∫⁻ y in Hi, F y ∂A.mu ≤ ∫⁻ y in Hi, ENNReal.ofReal
          (A.nsq (A.kap + E) D y * (fun _ => Real.exp (1 / δ)) y) ∂A.mu := by
          refine setLIntegral_mono' hHim fun y hy => ?_
          have hy2 : -1 ≤ δ * ψ y := hy.2
          have hexp : Real.exp (-ψ y) ≤ Real.exp (1 / δ) := by
            refine Real.exp_le_exp.mpr ?_
            rw [le_div_iff₀ hδ]
            linarith
          have hw1 : 1 / (1 + (δ * ψ y) ^ 2) ≤ 1 := by
            rw [div_le_one (by positivity)]
            nlinarith
          refine ENNReal.ofReal_le_ofReal ?_
          calc 1 / (1 + (δ * ψ y) ^ 2) * A.nsq (A.kap + E) D y * Real.exp (-ψ y)
              ≤ 1 * A.nsq (A.kap + E) D y * Real.exp (-ψ y) := by
                gcongr
                exact A.nsq_nonneg _ _ _
            _ ≤ A.nsq (A.kap + E) D y * Real.exp (1 / δ) := by
                rw [one_mul]
                exact mul_le_mul_of_nonneg_left hexp (A.nsq_nonneg _ _ _)
      _ ≤ ∫⁻ y in N, ENNReal.ofReal
          (A.nsq (A.kap + E) D y * (fun _ => Real.exp (1 / δ)) y) ∂A.mu :=
          lintegral_mono_set Set.inter_subset_left
      _ = ∫⁻ v in W, ENNReal.ofReal (‖c‖ ^ 2 * Real.exp (1 / δ) *
          Real.exp (-A.ph E i (e.symm v))) :=
          lintegral_nsq_transition_eq_chart_lintegral A E i c (fun _ => Real.exp (1 / δ)) measurable_const
            (fun _ => (Real.exp_pos _).le) W hWm hWt
      _ ≤ ∫⁻ v in W, ENNReal.ofReal (‖c‖ ^ 2 * Real.exp (1 / δ) * Real.exp C) := by
          refine setLIntegral_mono' hWm fun v hv => ENNReal.ofReal_le_ofReal ?_
          have hv' : v ∈ closedBall (e P) (ρ / 2) := ball_subset_closedBall hv
          have hCv : -φ v ≤ C := (neg_le_abs _).trans (hC v hv')
          gcongr
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

  have hcover : N ⊆ Hi ∪ ⋃ m : ℕ, Sh m := by
    intro y hy
    by_cases h1 : -1 ≤ δ * ψ y
    · exact Or.inl ⟨hy, h1⟩
    · right
      push_neg at h1
      set t := -(δ * ψ y) with ht
      have ht1 : 1 ≤ t := by linarith
      have hfl : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht1)
      have hfle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
      have hlt : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
      refine Set.mem_iUnion.mpr ⟨⌊t⌋₊ - 1, hy, ?_, ?_⟩
      · rw [Nat.cast_sub hfl]
        push_cast
        linarith
      · rw [Nat.cast_sub hfl]
        push_cast
        linarith
  have hsum : Summable w := by
    have h2 : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa [Nat.cast_add, Nat.cast_one] using this
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) h2
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  calc ∫⁻ y in N, F y ∂A.mu ≤ ∫⁻ y in Hi ∪ ⋃ m : ℕ, Sh m, F y ∂A.mu := lintegral_mono_set hcover
    _ ≤ ∫⁻ y in Hi, F y ∂A.mu + ∫⁻ y in ⋃ m : ℕ, Sh m, F y ∂A.mu := lintegral_union_le _ _ _
    _ ≤ ∫⁻ y in Hi, F y ∂A.mu + ∑' m : ℕ, ENNReal.ofReal (w m) * Kc := by
        gcongr
        exact (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hshellF)
    _ < ⊤ := by
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
        exact ENNReal.add_lt_top.mpr ⟨hHiF, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ENNReal.ofReal_lt_top⟩

end GlobalTheory.OTY.ShellZero
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma continuous_sqn_of_isSec' {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) {L : La} {N : ℕ} {s : Fin N → ι → Y → ℂ}
    (hs : ∀ k, A.IsSec L (s k)) : Continuous (A.sqn L s) := by
  have hsum : A.sqn L s = fun y => ∑ k, A.nsq L (s k) y := by
    funext y
    rfl
  rw [hsum]
  refine continuous_finsetSum _ fun k _ => ?_
  have hk : A.IsSecOn L Set.univ (s k) := hs k
  exact continuousOn_univ.mp (_root_.ReciprocityTheory.L2DbarEstimates.Y.api_nsq_contOn A isOpen_univ hk)

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma mem_zeroSet_of_sqn_eq_zero {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) {L : La} {N : ℕ} (s : Fin N → ι → Y → ℂ) {y : Y}
    (hy : A.sqn L s y = 0) : y ∈ A.zeroSet s := by
  have hy' : ∑ k, A.nsq L (s k) y = 0 := hy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => A.nsq_nonneg L (s k) y)] at hy'
  simp only [_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zeroSet, Set.mem_setOf_eq]
  intro k
  have hk : ‖s k (A.pick y) y‖ ^ 2 * Real.exp (-A.ph L (A.pick y) y) = 0 :=
    hy' k (Finset.mem_univ _)
  have h2 := (mul_eq_zero.mp hk).resolve_right (Real.exp_pos _).ne'
  simpa using h2

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma lintegral_le_sum_of_pairwiseDisjoint_pieces {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (Z : Finset Y) (V W : Y → Set Y) (hd : (↑Z : Set Y).PairwiseDisjoint V)
    (hV : ∀ P ∈ Z, MeasurableSet (V P)) (hVW : ∀ P ∈ Z, V P ⊆ W P) (F : Y → ℝ≥0∞)
    (G : Y → Y → ℝ≥0∞) (hF0 : ∀ y, y ∉ ⋃ P ∈ Z, V P → F y = 0)
    (hFG : ∀ P ∈ Z, ∀ y ∈ V P, F y = G P y) :
    ∫⁻ y, F y ∂ν ≤ ∑ P ∈ Z, ∫⁻ y in W P, G P y ∂ν := by
  rw [← setLIntegral_eq_of_support_subset (s := ⋃ P ∈ Z, V P), lintegral_biUnion_finset hd hV]
  · refine Finset.sum_le_sum fun P hP => ?_
    rw [setLIntegral_congr_fun (hV P hP) (fun y hy => hFG P hP y hy)]
    exact lintegral_mono_set (hVW P hP)
  · intro y hy
    by_contra hyn
    exact hy (hF0 y hyn)

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma resSq_nonneg {n : ℕ} {Y : Type*} [TopologicalSpace Y]
    [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*}
    [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (E L : La) (s : Fin n → ι → Y → ℂ) (P : Y) (c : ℂ) :
    0 ≤ _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c := by
  unfold _root_.GlobalTheory.Published.L2Extension.resSq
  positivity


open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.exists_local_extension : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ hS : (A.zeroSet s).Finite, (∀ P ∈ A.zeroSet s, _root_.GlobalTheory.Published.L2Extension.jacAt A s P ≠ 0) → ∀ (f : Y → ℂ) (δ : ℝ), 0 < δ → ∃ (Ω : Set Y) (h : ι → Y → ℂ) (m : ℝ), (IsOpen Ω ∧ A.IsSecOn (A.kap + E) Ω h ∧ (∀ i y, y ∉ Ω → h i y = 0)) ∧ 0 < m ∧ (∀ y, A.sqn L s y < m → y ∈ Ω) ∧ (∀ P ∈ A.zeroSet s, h (A.pick P) P = f P) ∧ (∀ T : ℝ, 2 ≤ T → ∫⁻ y in {y | -T - 1 ≤ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ∧ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) h y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu ≤ ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ * ∑ P ∈ hS.toFinset, _root_.GlobalTheory.Published.L2Extension.resSq A E L s P (f P))) ∧ ∫⁻ y, ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) * A.nsq (A.kap + E) h y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu < ⊤ := by
  intro n Y _ _ _ _ _ _ ι La _ A hn E L s hs hS hjac f δ hδ
  choose! N hNo hPN hNsub hNT hNfin using fun P (hP : P ∈ A.zeroSet s) =>
    _root_.GlobalTheory.OTY.ShellZero.shell_near_zero n Y ι La A hn E L s hs P hP (hjac P hP) (f P) δ hδ
  obtain ⟨U, hU, hUd⟩ := hS.t2_separation
  set Z := hS.toFinset with hZ
  have hmemZ : ∀ {P}, P ∈ Z → P ∈ A.zeroSet s := fun hP => hS.mem_toFinset.mp hP
  have hd : (↑Z : Set Y).PairwiseDisjoint (fun P => N P ∩ U P) := by
    intro P hP Q hQ hPQ
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right
      (hUd (hmemZ (Finset.mem_coe.mp hP)) (hmemZ (Finset.mem_coe.mp hQ)) hPQ)
  have hVo : ∀ P ∈ Z, IsOpen (N P ∩ U P) := fun P hP => (hNo P (hmemZ hP)).inter (hU P).2
  obtain ⟨h, hh⟩ : ∃ h : ι → Y → ℂ, h = fun i y =>
      ∑ P ∈ Z, (N P ∩ U P).indicator (fun y => A.g (A.kap + E) i (A.pick P) y * f P) y :=
    ⟨_, rfl⟩
  have hloc : ∀ P ∈ Z, ∀ y ∈ N P ∩ U P, ∀ i, h i y = A.g (A.kap + E) i (A.pick P) y * f P := by
    intro P hP y hy i
    rw [hh]
    dsimp only
    rw [Finset.sum_eq_single P]
    · exact Set.indicator_of_mem hy _
    · intro Q hQ hQP
      refine Set.indicator_of_notMem (fun hyQ => ?_) _
      exact Set.disjoint_left.mp (hd (Finset.mem_coe.mpr hQ) (Finset.mem_coe.mpr hP) hQP) hyQ hy
    · intro hPn
      exact absurd hP hPn
  have hout : ∀ y, y ∉ ⋃ P ∈ Z, N P ∩ U P → ∀ i, h i y = 0 := by
    intro y hy i
    rw [hh]
    exact Finset.sum_eq_zero fun P hP =>
      Set.indicator_of_notMem (fun hyP => hy (Set.mem_iUnion₂.mpr ⟨P, hP, hyP⟩)) _
  have hZΩ : ∀ y ∈ A.zeroSet s, y ∈ ⋃ P ∈ Z, N P ∩ U P := fun y hy =>
    Set.mem_iUnion₂.mpr ⟨y, hS.mem_toFinset.mpr hy, hPN y hy, (hU y).1⟩
  have hΩo : IsOpen (⋃ P ∈ Z, N P ∩ U P) :=
    isOpen_iUnion fun P => isOpen_iUnion fun hP => hVo P hP
  have hnsq : ∀ P ∈ Z, ∀ y ∈ N P ∩ U P, A.nsq (A.kap + E) h y =
      A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y := by
    intro P hP y hy
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq
    rw [hloc P hP y hy]
  have hnsq0 : ∀ y, y ∉ ⋃ P ∈ Z, N P ∩ U P → A.nsq (A.kap + E) h y = 0 := by
    intro y hy
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq
    rw [hout y hy]
    simp
  obtain ⟨m, hm, hmΩ⟩ : ∃ m : ℝ, 0 < m ∧ ∀ y, A.sqn L s y < m → y ∈ ⋃ P ∈ Z, N P ∩ U P := by
    rcases (⋃ P ∈ Z, N P ∩ U P)ᶜ.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun y _ => ?_⟩
      by_contra hy
      have hyc : y ∈ (⋃ P ∈ Z, N P ∩ U P)ᶜ := hy
      rw [he] at hyc
      exact hyc
    · obtain ⟨x0, hx0, hmin⟩ := hΩo.isClosed_compl.isCompact.exists_isMinOn hne
        (continuous_sqn_of_isSec' A hs).continuousOn
      refine ⟨A.sqn L s x0, lt_of_le_of_ne (A.sqn_nonneg L s x0)
        (fun h0 => hx0 (hZΩ x0 (mem_zeroSet_of_sqn_eq_zero A s h0.symm))), fun y hy => ?_⟩
      by_contra hyΩ
      exact (not_le.mpr hy) (isMinOn_iff.mp hmin y hyΩ)
  refine ⟨⋃ P ∈ Z, N P ∩ U P, h, m, ⟨hΩo, ⟨?_, ?_⟩, fun i y hy => hout y hy i⟩, hm, hmΩ, ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hx.2
    have hWo : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (N P ∩ U P)) :=
      (A.chart i).isOpen_inter_preimage_symm (hVo P hP)
    have hW : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (N P ∩ U P) ∈ 𝓝 x :=
      hWo.mem_nhds ⟨hx.1, hxP⟩
    have hg : DifferentiableAt ℂ (A.g (A.kap + E) i (A.pick P) ∘ (A.chart i).symm) x := by
      refine ((A.holo_g (A.kap + E) i (A.pick P)).mono ?_).differentiableAt hW
      intro z hz
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.ovl
      exact ⟨hz.1, hNsub P (hmemZ hP) hz.2.1⟩
    refine ((hg.mul_const (f P)).congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hW] with z hz
    simp only [Function.comp_apply]
    exact hloc P hP _ hz.2 i
  · intro i j y hy hi hj
    obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.mp hy
    rw [hloc P hP y hyP i, hloc P hP y hyP j, ← mul_assoc,
      ← A.g_cocycle _ i j _ y hi hj (hNsub P (hmemZ hP) hyP.1)]
  · intro P hP
    rw [hloc P (hS.mem_toFinset.mpr hP) P ⟨hPN P hP, (hU P).1⟩, A.g_self _ _ (A.mem_pick P),
      one_mul]
  · intro T hT
    refine (lintegral_le_sum_of_pairwiseDisjoint_pieces _ Z (fun P => N P ∩ U P) N hd
      (fun P hP => (hVo P hP).measurableSet) (fun P _ => Set.inter_subset_left) _
      (fun P y => ENNReal.ofReal (A.nsq (A.kap + E)
        (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y *
          Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)))
      (fun y hy => by simp only [hnsq0 y hy, zero_mul, ENNReal.ofReal_zero])
      (fun P hP y hy => by simp only [hnsq P hP y hy])).trans ?_
    calc _ ≤ ∑ P ∈ Z, ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
          _root_.GlobalTheory.Published.L2Extension.resSq A E L s P (f P)) := by
          refine Finset.sum_le_sum fun P hP => ?_
          rw [Measure.restrict_restrict (hNo P (hmemZ hP)).measurableSet]
          exact hNT P (hmemZ hP) T hT
      _ = _ := by
          rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          intro P _
          exact mul_nonneg (by positivity) (resSq_nonneg A E L s P (f P))
  · refine lt_of_le_of_lt (lintegral_le_sum_of_pairwiseDisjoint_pieces A.mu Z (fun P => N P ∩ U P) N hd
      (fun P hP => (hVo P hP).measurableSet) (fun P _ => Set.inter_subset_left) _
      (fun P y => ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) *
        A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * f P) y *
          Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)))
      (fun y hy => by simp only [hnsq0 y hy, mul_zero, zero_mul, ENNReal.ofReal_zero])
      (fun P hP y hy => by simp only [hnsq P hP y hy])) ?_
    exact ENNReal.sum_lt_top.2 fun P hP => hNfin P (hmemZ hP)

end GlobalTheory.OTY
