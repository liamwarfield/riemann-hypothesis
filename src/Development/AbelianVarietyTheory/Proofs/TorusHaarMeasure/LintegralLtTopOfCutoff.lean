module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddInvFirstMinimumLeOfMajorants
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KronHolPsiOf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfLePolyExp
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLtTopOfCutoff
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.KronValue

theorem lintegral_ball_lt_top {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {d w g H : V n → ℝ}
    (hd : ContinuousOn d Ω) (hdpos : ∀ z ∈ Ω, 0 < d z)
    (hw : ContinuousOn w Ω) (hwpos : ∀ z ∈ Ω, 0 < w z) {ρ : ℝ} (hρ : 0 < ρ)
    (hB : Metric.closedBall (0 : V n) ρ ⊆ Ω) (hg : ∀ z, 0 ≤ g z)
    (hH : ∀ z ∈ Metric.ball (0 : V n) ρ, H z = g z * w z)
    (hfin : ∫⁻ z, ENNReal.ofReal (H z)
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤) :
    ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (g z) < ⊤ := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal (d z)) (volume.restrict Ω) :=
    (hd.aemeasurable hΩ.measurableSet).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hm
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hfin
  obtain ⟨z0, hz0, hmin⟩ := (isCompact_closedBall (0 : V n) ρ).exists_isMinOn
    ⟨0, Metric.mem_closedBall_self hρ.le⟩ ((hd.mul hw).mono hB)
  set c := d z0 * w z0 with hc
  have hcpos : 0 < c := mul_pos (hdpos _ (hB hz0)) (hwpos _ (hB hz0))
  have hsub : Metric.ball (0 : V n) ρ ⊆ Ω := Metric.ball_subset_closedBall.trans hB
  calc ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal (g z)
      ≤ ∫⁻ z in Metric.ball (0 : V n) ρ, ENNReal.ofReal c⁻¹ *
          ((fun z => ENNReal.ofReal (d z)) * fun z => ENNReal.ofReal (H z)) z := by
        refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
        have h1 : c ≤ d z * w z := hmin (Metric.ball_subset_closedBall hz)
        simp only [Pi.mul_apply]
        rw [← ENNReal.ofReal_mul (hdpos z (hsub hz)).le, ← ENNReal.ofReal_mul (inv_pos.2 hcpos).le,
          hH z hz]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_inv_mul_iff₀ hcpos]
        nlinarith [mul_le_mul_of_nonneg_right h1 (hg z)]
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ z in Metric.ball (0 : V n) ρ,
          ((fun z => ENNReal.ofReal (d z)) * fun z => ENNReal.ofReal (H z)) z :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lintegral_mono_set hsub).trans_lt hfin)

theorem lintegral_lt_top_of_cutoff {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {d w S : V n → ℝ}
    {χ F : V n → ℂ} (hd : ContinuousOn d Ω)
    (hw : ContinuousOn w Ω) (hwpos : ∀ z ∈ Ω, 0 < w z) {δ : ℝ}
    (hB : Metric.closedBall (0 : V n) δ ⊆ Ω) (hχ : Continuous χ) (hχ0 : ∀ z, δ ≤ ‖z‖ → χ z = 0)
    {M : ℝ} (hM : ∀ z ∈ Ω, S z ≤ M) (hS : ∀ᵐ z ∂(volume.restrict Ω), 0 < S z) {p : ℝ} (hp : 0 ≤ p)
    (hfin : ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z * S z ^ (-p))
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤) :
    ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * w z)
      ∂((volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z)) < ⊤ := by
  set μ := (volume.restrict Ω).withDensity fun z => ENNReal.ofReal (d z) with hμ
  have hK := isCompact_closedBall (0 : V n) δ
  have hKm : MeasurableSet (Metric.closedBall (0 : V n) δ) := hK.measurableSet
  have hμK : μ (Metric.closedBall 0 δ) < ⊤ := by
    rw [hμ, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.2 hB]
    exact Integrable.lintegral_lt_top ((hd.mono hB).integrableOn_compact hK)
  obtain ⟨B, hBd⟩ := hK.exists_bound_of_continuousOn
    (f := fun z => 2 * (‖χ z‖ ^ 2 * w z))
    (continuousOn_const.mul ((hχ.norm.pow 2).continuousOn.mul (hw.mono hB)))
  have hac : μ ≪ volume.restrict Ω := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ z ∂μ, ENNReal.ofReal (‖F z‖ ^ 2 * w z) ≤
      (Metric.closedBall (0 : V n) δ).indicator (fun _ => ENNReal.ofReal B) z +
        ENNReal.ofReal (2 * M ^ p) * ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z * S z ^ (-p)) := by
    filter_upwards [hac.ae_le hS, hac.ae_le (ae_restrict_mem hΩ.measurableSet)] with z hz hzΩ
    have hz : 0 < S z := hz
    have hzΩ : z ∈ Ω := hzΩ
    have hMpos : 0 < M := hz.trans_le (hM z hzΩ)
    have hwz := hwpos z hzΩ
    have h1 : ENNReal.ofReal (2 * (‖χ z‖ ^ 2 * w z)) ≤
        (Metric.closedBall (0 : V n) δ).indicator (fun _ => ENNReal.ofReal B) z := by
      by_cases hzK : z ∈ Metric.closedBall (0 : V n) δ
      · rw [Set.indicator_of_mem hzK]
        exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hBd z hzK))
      · have : δ ≤ ‖z‖ := by
          rw [mem_closedBall_zero_iff, not_le] at hzK; exact hzK.le
        simp [hχ0 z this]
    have h2 : 1 ≤ M ^ p * S z ^ (-p) := by
      rw [Real.rpow_neg hz.le, ← div_eq_mul_inv, one_le_div (Real.rpow_pos_of_pos hz p)]
      exact Real.rpow_le_rpow hz.le (hM z hzΩ) hp
    have h3 : ‖F z‖ ^ 2 ≤ 2 * ‖χ z‖ ^ 2 + 2 * ‖χ z - F z‖ ^ 2 := by
      have : ‖F z‖ ≤ ‖χ z‖ + ‖χ z - F z‖ := by
        simpa using norm_sub_le (χ z) (χ z - F z)
      nlinarith [norm_nonneg (F z), norm_nonneg (χ z), norm_nonneg (χ z - F z),
        sq_nonneg (‖χ z‖ - ‖χ z - F z‖)]
    have hA : 0 ≤ ‖χ z - F z‖ ^ 2 * w z := by positivity
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine le_trans ?_ (add_le_add_left h1 _)
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_add (by positivity)
      (mul_nonneg (by positivity) (mul_nonneg hA (Real.rpow_nonneg hz.le _)))).le
    nlinarith [mul_le_mul_of_nonneg_right h3 hwz.le, mul_le_mul_of_nonneg_right h2 hA]
  refine (lintegral_mono_ae hae).trans_lt ?_
  rw [lintegral_add_left (measurable_const.indicator hKm), lintegral_indicator_const hKm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμK,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem pnorm_eq {r : ℕ} (X : Data E r) (L : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm L P x = ‖P x‖ * X.nfac L x := rfl

theorem value_and_integrability : (VanishAtSStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (la L : Wt X.Ψ r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) (ψ : Frame X.Ψ r → ℝ) (x0 : Frame X.Ψ r) (bb ε δ : ℝ) (χ F : V (nd X) → ℂ), 0 < nd X → IsOrth X x0 → X.IsBddSec L w0 → (∀ k, X.IsBddSec L (s k)) → ContinuousOn ψ X.dom → (∃ C : ℝ, ∀ x ∈ X.dom, ψ x ≤ C) → 0 ≤ bb → 0 < ε → Metric.closedBall (0 : V (nd X)) δ ⊆ OmF X x0 → Continuous χ → (∀ z, ‖z‖ ≤ ε → χ z = 1) → (∀ z, δ ≤ ‖z‖ → χ z = 0) → DifferentiableOn ℂ F (OmF X x0) → ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z * (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ → w0 x0 ≠ 0 → (∀ k, s k x0 = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => s k (cpt X (x0) z) / w0 (cpt X (x0) z) : V (nd X))) 0).det ≠ 0 → F 0 = 1 ∧ InAt X x0 (X.dom.indicator fun x => ENNReal.ofReal (Real.exp (-(phla X la x + ψ x)))) bb F ∧ ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom → ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤) := by
  intro hV r X la L w0 s ψ x0 bb ε δ χ F hn ho hw0 hs hψ hψC hbb hε hB hχ hχ1 hχ0 hF hfin hw0x hsx hdet
  have hΩ := OntoB.isOpen_OmF X x0
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := IW.zero_mem_OmF X x0 ho
  have hcpt : Continuous (cpt X x0) := (OntoB.cd_cpt X x0).continuous
  set w : V (nd X) → ℝ := fun z =>
    Real.exp (-(phla X la (cpt X x0 z) + ψ (cpt X x0 z))) / kaF X x0 bb z with hwdef
  have hka : ∀ z, 0 < kaF X x0 bb z := fun z => Real.exp_pos _
  have hwpos : ∀ z ∈ OmF X x0, 0 < w z := fun z _ => div_pos (Real.exp_pos _) (hka z)
  have hw : ContinuousOn w (OmF X x0) := by
    have h1 := OntoE.expPhla_cont X x0 la
    have h2 : ContinuousOn (fun z => Real.exp (-ψ (cpt X x0 z))) (OmF X x0) :=
      Real.continuous_exp.comp_continuousOn (hψ.comp hcpt.continuousOn fun _ hz => hz).neg
    have h3 : ContinuousOn (kaF X x0 bb) (OmF X x0) := fun z hz =>
      (OntoB.ka_contDiffAt bb hz).continuousAt.continuousWithinAt
    refine ((h1.mul h2).div h3 fun z _ => (hka z).ne').congr fun z _ => ?_
    simp only [hwdef, Pi.div_apply, Pi.mul_apply]
    rw [← Real.exp_add, neg_add]
  have hfin' : ∫⁻ z, ENNReal.ofReal (‖χ z - F z‖ ^ 2 * w z *
      (∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ∂muF X x0 < ⊤ := by
    simpa only [hwdef, mul_div_assoc] using hfin
  have hS : ∀ z, ∑ k, X.pnorm L (s k) (cpt X x0 z) ^ 2 =
      (∑ k, ‖s k (cpt X x0 z)‖ ^ 2) * X.nfac L (cpt X x0 z) ^ 2 := fun z => by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [pnorm_eq, mul_pow]
  have hsd : ∀ k, DifferentiableOn ℂ (fun z => s k (cpt X x0 z)) (OmF X x0) := fun k =>
    OntoB.hol_comp X x0 (hs k).1.1
  have hmain : ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 * w z) ∂muF X x0 < ⊤ := by
    choose C hC using fun k => (hs k).2
    refine lintegral_lt_top_of_cutoff hΩ OntoB.densF_continuousOn hw hwpos hB hχ hχ0
      (M := ∑ k, C k ^ 2) (fun z hz => Finset.sum_le_sum fun k _ => ?_) ?_ (Nat.cast_nonneg _) hfin'
    · have hp : 0 ≤ X.pnorm L (s k) (cpt X x0 z) := by
        rw [pnorm_eq]; exact mul_nonneg (norm_nonneg _) (OntoE.nfac_pos X x0 hz).le
      exact pow_le_pow_left₀ hp (hC k _ hz) 2
    · obtain ⟨k, hk⟩ := HE.coord_ne_of_det hn hdet
      have hne : ∃ z ∈ OmF X x0, s k (cpt X x0 z) ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hk
        filter_upwards [hΩ.mem_nhds h0] with z hz
        simp [hall z hz]
      have hnull := OntoD.null_zero hΩ (OmFConnStatement_holds r X x0 ho) (hsd k) hne
      rw [ae_restrict_iff' hΩ.measurableSet]
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz hzΩ
      have hsk : s k (cpt X x0 z) ≠ 0 := fun h => hz ⟨hzΩ, h⟩
      rw [hS]
      refine mul_pos ?_ (pow_pos (OntoE.nfac_pos X x0 hzΩ) 2)
      exact Finset.sum_pos' (fun _ _ => by positivity)
        ⟨k, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hsk) 2⟩
  have haeΩ : ∀ᵐ z ∂muF X x0, z ∈ OmF X x0 :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ.measurableSet)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨Δ, zOf, bOf, -, -, -, -, -, hLU⟩ := lu_holds r X x0 ho
    have hz : ∀ z ∈ OmF X x0, zOf (cpt X x0 z) = z := fun z hz => by
      have := (hLU z hz _ (ExtFPf.oneF_mem X)).2.1
      rwa [ExtFPf.rmul_oneF] at this
    obtain ⟨ρ0, hρ0, hρB⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds h0)
    set ρ := min ρ0 ε
    have hρ : 0 < ρ := lt_min hρ0 hε
    have hcB : Metric.closedBall (0 : V (nd X)) ρ ⊆ OmF X x0 :=
      (Metric.closedBall_subset_closedBall (min_le_left _ _)).trans hρB
    have hbB : Metric.ball (0 : V (nd X)) ρ ⊆ OmF X x0 := Metric.ball_subset_closedBall.trans hcB
    have key := hV r X x0 hn ho (IW.orth_mem_dom X x0 ho) (fun y => 1 - F (zOf y)) w0 s ρ hρ
      (((differentiableOn_const (1 : ℂ)).sub (hF.mono hbB)).congr fun z hz' => by
        simp [hz z (hbB hz')])
      (fun k => (hsd k).mono hbB) ((OntoB.hol_comp X x0 hw0.1.1).mono hbB) hw0x hsx hdet ?_
    · have h00 : zOf x0 = 0 := by simpa [IW.cpt_zero] using hz 0 h0
      simp only [h00] at key
      exact (sub_eq_zero.1 key).symm
    · refine lintegral_ball_lt_top hΩ OntoB.densF_continuousOn (fun z => OntoB.densF_pos)
        (w := fun z => w z * (X.nfac L (cpt X x0 z) ^ 2) ^ (-(nd X : ℝ))) ?_ ?_ hρ hcB ?_ ?_ hfin'
      · exact hw.mul (((OntoE.nfac_cont X x0 L).pow 2).rpow_const fun z hz' =>
          Or.inl (pow_pos (OntoE.nfac_pos X x0 hz') 2).ne')
      · exact fun z hz' => mul_pos (hwpos z hz')
          (Real.rpow_pos_of_pos (pow_pos (OntoE.nfac_pos X x0 hz') 2) _)
      · intro z; positivity
      · intro z hz'
        have : ‖z‖ ≤ ε := (mem_ball_zero_iff.1 hz').le.trans (min_le_right _ _)
        rw [hS, Real.mul_rpow (by positivity) (by positivity), hχ1 z this, hz z (hbB hz')]
        ring
  · unfold InAt
    refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hmain
    filter_upwards [haeΩ] with z hz
    have hz' : cpt X x0 z ∈ X.dom := hz
    rw [Set.indicator_of_mem hz', ← ENNReal.ofReal_mul (div_nonneg (by positivity) (hka z).le)]
    congr 1
    simp only [hwdef]; ring
  · intro C _ _
    obtain ⟨A, hA⟩ := hψC
    refine (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt ?_
    refine lt_of_le_of_lt (lintegral_mono_ae (g := fun z => ENNReal.ofReal (Real.exp A) *
      ENNReal.ofReal (‖F z‖ ^ 2 * w z)) ?_) ?_
    · filter_upwards [haeΩ] with z hz
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simp only [hwdef, kaF]
      rw [← Real.exp_sub, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      nlinarith [hA _ hz, mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)]
    · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmain

end GlobalTheory.KronValue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealRpowNegLe
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivMetricPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem _root_.GlobalTheory.Up.DivMetricPf.exp_neg_phla {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    Real.exp (-_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la x) = X.nfac la x ^ 2 := by
  have hpos := _root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla
  rw [show -(-2 * Real.log (X.nfac la x)) = Real.log (X.nfac la x) + Real.log (X.nfac la x) by
    ring, Real.exp_add, Real.exp_log hpos]
  ring

theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_rmul (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = X.pnorm la P x :=
  _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx b hb

theorem _root_.GlobalTheory.Up.DivMetricPf.pnorm_lact (hN : _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E)) {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = X.pnorm la P x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement at hN
  change ‖P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x)‖ * X.nfac la (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = ‖P x‖ * X.nfac la x
  rw [hP.2.2 γ hγ x hx, norm_mul, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE.chi_norm X la hγ, one_mul, hN r X la γ hγ x hx]

theorem _root_.GlobalTheory.Up.DivMetricPf.measurable_cut {f : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ}
    (hf : ContinuousOn f X.dom) :
    Measurable (X.dom.indicator fun x => ENNReal.ofReal (f x)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise (ENNReal.continuous_ofReal.comp_continuousOn hf)
    continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet

theorem _root_.GlobalTheory.Up.DivMetricPf.exists_sum_le {N : ℕ} {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r}
    {P : Fin N → _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ} (hP : ∀ k, X.IsBddSec la (P k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ X.dom, ∑ k, X.pnorm la (P k) x ^ 2 ≤ C := by
  choose C hC using fun k => (hP k).2
  refine ⟨1 + ∑ k, C k ^ 2, by positivity, fun x hx => ?_⟩
  have hle : ∀ k, X.pnorm la (P k) x ^ 2 ≤ C k ^ 2 := by
    intro k
    have h0 : 0 ≤ X.pnorm la (P k) x := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      exact mul_nonneg (norm_nonneg _) (_root_.ReciprocityTheory.ChartRestriction.G.FD.FlowCoefficientBounds.nfac_pos X hx la).le
    exact pow_le_pow_left₀ h0 (hC k x hx) 2
  calc ∑ k, X.pnorm la (P k) x ^ 2 ≤ ∑ k, C k ^ 2 := Finset.sum_le_sum fun k _ => hle k
    _ ≤ 1 + ∑ k, C k ^ 2 := by linarith

theorem _root_.GlobalTheory.Up.DivMetricPf.ofReal_rpow_neg_le {a C t : ℝ} (hC : 0 < C) (h : a ≤ C) (ht : 0 ≤ t) :
    ENNReal.ofReal (C ^ (-t)) ≤ ENNReal.ofReal a ^ (-t) := by
  rcases lt_or_ge 0 a with ha | ha
  · rw [ENNReal.ofReal_rpow_of_pos ha]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ha h (by linarith))
  · rw [ENNReal.ofReal_of_nonpos ha]
    rcases ht.lt_or_eq with ht | ht
    · rw [ENNReal.zero_rpow_of_neg (by linarith)]
      exact le_top
    · subst ht
      simp

variable (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ)

end GlobalTheory.Up.DivMetricPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.VanishOfSimpleZero
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.VanishAtSimpleZero

open Filter Metric

theorem lintegral_eq_top {n : ℕ} (hn : 0 < n) {g S : V n → ℝ} {a c ρ : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hρ : 0 < ρ) (hg : ∀ᶠ z in 𝓝 (0 : V n), a ≤ g z)
    (hS : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < S z ∧ S z ≤ c * ‖z‖ ^ 2) :
    ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) = ⊤ := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hg.and hS)
  have hr0 : 0 < min ε ρ := lt_min hε hρ
  have hsubε : ball (0 : V n) (min ε ρ) ⊆ ball 0 ε := ball_subset_ball (min_le_left _ _)
  have hsubρ : ball (0 : V n) (min ε ρ) ⊆ ball 0 ρ := ball_subset_ball (min_le_right _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h0 : ∀ᵐ z ∂(volume : Measure (V n)), z ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.ofPred_eq_eq_singleton]
    exact measure_singleton 0
  have hinf : ∫⁻ z in ball (0 : V n) (min ε ρ), ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) = ⊤ := by
    have hδ : Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
    have hT := ReciprocityTheory.L2DbarEstimates.I.vanish_div n hn ReciprocityTheory.L2DbarEstimates.C.mvDiv hr0 hc hδ
    refine top_unique (le_of_tendsto' hT fun k => ?_)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz _ => ?_))
    have hpos : 0 < c * ‖z‖ ^ 2 := mul_pos hc (pow_pos (norm_pos_iff.2 hz) 2)
    refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hpos ?_ ?_)
    · have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    · simp
  have hlow : ENNReal.ofReal a * ∫⁻ z in ball (0 : V n) (min ε ρ),
      ENNReal.ofReal ((c * ‖z‖ ^ 2) ^ (-(n : ℝ))) ≤
      ∫⁻ z in ball (0 : V n) ρ, ENNReal.ofReal (g z * S z ^ (-(n : ℝ))) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans ?_ (lintegral_mono_set hsubρ)
    refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_ball).2 (h0.mono fun z hz hzb => ?_))
    obtain ⟨hgz, hSz⟩ := hball z (hsubε hzb)
    obtain ⟨hS0, hSle⟩ := hSz hz
    rw [← ENNReal.ofReal_mul ha.le]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hgz (Real.rpow_le_rpow_of_nonpos hS0 hSle (by simp))
      (Real.rpow_nonneg (by positivity) _) (ha.le.trans hgz))
  rw [hinf, ENNReal.mul_top (by simpa using ha)] at hlow
  exact top_unique hlow

theorem vanish_of_simple_zero {n : ℕ} (hn : 0 < n) {u w : V n → ℂ} {s : Fin n → V n → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hu : ContinuousAt u 0) (hs : ∀ k, DifferentiableAt ℂ (s k) 0)
    (hw : DifferentiableAt ℂ w 0) (hw0 : w 0 ≠ 0) (hs0 : ∀ k, s k 0 = 0)
    (hdet : (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => s k z / w z : V n)) 0).det ≠ 0)
    (hint : ∫⁻ z in ball (0 : V n) ρ,
      ENNReal.ofReal (‖u z‖ ^ 2 * (∑ k, ‖s k z‖ ^ 2) ^ (-(n : ℝ))) < ⊤) : u 0 = 0 := by
  by_contra hu0
  set f : V n → V n := fun z => (WithLp.toLp 2 fun k => s k z / w z : V n) with hf
  have hfd : DifferentiableAt ℂ f 0 := by
    by_contra hnd
    apply hdet
    rw [fderiv_zero_of_not_differentiableAt hnd]
    simp [ContinuousLinearMap.det, LinearMap.det_zero, hn.ne']
  have hf0 : f 0 = 0 := by
    ext k
    simp [hf, hs0 k]
  obtain ⟨δ, hδ, hiso⟩ := ReciprocityTheory.ChartRestriction.G.AR.Up.HE.iso_zero hfd.hasFDerivAt hdet hf0
  have hSpos : ∀ᶠ z in 𝓝 (0 : V n), z ≠ 0 → 0 < ∑ k, ‖s k z‖ ^ 2 := by
    filter_upwards [closedBall_mem_nhds (0 : V n) hδ] with z hz hz0
    refine lt_of_le_of_ne (Finset.sum_nonneg fun k _ => by positivity) (Ne.symm fun hsum => hz0 ?_)
    refine hiso z hz ?_
    have hk : ∀ k, s k z = 0 := fun k => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by positivity)).1 hsum k (Finset.mem_univ _)
      simpa using this
    ext k
    simp [hf, hk k]
  have hbig : ∀ k, ∃ C > 0, ∀ᶠ z in 𝓝 (0 : V n), ‖s k z‖ ≤ C * ‖z‖ := fun k => by
    obtain ⟨C, hC, hCw⟩ := ((hs k).hasFDerivAt.isBigO_sub).exists_pos
    refine ⟨C, hC, hCw.bound.mono fun z hz => ?_⟩
    simpa [hs0 k] using hz
  choose C hC hCb using hbig
  have hSle : ∀ᶠ z in 𝓝 (0 : V n), ∑ k, ‖s k z‖ ^ 2 ≤ (∑ k, C k ^ 2 + 1) * ‖z‖ ^ 2 := by
    filter_upwards [Filter.eventually_all.2 hCb] with z hz
    calc ∑ k, ‖s k z‖ ^ 2 ≤ ∑ k, (C k * ‖z‖) ^ 2 :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hz k) 2
      _ = (∑ k, C k ^ 2) * ‖z‖ ^ 2 := by rw [Finset.sum_mul]; simp [mul_pow]
      _ ≤ _ := by nlinarith [sq_nonneg ‖z‖]
  have hpos : 0 < ‖u 0‖ ^ 2 := pow_pos (norm_pos_iff.2 hu0) 2
  have hcont : ContinuousAt (fun z => ‖u z‖ ^ 2) 0 := hu.norm.pow 2
  have hg : ∀ᶠ z in 𝓝 (0 : V n), ‖u 0‖ ^ 2 / 2 ≤ ‖u z‖ ^ 2 :=
    hcont.eventually (le_mem_nhds (show ‖u 0‖ ^ 2 / 2 < ‖u 0‖ ^ 2 by linarith))
  have htop := lintegral_eq_top hn (g := fun z => ‖u z‖ ^ 2) (S := fun z => ∑ k, ‖s k z‖ ^ 2)
    (by positivity) (by positivity : (0 : ℝ) < ∑ k, C k ^ 2 + 1) hρ hg
    (by filter_upwards [hSpos, hSle] with z h1 h2 hz0 using ⟨h1 hz0, h2⟩)
  exact absurd hint (by rw [htop]; exact lt_irrefl _)

end GlobalTheory.VanishAtSimpleZero

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem vanishAtS_holds : VanishAtSStatement (E := E) := by
  intro r X x1 hn _ _ u w0 s ρ hρ hdu hds hdw hw0 hs0 hdet hint
  have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero X x1
  have hb : Metric.ball (0 : V (nd X)) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have key := VanishAtSimpleZero.vanish_of_simple_zero hn (u := fun z => u (cpt X x1 z))
    (w := fun z => w0 (cpt X x1 z)) (s := fun k z => s k (cpt X x1 z)) hρ
    ((hdu.differentiableAt hb).continuousAt) (fun k => (hds k).differentiableAt hb)
    (hdw.differentiableAt hb) (by simpa [h0] using hw0) (fun k => by simpa [h0] using hs0 k) hdet hint
  simpa [h0] using key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.BorelDiagNeZero
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeviTransfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem borel_diag_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  have hdet := (hb τ).1
  have htri : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  rw [Matrix.det_of_upperTriangular htri] at hdet
  exact (Finset.prod_ne_zero_iff.1 hdet) i (Finset.mem_univ i)

omit [NumberField E] [IsCMField E] in
theorem borel_char_ne_zero {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (la : Wt Ψ r) : bchar la b ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun i _ =>
    zpow_ne_zero _ (borel_diag_ne_zero hb τ i)

omit [NumberField E] [IsCMField E] in
theorem left_act_one {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    lact (1 : GL (Fin r) E) x = x := by
  funext τ
  show ((((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1) * mat x τ :
    Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  rfl

theorem normFactor_pos {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    0 < X.nfac la x :=
  Finset.prod_pos fun τ _ => Finset.prod_pos fun _ _ => Real.rpow_pos_of_pos
    (norm_pos_iff.2 (div_ne_zero (IW.dmin_ne_zero X hx τ _) (IW.dmin_ne_zero X hx τ _))) _

theorem metric_rmul (h : NfacRmulStatement (E := E)) {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r) :
    phla X la (rmul x b) = phla X la x + Real.log (Complex.normSq (bchar la b)) := by
  have h1 := normFactor_pos X la hx
  have h2 : 0 < ‖bchar la b‖ := norm_pos_iff.2 (borel_char_ne_zero hb la)
  unfold phla
  rw [h r X la x hx b hb, Real.log_mul (inv_pos.2 h2).ne' h1.ne', Real.log_inv,
    Complex.normSq_eq_norm_sq, Real.log_pow]
  push_cast
  ring

theorem levi_transfer :
    (KapGGStatement (E := E)) → (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom → ∃ (x1 : Frame X.Ψ r) (D : (Fin (nd X) → ℂ) →ₗ[ℂ] (Fin (nd X) → ℂ)), IsOrth X x1 ∧ Function.Injective D ∧ ∀ (la : Wt X.Ψ r) (ξ : Fin (nd X) → ℂ), leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 (D ξ)) := by
  intro hK hN r X x0 z hz
  obtain ⟨x1, ho, b, hb, hxb⟩ := ortho_holds r X _ hz
  obtain ⟨Δ, zOf, bOf, hΔ, -, hzd, hbd, hsplit, hinv⟩ := lu_holds r X x1 ho
  have h0 := hinv 0 (IW.zero_mem_OmF X x1 ho) b hb
  rw [IW.cpt_zero, ← hxb] at h0
  have hcd : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c =>
      (IW.cpt_entry_cd X x0 τ a c).differentiable (by simp)
  set U : Set (V (nd X)) := {w | cpt X x0 w ∈ X.dom ∧ Δ (cpt X x0 w) ≠ 0} with hUdef
  have hU : IsOpen U :=
    (ExF.isOpen_OmF X x0).inter
      (isOpen_compl_singleton.preimage (hΔ.comp hcd).continuous)
  have hzU : z ∈ U := ⟨hz, h0.1⟩
  set Φ : V (nd X) → V (nd X) := fun w => zOf (cpt X x0 w) with hΦdef
  set bf : V (nd X) → Frame X.Ψ r := fun w => bOf (cpt X x0 w) with hbfdef
  have hΦ : DifferentiableOn ℂ Φ U := hzd.comp hcd.differentiableOn fun w hw => hw
  have hbf : DifferentiableOn ℂ bf U := hbd.comp hcd.differentiableOn fun w hw => hw
  have hΦz : Φ z = 0 := h0.2.1
  have hdet := hK r X x0 x1 1 U Φ bf hU hΦ (fun w hw =>
    ⟨hw.1, (hsplit _ hw.1 hw.2).2.1, by
      rw [left_act_one]; exact (hsplit _ hw.1 hw.2).2.2⟩) z hzU
  have hdet' : (fderiv ℂ Φ z).det ≠ 0 := by
    rw [hdet]; exact borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hinj : Function.Injective (fderiv ℂ Φ z) := by
    have hu : IsUnit ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet')
    exact LinearMap.ker_eq_bot.1 ((LinearMap.isUnit_iff_ker_eq_bot _).1 hu)
  have hΦ2 : ContDiffOn ℂ 2 Φ U := by
    rw [contDiffOn_piLp]
    intro i
    exact (contDiffOn_of_differentiableOn _ _ U hU
      ((differentiableOn_piLp 2).1 hΦ i)).of_le HE.two_le_inf
  refine ⟨x1, (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).toLinearMap ∘ₗ
    ((fderiv ℂ Φ z : V (nd X) →L[ℂ] V (nd X)) : V (nd X) →ₗ[ℂ] V (nd X)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.toLinearMap, ho, ?_, ?_⟩
  · exact (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).injective.comp
      (hinj.comp (WithLp.linearEquiv 2 ℂ (Fin (nd X) → ℂ)).symm.injective)
  intro la ξ
  have hch : DifferentiableOn ℂ (fun w => bchar la (bf w)) U := by
    classical
    intro w hw
    unfold bchar
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (HasFDerivAt.finsetProd (g' := fun τ => fderiv ℂ (fun w => ∏ i, bf w τ i i ^ la τ i) w)
      fun τ _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    refine (HasFDerivAt.finsetProd (g' := fun i => fderiv ℂ (fun w => bf w τ i i ^ la τ i) w)
      fun i _ => DifferentiableAt.hasFDerivAt ?_).differentiableAt
    have hw' : DifferentiableAt ℂ bf w := hbf.differentiableAt (hU.mem_nhds hw)
    have hi : DifferentiableAt ℂ (fun w => bf w τ i i) w :=
      differentiableAt_pi.1 (differentiableAt_pi.1 (differentiableAt_pi.1 hw' τ) i) i
    have hzp : DifferentiableAt ℂ (fun t : ℂ => t ^ la τ i) (bf w τ i i) :=
      differentiableAt_zpow.2 (Or.inl (borel_diag_ne_zero (hsplit _ hw.1 hw.2).2.1 τ i))
    exact DifferentiableAt.comp (g := fun t : ℂ => t ^ la τ i) w hzp hi
  have hchz : ContDiffAt ℂ 2 (fun w => bchar la (bf w)) z :=
    (HE.contDiffAt_of_punct hU hch hzU).of_le HE.two_le_inf
  have hne : bchar la (bf z) ≠ 0 := borel_char_ne_zero (hsplit _ hz h0.1).2.1 _
  have hev : (fun w => ((phla X la (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun w => ((phla X la (cpt X x1 (Φ w)) + Real.log (Complex.normSq (bchar la (bf w))) : ℝ) : ℂ) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    obtain ⟨h1, h2, h3⟩ := hsplit _ hw.1 hw.2
    rw [← metric_rmul hN.1 X la h1 h2, ← h3]
  have hg : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 w)) (Φ z) := by
    rw [hΦz]
    exact (IW.phla_cpt_cdAt X x1 (IW.zero_mem_OmF X x1 ho) la).of_le HE.two_le_inf
  have h1 : ContDiffAt ℝ 2 (fun w => phla X la (cpt X x1 (Φ w))) z :=
    hg.comp z ((hΦ2.contDiffAt (hU.mem_nhds hzU)).restrict_scalars ℝ)
  have h2 : ContDiffAt ℝ 2 (fun w => Real.log (Complex.normSq (bchar la (bf w)))) z :=
    (HE.normSq_contDiffAt hchz).log (Complex.normSq_pos.2 hne).ne'
  have hgC : ContDiffAt ℝ 2 (fun w => ((phla X la (cpt X x1 w) : ℝ) : ℂ)) (Φ z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ hg
  have hc := RGF.gc_leviV_comp _ _ _ Φ U hU z hzU hΦ2 hgC ξ
  rw [hΦz] at hc
  unfold leviM
  rw [leviV_congr hev, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 h2,
    HE.levi_logNormSq_zero_at _ z hchz hne ξ, add_zero]
  exact congrArg Complex.re hc

end GlobalTheory.LeviTransfer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIndepForms
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ManyForms

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_pow_mem_SSgt {r : ℕ} (X : Data E r) {G L : Wt X.Ψ r} {c : ℝ}
    {P Q : Frame X.Ψ r → ℂ} (hP : P ∈ X.SSgt G c) (hQ : X.IsBddSec L Q) (m : ℕ) :
    P * Q ^ m ∈ X.SSgt (G + m • L) c := by
  induction m with
  | zero => simpa using hP
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]
    exact (siegelSpaceAlgebra_holds r X _ L c).2.2.2 _ ih Q hQ

theorem mul_prod_mem_SSgt {r : ℕ} (X : Data E r) {G L : Wt X.Ψ r} {c : ℝ} {ι : Type}
    {P : Frame X.Ψ r → ℂ} {s : ι → Frame X.Ψ r → ℂ} (hP : P ∈ X.SSgt G c)
    (hs : ∀ k, X.IsBddSec L (s k)) (α : ι → ℕ) (S : Finset ι) :
    P * ∏ k ∈ S, s k ^ α k ∈ X.SSgt (G + (∑ k ∈ S, α k) • L) c := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hP
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_comm (s a ^ α a), ← mul_assoc,
      add_comm (α a), add_nsmul, ← add_assoc]
    exact mul_pow_mem_SSgt X ih (hs a) _

theorem card_multiLt_succ (n T : ℕ) : (multiLt n (T + 1)).card = (T + n).choose n := by
  have h : multiLt n (T + 1) = Y.multiLe n T := by
    ext α
    rw [GlobalTheory.LeadIndep.mem_multiLt, Y.mem_multiLe_iff, Nat.lt_succ_iff]
  rw [h, Y.ind_count]

theorem exists_indep_forms : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T : ℕ) (c : ℝ), 0 ≤ c →
    (∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt G c, ∀ j, F (Fl.xs j) = v j) →
    ∃ f : Fin (Fl.δ * (T + nd X).choose (nd X)) → Frame X.Ψ r → ℂ,
      (∀ q, f q ∈ X.SSgt (G + T • Xa.L) c) ∧
      ∀ u : Fin (Fl.δ * (T + nd X).choose (nd X)) → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0 := by
  classical
  intro r X Xa Fl G T c _ hint
  choose F hF hFv using fun j : Fin Fl.δ => hint (Pi.single j 1)
  set M := multiLt (nd X) (T + 1) with hM
  set S : Finset (Fin Fl.δ) := Finset.univ with hS
  have hcard : (S ×ˢ M).card = Fl.δ * (T + nd X).choose (nd X) := by
    rw [Finset.card_product, hM, card_multiLt_succ, hS, Finset.card_univ, Fintype.card_fin]
  let e := (Finset.equivFinOfCardEq hcard).symm
  let fP : Fin Fl.δ → (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ :=
    fun j α => F j * (∏ k, Fl.s k ^ α k) * Fl.w0 ^ (T - ∑ q, α q)
  refine ⟨fun q => fP (e q).1.1 (e q).1.2, fun q => ?_, fun a ha => ?_⟩
  · have hα : ∑ q', (e q).1.2 q' ≤ T :=
      Nat.lt_succ_iff.mp (GlobalTheory.LeadIndep.mem_multiLt.mp (Finset.mem_product.mp (e q).2).2)
    have h := mul_pow_mem_SSgt X
      (mul_prod_mem_SSgt X (hF (e q).1.1) (fun k => (Fl.s_van k).1.1) (e q).1.2 Finset.univ)
      Fl.weightForm_vanishes.1.1 (T - ∑ q', (e q).1.2 q')
    rwa [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hα] at h
  · let cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ := fun α j =>
      if h : (j, α) ∈ S ×ˢ M then a (e.symm ⟨(j, α), h⟩) else 0
    have hc : ∀ q, cc (e q).1.2 (e q).1.1 = a q := by
      intro q
      have h : ((e q).1.1, (e q).1.2) ∈ S ×ˢ M := (e q).2
      simp only [cc, dif_pos h]
      exact congrArg a (e.symm_apply_apply q)
    have hcomb : ∀ x, leadM X Fl.s Fl.w0 F T (T + 1) cc x =
        ∑ q, a q * fP (e q).1.1 (e q).1.2 x := by
      intro x
      have h1 : leadM X Fl.s Fl.w0 F T (T + 1) cc x =
          ∑ p ∈ S ×ˢ M, cc p.2 p.1 * fP p.1 p.2 x := by
        rw [Finset.sum_product_right]
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [fP, monoM, Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
        ring
      rw [h1, ← Finset.sum_coe_sort (S ×ˢ M), ← e.sum_comp]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hc q]
    have hind := GlobalTheory.LeadIndep.leadM_coeff_eq_zero r X Xa Fl G T (T + 1) Fl.δ F
      (fun k => (hF k).1.1.1)
      (fun u hu => by
        funext j
        have := hu j
        simpa [hFv, Pi.single_apply] using this) cc
      (fun j => by
        have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
          show cpt X (Fl.xs j) 0 ∈ X.dom
          rw [IW.cpt_zero]
          exact Fl.xs_mem j
        refine Asymptotics.IsBigO.of_bound 0 ?_
        filter_upwards [(OntoB.isOpen_OmF X (Fl.xs j)).mem_nhds h0] with z hz
        rw [zero_mul, norm_le_zero_iff, hcomb]
        exact ha _ hz)
    funext q
    rw [← hc q]
    exact hind _ (Finset.mem_product.mp (e q).2).2 _

end GlobalTheory.ManyForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLtMulOfLt
section -- merged from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsomOfGramEq
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate

namespace GlobalTheory.MajNear

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem hermC_mulVec {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (M : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (M *ᵥ a) (M *ᵥ b) = ∑ i, ∑ j, a i * gram τ G M i j * conj (b j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, gram, col, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  have h : ∀ (f : Fin r → Fin r → Fin r → Fin r → ℂ),
      ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := by
    intro f
    calc ∑ k, ∑ l, ∑ j, ∑ i, f k l i j = ∑ k, ∑ l, ∑ i, ∑ j, f k l i j :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f k l i j := Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ l, ∑ j, f k l i j := Finset.sum_comm
      _ = ∑ i, ∑ k, ∑ j, ∑ l, f k l i j :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ i, ∑ j, ∑ k, ∑ l, f k l i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h (fun k l i j => M k i * a i * τ (G k l) * (conj (M l j) * conj (b j)))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

omit [NumberField E] [IsCMField E] in
theorem isom_of_gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {M N : Matrix (Fin r) (Fin r) ℂ} (hN : N.det ≠ 0) (h : gram τ G M = gram τ G N)
    (u v : Fin r → ℂ) :
    hermC τ G ((M * N⁻¹) *ᵥ u) ((M * N⁻¹) *ᵥ v) = hermC τ G u v := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hermC_mulVec, h, ← hermC_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit hN),
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem col_mul {r : ℕ} (g M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    col (g * M) a = g *ᵥ col M a := by
  funext k
  simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]

omit [NumberField E] [IsCMField E] in
theorem gram_isom {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {g : Matrix (Fin r) (Fin r) ℂ} (hg : ∀ u v, hermC τ G (g *ᵥ u) (g *ᵥ v) = hermC τ G u v)
    (M : Matrix (Fin r) (Fin r) ℂ) : gram τ G (g * M) = gram τ G M := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

theorem maj_isom {r : ℕ} (X : Data E r) (τ : X.Ψ) {x y : Frame X.Ψ r}
    {g : Matrix (Fin r) (Fin r) ℂ}
    (hg : ∀ u v, hermC τ.1 X.Gm (g *ᵥ u) (g *ᵥ v) = hermC τ.1 X.Gm u v)
    (hxy : mat y τ = g * mat x τ) (v : Fin r → ℂ) :
    X.maj y τ (g *ᵥ v) = X.maj x τ v := by
  simp only [Data.maj, Data.posPart, Data.gramPos, hxy, gram_isom τ.1 X.Gm hg, col_mul, hg]

theorem mat_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (z : V (nd X)) (τ : X.Ψ) :
    mat (cpt X x z) τ = mat x τ * mat (nmat X z) τ := rfl

theorem continuous_cpt {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Continuous (cpt X x) :=
  continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b =>
    (IW.cpt_entry_cd X x τ a b).continuous

theorem maj_near_orth :
    (∀ (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, y ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj y τ v ∧ X.maj y τ v ≤ (1 + ε) * X.maj x τ v) → (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ x, IsOrth X x → ∀ z : V (nd X), ‖z‖ < ρ → cpt X x z ∈ X.dom ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v ≤ (1 + ε) * X.maj (cpt X x z) τ v ∧ X.maj (cpt X x z) τ v ≤ (1 + ε) * X.maj x τ v) := by
  intro H r X ε hε
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have hd : x0F X ∈ X.dom := IW.orth_mem_dom X _ ho
  have ht : Filter.Tendsto (cpt X (x0F X)) (𝓝 0) (𝓝 (x0F X)) := by
    have := (continuous_cpt X (x0F X)).tendsto 0
    rwa [IW.cpt_zero] at this
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 (ht.eventually (H r X _ hd ε hε))
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun x hx z hz => ?_⟩
  obtain ⟨hz0, hm⟩ := hb (y := z) (by rw [dist_zero_right]; exact hz.trans_le (min_le_left _ _))
  have hxd : x ∈ X.dom := IW.orth_mem_dom X _ hx
  have hiso : ∀ τ : X.Ψ, ∀ u v, hermC τ.1 X.Gm ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ u)
      ((mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ v) = hermC τ.1 X.Gm u v := fun τ =>
    isom_of_gram_eq τ.1 X.Gm (hd τ).1 ((hx τ).trans (ho τ).symm)
  have h1 : ∀ τ : X.Ψ, mat x τ = (mat x τ * (mat (x0F X) τ)⁻¹) * mat (x0F X) τ := fun τ => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit (hd τ).1), Matrix.mul_one]
  have h2 : ∀ τ : X.Ψ, mat (cpt X x z) τ =
      (mat x τ * (mat (x0F X) τ)⁻¹) * mat (cpt X (x0F X) z) τ := fun τ => by
    rw [mat_cpt, mat_cpt, ← Matrix.mul_assoc, ← h1]
  have hdet : ∀ τ : X.Ψ, (mat x τ * (mat (x0F X) τ)⁻¹).det ≠ 0 := fun τ h0 => by
    have := (hxd τ).1
    rw [h1, Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  refine ⟨fun τ => ⟨?_, fun i => ?_⟩, fun τ v => ?_⟩
  · rw [h2, Matrix.det_mul]
    exact mul_ne_zero (hdet τ) (hz0 τ).1
  · have := (hz0 τ).2 i
    simp only [dmin] at this ⊢
    rwa [h2, gram_isom τ.1 X.Gm (hiso τ)]
  · obtain ⟨w, rfl⟩ : ∃ w, v = (mat x τ * (mat (x0F X) τ)⁻¹) *ᵥ w :=
      ⟨(mat x τ * (mat (x0F X) τ)⁻¹)⁻¹ *ᵥ v, by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (Ne.isUnit (hdet τ)), Matrix.one_mulVec]⟩
    rw [maj_isom X τ (hiso τ) (h1 τ), maj_isom X τ (hiso τ) (h2 τ)]
    exact hm τ w

end GlobalTheory.MajNear
end

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ClosedModes

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_lt_mul_of_lt {s a : ℝ} (ha : 0 ≤ a) (hs : s < a) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ s < θ * a := by
  rcases ha.eq_or_lt with h | h
  · subst h
    exact ⟨1 / 2, by norm_num, by norm_num, by simpa using hs⟩
  · have hm : max s 0 < a := max_lt hs h
    have h0 : 0 ≤ max s 0 := le_max_right _ _
    have h1 : s ≤ max s 0 := le_max_left _ _
    refine ⟨(max s 0 + a) / (2 * a), by positivity, ?_, ?_⟩
    · rw [div_lt_one (by positivity)]
      linarith
    · have : (max s 0 + a) / (2 * a) * a = (max s 0 + a) / 2 := by field_simp
      rw [this]
      linarith

theorem modeHalf_closed : (∀ (r : ℕ) (X : Data E r), ModeHalfStatement X) := by
  intro r X la F ps a hF hps ha hmean ξ hξ ν hν x hx
  obtain ⟨θ, hθ0, hθ1, hνθ⟩ := exists_lt_mul_of_lt ha hν
  exact ModeDecay.fj_eq_zero_of_decay fj_norm_mul_exp_le_sup_flow
    ClosedDiscontinuity.propDisc_and_la1GG.2 r X la F (θ * a) hF
    (pnorm_le_exp_neg_tt_near_cusp
      (MajNear.maj_near_orth MajorantContinuity.majorant_continuity.1) maj_lact_rmul
      NormFactor.nfac_transform r X la F ps a hF hps ha hmean θ (θ * a) hθ0 hθ1 rfl)
    ξ hξ ν hνθ x hx

end GlobalTheory.ClosedModes
end
