module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensChartSum

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.A
open scoped ENNReal ContDiff ComplexConjugate Matrix

noncomputable section

namespace BergmanDensIntegrable

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

theorem weight_contDiffOn {L : HolLineBundle A} (W : Weight L) (j : Fin A.n) :
    ContDiffOn ℝ ∞ (W.φ j ∘ (A.chart j).symm) (A.chart j).target :=
  (W.smooth j j).mono fun _ hy => ⟨hy, (A.chart j).map_target hy⟩

theorem trans_source_eq (j k : Fin A.n) :
    ((A.chart j).symm.trans (A.chart k)).source =
      (A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart k).source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]

theorem trans_target_eq (j k : Fin A.n) :
    ((A.chart j).symm.trans (A.chart k)).target =
      (A.chart k).target ∩ (A.chart k).symm ⁻¹' (A.chart j).source := by
  rw [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target]

theorem trans_analytic (j k : Fin A.n) :
    AnalyticOnNhd ℂ ((A.chart j).symm.trans (A.chart k))
      ((A.chart j).symm.trans (A.chart k)).source := by
  rw [trans_source_eq, OpenPartialHomeomorph.coe_trans]
  exact A.holo j k

theorem hessC_weight_trans {L : HolLineBundle A} (W : Weight L) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    hessC (W.φ j ∘ (A.chart j).symm) y =
      (jacC ((A.chart j).symm.trans (A.chart k)) y)ᵀ *
        hessC (W.φ k ∘ (A.chart k).symm) (((A.chart j).symm.trans (A.chart k)) y) *
        (jacC ((A.chart j).symm.trans (A.chart k)) y).map (starRingEnd ℂ) := _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.hessC_weight_trans (L := L) (y := y) W j k hy

theorem chernTopDens_trans {L : HolLineBundle A} (W : Weight L) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    chernTopDens W j y = Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det *
      chernTopDens W k (((A.chart j).symm.trans (A.chart k)) y) := _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.chernTopDens_trans (L := L) (y := y) W j k hy

variable [MeasurableSpace X] [BorelSpace X]

theorem lintegral_dens_trans (dV : SmoothVolume A) (j k : Fin A.n)
    (f : (Fin D → ℂ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y in ((A.chart j).symm.trans (A.chart k)).source, f y * ENNReal.ofReal (dV.dens j y) =
      ∫⁻ y in ((A.chart j).symm.trans (A.chart k)).source,
        ENNReal.ofReal (Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det) *
          (f y * ENNReal.ofReal (dV.dens k (((A.chart j).symm.trans (A.chart k)) y))) := by
  classical
  set T := (A.chart j).symm.trans (A.chart k) with hT
  set S := (A.chart j).source ∩ (A.chart k).source with hS
  have hSo : IsOpen S := (A.chart j).open_source.inter (A.chart k).open_source
  have hSm : MeasurableSet S := hSo.measurableSet
  set p : X → Fin D → ℂ := S.piecewise (A.chart j) (fun _ => 0) with hp
  have hpm : Measurable p :=
    ContinuousOn.measurable_piecewise ((A.chart j).continuousOn.mono inter_subset_left)
      continuousOn_const hSm
  set g : X → ℝ≥0∞ := S.indicator (fun x => f (p x)) with hg
  have hgm : Measurable g := (hf.comp hpm).indicator hSm
  have hsame : ∀ i, (A.chart i).source ∩ S = S → ∫⁻ x in (A.chart i).source, g x ∂dV.μ =
      ∫⁻ x in S, f (p x) ∂dV.μ := by
    intro i hi
    rw [hg, lintegral_indicator hSm, Measure.restrict_restrict hSm, inter_comm, hi]
  have hL := dV.chart_lintegral j g hgm
  have hR := dV.chart_lintegral k g hgm
  rw [hsame j (inter_eq_right.2 inter_subset_left)] at hL
  rw [hsame k (inter_eq_right.2 inter_subset_right)] at hR
  have hTsrc := trans_source_eq (A := A) j k
  have hTtgt := trans_target_eq (A := A) j k
  have hLe : ∫⁻ y in (A.chart j).target, g ((A.chart j).symm y) * ENNReal.ofReal (dV.dens j y) =
      ∫⁻ y in T.source, f y * ENNReal.ofReal (dV.dens j y) := by
    have hsub : T.source ⊆ (A.chart j).target := hTsrc ▸ inter_subset_left
    conv_rhs => rw [← inter_eq_left.2 hsub, ← Measure.restrict_restrict T.open_source.measurableSet,
      ← lintegral_indicator T.open_source.measurableSet]
    refine setLIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    have hyj : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hy
    by_cases hk : (A.chart j).symm y ∈ (A.chart k).source
    · have hyT : y ∈ T.source := by rw [hTsrc]; exact ⟨hy, hk⟩
      simp [hg, hp, Set.indicator_of_mem hyT, Set.indicator_of_mem (show (A.chart j).symm y ∈ S
        from ⟨hyj, hk⟩), Set.piecewise_eq_of_mem _ _ _ (show (A.chart j).symm y ∈ S from ⟨hyj, hk⟩),
        (A.chart j).right_inv hy]
    · have hyT : y ∉ T.source := by rw [hTsrc]; exact fun h => hk h.2
      simp [hg, Set.indicator_of_notMem hyT, Set.indicator_of_notMem
        (show (A.chart j).symm y ∉ S from fun h => hk h.2)]
  have hRe : ∫⁻ z in (A.chart k).target, g ((A.chart k).symm z) * ENNReal.ofReal (dV.dens k z) =
      ∫⁻ z in T.target, f (T.symm z) * ENNReal.ofReal (dV.dens k z) := by
    have hsub : T.target ⊆ (A.chart k).target := hTtgt ▸ inter_subset_left
    conv_rhs => rw [← inter_eq_left.2 hsub, ← Measure.restrict_restrict T.open_target.measurableSet,
      ← lintegral_indicator T.open_target.measurableSet]
    refine setLIntegral_congr_fun (A.chart k).open_target.measurableSet fun z hz => ?_
    have hzk : (A.chart k).symm z ∈ (A.chart k).source := (A.chart k).map_target hz
    by_cases hj : (A.chart k).symm z ∈ (A.chart j).source
    · have hzT : z ∈ T.target := by rw [hTtgt]; exact ⟨hz, hj⟩
      rw [Set.indicator_of_mem hzT]
      simp [hg, hp, hT, Set.indicator_of_mem (show (A.chart k).symm z ∈ S
        from ⟨hj, hzk⟩), Set.piecewise_eq_of_mem _ _ _ (show (A.chart k).symm z ∈ S from ⟨hj, hzk⟩),
        OpenPartialHomeomorph.coe_trans_symm]
    · have hzT : z ∉ T.target := by rw [hTtgt]; exact fun h => hj h.2
      simp [hg, Set.indicator_of_notMem hzT, Set.indicator_of_notMem
        (show (A.chart k).symm z ∉ S from fun h => hj h.1)]
  rw [← hLe, ← hL, hR, hRe, ← T.image_source_eq_target,
    lintegral_image_eq_lintegral_normSq_det_mul T T.source T.open_source (trans_analytic j k)
      T.injOn]
  refine setLIntegral_congr_fun T.open_source.measurableSet fun y hy => ?_
  simp only [T.left_inv hy]


omit [MeasurableSpace X] [BorelSpace X] in
theorem jacC_trans_continuousOn (j k : Fin A.n) :
    ContinuousOn (jacC ((A.chart j).symm.trans (A.chart k)))
      ((A.chart j).symm.trans (A.chart k)).source := by
  have h := (trans_analytic (A := A) j k).fderiv.continuousOn
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  exact (continuous_apply a).comp_continuousOn
    ((ContinuousLinearMap.apply ℂ _ (Pi.single b 1)).continuous.comp_continuousOn h)

theorem dens_trans (dV : SmoothVolume A) (j k : Fin A.n) {y : Fin D → ℂ}
    (hy : y ∈ ((A.chart j).symm.trans (A.chart k)).source) :
    dV.dens j y = Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) y).det *
      dV.dens k (((A.chart j).symm.trans (A.chart k)) y) := _root_.GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.dens_trans (y := y) dV j k hy

variable {L : HolLineBundle A}

def densIn (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) (x : X) : ℝ :=
  chernTopDens W j (A.chart j x) / ((D.factorial : ℝ) * dV.dens j (A.chart j x))

theorem densIn_eq (W : Weight L) (dV : SmoothVolume A) (j k : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source ∩ (A.chart k).source) :
    densIn W dV j x = densIn W dV k x := by
  have hy : A.chart j x ∈ ((A.chart j).symm.trans (A.chart k)).source := by
    rw [trans_source_eq]
    exact ⟨(A.chart j).map_source hx.1,
      Set.mem_preimage.2 (by rw [(A.chart j).left_inv hx.1]; exact hx.2)⟩
  have hT : ((A.chart j).symm.trans (A.chart k)) (A.chart j x) = A.chart k x := by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, (A.chart j).left_inv hx.1]
  have hc := chernTopDens_trans W j k hy
  have hd := dens_trans dV j k hy
  rw [hT] at hc hd
  set n := Complex.normSq (jacC ((A.chart j).symm.trans (A.chart k)) (A.chart j x)).det
  have hpos : 0 < dV.dens j (A.chart j x) := dV.pos j _ ((A.chart j).map_source hx.1)
  have hn : n ≠ 0 := by
    intro h0; rw [hd, h0, zero_mul] at hpos; exact lt_irrefl 0 hpos
  unfold densIn
  rw [hc, hd, show (D.factorial : ℝ) * (n * dV.dens k (A.chart k x)) =
    n * ((D.factorial : ℝ) * dV.dens k (A.chart k x)) by ring, mul_div_mul_left _ _ hn]


omit [BorelSpace X] in
theorem densIn_continuousAt (W : Weight L) (dV : SmoothVolume A) (j : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source) : ContinuousAt (densIn W dV j) x := by
  have hy : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hx
  have hnhds : (A.chart j).target ∈ 𝓝 (A.chart j x) := (A.chart j).open_target.mem_nhds hy
  have hH : ContinuousAt (hessC (W.φ j ∘ (A.chart j).symm)) (A.chart j x) :=
    (hessC_continuousOn _ _ (A.chart j).open_target
      ((weight_contDiffOn W j).of_le (by first | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp |
        exact WithTop.coe_le_coe.2 le_top))).continuousAt hnhds
  have hdet : Continuous fun M : Matrix (Fin D) (Fin D) ℂ =>
      (D.factorial : ℝ) * ((((1 / Real.pi : ℝ) : ℂ) • M).det).re := by fun_prop
  have hC : ContinuousAt (chernTopDens W j) (A.chart j x) := hdet.continuousAt.comp hH
  have hdens : ContinuousAt (dV.dens j) (A.chart j x) :=
    (dV.smooth j).continuousOn.continuousAt hnhds
  have hc := (A.chart j).continuousAt hx
  refine (hC.comp hc).div (continuousAt_const.mul (hdens.comp hc)) ?_
  exact mul_ne_zero (by exact_mod_cast (Nat.factorial_pos D).ne') (dV.pos j _ hy).ne'

theorem bergmanDens_continuous (W : Weight L) (dV : SmoothVolume A) :
    Continuous (bergmanDens W dV) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hx : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hev : densIn W dV (chartIdx A x) =ᶠ[𝓝 x] bergmanDens W dV := by
    filter_upwards [(A.chart (chartIdx A x)).open_source.mem_nhds hx] with x' hx'
    exact densIn_eq W dV _ _ ⟨hx', Classical.choose_spec (A.cover x')⟩
  exact (densIn_continuousAt W dV _ hx).congr hev

end BergmanDensIntegrable

theorem BergmanDensIntegrable.proof : BergmanDensIntegrable.Statement := by
  intro D X _ _ _ _ _ A L W dV
  have := dV.isProb
  exact integrableOn_univ.1
    ((BergmanDensIntegrable.bergmanDens_continuous W dV).continuousOn.integrableOn_compact
      isCompact_univ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
