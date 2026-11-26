module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloSectionAeEqOfBallCover
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.AeHoloGlue

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem mu_ne_zero_of_open (A : WeightedAtlas n Y ι La) {O : Set Y} (hO : IsOpen O)
    (hne : O.Nonempty) : A.mu O ≠ 0 := by
  obtain ⟨y, hy⟩ := hne
  have hW : IsOpen (O ∩ (A.chart (A.pick y)).source) := hO.inter (A.chart (A.pick y)).open_source
  have hWs : O ∩ (A.chart (A.pick y)).source ⊆ (A.chart (A.pick y)).source := Set.inter_subset_right
  have hS : IsOpen (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) :=
    (A.chart (A.pick y)).isOpen_image_of_subset_source hW hWs
  have hSne : (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ ⟨hy, A.mem_pick y⟩⟩
  have hSt : A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source) ⊆ (A.chart (A.pick y)).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart (A.pick y)).map_source hx.2
  intro h0
  have h1 : A.mu (O ∩ (A.chart (A.pick y)).source) = 0 := measure_mono_null Set.inter_subset_left h0
  rw [A.mu_chart _ _ hW.measurableSet hWs] at h1
  have hc : ContinuousOn (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v))))
      (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) := by
    have := (A.smooth_ph A.kap (A.pick y)).continuousOn.mono hSt
    exact ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn this)
  rw [lintegral_eq_zero_iff' (hc.aemeasurable hS.measurableSet)] at h1
  have h3 := ae_iff.mp h1
  have hu : {v | ¬ (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v)))) v
      = (0 : V n → ℝ≥0∞) v} = Set.univ := by
    ext v; simp [ENNReal.ofReal_eq_zero, Real.exp_pos]
  rw [hu, Measure.restrict_apply_univ] at h3
  exact hS.measure_ne_zero volume hSne h3

theorem exists_null (A : WeightedAtlas n Y ι La) (i : ι) (c : V n) (r : ℝ) (u : V n → ℂ)
    (f : Y → ℂ) (h : u =ᵐ[volume.restrict (ball c r)] f ∘ (A.chart i).symm) :
    ∃ M : Set Y, A.mu M = 0 ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball c r → y ∉ M →
      u (A.chart i y) = f y := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at h
  obtain ⟨T, hET, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  classical
  have hφ : Measurable ((A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n))) :=
    ContinuousOn.measurable_piecewise (A.chart i).continuousOn continuousOn_const
      (A.chart i).open_source.measurableSet
  refine ⟨(A.chart i).source ∩ (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T,
    ?_, ?_⟩
  · have hm : MeasurableSet ((A.chart i).source ∩
        (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T) :=
      (A.chart i).open_source.measurableSet.inter (hφ hTm)
    rw [A.mu_chart i _ hm Set.inter_subset_left]
    refine le_antisymm ?_ (by simp)
    calc _ ≤ ∫⁻ v in T, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
          apply lintegral_mono_set
          rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
          have : (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) x = A.chart i x :=
            Set.piecewise_eq_of_mem _ _ _ hx1
          simpa [this] using hx2
      _ = 0 := setLIntegral_measure_zero _ _ hT0
  · intro y hy hb hM
    by_contra hne
    apply hM
    refine ⟨hy, ?_⟩
    show (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) y ∈ T
    rw [Set.piecewise_eq_of_mem _ _ _ hy]
    apply hET
    simp only [Set.mem_setOf_eq]
    intro heq
    apply hne
    simpa [Function.comp, (A.chart i).left_inv hy] using heq hb

theorem continuousOn_g (A : WeightedAtlas n Y ι La) (la : La) (i j : ι) :
    ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
  have h1 : ContinuousOn (A.g la i j ∘ (A.chart i).symm ∘ A.chart i)
      ((A.chart i).source ∩ (A.chart j).source) := by
    refine (A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left) ?_
    intro y hy
    exact ⟨(A.chart i).map_source hy.1, by simpa [(A.chart i).left_inv hy.1] using hy.2⟩
  refine h1.congr ?_
  intro y hy
  simp [(A.chart i).left_inv hy.1]

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La),
    ∀ (C : Cover A) (la : La) (f : ι → Y → ℂ) (u : Fin C.m → V n → ℂ),
    (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g la i j y * f j y) →
    (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    (∀ a, u a =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm) →
    ∃ F : ι → Y → ℂ, A.IsSec la F ∧ ∀ᵐ y ∂A.mu, F (A.pick y) y = f (A.pick y) y := by
  intro n Y _ _ _ _ _ ι La _ A C la f u hf hu hae
  classical

  have hBo : ∀ a, IsOpen ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :=
    fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hcov : ∀ y, ∃ a, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) := by
    intro y
    by_contra hno
    push_neg at hno
    have h0 : ∀ a, C.chi a y = 0 := fun a => by
      by_contra hne
      exact hno a (C.supp a (subset_tsupport _ hne))
    have := C.sum_one y
    simp [h0] at this
  choose M hM0 hM using fun a => exists_null A (C.idx a) (C.c a) (C.r a) (u a) (f (C.idx a)) (hae a)
  have hM0' : A.mu (⋃ a, M a) = 0 := measure_iUnion_null hM0

  have hoff : ∀ a y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∉ ⋃ a, M a → u a (A.chart (C.idx a) y) = f (C.idx a) y := fun a y hy hn =>
    hM a y hy.1 hy.2 (fun h => hn (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hcu : ∀ a, ContinuousOn (fun y => u a (A.chart (C.idx a) y))
      ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) := fun a =>
    (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
      (fun y hy => hy.2)

  have hagree : ∀ a b y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∈ (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b) →
      u a (A.chart (C.idx a) y) = A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y) := by
    intro a b y hya hyb
    set D := ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) ∩
      ((A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b)) with hD
    have hcont : ContinuousOn (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) D :=
      ((hcu a).mono Set.inter_subset_left).sub
        (((continuousOn_g A la (C.idx a) (C.idx b)).mono
          (show D ⊆ (A.chart (C.idx a)).source ∩ (A.chart (C.idx b)).source from
            fun z hz => ⟨hz.1.1, hz.2.1⟩)).mul ((hcu b).mono Set.inter_subset_right))
    have hop := hcont.isOpen_inter_preimage ((hBo a).inter (hBo b)) (isOpen_compl_singleton (x := (0 : ℂ)))
    have hsub : D ∩ (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) ⁻¹' {0}ᶜ ⊆ ⋃ a, M a := by
      intro z ⟨hz, hz0⟩
      by_contra hn
      apply hz0
      simp only [Set.mem_singleton_iff]
      rw [hoff a z hz.1 hn, hoff b z hz.2 hn, hf _ _ z hz.1.1 hz.2.1]
      ring
    by_contra hne
    exact mu_ne_zero_of_open A hop ⟨y, ⟨hya, hyb⟩, by simpa [sub_eq_zero] using hne⟩
      (measure_mono_null hsub hM0')
  choose α hα using hcov
  refine ⟨fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y), ⟨?_, ?_⟩, ?_⟩
  ·
    intro i v hv
    have hvs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv.1
    set a0 := α ((A.chart i).symm v)
    have hO : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      (A.chart i).isOpen_inter_preimage_symm (hBo a0)
    have hvO : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) :=
      ⟨hv.1, hα _⟩
    have hOovl : (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) ⊆
        ovl A.chart i (C.idx a0) := fun w hw => ⟨hw.1, hw.2.1⟩
    have hG : DifferentiableOn ℂ (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
          ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      ((A.holo_g la i (C.idx a0)).mono hOovl).mul
        ((hu a0).comp ((A.holo_trans i (C.idx a0)).mono hOovl) (fun w hw => hw.2.2))
    have hloc : (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w)) =ᶠ[𝓝 v]
        ((fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y)) i ∘
          (A.chart i).symm) := by
      filter_upwards [hO.mem_nhds hvO] with w hw
      have hws : (A.chart i).symm w ∈ (A.chart i).source := (A.chart i).map_target hw.1
      simp only [Function.comp]
      rw [hagree (α ((A.chart i).symm w)) a0 _ (hα _) hw.2, ← mul_assoc,
        ← A.g_cocycle la i _ _ _ hws (hα _).1 hw.2.1]
    exact ((hG.differentiableAt (hO.mem_nhds hvO)).congr_of_eventuallyEq hloc.symm).differentiableWithinAt
  ·
    intro i j y _ hi hj
    simp only
    rw [A.g_cocycle la i j (C.idx (α y)) y hi hj (hα y).1]
    ring
  ·
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hM0'] with y hy
    rw [hoff _ y (hα y) hy, ← hf _ _ y (A.mem_pick y) (hα y).1]

end GlobalTheory.AeHoloGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloAeEq
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2LimitHolomorphic

open Set

variable {n : ℕ}

theorem exists_pos_le_on_compact {W K : Set (V n)} {ρ : V n → ℝ} (hρ : ContinuousOn ρ W)
    (hpos : ∀ v ∈ W, 0 < ρ v) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ c : ℝ, 0 < c ∧ ∀ v ∈ K, c ≤ ρ v := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne (hρ.mono hKW)
  exact ⟨ρ x, hpos x (hKW hx), fun v hv => hmin hv⟩

theorem lintegral_sq_le {W K : Set (V n)} {ρ : V n → ℝ} {c : ℝ} (hc : 0 < c)
    (hK : MeasurableSet K) (hKW : K ⊆ W) (hcK : ∀ v ∈ K, c ≤ ρ v) (g : V n → ℂ) :
    ∫⁻ v in K, ‖g v‖ₑ ^ 2 ≤
      ENNReal.ofReal c⁻¹ * ∫⁻ v in W, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
  calc ∫⁻ v in K, ‖g v‖ₑ ^ 2
      ≤ ∫⁻ v in K, ENNReal.ofReal c⁻¹ * ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) := by
        apply setLIntegral_mono' hK
        intro v hv
        rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
          ← ENNReal.ofReal_pow (norm_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        have h1 : 1 ≤ c⁻¹ * ρ v := by
          rw [le_inv_mul_iff₀ hc]; simpa using hcK v hv
        have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖g v‖)
        nlinarith
    _ = ENNReal.ofReal c⁻¹ * ∫⁻ v in K, ENNReal.ofReal (‖g v‖ ^ 2 * ρ v) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr

theorem integrableOn_of_limit {W K : Set (V n)} {ρ : V n → ℝ} {u : ℕ → V n → ℂ}
    {f : V n → ℂ} (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v)
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    (hK : IsCompact K) (hKW : K ⊆ W) : IntegrableOn f K := by
  obtain ⟨c, hc, hcK⟩ := exists_pos_le_on_compact hρ hpos hK hKW
  obtain ⟨m, hm⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  have hum : IntegrableOn (u m) K := ((hu m).continuousOn.mono hKW).integrableOn_compact hK
  have hfK : AEStronglyMeasurable f (volume.restrict K) :=
    (hf.mono_measure (Measure.restrict_mono hKW le_rfl)).aestronglyMeasurable
  have hfin : ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 < ⊤ :=
    lt_of_le_of_lt (lintegral_sq_le hc hK.measurableSet hKW hcK (fun v => f v - u m v))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hm.trans ENNReal.one_lt_top))
  have hd : IntegrableOn (fun v => f v - u m v) K := by
    refine ⟨hfK.sub hum.aestronglyMeasurable, ?_⟩
    show ∫⁻ v in K, ‖f v - u m v‖ₑ < ⊤
    have hpt : ∀ x : ℝ≥0∞, x ≤ 1 + x ^ 2 := by
      intro x
      rcases le_total x 1 with h | h
      · exact h.trans le_self_add
      · calc x = x * 1 := (mul_one x).symm
          _ ≤ x * x := by gcongr
          _ = x ^ 2 := (sq x).symm
          _ ≤ 1 + x ^ 2 := le_add_self
    calc ∫⁻ v in K, ‖f v - u m v‖ₑ ≤ ∫⁻ v in K, (1 + ‖f v - u m v‖ₑ ^ 2) :=
          lintegral_mono fun v => hpt _
      _ = volume K + ∫⁻ v in K, ‖f v - u m v‖ₑ ^ 2 := by
          rw [lintegral_add_left measurable_const]; simp
      _ < ⊤ := ENNReal.add_lt_top.2 ⟨hK.measure_lt_top, hfin⟩
  exact (hd.add hum).congr_fun (fun v _ => by simp) hK.measurableSet

theorem enorm_integral_mul_le {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {d h : V n → ℂ}
    (hd : AEMeasurable d (volume.restrict W)) (hh : Continuous h) :
    ‖∫ v in W, d v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
  have hρm : AEMeasurable ρ (volume.restrict W) := hρ.aemeasurable hW.measurableSet
  have hsq : AEMeasurable (fun v => Real.sqrt (ρ v)) (volume.restrict W) :=
    Real.continuous_sqrt.measurable.comp_aemeasurable hρm
  have ham : AEMeasurable (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)))
      (volume.restrict W) := (hd.norm.mul hsq).ennreal_ofReal
  have hbm : AEMeasurable (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)))
      (volume.restrict W) := (hh.measurable.norm.aemeasurable.div hsq).ennreal_ofReal
  have hab : EqOn (fun v => ‖d v * h v‖ₑ)
      ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
        fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) W := by
    intro v hv
    have hs : 0 < Real.sqrt (ρ v) := Real.sqrt_pos.2 (hpos v hv)
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, norm_mul]
    congr 1
    field_simp
  have ha2 : EqOn (fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖d v‖ ^ 2 * ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, mul_pow,
      Real.sq_sqrt (hpos v hv).le]
  have hb2 : EqOn (fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ))
      (fun v => ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) W := by
    intro v hv
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.rpow_two, div_pow,
      Real.sq_sqrt (hpos v hv).le]
  calc ‖∫ v in W, d v * h v‖ₑ ≤ ∫⁻ v in W, ‖d v * h v‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ v in W, ((fun v => ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v))) *
          fun v => ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v))) v :=
        setLIntegral_congr_fun hW.measurableSet hab
    _ ≤ (∫⁻ v in W, ENNReal.ofReal (‖d v‖ * Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫⁻ v in W, ENNReal.ofReal (‖h v‖ / Real.sqrt (ρ v)) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two ham hbm
    _ = _ := by
        rw [setLIntegral_congr_fun hW.measurableSet ha2,
          setLIntegral_congr_fun hW.measurableSet hb2]

theorem integral_mul_eq_zero {W : Set (V n)} (hW : IsOpen W) {ρ : V n → ℝ}
    (hρ : ContinuousOn ρ W) (hpos : ∀ v ∈ W, 0 < ρ v) {u : ℕ → V n → ℂ} {f : V n → ℂ}
    (hu : ∀ m, DifferentiableOn ℂ (u m) W) (hf : AEMeasurable f (volume.restrict W))
    (hlim : Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0))
    {h : V n → ℂ} (hhc : Continuous h) (hhs : HasCompactSupport h) (hsupp : tsupport h ⊆ W)
    (h0 : ∀ m, ∫ v in W, u m v * h v = 0) : ∫ v in W, f v * h v = 0 := by
  have hkc : Continuous fun v => ‖h v‖ ^ 2 / ρ v := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ W
    · exact (hhc.norm.pow 2).continuousAt.div (hρ.continuousAt (hW.mem_nhds hx))
        (hpos x hx).ne'
    · have hx' : x ∉ tsupport h := fun h' => hx (hsupp h')
      have hev : (fun v => ‖h v‖ ^ 2 / ρ v) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hx')] with v hv
        simp [hv]
      exact continuousAt_const.congr hev.symm
  have hks : HasCompactSupport fun v => ‖h v‖ ^ 2 / ρ v := by
    refine hhs.mono fun x hx => ?_
    intro h1
    apply hx
    simp [h1]
  have hH : ∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v) < ⊤ :=
    lt_of_le_of_lt (setLIntegral_le_lintegral _ _)
      (hkc.integrable_of_hasCompactSupport hks).lintegral_lt_top
  by_cases hfi : Integrable (fun v => f v * h v) (volume.restrict W)
  swap
  · exact integral_undef hfi
  have key : ∀ m, ‖∫ v in W, f v * h v‖ₑ ≤
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ) := by
    intro m
    have hUi : Integrable (fun v => u m v * h v) (volume.restrict W) := by
      have h1 : IntegrableOn (fun v => u m v * h v) (tsupport h) :=
        (((hu m).continuousOn.mono hsupp).mul hhc.continuousOn).integrableOn_compact hhs
      exact h1.of_forall_sdiff_eq_zero hW.measurableSet fun x hx => by
        simp [image_eq_zero_of_notMem_tsupport hx.2]
    have heq : ∫ v in W, f v * h v = ∫ v in W, (f v - u m v) * h v := by
      simp_rw [sub_mul]
      rw [integral_sub hfi hUi, h0 m, sub_zero]
    rw [heq]
    exact enorm_integral_mul_le hW hρ hpos
      (hf.sub ((hu m).continuousOn.aemeasurable hW.measurableSet)) hhc
  have hT : Tendsto (fun m =>
      (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ) *
        (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m =>
        (∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
      simpa [Function.comp_def] using this
    have := ENNReal.Tendsto.mul_const h1
      (b := (∫⁻ v in W, ENNReal.ofReal (‖h v‖ ^ 2 / ρ v)) ^ (1 / 2 : ℝ))
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hH.ne))
    simpa using this
  have hle := ge_of_tendsto' hT key
  exact enorm_eq_zero.mp (le_antisymm hle bot_le)

theorem tsupport_dbarDir_subset (g : V n → ℂ) (w : V n) :
    tsupport (fun z => C.dbarDir g z w) ⊆ tsupport g := by
  refine (closure_mono ?_).trans (tsupport_fderiv_subset ℝ)
  intro z hz
  refine Function.mem_support.2 fun h0 => Function.mem_support.1 hz ?_
  simp [C.dbarDir, h0]

theorem exists_holo_ae_eq : ∀ (n : ℕ) (W : Set (V n)) (ρ : V n → ℝ) (u : ℕ → V n → ℂ) (f : V n → ℂ), IsOpen W → ContinuousOn ρ W → (∀ v ∈ W, 0 < ρ v) → (∀ m, DifferentiableOn ℂ (u m) W) → AEMeasurable f (volume.restrict W) → Tendsto (fun m => ∫⁻ v in W, ENNReal.ofReal (‖f v - u m v‖ ^ 2 * ρ v)) atTop (𝓝 0) → ∃ g : V n → ℂ, DifferentiableOn ℂ g W ∧ g =ᵐ[volume.restrict W] f := by
  intro n W ρ u f hW hρ hpos hu hf hlim
  have hwh : C.WeakHolo W f := by
    refine ⟨(locallyIntegrableOn_iff hW.isLocallyClosed).2 fun K hKW hK =>
      integrableOn_of_limit hρ hpos hu hf hlim hK hKW, ?_⟩
    intro g hg w
    obtain ⟨hhc, hhs⟩ := C.dbarDir_continuous_hasCompactSupport hg.1 hg.2.1 w
    exact integral_mul_eq_zero hW hρ hpos hu hf hlim hhc hhs
      ((tsupport_dbarDir_subset g w).trans hg.2.2)
      (fun m => (C.holoWeak n W (u m) hW (hu m)).2 g hg w)
  obtain ⟨U, hU, hfU⟩ := C.reg n W f hW hwh
  exact ⟨U, hU, hfU.symm⟩

end GlobalTheory.L2LimitHolomorphic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricSeriesSectionsL2Limit
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.L2Limit

theorem norm_sub_sq_le (a : ℕ → ℂ) (m k : ℕ) :
    ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m *
      ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
  have htel : a m - a (k + m) = ∑ i ∈ Finset.range k, (a (i + m) - a (i + m + 1)) := by
    have := Finset.sum_range_sub' (fun i => a (i + m)) k
    simp only [zero_add] at this
    rw [← this]; exact Finset.sum_congr rfl fun i _ => by rw [add_right_comm]
  have h1 : ‖a m - a (k + m)‖ ≤ ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ := by
    rw [htel]; exact norm_sum_le _ _
  have hg : ∀ i ∈ Finset.range k, (0:ℝ) < (1/2) ^ (i + m) := fun i _ => by positivity
  have h2 := Finset.sq_sum_div_le_sum_sq_div (Finset.range k)
    (fun i => ‖a (i + m) - a (i + m + 1)‖) hg
  have hsg : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ≤ 2 / 2 ^ m := by
    have : ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) =
        (1/2) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by rw [pow_add]; ring
    rw [this]
    have := sum_geometric_two_le k
    have h2m : (0:ℝ) < (1/2) ^ m := by positivity
    calc (1/2:ℝ) ^ m * ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ i ≤ (1/2) ^ m * 2 :=
          mul_le_mul_of_nonneg_left this h2m.le
      _ = 2 / 2 ^ m := by rw [one_div_pow]; ring
  have hsum_pos : 0 < ∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m) ∨ k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact Or.inr h
    · exact Or.inl (Finset.sum_pos (fun i hi => hg i hi) ⟨0, by simp [h]⟩)
  rcases hsum_pos with hpos | hk
  · have h3 : (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 ≤
        (∑ i ∈ Finset.range k, ((1:ℝ)/2) ^ (i + m)) *
          ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) := by
      rwa [div_le_iff₀ hpos, mul_comm] at h2
    have h4 : ∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖ ^ 2 / (1/2) ^ (i + m) =
        ∑ i ∈ Finset.range k, 2 ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_div_pow, div_div_eq_mul_div, div_one, mul_comm]
    rw [h4] at h3
    have hn : 0 ≤ ∑ i ∈ Finset.range k, (2:ℝ) ^ (i + m) * ‖a (i + m) - a (i + m + 1)‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    calc ‖a m - a (k + m)‖ ^ 2 ≤ (∑ i ∈ Finset.range k, ‖a (i + m) - a (i + m + 1)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_right hsg hn
  · subst hk; simp

theorem tendsto_of_summable (a : ℕ → ℂ)
    (hs : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2)) :
    ∃ L, Tendsto a atTop (𝓝 L) ∧ ∀ m, ‖a m - L‖ ^ 2 ≤
      2 / 2 ^ m * ∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2 := by
  set c : ℕ → ℝ := fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by positivity
  have hfin : ∀ m k, ‖a m - a (k + m)‖ ^ 2 ≤ 2 / 2 ^ m * ∑' i, c (i + m) := by
    intro m k
    refine (norm_sub_sq_le a m k).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact Summable.sum_le_tsum _ (fun i _ => hc0 _) ((summable_nat_add_iff m).mpr hs)
  have htail := tendsto_sum_nat_add c
  have hcau : CauchySeq a := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev : ∀ᶠ m in atTop, 2 * ∑' i, c (i + m) < ε ^ 2 := by
      have := htail.const_mul 2
      rw [mul_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨m, hm⟩ := hev.exists_forall_of_atTop
    refine ⟨m, fun N hN => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, N = k + m := ⟨N - m, by omega⟩
    have h1 := hfin m k
    have h2 : 2 / 2 ^ m * ∑' i, c (i + m) ≤ 2 * ∑' i, c (i + m) := by
      refine mul_le_mul_of_nonneg_right ?_ (tsum_nonneg fun i => hc0 _)
      exact div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
    have h3 : dist (a (k + m)) (a m) ^ 2 < ε ^ 2 := by
      rw [dist_eq_norm, norm_sub_rev]; linarith [hm m le_rfl]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h3
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, fun m => ?_⟩
  have hlim : Tendsto (fun k => ‖a m - a (k + m)‖ ^ 2) atTop (𝓝 (‖a m - L‖ ^ 2)) :=
    (((hL.comp (tendsto_add_atTop_nat m)).const_sub (a m)).norm).pow 2
  exact le_of_tendsto' hlim fun k => hfin m k

end GlobalTheory.L2Limit

namespace GlobalTheory.L2Limit

section
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]


open Classical in
noncomputable def limSec (F : ℕ → ι → Y → ℂ) : ι → Y → ℂ := fun i y =>
  if ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) then limUnder atTop (fun m => F m i y) else 0

theorem limSec_eq (F : ℕ → ι → Y → ℂ) (i : ι) (y : Y) {c : ℂ}
    (h : Tendsto (fun m => F m i y) atTop (𝓝 c)) : limSec F i y = c := by
  unfold limSec; rw [if_pos ⟨c, h⟩]; exact h.limUnder_eq

theorem limSec_trans (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i j : ι) (y : Y) (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : limSec F i y = A.g la i j y * limSec F j y := by
  have hg := A.g_ne la i j y hi hj
  have hseq : (fun m => F m i y) = fun m => A.g la i j y * F m j y :=
    funext fun m => (hF m).2 i j y hi hj
  by_cases hc : ∃ c, Tendsto (fun m => F m j y) atTop (𝓝 c)
  · obtain ⟨c, hc⟩ := hc
    rw [limSec_eq F j y hc, limSec_eq F i y (by rw [hseq]; exact hc.const_mul _)]
  · have hc' : ¬ ∃ c, Tendsto (fun m => F m i y) atTop (𝓝 c) := by
      rintro ⟨c, hc'⟩
      apply hc
      refine ⟨(A.g la i j y)⁻¹ * c, ?_⟩
      have h2 : Tendsto (fun m => A.g la i j y * F m j y) atTop (𝓝 c) := by
        rw [← hseq]; exact hc'
      have := h2.const_mul (A.g la i j y)⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hg] using this
    unfold limSec
    rw [if_neg hc, if_neg hc', mul_zero]

theorem limSec_aemeas (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (i : ι) :
    AEMeasurable (limSec F i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target) := by
  classical
  set T := (A.chart i).target with hTdef
  have hT : MeasurableSet T := (A.chart i).open_target.measurableSet
  let G : ℕ → V n → ℂ := fun m => T.piecewise (F m i ∘ (A.chart i).symm) 0
  have hG : ∀ m, StronglyMeasurable (G m) := fun m =>
    (ContinuousOn.measurable_piecewise ((hF m).1 i).continuousOn continuousOn_const
      hT).stronglyMeasurable
  have hS := StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hG
  have hL := StronglyMeasurable.limUnder (l := atTop) hG
  have hmeas : StronglyMeasurable ({v | ∃ c, Tendsto (fun m => G m v) atTop (𝓝 c)}.piecewise
      (fun v => limUnder atTop (fun m => G m v)) (fun _ => (0:ℂ))) :=
    StronglyMeasurable.piecewise hS hL stronglyMeasurable_const
  refine hmeas.measurable.aemeasurable.congr ?_
  refine (ae_restrict_iff' hT).mpr (Eventually.of_forall fun v hv => ?_)
  have hGv : (fun m => G m v) = fun m => F m i ((A.chart i).symm v) :=
    funext fun m => by simp only [G, Set.piecewise_eq_of_mem _ _ _ hv, Function.comp_apply]
  simp only [Set.piecewise, Set.mem_setOf_eq, hGv, Function.comp_apply, limSec]

theorem measurable_step (A : WeightedAtlas n Y ι La) (la : La) (F : ℕ → ι → Y → ℂ)
    (hF : ∀ m, A.IsSSec la (F m)) (j : ℕ) :
    Measurable (fun y => ENNReal.ofReal (A.nsq la (F j - F (j + 1)) y)) :=
  ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq la (F j - F (j + 1)) (fun i k y hi hk => by
      simp only [Pi.sub_apply]; rw [(hF j).2 i k y hi hk, (hF (j + 1)).2 i k y hi hk]; ring)
    (fun i => ((hF j).1 i).continuousOn.sub ((hF (j + 1)).1 i).continuousOn)).measurable

end

theorem exists_l2_limit : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (F : ℕ → ι → Y → ℂ) (K : ℝ), 0 ≤ K → (∀ m, A.IsSSec (A.kap + la) (F m)) → (∀ m, n0 A la (F m - F (m + 1)) ≤ ENNReal.ofReal (K / 4 ^ m)) → ∃ f : ι → Y → ℂ, (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g (A.kap + la) i j y * f j y) ∧ (∀ i, AEMeasurable (f i ∘ (A.chart i).symm) (volume.restrict (A.chart i).target)) ∧ ∀ m, n0 A la (F m - f) ≤ ENNReal.ofReal (4 * K / 4 ^ m) := by
  intro n Y _ _ _ _ _ ι La _ A la F K hK hF hn
  set L := A.kap + la with hLdef
  set e : ℕ → Y → ℝ≥0∞ := fun j y => ENNReal.ofReal (A.nsq L (F j - F (j + 1)) y) with he_def
  have he : ∀ j, Measurable (e j) := measurable_step A L F hF
  have hint : ∀ j, ∫⁻ y, e j y ∂A.mu ≤ ENNReal.ofReal (K / 4 ^ j) := hn
  set S : ℕ → Y → ℝ≥0∞ := fun m y => ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y with hSdef
  have hSm : ∀ m, Measurable (S m) := fun m =>
    Measurable.tsum fun k => measurable_const.mul (he _)
  have hSint : ∀ m, ∫⁻ y, S m y ∂A.mu ≤ ENNReal.ofReal (K / 2 ^ m * 2) := by
    intro m
    show ∫⁻ y, ∑' k, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu ≤ _
    rw [lintegral_tsum fun k => ((he (k + m)).const_mul _).aemeasurable]
    calc ∑' k, ∫⁻ y, ENNReal.ofReal (2 ^ (k + m)) * e (k + m) y ∂A.mu
        = ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ∫⁻ y, e (k + m) y ∂A.mu := by
          congr 1; ext k; exact lintegral_const_mul _ (he _)
      _ ≤ ∑' k, ENNReal.ofReal (2 ^ (k + m)) * ENNReal.ofReal (K / 4 ^ (k + m)) :=
          ENNReal.tsum_le_tsum fun k => by gcongr; exact hint _
      _ = ∑' k, ENNReal.ofReal (K / 2 ^ m * (1 / 2) ^ k) := by
          congr 1; ext k
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show (4:ℝ) ^ (k + m) = 2 ^ (k + m) * 2 ^ (k + m) by rw [← mul_pow]; norm_num]
          rw [pow_add, one_div_pow]; field_simp
      _ = ENNReal.ofReal (∑' k, K / 2 ^ m * (1 / 2) ^ k) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
            (summable_geometric_two.mul_left _)).symm
      _ = ENNReal.ofReal (K / 2 ^ m * 2) := by rw [tsum_mul_left, tsum_geometric_two]
  have hfin : ∀ᵐ y ∂A.mu, S 0 y < ⊤ :=
    ae_lt_top (hSm 0) ((hSint 0).trans_lt ENNReal.ofReal_lt_top).ne
  have hpt : ∀ m, ∀ᵐ y ∂A.mu, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ≤
      ENNReal.ofReal (2 / 2 ^ m) * S m y := by
    intro m
    filter_upwards [hfin] with y hy
    set p := A.pick y
    set E := Real.exp (-A.ph L p y) with hE
    have hEpos : 0 < E := Real.exp_pos _
    set a : ℕ → ℂ := fun j => F j p y with ha
    have he_eq : ∀ j, e j y = ENNReal.ofReal (‖a j - a (j + 1)‖ ^ 2 * E) := fun j => rfl
    set b : ℕ → ℝ := fun k => 2 ^ k * (‖a k - a (k + 1)‖ ^ 2 * E) with hb_def
    have hb0 : ∀ k, 0 ≤ b k := fun k => by positivity
    have hSb : ∀ m', S m' y = ∑' k, ENNReal.ofReal (b (k + m')) := by
      intro m'
      simp only [hSdef, he_eq]
      congr 1; ext k
      rw [← ENNReal.ofReal_mul (by positivity)]
    have hb : Summable b := by
      have h0 := hSb 0
      simp only [add_zero] at h0
      have hs := ENNReal.summable_toReal (h0 ▸ hy.ne)
      refine hs.congr fun k => ?_
      exact ENNReal.toReal_ofReal (hb0 k)
    have hb' : Summable (fun j => (2:ℝ) ^ j * ‖a j - a (j + 1)‖ ^ 2) := by
      refine (hb.div_const E).congr fun k => ?_
      simp only [hb_def]; field_simp
    obtain ⟨Lm, hLm, hbd⟩ := tendsto_of_summable a hb'
    have hf : limSec F p y = Lm := limSec_eq F p y hLm
    have hnsq : A.nsq L (F m - limSec F) y = ‖a m - Lm‖ ^ 2 * E := by
      show ‖F m p y - limSec F p y‖ ^ 2 * E = _
      rw [hf]
    rw [hnsq, hSb m, ← ENNReal.ofReal_tsum_of_nonneg (fun k => hb0 _)
      ((summable_nat_add_iff m).mpr hb), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_right (hbd m) hEpos.le
    calc ‖a m - Lm‖ ^ 2 * E
        ≤ 2 / 2 ^ m * (∑' k, (2:ℝ) ^ (k + m) * ‖a (k + m) - a (k + m + 1)‖ ^ 2) * E := this
      _ = 2 / 2 ^ m * ∑' k, b (k + m) := by
          rw [mul_assoc, ← tsum_mul_right]
          congr 2; ext k; simp only [hb_def]; ring
  refine ⟨limSec F, fun i j y hi hj => limSec_trans A L F hF i j y hi hj,
    fun i => limSec_aemeas A L F hF i, fun m => ?_⟩
  calc n0 A la (F m - limSec F) = ∫⁻ y, ENNReal.ofReal (A.nsq L (F m - limSec F) y) ∂A.mu := rfl
    _ ≤ ∫⁻ y, ENNReal.ofReal (2 / 2 ^ m) * S m y ∂A.mu := lintegral_mono_ae (hpt m)
    _ = ENNReal.ofReal (2 / 2 ^ m) * ∫⁻ y, S m y ∂A.mu := lintegral_const_mul _ (hSm m)
    _ ≤ ENNReal.ofReal (2 / 2 ^ m) * ENNReal.ofReal (K / 2 ^ m * 2) := by gcongr; exact hSint m
    _ = ENNReal.ofReal (4 * K / 4 ^ m) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (4:ℝ) ^ m = 2 ^ m * 2 ^ m by rw [← mul_pow]; norm_num]
      field_simp; ring

end GlobalTheory.L2Limit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibre
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_bijective : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  intro R k _ _ σ hσ X s X₀ s₀ ψ w
  let e : R ≃+* k := RingEquiv.ofBijective σ hσ
  let τ : k →+* R := e.symm.toRingHom
  have hστ : ∀ r, σ (τ r) = r := fun r => e.apply_symm_apply r
  have hτσ : ∀ r, τ (σ r) = r := fun r => e.symm_apply_apply r
  have c1 : spMap τ ≫ spMap σ = 𝟙 (Sp R) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : σ.comp τ = RingHom.id k := RingHom.ext hστ
    have : τ.comp σ = RingHom.id R := RingHom.ext hτσ
    rw [this]; simp
  have c2 : spMap σ ≫ spMap τ = 𝟙 (Sp k) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : σ.comp τ = RingHom.id k := RingHom.ext hστ
    rw [this]; simp
  let l : X ⟶ X₀ := w.lift (𝟙 X) (s ≫ spMap τ) (by rw [Category.id_comp, Category.assoc, c1, Category.comp_id])
  have hl1 : l ≫ ψ = 𝟙 X := w.lift_fst _ _ _
  have hl2 : l ≫ s₀ = s ≫ spMap τ := w.lift_snd _ _ _
  have hl3 : ψ ≫ l = 𝟙 X₀ := by
    apply w.hom_ext
    · rw [Category.assoc, hl1, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, hl2, ← Category.assoc, w.w, Category.assoc, c2, Category.comp_id, Category.id_comp]
  obtain ⟨hcomp, -, hid⟩ := GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id
  intro b
  refine ⟨pullHO1 hl2 b, ?_⟩
  have := (hcomp k R X₀ X s₀ s τ l hl2 k X₀ s₀ σ ψ w.w (RingHom.id k) (𝟙 (Over.mk s₀) : Over.mk s₀ ⟶ Over.mk s₀).left
    (ovw (𝟙 (Over.mk s₀))) (by simp [hl3]) (fun r => (hστ r).symm)).1 b
  rw [this]
  exact (hid k (Over.mk s₀)).1 b

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibreStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_h1_surjective_bijective_fibre : ∀ (R k : Type) [CommRing R] [CommRing k] (σ : R →+* k), Function.Bijective σ → ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X) (w : IsPullback ψ s₀ s (spMap σ)), Function.Surjective (pullHO1 w.w) := by
  first | exact @GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | exact GlobalTheory.AbCoh.pullHO1_surjective_of_bijective | (intros; apply GlobalTheory.AbCoh.pullHO1_surjective_of_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechPullbackComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechPullbackComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_pull_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {g' : R →+* R'} {g'' : R →+* R''}
    {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X}
    (w' : φ ≫ s = s' ≫ spMap g') (w'' : φ' ≫ s = s'' ≫ spMap g'') (ψ : X'' ⟶ X') (h : ψ ≫ φ = φ')
    (V : X.Opens) (V' : X'.Opens) (V'' : X''.Opens) (e' : V' ≤ φ ⁻¹ᵁ V) (e'' : V'' ≤ φ' ⁻¹ᵁ V) (e : V'' ≤ ψ ⁻¹ᵁ V')
    (x : GlobalTheory.AbLaw.SecOnR s (LB.triv X) V) :
    trivCoord φ' s'' V'' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w'' V V'' e'' x) =
      (ψ.appLE V' V'' e).hom (trivCoord φ s' V' (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w' V V' e' x)) := by
  subst h
  have k : ∀ {Y : Scheme.{0}} {S : Type} [CommRing S] {g : R →+* S} (t : Y ⟶ Sp S) (π : Y ⟶ X)
      (w : π ≫ s = t ≫ spMap g) (O : Y.Opens) (eO : O ≤ π ⁻¹ᵁ V) (e2 : O ≤ π ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit)),
      trivCoord π t O (GlobalTheory.AbLaw.SecOnR.pull (LB.triv X) w V O eO x) =
        (π.appLE _ O e2).hom (x.coord PUnit.unit) := by
    intro Y S _ g t π w O eO e2
    have := GlobalTheory.AbLaw.SecOn.coord_pullLE π eO ((GlobalTheory.AbLaw.SecOnR.of s (LB.triv X) V).symm x) (i0 π)
    refine (congrArg (Sec.res t (le_inf le_rfl (by rw [triv_pull_U]; exact le_top))) this).trans ?_
    exact GlobalTheory.LB.resG_appLE π _ _ _
  have e2 : V' ≤ φ ⁻¹ᵁ (V ⊓ (LB.triv X).U PUnit.unit) := fun y hy => ⟨e' hy, trivial⟩
  rw [k s' φ w' V' e' e2, k s'' (ψ ≫ φ) w'' V'' e'' (fun y hy => e2 (e hy))]
  exact (congrArg (fun q => q.hom (x.coord PUnit.unit)) (Scheme.Hom.appLE_comp_appLE ψ φ _ V' V'' e2 e)).symm

theorem Φ_ext_eq_pullCoef : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  intro R R' R'' _ _ _ _ _ X X' X'' s s' s'' φ φ' w' w'' α ψ wψ h κ _ D hD' hD'' hle p z t
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero, map_zero]
    exact (map_zero ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)))).symm
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _)]
    exact (congrArg₂ (· + ·) hx hy).trans (map_add ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) _ _).symm
  | tmul r x =>
    have a1 : Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ (r ⊗ₜ x)) t = trivCoord φ' s'' _ (α r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w'' t.1 (x t)) := rfl
    have a2 : Φ w' D hD' p (r ⊗ₜ x) t = trivCoord φ s' _ (r • GlobalTheory.AbLaw.secCubePull (LB.triv X) D w' t.1 (x t)) := rfl
    refine a1.trans (Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) a2).symm)
    refine ((trivCoord φ' s'' _).map_smul _ _).trans ?_
    refine Eq.trans ?_ (congrArg ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t))) ((trivCoord φ s' _).map_smul _ _)).symm
    refine Eq.trans ?_ ((pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).smul (ne t.1 (card_nonempty t)) r _).symm
    exact congrArg (α r • ·) (trivCoord_pull_comp w' w'' ψ h _ _ _ _ _ (pr _ hD' _ hD'' hle (ne t.1 (card_nonempty t)).unop).2 (x t))

end GlobalTheory.CechPoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechPullbackCommStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_pullback_comm : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := by
  first | exact @GlobalTheory.CechPoset.Φ_ext_eq_pullCoef | exact GlobalTheory.CechPoset.Φ_ext_eq_pullCoef | (intros; apply GlobalTheory.CechPoset.Φ_ext_eq_pullCoef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsZeroCoboundaryComm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsZeroCoboundaryComm
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem mp_cochain_congr {p : ℕ} (c : CC F p) {s s' : {s : Finset κ // s.card = p + 1}} (h : s.1 = s'.1)
    {b : (NE κ)ᵒᵖ} (φ : ne s.1 (card_nonempty s) ⟶ b) (φ' : ne s'.1 (card_nonempty s') ⟶ b) :
    mp F φ (c s) = mp F φ' (c s') := by
  obtain rfl : s = s' := Subtype.ext h
  rw [Subsingleton.elim φ φ']

theorem orderedCech_cochainsZero_coboundary_comm {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0) : d0 F (e0 F c) = e1 F (δ F 0 c) := by
  funext a b f
  rw [amitsur_d0_apply]
  simp only [e0, e1, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    AlgHom.toLinearMap_apply]
  rw [← mp_comp]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      AlgHom.toLinearMap_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [δ_apply, map_sum]
    have hb : mn b ∈ ({mn b, mn a} : Finset κ) := by simp
    have ha : mn a ∈ ({mn b, mn a} : Finset κ) := by simp
    have s1 : GlobalTheory.cubeSign ({mn b, mn a} : Finset κ) (mn b) = 1 :=
      GlobalTheory.cubeSign_eq_one_of_forall_le (by simp [h.le])
    have s2 : GlobalTheory.cubeSign ({mn b, mn a} : Finset κ) (mn a) = -1 := by
      have := GlobalTheory.cubeSign_erase_of_lt (t := {mn b, mn a}) hb h
      rw [Finset.erase_insert (by simp [h.ne]), GlobalTheory.cubeSign_singleton] at this
      omega
    rw [Fintype.sum_eq_add (⟨mn b, hb⟩ : ({mn b, mn a} : Finset κ)) ⟨mn a, ha⟩
      (fun e => h.ne (congrArg Subtype.val e))
      (by
        rintro ⟨x, hx⟩ ⟨h1, h2⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (h1 rfl).elim
        · exact (h2 rfl).elim)]
    simp only [s1, s2, one_smul, neg_smul, map_neg, ← mp_comp]
    rw [neg_add, neg_neg, neg_add_eq_sub]
    refine congrArg₂ (· - ·) ?_ ?_
    · refine mp_cochain_congr F c (s := ⟨{mn b}, Finset.card_singleton _⟩)
        (s' := GlobalTheory.Cube.eraseIdx ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ ⟨mn a, ha⟩) ?_ _ _
      show {mn b} = Finset.erase {mn b, mn a} (mn a)
      rw [Finset.pair_comm, Finset.erase_insert (by simp [h.ne'])]
    · refine mp_cochain_congr F c (s := ⟨{mn a}, Finset.card_singleton _⟩)
        (s' := GlobalTheory.Cube.eraseIdx ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ ⟨mn b, hb⟩) ?_ _ _
      show {mn a} = Finset.erase {mn b, mn a} (mn b)
      rw [Finset.erase_insert (by simp [h.ne])]
  · have e : mn b = mn a := le_antisymm (mn_le_of_hom f) (not_lt.1 h)
    rw [LinearMap.zero_apply, sub_eq_zero]
    refine mp_cochain_congr F c (s := ⟨{mn b}, Finset.card_singleton _⟩)
      (s' := ⟨{mn a}, Finset.card_singleton _⟩) ?_ _ _
    show ({mn b} : Finset κ) = {mn a}
    rw [e]

end GlobalTheory.CechPoset
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsZeroCoboundaryCommStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderedCechToCatCochainsZero_coboundary_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0), d0 F (e0 F c) = e1 F (δ F 0 c) := by
  first | exact @GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm | exact GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm | (intros; apply GlobalTheory.CechPoset.orderedCech_cochainsZero_coboundary_comm <;> assumption)
end
end
