module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Nonzero

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SmoothPf
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_restrict_of_zero (ν : Measure (GR n)) {C : Set (GR n)} (_hCm : MeasurableSet C) {F : GR n → ℂ}
    (hF : ∀ u ∉ C, F u = 0) : ∫ u, F u ∂ν = ∫ u, F u ∂(ν.restrict C) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

theorem holInt (ν : Measure (GR n)) [ν.IsHaarMeasure] {C : Set (GR n)} (hC : IsCompact C) {U : Set ℂ} (hU : IsOpen U)
    (F : GR n → ℂ → ℂ) (hF0 : ∀ u ∉ C, ∀ z, F u z = 0)
    (hcont : ContinuousOn (fun y : GR n × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ u ∈ C, DifferentiableOn ℂ (F u) U) :
    DifferentiableOn ℂ (fun z => ∫ u, F u z ∂ν) U ∧
      ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ u, F u z ∂ν) z = ∫ u, iteratedDeriv r (F u) z ∂ν := by
  classical
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  haveI : IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hdF : ∀ u, DifferentiableOn ℂ (F u) U := by
    intro u
    by_cases hu : u ∈ C
    · exact hd u hu
    · have h0 : F u = fun _ => 0 := funext (hF0 u hu)
      rw [h0]
      exact differentiableOn_const 0
  have key : ∀ z ∈ U, ∃ R : ℝ≥0, 0 < R ∧ Metric.closedBall z (R : ℝ) ⊆ U := by
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
    refine ⟨(ε / 2).toNNReal, Real.toNNReal_pos.mpr (half_pos hε), ?_⟩
    rw [Real.coe_toNNReal _ (half_pos hε).le]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hint : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ a : ℝ → ℂ, Continuous a →
      Integrable (fun p : ℝ × GR n => a p.1 • F p.2 (circleMap z R p.1))
        ((volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))).prod (ν.restrict C)) := by
    intro z R hzR a ha
    rw [Measure.prod_restrict]
    have hc2 : ContinuousOn (fun p : ℝ × GR n => a p.1 • F p.2 (circleMap z R p.1))
        (Set.Icc 0 (2 * Real.pi) ×ˢ C) := by
      apply ContinuousOn.smul (ha.comp continuous_fst).continuousOn
      have h1 : ContinuousOn (fun p : ℝ × GR n => (p.2, circleMap z R p.1)) (Set.Icc 0 (2 * Real.pi) ×ˢ C) :=
        (continuous_snd.prodMk ((continuous_circleMap z R).comp continuous_fst)).continuousOn
      refine hcont.comp h1 ?_
      rintro ⟨θ, u⟩ ⟨_, hu⟩
      exact ⟨hu, hzR (circleMap_mem_closedBall z R.coe_nonneg θ)⟩
    exact (hc2.integrableOn_compact (isCompact_Icc.prod hC)).mono_set
      (Set.prod_mono (Set.uIoc_subset_uIcc.trans (Set.uIcc_of_le (by positivity)).subset) subset_rfl)
  have hfub : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ a : ℝ → ℂ, Continuous a →
      (∫ θ in (0 : ℝ)..2 * Real.pi, a θ • ∫ u, F u (circleMap z R θ) ∂ν)
        = ∫ u, (∫ θ in (0 : ℝ)..2 * Real.pi, a θ • F u (circleMap z R θ)) ∂ν := by
    intro z R hzR a ha
    have e1 : ∀ θ, a θ • ∫ u, F u (circleMap z R θ) ∂ν
        = ∫ u, a θ • F u (circleMap z R θ) ∂(ν.restrict C) := by
      intro θ
      rw [integral_restrict_of_zero ν hCm (fun u hu => hF0 u hu (circleMap z R θ)), integral_smul]
    simp_rw [e1]
    rw [intervalIntegral_integral_swap (hint z R hzR a ha)]
    exact (integral_restrict_of_zero ν hCm (fun u hu => by simp [hF0 u hu])).symm
  have hcirc : ∀ (z : ℂ) (R : ℝ≥0), Metric.closedBall z (R : ℝ) ⊆ U → ∀ k : ℂ → ℂ,
      Continuous (fun θ => k (circleMap z R θ)) →
      (∮ ζ in C(z, R), k ζ • ∫ u, F u ζ ∂ν) = ∫ u, (∮ ζ in C(z, R), k ζ • F u ζ) ∂ν := by
    intro z R hzR k hk
    simp only [circleIntegral, deriv_circleMap, smul_smul]
    exact hfub z R hzR (fun θ => circleMap 0 R θ * Complex.I * k (circleMap z R θ))
      (((continuous_circleMap 0 R).mul continuous_const).mul hk)
  have hps : ∀ z ∈ U, ∃ R : ℝ≥0, 0 < R ∧ Metric.closedBall z (R : ℝ) ⊆ U ∧
      HasFPowerSeriesOnBall (fun w => ∫ u, F u w ∂ν) (cauchyPowerSeries (fun w => ∫ u, F u w ∂ν) z R) z R := by
    intro z hz
    obtain ⟨R, hR, hzR⟩ := key z hz
    refine ⟨R, hR, hzR, ?_⟩
    have hci : CircleIntegrable (fun w => ∫ u, F u w ∂ν) z R := by
      have h := (hint z R hzR (fun _ => 1) continuous_const).integral_prod_left
      rw [CircleIntegrable, intervalIntegrable_iff]
      refine h.congr (Eventually.of_forall fun θ => ?_)
      simp only [one_smul]
      exact (integral_restrict_of_zero ν hCm (fun u hu => hF0 u hu _)).symm
    refine (hasFPowerSeriesOn_cauchy_integral hci hR).congr ?_
    intro w hw
    rw [Metric.eball_coe] at hw
    have hk : Continuous (fun θ => (circleMap z R θ - w)⁻¹) :=
      ((continuous_circleMap z R).sub continuous_const).inv₀
        (fun θ => sub_ne_zero.mpr (circleMap_ne_mem_ball hw θ))
    show (2 * ↑Real.pi * Complex.I)⁻¹ • (∮ ζ in C(z, R), (ζ - w)⁻¹ • ∫ u, F u ζ ∂ν) = ∫ u, F u w ∂ν
    rw [hcirc z R hzR (fun ζ => (ζ - w)⁻¹) hk, ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw ((hdF u).continuousOn.mono hzR)
      (fun x hx => (hdF u).differentiableAt (hU.mem_nhds (hzR (Metric.ball_subset_closedBall hx.1))))
  constructor
  · intro z hz
    obtain ⟨R, -, -, h⟩ := hps z hz
    exact h.analyticAt.differentiableAt.differentiableWithinAt
  · intro z hz r
    obtain ⟨R, hR, hzR, h⟩ := hps z hz
    have hFu : ∀ u, iteratedDeriv r (F u) z = r.factorial • cauchyPowerSeries (F u) z R r (fun _ => 1) := by
      intro u
      rw [iteratedDeriv_eq_iteratedFDeriv, ← (((hdF u).mono hzR).hasFPowerSeriesOnBall hR).factorial_smul]
    have hne : ∀ θ, circleMap z R θ - z ≠ 0 := fun θ =>
      sub_ne_zero.mpr (fun h' => hR.ne' (by exact_mod_cast circleMap_eq_center_iff.mp h'))
    have hG : cauchyPowerSeries (fun w => ∫ u, F u w ∂ν) z R r (fun _ => 1)
        = ∫ u, cauchyPowerSeries (F u) z R r (fun _ => 1) ∂ν := by
      simp only [cauchyPowerSeries_apply, smul_smul]
      rw [hcirc z R hzR (fun ζ => (1 / (ζ - z)) ^ r * (ζ - z)⁻¹)
        (((continuous_const.div ((continuous_circleMap z R).sub continuous_const) hne).pow r).mul
          (((continuous_circleMap z R).sub continuous_const).inv₀ hne)), integral_smul]
    rw [iteratedDeriv_eq_iteratedFDeriv, ← h.factorial_smul, integral_congr_ae (Eventually.of_forall hFu), hG]
    simp only [nsmul_eq_mul]
    rw [integral_const_mul]

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.IntegralRestrictC
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hLoc_nonneg' (g : GR n) : 0 ≤ hLoc g := by unfold hLoc; positivity

theorem hLoc_pos' (g : GR n) : 0 < hLoc g := Vac.hLoc_pos detU1 g

theorem hLoc_slit (g : GR n) : ((hLoc g : ℝ) : ℂ) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.2 (hLoc_pos' g)

theorem continuous_phi (m : ℕ) (e : ℤ) (w : ℂ) : Continuous (phi (n := n) m e w) := by
  unfold phi
  refine (Vac.continuous_weight_factor detU1 m 0 e).mul ?_
  exact (Complex.continuous_ofReal.comp (Vac.continuous_hLoc detU1)).cpow continuous_const fun g => hLoc_slit g

theorem continuous_phi₂ (m : ℕ) (e : ℤ) :
    Continuous fun p : GR n × ℂ => phi m e p.2 p.1 := by
  unfold phi
  refine ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_fst).mul ?_
  exact (Complex.continuous_ofReal.comp ((Vac.continuous_hLoc detU1).comp continuous_fst)).cpow continuous_snd
    fun p => hLoc_slit p.1

theorem differentiable_phi (m : ℕ) (e : ℤ) (u : GR n) : Differentiable ℂ fun w => phi m e w u := by
  unfold phi
  have h0 : ((hLoc u : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hLoc_pos' u).ne'
  exact (differentiable_const _).mul (differentiable_id.const_cpow (Or.inl h0))

section

variable {m : ℕ} {e : ℤ} (ν : Measure (GR n)) (μK : Measure (KR n)) {β : M2 n → ℝ}

theorem twC (hβs : HasCompactSupport β) : IsCompact ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) :=
  isCompact_preimage_mR (tw_support m e μK hβs)

theorem tw_zero_off {u : GR n} (hu : u ∉ (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) : tw m e μK β (mR u) = 0 :=
  image_eq_zero_of_notMem_tsupport hu

theorem continuous_twR [IsFiniteMeasure μK] (hβc : Continuous β) : Continuous fun u : GR n => tw m e μK β (mR u) := by
  have hF : Continuous fun k : KR n => (F0 m 0 e (k : GR n))⁻¹ :=
    ((Vac.continuous_weight_factor detU1 m 0 e).comp continuous_subtype_val).inv₀
      (fun k => Vac.spherical_section_ne_zero detU1 m 0 e _)
  have hc : Continuous (Function.uncurry fun (X : M2 n) (k : KR n) =>
      (F0 m 0 e (k : GR n))⁻¹ * (β ((mR (k : GR n))ᴴ * X) : ℂ)) := by
    refine (hF.comp continuous_snd).mul (Complex.continuous_ofReal.comp (hβc.comp ?_))
    exact ((continuous_mR.comp (continuous_subtype_val.comp continuous_snd)).matrix_conjTranspose).matrix_mul
      continuous_fst
  have h := continuous_parametric_integral_of_continuous (μ := μK) hc isCompact_univ
  simp only [Measure.restrict_univ] at h
  exact h.comp continuous_mR

theorem integral_restrict_C (F : GR n → ℂ) (hF : ∀ u, u ∉ (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β) → F u = 0) :
    ∫ u, F u ∂ν = ∫ u, F u ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm

theorem cw_differentiable [ν.IsHaarMeasure] [μK.IsHaarMeasure] (hβc : Continuous β) (hβs : HasCompactSupport β) :
    Differentiable ℂ fun w => cw m e ν μK β w := by
  have hC := twC (m := m) (e := e) μK hβs
  haveI : IsFiniteMeasure (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
    isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have key := holParam (GR n) (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)))
    ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) hC
    (by rw [Measure.restrict_apply' hC.isClosed.measurableSet]; simp) univ
    (fun u w => phi m e w u * tw m e μK β (mR u)) isOpen_univ
    (by
      refine Continuous.continuousOn ?_
      exact ((continuous_phi₂ m e).comp (continuous_fst.prodMk continuous_snd)).mul
        (hcont.comp continuous_fst))
    (fun u _ => ((differentiable_phi m e u).mul_const _).differentiableOn)
  have heq : (fun w => cw m e ν μK β w) =
      fun w => ∫ u, phi m e w u * tw m e μK β (mR u) ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) := by
    funext w
    exact integral_restrict_C ν μK _ (fun u hu => by rw [tw_zero_off μK hu, mul_zero])
  rw [heq]
  exact differentiableOn_univ.mp key.1

end

section Glob

variable {m : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ}
  {U : Set ℂ} {d : Polynomial ℂ} {Ê : ℂ → G → ℂ} {t : ℝ}

theorem lhs_diff (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β)
    (g : G) (y : GR n) : DifferentiableOn ℂ (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) U := by
  have hC := twC (m := m) (e := e) μK hβs
  haveI : IsFiniteMeasure (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) :=
    isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have hmap : Continuous fun q : GR n × ℂ => (q.2, g * ι (y * q.1)) :=
    continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp (continuous_const.mul continuous_fst)))
  have key := holParam (GR n) (ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)))
    ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β)) hC
    (by rw [Measure.restrict_apply' hC.isClosed.measurableSet]; simp) U
    (fun u z => Ê z (g * ι (y * u)) * tw m e μK β (mR u)) hD.hU
    (by
      refine ContinuousOn.mul ?_ (hcont.comp continuous_fst).continuousOn
      refine hD.cont.comp hmap.continuousOn ?_
      intro q hq
      exact ⟨hq.2, mem_univ _⟩)
    (fun u _ => (hD.hol (g * ι (y * u))).mul_const _)
  have heq : (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) =
      fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u)
        ∂(ν.restrict ((mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β))) := by
    funext z
    exact integral_restrict_C ν μK _ (fun u hu => by rw [tw_zero_off μK hu, mul_zero])
  rw [heq]
  exact key.1

theorem term_rep (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (w : ℂ) (g : G) (q : GlobalTheory.Eis.Cosets Pp Γ) :
    ∃ (c : ℂ) (y₀ : GR n), ∀ v : GR n,
      GlobalTheory.Eis.term Pp Γ (fun x => ((Ht x : ℝ) : ℂ) ^ w * f x) (g * ι v) q = c * phi m e w (y₀ * v) := by
  obtain ⟨x₀, y₀, S, r, hr, hxy, hp⟩ := hD.split (((q.out : Γ) : G) * g)
  refine ⟨(r : ℂ) ^ w * S, y₀, fun v => ?_⟩
  have e1 : ((q.out : Γ) : G) * (g * ι v) = x₀ * ι (y₀ * v) := by rw [← mul_assoc, hxy, map_mul, mul_assoc]
  show ((Ht (((q.out : Γ) : G) * (g * ι v)) : ℝ) : ℂ) ^ w * f (((q.out : Γ) : G) * (g * ι v)) = _
  rw [e1, (hp (y₀ * v)).1, (hp (y₀ * v)).2, phi, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_nonneg' _)]
  ring

theorem conv_far (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β)
    (z : ℂ) (hz : t < z.re) (g : G) (y : GR n) :
    ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
  obtain ⟨hfar, hE⟩ := hD.far z hz
  set Φ : G → ℂ := fun x => ((Ht x : ℝ) : ℂ) ^ (z - s₀) * f x with hΦ
  set C := (mR : GR n → M2 n) ⁻¹' tsupport (tw m e μK β) with hCdef
  have hC : IsCompact C := twC μK hβs
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  haveI : IsFiniteMeasure (ν.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  have hcont : Continuous fun u : GR n => tw m e μK β (mR u) := continuous_twR μK hβc
  have hι : Continuous fun u : GR n => g * ι (y * u) :=
    continuous_const.mul (hD.ιc.comp (continuous_const.mul continuous_id))
  obtain ⟨b, hb, hbd⟩ := hfar (insert (g * ι y) ((fun u => g * ι (y * u)) '' C)) ((hC.image hι).insert _)
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  haveI : Countable (Function.support b) := hb.countable_support.to_subtype
  have hmemC : ∀ u ∈ C, g * ι (y * u) ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C) :=
    fun u hu => mem_insert_of_mem _ ⟨u, hu, rfl⟩
  have hzero : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C), ∀ q,
      q ∉ Function.support b → GlobalTheory.Eis.term Pp Γ Φ h q = 0 := by
    intro h hh q hq
    have h1 := hbd h hh q
    rw [Function.notMem_support.mp hq] at h1
    exact norm_le_zero_iff.mp h1
  have hsum_eq : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C),
      GlobalTheory.Eis.cosetSum Pp Γ Φ h = ∑' q : Function.support b, GlobalTheory.Eis.term Pp Γ Φ h q := by
    intro h hh
    unfold GlobalTheory.Eis.cosetSum
    exact (tsum_subtype_eq_of_support_subset
      (fun q hq => by_contra fun hq' => hq (hzero h hh q hq'))).symm
  have hsumm : ∀ h ∈ insert (g * ι y) ((fun u => g * ι (y * u)) '' C),
      Summable fun q : Function.support b => GlobalTheory.Eis.term Pp Γ Φ h q :=
    fun h hh => Summable.of_norm_bounded (hb.subtype _) (fun q => hbd h hh q)
  have hvan : ∀ F : GR n → ℂ, ∀ u, u ∉ C → F u * tw m e μK β (mR u) = 0 :=
    fun F u hu => by rw [tw_zero_off μK hu, mul_zero]
  have hrep : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, ∃ (c : ℂ) (y₀ : GR n), ∀ v : GR n,
      GlobalTheory.Eis.term Pp Γ Φ (g * ι v) q = c * phi m e (z - s₀) (y₀ * v) := by
    intro q
    obtain ⟨c, y₀, hc⟩ := term_rep hD (z - s₀) g q
    exact ⟨c, y₀, fun v => by rw [hΦ]; exact hc v⟩
  have hterm : ∀ q : GlobalTheory.Eis.Cosets Pp Γ,
      ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂ν =
        cw m e ν μK β (z - s₀) * GlobalTheory.Eis.term Pp Γ Φ (g * ι y) q := by
    intro q
    obtain ⟨c, y₀, hc⟩ := hrep q
    simp only [hc, mul_assoc c]
    rw [integral_const_mul]
    simp only [← mul_assoc y₀ y]
    rw [conv_phi]
    ring
  have hmeas : ∀ q : GlobalTheory.Eis.Cosets Pp Γ, AEStronglyMeasurable
      (fun u => GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u)) (ν.restrict C) := by
    intro q
    obtain ⟨c, y₀, hc⟩ := hrep q
    have hcq : Continuous fun u : GR n =>
        c * phi m e (z - s₀) (y₀ * (y * u)) * tw m e μK β (mR u) :=
      (continuous_const.mul ((continuous_phi m e (z - s₀)).comp
        (continuous_const.mul (continuous_const.mul continuous_id)))).mul hcont
    simp only [hc]
    exact hcq.aestronglyMeasurable
  have hHas : HasSum
      (fun q : Function.support b =>
        ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂(ν.restrict C))
      (∫ u, (∑' q : Function.support b, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q) *
        tw m e μK β (mR u) ∂(ν.restrict C)) := by
    refine hasSum_integral_of_dominated_convergence (fun q _ => b q * M) (fun q => hmeas q) ?_ ?_ ?_ ?_
    · intro q
      filter_upwards [ae_restrict_mem hCm] with u hu
      rw [norm_mul]
      have h1 := hbd _ (hmemC u hu) q
      exact mul_le_mul h1 (hM u hu) (norm_nonneg _) ((norm_nonneg _).trans h1)
    · exact Eventually.of_forall fun _ => (hb.subtype _).mul_right M
    · exact integrable_const _
    · filter_upwards [ae_restrict_mem hCm] with u hu
      exact (hsumm _ (hmemC u hu)).hasSum.mul_right _
  calc ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν
      = ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂(ν.restrict C) :=
        integral_restrict_C ν μK _ (hvan _)
    _ = ∫ u, Polynomial.eval z d * ((∑' q : Function.support b,
          GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q) * tw m e μK β (mR u)) ∂(ν.restrict C) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem hCm] with u hu
        rw [hE, hsum_eq _ (hmemC u hu)]
        ring
    _ = Polynomial.eval z d * ∑' q : Function.support b,
          ∫ u, GlobalTheory.Eis.term Pp Γ Φ (g * ι (y * u)) q * tw m e μK β (mR u) ∂(ν.restrict C) := by
        rw [integral_const_mul, hHas.tsum_eq]
    _ = Polynomial.eval z d * ∑' q : Function.support b,
          cw m e ν μK β (z - s₀) * GlobalTheory.Eis.term Pp Γ Φ (g * ι y) q := by
        congr 1
        refine tsum_congr fun q => ?_
        rw [← integral_restrict_C ν μK _ (hvan _), hterm]
    _ = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
        rw [tsum_mul_left, hE, hsum_eq _ (mem_insert _ _)]
        ring

theorem conv_U (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) (ν : Measure (GR n)) [ν.IsHaarMeasure]
    (μK : Measure (KR n)) [μK.IsHaarMeasure] {β : M2 n → ℝ} (hβc : Continuous β) (hβs : HasCompactSupport β) :
    ∀ z ∈ U, ∀ (g : G) (y : GR n),
      ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν = cw m e ν μK β (z - s₀) * Ê z (g * ι y) := by
  intro z hz g y
  obtain ⟨σ, hσ⟩ := hD.hR.1
  have hz0U : (((max σ t + 1 : ℝ)) : ℂ) ∈ U := by
    apply hσ
    simp only [GlobalTheory.Cont.rightOf, mem_setOf_eq, Complex.ofReal_re]
    linarith [le_max_left σ t]
  have hL : AnalyticOnNhd ℂ (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) U :=
    (lhs_diff hD ν μK hβc hβs g y).analyticOnNhd hD.hU
  have hdc : Differentiable ℂ fun z : ℂ => cw m e ν μK β (z - s₀) :=
    (cw_differentiable ν μK hβc hβs).comp (differentiable_id.sub_const s₀)
  have hR : AnalyticOnNhd ℂ (fun z => cw m e ν μK β (z - s₀) * Ê z (g * ι y)) U :=
    (hdc.differentiableOn.mul (hD.hol _)).analyticOnNhd hD.hU
  have hev : (fun z => ∫ u, Ê z (g * ι (y * u)) * tw m e μK β (mR u) ∂ν) =ᶠ[𝓝 (((max σ t + 1 : ℝ)) : ℂ)]
      (fun z => cw m e ν μK β (z - s₀) * Ê z (g * ι y)) := by
    have hopen : IsOpen {w : ℂ | t < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (((max σ t + 1 : ℝ)) : ℂ) ∈ {w : ℂ | t < w.re} := by
      simp only [mem_setOf_eq, Complex.ofReal_re]
      linarith [le_max_right σ t]
    filter_upwards [hopen.mem_nhds hmem] with w hw
    exact conv_far hD ν μK hβc hβs w hw g y
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR hD.hR.isPreconnected hz0U hev hz

end Glob

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.KerInt
section -- merged from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DerivCurveOfHasFDerivAt
noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.HSt.MI

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Z1 (Z : M2 n) : M2 n := (1 / 2 : ℂ) • (Z + sig Z)

def Z2 (Z : M2 n) : M2 n := (1 / (2 * Complex.I)) • (Z - sig Z)

theorem curve_zero (x Y : M2 n) : x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = x := by
  simp

theorem rC_eq (Z : M2 n) (F : M2 n → ℂ) (x : M2 n) :
    rC Z F x = deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z1 Z))) 0 +
      Complex.I * deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Z2 Z))) 0 := rfl

theorem deriv_curve_of_hasFDerivAt {F : M2 n → ℂ} {D : M2 n →L[ℝ] ℂ} {x : M2 n} (hF : HasFDerivAt F D x) (Y : M2 n) :
    deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 = D (x * Y) := by
  exact (hF.comp_hasDerivAt_of_eq 0 (hasDerivAt_curve x Y) (curve_zero x Y).symm).deriv

theorem rC_of_diff {F : M2 n → ℂ} {x : M2 n} (hF : DifferentiableAt ℝ F x) (Z : M2 n) :
    rC Z F x = fderiv ℝ F x (x * Z1 Z) + Complex.I * fderiv ℝ F x (x * Z2 Z) := by
  rw [rC_eq, deriv_curve_of_hasFDerivAt hF.hasFDerivAt, deriv_curve_of_hasFDerivAt hF.hasFDerivAt]

theorem rC_congr {F F' : M2 n → ℂ} {O : Set (M2 n)} (hO : IsOpen O) {x : M2 n} (hx : x ∈ O) (h : EqOn F F' O)
    (Z : M2 n) : rC Z F x = rC Z F' x := by
  have key : ∀ Y : M2 n, deriv (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • Y))) 0 =
      deriv (fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • Y))) 0 := by
    intro Y
    apply Filter.EventuallyEq.deriv_eq
    have hc := (hasDerivAt_curve x Y).continuousAt
    have hO' : O ∈ 𝓝 (x * NormedSpace.exp (((0 : ℝ) : ℂ) • Y)) := by
      rw [curve_zero]
      exact hO.mem_nhds hx
    filter_upwards [hc.preimage_mem_nhds hO'] with t ht
    exact h ht
  rw [rC_eq, rC_eq, key, key]

end PositivityTheory.Rg.Sw.HSt.MI
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable (m : ℕ) (e : ℤ) (ν : Measure (GR n)) [ν.IsHaarMeasure] (μK : Measure (KR n)) [μK.IsHaarMeasure]
  {β : M2 n → ℝ} (hβ : ContDiff ℝ ∞ β) (hβs : HasCompactSupport β)

def Psi (β : M2 n → ℝ) (h : GR n → ℂ) (x : M2 n) : ℂ := ∫ u, h u • kk m e μK β (x, mR u) ∂ν

def Lk (β : M2 n → ℝ) (Z x₀ : M2 n) (u : GR n) : ℂ :=
  fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ (x₀ * Z1 Z) +
    Complex.I * fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ (x₀ * Z2 Z)

include hβ hβs in
theorem good (h : GR n → ℂ) (hh : Continuous h) :
    PCD.Good (Inv n) (fun x u => h u • kk m e μK β (x, mR u)) :=
  PCD.good_of_joint isOpen_Inv _ (kk_contDiffOn m e μK hβ) (fun u : GR n => mR u) continuous_mR h hh
    (kk_supp m e μK hβs)

include hβ hβs in
theorem psi_contDiffOn (h : GR n → ℂ) (hh : Continuous h) : ContDiffOn ℝ ∞ (Psi m e ν μK β h) (Inv n) :=
  PCD.contDiffOn_integral isOpen_Inv ν (good m e μK hβ hβs h hh)

include hβ in
theorem kk_diff {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) (u : GR n) :
    DifferentiableAt ℝ (fun x' => kk m e μK β (x', mR u)) x₀ := by
  have hsl : ContDiffOn ℝ ∞ (fun x' => kk m e μK β (x', mR u)) (Inv n) :=
    (kk_contDiffOn m e μK hβ).comp (contDiffOn_id.prodMk contDiffOn_const) fun x hx => ⟨hx, mem_univ _⟩
  exact (hsl.differentiableOn (by simp) x₀ hx₀).differentiableAt (isOpen_Inv.mem_nhds hx₀)

include hβ hβs in
theorem rC_psi (h : GR n → ℂ) (hh : Continuous h) (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) :
    rC Z (Psi m e ν μK β h) x₀ = ∫ u, h u * Lk m e μK β Z x₀ u ∂ν := by
  have hG := good m e μK hβ hβs h hh
  have hF := hG.hasFDerivAt isOpen_Inv ν hx₀
  have hI := (hG.dK isOpen_Inv).integrable ν hx₀
  have hfd : ∀ u, fderiv ℝ (fun x => h u • kk m e μK β (x, mR u)) x₀ =
      h u • fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀ := fun u =>
    fderiv_const_smul (kk_diff m e μK hβ hx₀ u) (h u)
  rw [show Psi m e ν μK β h = fun x => ∫ u, h u • kk m e μK β (x, mR u) ∂ν from rfl]
  rw [rC_of_diff hF.differentiableAt]
  erw [hF.fderiv, ContinuousLinearMap.integral_apply hI, ContinuousLinearMap.integral_apply hI]
  have i1 := hI.apply_continuousLinearMap (x₀ * Z1 Z)
  have i2 := hI.apply_continuousLinearMap (x₀ * Z2 Z)
  rw [← integral_const_mul, ← integral_add i1 (i2.const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  erw [hfd u]
  change h u • (fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀) (x₀ * Z1 Z) +
    Complex.I * (h u • (fderiv ℝ (fun x' => kk m e μK β (x', mR u)) x₀) (x₀ * Z2 Z)) = _
  simp only [Lk, smul_eq_mul]
  ring

include hβ in
theorem slice_fderiv {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) (v : M2 n) :
    fderiv ℝ (fun x' => kk m e μK β (x', v)) x₀ = (fderiv ℝ (kk m e μK β) (x₀, v)).comp (ContinuousLinearMap.inl ℝ (M2 n) (M2 n)) := by
  have hS : IsOpen (Inv n ×ˢ (univ : Set (M2 n))) := isOpen_Inv.prod isOpen_univ
  have hd : DifferentiableAt ℝ (kk m e μK β) (x₀, v) :=
    ((kk_contDiffOn m e μK hβ).differentiableOn (by simp) _ ⟨hx₀, mem_univ _⟩).differentiableAt
      (hS.mem_nhds ⟨hx₀, mem_univ _⟩)
  have hi : HasFDerivAt (fun x' : M2 n => (x', v)) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n)) x₀ :=
    (hasFDerivAt_id x₀).prodMk (hasFDerivAt_const v x₀)
  exact (hd.hasFDerivAt.comp x₀ hi).fderiv

include hβ in
theorem Lk_cont (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) : Continuous (Lk m e μK β Z x₀) := by
  have hS : IsOpen (Inv n ×ˢ (univ : Set (M2 n))) := isOpen_Inv.prod isOpen_univ
  have hc : ContinuousOn (fun p => fderiv ℝ (kk m e μK β) p) (Inv n ×ˢ univ) :=
    (kk_contDiffOn m e μK hβ).continuousOn_fderiv_of_isOpen hS (by simp)
  have hc' : Continuous fun u : GR n => fderiv ℝ (kk m e μK β) (x₀, mR u) :=
    hc.comp_continuous (continuous_const.prodMk continuous_mR) fun u => ⟨hx₀, mem_univ _⟩
  have e1 : Lk m e μK β Z x₀ = fun u => fderiv ℝ (kk m e μK β) (x₀, mR u) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n) (x₀ * Z1 Z)) +
      Complex.I * fderiv ℝ (kk m e μK β) (x₀, mR u) (ContinuousLinearMap.inl ℝ (M2 n) (M2 n) (x₀ * Z2 Z)) := by
    funext u
    simp only [Lk, slice_fderiv m e μK hβ hx₀, ContinuousLinearMap.comp_apply]
  rw [e1]
  exact (hc'.clm_apply continuous_const).add (continuous_const.mul (hc'.clm_apply continuous_const))

omit [μK.IsHaarMeasure] in
include hβs in
theorem Lk_zero (Z : M2 n) {x₀ : M2 n} (hx₀ : x₀ ∈ Inv n) :
    ∃ C : Set (GR n), IsCompact C ∧ ∀ u ∉ C, Lk m e μK β Z x₀ u = 0 := by
  obtain ⟨W, hW, C, hC, hz⟩ := kk_supp m e μK hβs x₀ hx₀
  refine ⟨C, hC, fun u hu => ?_⟩
  have h0 : (fun x' => kk m e μK β (x', mR u)) =ᶠ[𝓝 x₀] fun _ => 0 := by
    filter_upwards [hW] with x' hx' using hz x' hx' u hu
  simp [Lk, h0.fderiv_eq]

end

end PositivityTheory.Rg.Sw.HSt.Conv
end
end

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt.Conv

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.GRH PositivityTheory.Rg.Sw.HSt.MI

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {n m : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ}
  {U : Set ℂ} {d : Polynomial ℂ} {Ê : ℂ → G → ℂ} {t : ℝ}

private theorem taylor_cont_lemma {X : Type} [TopologicalSpace X] {U : Set ℂ} (hU : IsOpen U)
    (Φ : X → ℂ → ℂ) (hc : ContinuousOn (fun p : X × ℂ => Φ p.1 p.2) (univ ×ˢ U))
    (hd : ∀ x, DifferentiableOn ℂ (Φ x) U) :
    ContinuousOn (fun p : X × ℂ => deriv (Φ p.1) p.2) (univ ×ˢ U) := by
  rintro ⟨x₀, z₀⟩ ⟨-, hz₀⟩
  obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  have rpos : 0 < ε / 2 := by positivity
  have hsub : Metric.closedBall z₀ (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hε
  set S : Set (X × ℂ) := (univ : Set X) ×ˢ Metric.ball z₀ (ε / 2) with hSdef
  set K : X × ℂ → ℂ := fun p =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ w in C(z₀, ε / 2), ((w - p.2) ^ 2)⁻¹ • Φ p.1 w with hKdef
  have heq : ∀ p ∈ S, deriv (Φ p.1) p.2 = K p := fun p hp =>
    (Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hsub (hd p.1)
      hp.2).symm
  have hS : IsOpen S := isOpen_univ.prod Metric.isOpen_ball
  have hmem : (x₀, z₀) ∈ S := ⟨trivial, Metric.mem_ball_self rpos⟩
  have hK : ContinuousOn K S := by
    rw [continuousOn_iff_continuous_restrict]
    have hsph : ∀ θ : ℝ, circleMap z₀ (ε / 2) θ ∈ U := fun θ =>
      hsub (Metric.sphere_subset_closedBall (circleMap_mem_sphere z₀ rpos.le θ))
    have h3 : Continuous (fun q : S × ℝ => Φ q.1.1.1 (circleMap z₀ (ε / 2) q.2)) := by
      have := hc.comp_continuous (f := fun q : S × ℝ => (q.1.1.1, circleMap z₀ (ε / 2) q.2))
        (by fun_prop) (fun q => ⟨trivial, hsph q.2⟩)
      exact this
    have h2 : Continuous (fun q : S × ℝ => ((circleMap z₀ (ε / 2) q.2 - q.1.1.2) ^ 2)⁻¹) := by
      refine Continuous.fun_inv₀ (by fun_prop) ?_
      intro q h
      have hq : q.1.1.2 ∈ Metric.ball z₀ (ε / 2) := q.1.2.2
      have h0 : circleMap z₀ (ε / 2) q.2 = q.1.1.2 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)
      have hs := circleMap_mem_sphere z₀ rpos.le q.2
      rw [h0] at hs
      rw [Metric.mem_sphere] at hs
      rw [Metric.mem_ball] at hq
      linarith
    have h1 : Continuous (fun q : S × ℝ => deriv (circleMap z₀ (ε / 2)) q.2) := by
      simp only [deriv_circleMap]
      fun_prop
    have hI := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume)
      (f := fun (q : S) (θ : ℝ) => deriv (circleMap z₀ (ε / 2)) θ •
        ((circleMap z₀ (ε / 2) θ - q.1.2) ^ 2)⁻¹ • Φ q.1.1 (circleMap z₀ (ε / 2) θ))
      (h1.smul (h2.smul h3)) 0 (2 * Real.pi)
    have hI2 := (continuous_const (y := (2 * Real.pi * Complex.I : ℂ)⁻¹)).mul hI
    convert hI2 using 1
    ext x
    rfl
  have hat : ContinuousAt (fun p : X × ℂ => deriv (Φ p.1) p.2) (x₀, z₀) := by
    refine (hK.continuousAt (hS.mem_nhds hmem)).congr ?_
    filter_upwards [hS.mem_nhds hmem] with p hp using (heq p hp).symm
  exact hat.continuousWithinAt

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] in
theorem taylor_cont (hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) : ∀ r : ℕ,
    ContinuousOn (fun y : G × ℂ => iteratedDeriv r (Ê · y.1) y.2) (univ ×ˢ U) ∧
      ∀ x, DifferentiableOn ℂ (iteratedDeriv r (Ê · x)) U := by
  intro r
  induction r with
  | zero =>
    simp only [iteratedDeriv_zero]
    refine ⟨?_, fun x => hD.hol x⟩
    exact hD.cont.comp (continuous_swap.continuousOn) (fun y hy => ⟨hy.2, trivial⟩)
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    exact ⟨taylor_cont_lemma hD.hU _ ih.1 ih.2, fun x => (ih.2 x).deriv hD.hU⟩

end

theorem gset_inv {n : ℕ} {x : M2 n} (hx : InG x) : x ∈ Inv n := by
  have hx' : xᴴ * JJ n * x = JJ n := hx
  have hJ : JJ n * JJ n = -1 := by
    simp [JJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_neg]
  have hl : (-(JJ n * xᴴ * JJ n)) * x = 1 := by
    have e : JJ n * xᴴ * JJ n * x = JJ n * (xᴴ * JJ n * x) := by simp only [Matrix.mul_assoc]
    rw [neg_mul, e, hx', hJ, neg_neg]
  exact Matrix.det_ne_zero_of_left_inverse hl

theorem mR_inv {n : ℕ} (y : GR n) : (mR y)⁻¹ = mR y⁻¹ := by
  simp [mR, Matrix.coe_units_inv]

theorem smoothX : SmoothX := by
  intro m n e _ _ G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD g
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (GR n), ν.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨μK, hμK⟩ : ∃ μ : Measure (KR n), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨β, hβs, hβc, hβ0⟩ := exists_bump m e ν μK
  have hmR : Continuous (fun u : GR n => mR u) := Units.continuous_val.comp continuous_subtype_val
  have hcont : ∀ z ∈ U, Continuous (fun u : GR n => Ê z (g * ι u)) := by
    intro z hz
    have := hD.cont.comp_continuous (f := fun u : GR n => (z, g * ι u))
      (continuous_const.prodMk (continuous_const.mul hD.ιc)) (fun u => ⟨hz, trivial⟩)
    exact this
  have hcont' : ∀ r : ℕ, Continuous (fun u : GR n => iteratedDeriv r (Ê · (g * ι u)) s₀) := by
    intro r
    have := (taylor_cont hD r).1.comp_continuous (f := fun u : GR n => (g * ι u, s₀))
      ((continuous_const.mul hD.ιc).prodMk continuous_const) (fun u => ⟨trivial, hD.hs⟩)
    exact this
  have hmc : ∀ (a : ℂ → ℂ) (c z : ℂ) (r : ℕ),
      iteratedDeriv r (fun w => a w * c) z = iteratedDeriv r a z * c := by
    intro a c z r
    have hfun : (fun w => a w * c) = (fun w => c * a w) := funext fun w => mul_comm _ _
    rw [hfun, iteratedDeriv_const_mul_field, mul_comm]
  have hloc : ∀ (f₁ f₂ : ℂ → ℂ) (r : ℕ), (∀ z ∈ U, f₁ z = f₂ z) →
      iteratedDeriv r f₁ s₀ = iteratedDeriv r f₂ s₀ := by
    intro f₁ f₂ r hf
    have hev : f₁ =ᶠ[𝓝[univ] s₀] f₂ := by
      rw [nhdsWithin_univ]
      exact Filter.eventually_of_mem (hD.hU.mem_nhds hD.hs) hf
    have := Filter.EventuallyEq.iteratedDerivWithin_eq (n := r) hev (hf s₀ hD.hs)
    simpa only [iteratedDerivWithin_univ] using this
  have key : ∀ x ∈ MI.Inv n,
      DifferentiableOn ℂ (fun z => Psi m e ν μK β (fun u => Ê z (g * ι u)) x) U ∧
      ∀ r : ℕ, iteratedDeriv r (fun z => Psi m e ν μK β (fun u => Ê z (g * ι u)) x) s₀ =
        Psi m e ν μK β (fun u => iteratedDeriv r (Ê · (g * ι u)) s₀) x := by
    intro x hx
    obtain ⟨W, hW, C, hC, hCz⟩ := kk_supp m e μK hβc x hx
    have hk0 : Continuous (fun u : GR n => x⁻¹ * mR u) := continuous_const.mul hmR
    have hk : Continuous (fun u : GR n => kk m e μK β (x, mR u)) :=
      (tw_contDiff m e μK hβs).continuous.comp hk0
    have hI := holInt ν hC hD.hU (fun u z => Ê z (g * ι u) • kk m e μK β (x, mR u))
      (fun u hu z => by simp [hCz x (mem_of_mem_nhds hW) u hu])
      (by
        have h1 : ContinuousOn (fun p : GR n × ℂ => Ê p.2 (g * ι p.1)) (C ×ˢ U) :=
          hD.cont.comp ((continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp continuous_fst))).continuousOn)
            (fun p hp => ⟨hp.2, trivial⟩)
        exact h1.smul (hk.comp continuous_fst).continuousOn)
      (fun u _ => (hD.hol (g * ι u)).smul_const _)
    refine ⟨hI.1, fun r => ?_⟩
    simp only [Psi]
    rw [hI.2 s₀ hD.hs r]
    simp only [smul_eq_mul]
    congr 1
    funext u
    exact hmc _ _ _ _
  refine ⟨fun z x => Psi m e ν μK β (fun u => Ê z (g * ι u)) x, MI.Inv n,
    fun z => cw m e ν μK β (z - s₀), MI.isOpen_Inv, fun x hx => gset_inv hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((cw_differentiable ν μK hβs.continuous hβc).comp (differentiable_id.sub_const s₀)).differentiableOn
  · simpa using hβ0
  · intro z hz y
    simp only [Psi, kk, smul_eq_mul]
    rw [← integral_mul_left_eq_self _ y]
    have := conv_U hD ν μK hβs.continuous hβc z hz g y
    rw [← this]
    congr 1
    funext u
    rw [mR_inv, ← mR_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro z hz
    exact psi_contDiffOn m e ν μK hβs hβc _ (hcont z hz)
  · intro r
    exact (psi_contDiffOn m e ν μK hβs hβc _ (hcont' r)).congr (fun x hx => (key x hx).2 r)
  · intro x hx
    exact (key x hx).1
  · intro Q y
    have hx₀ : mR y ∈ MI.Inv n := gset_inv y.2
    obtain ⟨C, hC, hCz⟩ := Lk_zero m e μK hβc (lowQ Q) hx₀
    have hL := Lk_cont m e μK hβs (lowQ Q) hx₀
    have hI := holInt ν hC hD.hU (fun u z => Ê z (g * ι u) * Lk m e μK β (lowQ Q) (mR y) u)
      (fun u hu z => by simp [hCz u hu])
      (by
        have h1 : ContinuousOn (fun p : GR n × ℂ => Ê p.2 (g * ι p.1)) (C ×ˢ U) :=
          hD.cont.comp ((continuous_snd.prodMk (continuous_const.mul (hD.ιc.comp continuous_fst))).continuousOn)
            (fun p hp => ⟨hp.2, trivial⟩)
        exact h1.mul (hL.comp continuous_fst).continuousOn)
      (fun u _ => (hD.hol (g * ι u)).mul_const _)
    have hrc : ∀ z ∈ U, rC (lowQ Q) (Psi m e ν μK β (fun u => Ê z (g * ι u))) (mR y) =
        ∫ u, Ê z (g * ι u) * Lk m e μK β (lowQ Q) (mR y) u ∂ν := by
      intro z hz
      exact rC_psi m e ν μK hβs hβc (fun u => Ê z (g * ι u)) (hcont z hz) (lowQ Q) hx₀
    refine ⟨hI.1.congr hrc, fun r => ?_⟩
    rw [hloc _ _ r hrc, hI.2 s₀ hD.hs r]
    rw [MI.rC_congr MI.isOpen_Inv hx₀ (fun x hx => (key x hx).2 r) (lowQ Q),
      rC_psi m e ν μK hβs hβc _ (hcont' r) (lowQ Q) hx₀]
    congr 1
    funext u
    exact hmc _ _ _ _

end PositivityTheory.Rg.Sw.HSt.Conv
