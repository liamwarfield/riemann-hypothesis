module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.FlatInt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Heckify
section Lie

open MeasureTheory Set Filter Topology GroundTheory.Automorphic
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private theorem partial_iter {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] {Φ : P × Q → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous fun p : P × Q => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1 := by
  set L := ContinuousLinearMap.inl ℝ P Q
  have hH : Continuous fun q : P × Q =>
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q) :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  convert hH using 2 with p
  obtain ⟨Y, Z⟩ := p
  have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
    funext Y; simp [L]
  have hZ : ContDiff ℝ ∞ fun w : P × Q => Φ (w + (0, Z)) := hΦ.comp (contDiff_id.add contDiff_const)
  simp only
  rw [e, L.iteratedFDeriv_comp_right hZ Y (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right]
  simp [L]

private theorem chart_form {f : G → ℂ} (hf : h.IsSmoothFun f) (q₀ r₀ : G) :
    ContDiff ℝ ∞ fun p : 𝔤 × 𝔤 × 𝔤 => f (q₀ * h.expG p.2.1 * h.expG p.1 * (r₀ * h.expG p.2.2)) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × 𝔤 × 𝔤) 𝓘(ℝ, 𝔤) ∞
      fun p : 𝔤 × 𝔤 × 𝔤 => q₀ * h.expG p.2.1 * h.expG p.1 * (r₀ * h.expG p.2.2) :=
    ((contMDiff_const.mul (h.contMDiff_expG_comp (contDiff_fst.comp contDiff_snd))).mul
      (h.contMDiff_expG_comp contDiff_fst)).mul
      (contMDiff_const.mul (h.contMDiff_expG_comp (contDiff_snd.comp contDiff_snd)))
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff

private theorem smooth_slice {f : G → ℂ} (hf : h.IsSmoothFun f) (q r : G) :
    ContDiff ℝ ∞ fun Y : 𝔤 => f (q * h.expG Y * r) := by
  have := (chart_form h hf q r).comp (contDiff_id.prodMk (contDiff_const (c := ((0 : 𝔤), (0 : 𝔤)))))
  simpa [Function.comp_def, h.expG_zero] using this

private theorem two_param {f : G → ℂ} (hf : h.IsSmoothFun f) (k : ℕ) :
    Continuous fun p : 𝔤 × G × G => iteratedFDeriv ℝ k (fun Y => f (p.2.1 * h.expG Y * p.2.2)) p.1 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨Y₀, q₀, r₀⟩
  letI := h.chartedSpace
  have hq : q₀ ∈ (h.chart q₀).source := mem_chart_source 𝔤 q₀
  have hr : r₀ ∈ (h.chart r₀).source := mem_chart_source 𝔤 r₀
  have hc := partial_iter (chart_form h hf q₀ r₀) k
  have hev : (fun p : 𝔤 × G × G => iteratedFDeriv ℝ k (fun Y => f (p.2.1 * h.expG Y * p.2.2)) p.1) =ᶠ[𝓝 (Y₀, q₀, r₀)]
      fun p => iteratedFDeriv ℝ k (fun Y => f (q₀ * h.expG (h.chart q₀ p.2.1) * h.expG Y *
        (r₀ * h.expG (h.chart r₀ p.2.2)))) p.1 := by
    filter_upwards [prod_mem_nhds univ_mem (prod_mem_nhds ((h.chart q₀).open_source.mem_nhds hq)
      ((h.chart r₀).open_source.mem_nhds hr))] with p hp
    rw [show q₀ * h.expG (h.chart q₀ p.2.1) = p.2.1 from (h.chart q₀).left_inv hp.2.1,
      show r₀ * h.expG (h.chart r₀ p.2.2) = p.2.2 from (h.chart r₀).left_inv hp.2.2]
  refine ContinuousAt.congr ?_ hev.symm
  exact hc.continuousAt.comp (f := fun p : 𝔤 × G × G => (p.1, h.chart q₀ p.2.1, h.chart r₀ p.2.2))
    (continuousAt_fst.prodMk ((((h.chart q₀).continuousAt hq).comp (continuousAt_fst.comp continuousAt_snd)).prodMk
      (((h.chart r₀).continuousAt hr).comp (continuousAt_snd.comp continuousAt_snd))))

private theorem smooth_family {S : Type*} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ρ : Measure S) [IsFiniteMeasure ρ] {f : S → G → ℂ}
    (hf : ∀ s, h.IsSmoothFun (f s))
    (hl : ∀ s₀, ∃ β : S → G, Continuous β ∧ ∀ᶠ s in 𝓝 s₀, ∀ A, f s A = f s₀ (A * β s))
    {w : S → ℂ} (hw : Continuous w) {q r : S → G} (hq : Continuous q) (hr : Continuous r) :
    h.IsSmoothFun fun A => ∫ s, w s * f s (q s * A * r s) ∂ρ := by
  rw [h.isSmoothFun_iff]
  intro g
  let F : 𝔤 → S → ℂ := fun Y s => w s * f s (q s * (g * h.expG Y) * r s)
  refine contDiff_integral_of_iteratedFDeriv F (fun s => ?_) (fun k => ?_) (fun Y₀ => ?_)
  · have := smooth_slice h (hf s) (q s * g) (r s)
    exact contDiff_const.mul (by simpa only [mul_assoc] using this)
  · rw [continuous_iff_continuousAt]
    rintro ⟨Y₀, s₀⟩
    obtain ⟨β, hβ, hev₀⟩ := hl s₀
    have hc := two_param h (hf s₀) k
    have hev : (fun p : 𝔤 × S => ParamIntegral.iter F k p.1 p.2) =ᶠ[𝓝 (Y₀, s₀)] fun p => w p.2 •
        iteratedFDeriv ℝ k (fun Y => f s₀ (q p.2 * g * h.expG Y * (r p.2 * β p.2))) p.1 := by
      filter_upwards [prod_mem_nhds univ_mem hev₀] with p hp
      have hF : (fun Y => F Y p.2) = fun Y => w p.2 • f s₀ (q p.2 * g * h.expG Y * (r p.2 * β p.2)) := by
        funext Y
        simp only [F, smul_eq_mul]
        rw [hp.2]
        simp only [mul_assoc]
      rw [ParamIntegral.iter, hF]
      exact iteratedFDeriv_const_smul_apply' ((smooth_slice h (hf s₀) _ _).contDiffAt.of_le (by exact_mod_cast le_top))
    refine ContinuousAt.congr ?_ hev.symm
    refine Continuous.continuousAt ?_
    exact (hw.comp continuous_snd).smul (hc.comp (continuous_fst.prodMk
      (((hq.comp continuous_snd).mul continuous_const).prodMk ((hr.comp continuous_snd).mul (hβ.comp continuous_snd)))))
  · exact ⟨univ, univ_mem, univ, isCompact_univ, fun _ _ _ h => absurd trivial h⟩

end Lie

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section Adel

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem retract_self (z : G1 K n) : retractOne (z : AdelicGLn.AdelicGL K n) = z := by
  ext1
  rw [coe_retractOne, (mem_normOneGL_iff_detModule).1 z.2, map_one, inv_one, mul_one]

private theorem dec_near (x₀ : G1 K n) (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) :
    ∀ᶠ y in 𝓝 x₀, ∃ u ∈ U, y = archP K n (infPart K n ((y * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)) * finOne K n u * x₀ := by
  have hc : Continuous fun y : G1 K n => finPart K n ((y * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) :=
    continuous_finPart.comp (continuous_subtype_val.comp (continuous_id.mul continuous_const))
  have ho : IsOpen ((finOpenSubgroup U hU : OpenSubgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (finOpenSubgroup U hU).isOpen
  have h1 : (1 : AdelicGLn.FiniteAdelicGL K n) ∈ ((finOpenSubgroup U hU : OpenSubgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (finOpenSubgroup U hU).one_mem
  filter_upwards [(ho.preimage hc).mem_nhds (by simpa using h1)] with y hy
  obtain ⟨u, hu, e⟩ : ∃ u ∈ U, ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) =
      finPart K n ((y * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) := by
    obtain ⟨u, hu, e⟩ := hy
    exact ⟨u, hu, e⟩
  refine ⟨u, hu, ?_⟩
  set z : G1 K n := y * x₀⁻¹ with hz
  have h2 := retractOne_mul_finEmb (infEmb K n (infPart K n (z : AdelicGLn.AdelicGL K n))) u.2
  have e' : infEmb K n (infPart K n (z : AdelicGLn.AdelicGL K n)) * finEmb K n (u : AdelicGLn.FiniteAdelicGL K n) =
      (z : AdelicGLn.AdelicGL K n) := by
    rw [e, infEmb_infPart_mul_finEmb_finPart]
  rw [e', retract_self, retract_infEmb] at h2
  rw [show archP K n (infPart K n (z : AdelicGLn.AdelicGL K n)) * finOne K n u = z from h2.symm, hz]
  simp

private theorem slide {b : G1 K n → ℂ} {U : Subgroup (AdelicGLn.integralFiniteGL K n)}
    (hinv : ∀ u ∈ U, ∀ x, b (finOne K n u * x) = b x) (B β : archGroup K n) {u : AdelicGLn.integralFiniteGL K n}
    (hu : u ∈ U) (x : G1 K n) :
    b (archP K n B * (archP K n β * finOne K n u * x)) = b (archP K n (B * β) * x) := by
  rw [map_mul, ← hinv u hu (archP K n B * archP K n β * x)]
  congr 1
  rw [archimedeanProjection_mul_finiteEmbedding_comm β u, mul_assoc (finOne K n u), ← mul_assoc (archP K n B), archimedeanProjection_mul_finiteEmbedding_comm B u]
  simp only [mul_assoc]

private theorem smooth_avg {S : Type*} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ρ : Measure S) [IsFiniteMeasure ρ] {b : G1 K n → ℂ}
    (hb : UpperTheory.ConvolutionTheory.C.IsLeftSmooth b) {w : S → ℂ} (hw : Continuous w) {q r : S → archGroup K n} (hq : Continuous q)
    (hr : Continuous r) {y : S → G1 K n} (hy : Continuous y) :
    (isExpLieAlgebra K n).IsSmoothFun fun A : archGroup K n => ∫ s, w s * b (archP K n (q s * A * r s) * y s) ∂ρ := by
  obtain ⟨hsm, U, hU, hinv⟩ := hb
  refine smooth_family (isExpLieAlgebra K n) ρ (f := fun s A => b (archP K n A * y s)) (fun s => hsm (y s)) (fun s₀ => ?_) hw hq hr
  refine ⟨fun s => infPart K n ((y s * (y s₀)⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n),
    continuous_infPart.comp (continuous_subtype_val.comp (hy.mul continuous_const)), ?_⟩
  filter_upwards [hy.continuousAt.preimage_mem_nhds (dec_near (y s₀) U hU)] with s hs A
  obtain ⟨u, hu, e⟩ := hs
  exact (congrArg (fun t => b (archP K n A * t)) e).trans (slide hinv _ _ hu (y s₀))

end Adel

section Gen

private theorem integ {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {U : Set X} (hU : IsCompact U) {ν : Measure X} [IsFiniteMeasure ν] (hs : ∀ᵐ k ∂ν, k ∈ U) {F : X → ℂ}
    (hF : Continuous F) : Integrable F ν := by
  have h := hF.continuousOn.integrableOn_compact (μ := ν) hU
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at h

private theorem inv_preserved {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (ν : Measure G) [IsProbabilityMeasure ν] (U : Subgroup G) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) : ν.map (·⁻¹) = ν := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ measurable_inv]
  have hm : Measurable fun p : G × G => φ (p.1⁻¹ * p.2) := hφ.comp (measurable_fst.inv.mul measurable_snd)
  have a1 : ∫⁻ k, ∫⁻ x, φ (k⁻¹ * x) ∂ν ∂ν = ∫⁻ x, φ x ∂ν := by
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ x, φ x ∂ν)
      (hs.mono fun k hk => (hi _ (U.inv_mem hk)).lintegral_comp hφ)]
    simp
  have a2 : ∫⁻ x, ∫⁻ k, φ (k⁻¹ * x) ∂ν ∂ν = ∫⁻ k, φ k⁻¹ ∂ν := by
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ k, φ k⁻¹ ∂ν) (hs.mono fun x hx => ?_)]
    · simp
    · have := (hi _ hx).lintegral_comp (f := fun k => φ (k⁻¹ * x)) (hφ.comp (measurable_inv.mul_const x))
      rw [← this]
      simp
  rw [← a1, ← a2]
  exact (lintegral_lintegral_swap hm.aemeasurable).symm

end Gen

section Typ

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n)

private theorem inv_int (φ : G1 K n → ℂ) : ∫ k, φ k⁻¹ ∂D.ν = ∫ k, φ k ∂D.ν := by
  haveI := D.prob
  have h := integral_map_equiv (μ := D.ν) (MeasurableEquiv.inv (G1 K n)) φ
  rw [show Measure.map (MeasurableEquiv.inv (G1 K n)) D.ν = D.ν from inv_preserved D.ν D.U D.supp D.inv] at h
  exact h.symm

private theorem integ₂ {F : G1 K n × G1 K n → ℂ} (hF : Continuous F) : Integrable F (D.ν.prod D.ν) := by
  haveI := D.prob
  have hU := (typeFin D).1
  refine integ (hU.prod hU) ?_ hF
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae D.supp, Measure.quasiMeasurePreserving_snd.ae D.supp] with z a b
  exact ⟨a, b⟩

private theorem cont_int {Φ : G1 K n → G1 K n → ℂ} (hΦ : Continuous (Function.uncurry Φ)) :
    Continuous fun x => ∫ k, Φ x k ∂D.ν := by
  set_option synthInstance.maxHeartbeats 400000 in
    haveI := D.prob
    have := continuous_parametric_integral_of_continuous (μ := D.ν) hΦ (typeFin D).1
    rwa [Measure.restrict_eq_self_of_ae_mem D.supp] at this

private theorem sub_int (f : G1 K n → ℂ) :
    ∫ k, f k ∂D.ν = ∫ s : (D.U : Set (G1 K n)), f s ∂(Measure.comap Subtype.val D.ν) := by
  rw [integral_subtype_comap (typeFin D).1.isClosed.measurableSet, Measure.restrict_eq_self_of_ae_mem D.supp]

private theorem fin_comap : IsFiniteMeasure (Measure.comap (Subtype.val : ↥(D.U : Set (G1 K n)) → G1 K n) D.ν) := by
  haveI := D.prob
  refine ⟨?_⟩
  rw [(MeasurableEmbedding.subtype_coe (typeFin D).1.isClosed.measurableSet).comap_apply]
  exact measure_lt_top _ _

private theorem idem_int {Φ : G1 K n → ℂ} (hΦ : Continuous Φ) :
    ∫ h, D.e h * ∫ k, D.e k * Φ (h * k) ∂D.ν ∂D.ν = ∫ k, D.e k * Φ k ∂D.ν := by
  set_option synthInstance.maxHeartbeats 400000 in
    haveI := D.prob
    have h1 : ∀ᵐ h ∂D.ν, D.e h * ∫ k, D.e k * Φ (h * k) ∂D.ν = ∫ k, D.e h * (D.e (h⁻¹ * k) * Φ k) ∂D.ν :=
      D.supp.mono fun h hh => by
        have := (D.inv h hh).integral_comp (measurableEmbedding_mulLeft h) (fun k => D.e (h⁻¹ * k) * Φ k)
        rw [integral_const_mul, ← this]
        simp
    rw [integral_congr_ae h1, integral_integral_swap
      (integ₂ D (F := Function.uncurry fun h k => D.e h * (D.e (h⁻¹ * k) * Φ k))
        ((D.cont.comp continuous_fst).mul ((D.cont.comp (continuous_fst.inv.mul continuous_snd)).mul (hΦ.comp continuous_snd))))]
    refine integral_congr_ae (D.supp.mono fun k hk => ?_)
    simp only [← mul_assoc]
    rw [integral_mul_const, D.idem k hk]

end Typ

section Ops

open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem conj_arch (m : G1 K n) (A : archGroup K n) :
    m * archP K n A = archP K n (infPart K n (m : AdelicGLn.AdelicGL K n) * A * (infPart K n (m : AdelicGLn.AdelicGL K n))⁻¹) * m := by
  set κ := infPart K n (m : AdelicGLn.AdelicGL K n) with hκ
  have hA : ∀ a : archGroup K n, (archP K n a : AdelicGLn.AdelicGL K n) =
      infEmb K n a * (centralSection K n (detModule K n (infEmb K n a)))⁻¹ := fun a => by
    rw [← retract_infEmb, coe_retractOne]
  have hd : detModule K n (infEmb K n (κ * A * κ⁻¹)) = detModule K n (infEmb K n A) := by
    simp only [map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  have hm : (m : AdelicGLn.AdelicGL K n) = infEmb K n κ * finEmb K n (finPart K n (m : AdelicGLn.AdelicGL K n)) :=
    (infEmb_infPart_mul_finEmb_finPart _).symm
  have h1 : (m : AdelicGLn.AdelicGL K n) * infEmb K n A = infEmb K n (κ * A * κ⁻¹) * m := by
    conv_lhs => rw [hm, mul_assoc, ← infEmb_mul_finEmb_comm, ← mul_assoc, ← map_mul]
    conv_rhs => rw [hm, ← mul_assoc, ← map_mul, inv_mul_cancel_right]
  ext1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hA, hA, hd, ← mul_assoc, h1, mul_assoc, ← centralSection_inv_mul_comm, ← mul_assoc]

private theorem fin_conj {m : G1 K n} (hm : (m : AdelicGLn.AdelicGL K n) ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)))
    (u : AdelicGLn.integralFiniteGL K n) :
    ∃ φ : AdelicGLn.integralFiniteGL K n, m * finOne K n u = finOne K n (φ * u * φ⁻¹) * m := by
  obtain ⟨φ, hφ⟩ : ∃ φ : AdelicGLn.integralFiniteGL K n,
      (φ : AdelicGLn.FiniteAdelicGL K n) = finPart K n (m : AdelicGLn.AdelicGL K n) := ⟨⟨_, finPart_mem_integralFiniteGL hm⟩, rfl⟩
  obtain ⟨κ, e⟩ : ∃ κ, (m : AdelicGLn.AdelicGL K n) = infEmb K n κ * finEmb K n (φ : AdelicGLn.FiniteAdelicGL K n) :=
    ⟨_, by rw [hφ, infEmb_infPart_mul_finEmb_finPart]⟩
  refine ⟨φ, ?_⟩
  ext1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_finOne, coe_finOne, e]
  have hw := infEmb_mul_finEmb_comm κ ((φ * u * φ⁻¹ : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)
  rw [← mul_assoc (finEmb K n _), ← hw, mul_assoc, mul_assoc]
  congr 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  simp

variable (D : TypeDat K n)

private theorem exR (f : CC K n) : ∃ b : CC K n, (∀ g, b g = ∫ k, f (g * k⁻¹) * D.e k ∂D.ν) ∧
    (UpperTheory.ConvolutionTheory.C.IsLeftSmooth f → UpperTheory.ConvolutionTheory.C.IsLeftSmooth b) := by
  set_option synthInstance.maxHeartbeats 400000 in
    have hU := (typeFin D).1
    have hc : Continuous fun g => ∫ k, f (g * k⁻¹) * D.e k ∂D.ν :=
      cont_int D (Φ := fun g k => f (g * k⁻¹) * D.e k)
        ((f.continuous.comp (continuous_fst.mul continuous_snd.inv)).mul (D.cont.comp continuous_snd))
    have hz : ∀ g, g ∉ tsupport f * (D.U : Set (G1 K n)) → ∫ k, f (g * k⁻¹) * D.e k ∂D.ν = 0 := fun g hg => by
      refine integral_eq_zero_of_ae (D.supp.mono fun k hk => ?_)
      have : f (g * k⁻¹) = 0 := by
        by_contra h0
        exact hg ⟨_, subset_tsupport _ h0, k, hk, by simp⟩
      simp [this]
    refine ⟨⟨⟨_, hc⟩, HasCompactSupport.intro (f.hasCompactSupport.isCompact.mul hU) hz⟩, fun _ => rfl, fun hf => ⟨fun x => ?_, ?_⟩⟩
    · haveI : CompactSpace (D.U : Set (G1 K n)) := isCompact_iff_compactSpace.1 hU
      haveI := fin_comap D
      have := smooth_avg (Measure.comap Subtype.val D.ν) hf (w := fun s : (D.U : Set (G1 K n)) => D.e s)
        (D.cont.comp continuous_subtype_val) (q := fun _ => 1) (r := fun _ => 1) continuous_const continuous_const
        (y := fun s => x * (s : G1 K n)⁻¹) (continuous_const.mul continuous_subtype_val.inv)
      convert this using 2 with A
      change ∫ k, f (archP K n A * x * k⁻¹) * D.e k ∂D.ν = _
      rw [sub_int]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp [mul_comm (D.e _), mul_assoc]
    · obtain ⟨-, U, hUo, hinv⟩ := hf
      refine ⟨U, hUo, fun u hu x => ?_⟩
      change ∫ k, f (finOne K n u * x * k⁻¹) * D.e k ∂D.ν = ∫ k, f (x * k⁻¹) * D.e k ∂D.ν
      simp only [mul_assoc, hinv u hu]

private theorem exL (f : CC K n) : ∃ c : CC K n, (∀ g, c g = ∫ k, D.e k * f (k⁻¹ * g) ∂D.ν) ∧
    (UpperTheory.ConvolutionTheory.C.IsLeftSmooth f → UpperTheory.ConvolutionTheory.C.IsLeftSmooth c) := by
  set_option synthInstance.maxHeartbeats 400000 in
    have hU := (typeFin D).1
    have hc : Continuous fun g => ∫ k, D.e k * f (k⁻¹ * g) ∂D.ν :=
      cont_int D (Φ := fun g k => D.e k * f (k⁻¹ * g))
        ((D.cont.comp continuous_snd).mul (f.continuous.comp (continuous_snd.inv.mul continuous_fst)))
    have hz : ∀ g, g ∉ (D.U : Set (G1 K n)) * tsupport f → ∫ k, D.e k * f (k⁻¹ * g) ∂D.ν = 0 := fun g hg => by
      refine integral_eq_zero_of_ae (D.supp.mono fun k hk => ?_)
      have : f (k⁻¹ * g) = 0 := by
        by_contra h0
        exact hg ⟨k, hk, _, subset_tsupport _ h0, by simp⟩
      simp [this]
    refine ⟨⟨⟨_, hc⟩, HasCompactSupport.intro (hU.mul f.hasCompactSupport.isCompact) hz⟩, fun _ => rfl, fun hf => ⟨fun x => ?_, ?_⟩⟩
    · haveI : CompactSpace (D.U : Set (G1 K n)) := isCompact_iff_compactSpace.1 hU
      haveI := fin_comap D
      let κ : ↥(D.U : Set (G1 K n)) → archGroup K n := fun s => infPart K n (((s : G1 K n)⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)
      have hκ : Continuous κ := continuous_infPart.comp (continuous_subtype_val.comp continuous_subtype_val.inv)
      have := smooth_avg (Measure.comap Subtype.val D.ν) hf (w := fun s : (D.U : Set (G1 K n)) => D.e s)
        (D.cont.comp continuous_subtype_val) (q := κ) (r := fun s => (κ s)⁻¹) hκ hκ.inv (y := fun s => (s : G1 K n)⁻¹ * x)
        (continuous_subtype_val.inv.mul continuous_const)
      convert this using 2 with A
      change ∫ k, D.e k * f (k⁻¹ * (archP K n A * x)) ∂D.ν = _
      rw [sub_int]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [← mul_assoc]
      rw [conj_arch]
    · obtain ⟨-, U, hUo, hinv⟩ := hf
      obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo U.one_mem
      refine ⟨N.toOpenSubgroup.toSubgroup, N.toOpenSubgroup.isOpen, fun u hu x => ?_⟩
      change ∫ k, D.e k * f (k⁻¹ * (finOne K n u * x)) ∂D.ν = ∫ k, D.e k * f (k⁻¹ * x) ∂D.ν
      refine integral_congr_ae (D.supp.mono fun k hk => ?_)
      have hk' : k⁻¹ ∈ KG K n := SetLike.le_def.1 (typeFin D).2.1 (D.U.inv_mem hk)
      rw [KG, Subgroup.mem_comap] at hk'
      obtain ⟨φ, hφ⟩ := fin_conj (m := k⁻¹) hk' u
      beta_reduce
      rw [← mul_assoc, hφ, mul_assoc, hinv _ (hN (N.isNormal'.conj_mem u hu φ))]

end Ops

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.heckify :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (D : TypeDat K n) (a₀ : CC K n), CuspidalProjection.ccStar a₀ = a₀ → UpperTheory.ConvolutionTheory.C.IsLeftSmooth a₀ →
      ∃ a : CC K n, D.Hecke a ∧ CuspidalProjection.ccStar a = a ∧ UpperTheory.ConvolutionTheory.C.IsLeftSmooth a ∧
        ∀ g, a g = ∫ k, ∫ k', D.e k * a₀ (k⁻¹ * g * k'⁻¹) * D.e k' ∂D.ν ∂D.ν := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro K _ _ n μ _ D a₀ hst hsm
    haveI := D.prob
    obtain ⟨b, hb, hbs⟩ := exR D a₀
    obtain ⟨a, ha, has⟩ := exL D b
    have hform : ∀ g, a g = ∫ k, ∫ k', D.e k * a₀ (k⁻¹ * g * k'⁻¹) * D.e k' ∂D.ν ∂D.ν := fun g => by
      rw [ha]
      refine integral_congr_ae (Eventually.of_forall fun k => ?_)
      beta_reduce
      rw [hb, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun k' => ?_)
      simp only [mul_assoc]
    have hs₀ : ∀ y, conj (a₀ y) = a₀ y⁻¹ := fun y => by
      have := DFunLike.congr_fun hst y⁻¹
      rwa [CuspidalProjection.ccStar_apply, inv_inv] at this
    have hTc : Continuous fun p : G1 K n × G1 K n => a₀ (p.1 * p.2) := a₀.continuous.comp (continuous_fst.mul continuous_snd)
    have key : ∀ g, conj (a g⁻¹) = a g := fun g => by
      let T : G1 K n → G1 K n → ℂ := fun k k' => D.e k * a₀ (k⁻¹ * g * k'⁻¹) * D.e k'
      have hT : Continuous (Function.uncurry fun k k' => T k' k) :=
        ((D.cont.comp continuous_snd).mul (a₀.continuous.comp ((continuous_snd.inv.mul continuous_const).mul
          continuous_fst.inv))).mul (D.cont.comp continuous_fst)
      calc conj (a g⁻¹) = ∫ k, ∫ k', T k'⁻¹ k⁻¹ ∂D.ν ∂D.ν := by
            rw [hform, ← integral_conj]
            refine integral_congr_ae (D.supp.mono fun k hk => ?_)
            beta_reduce
            rw [← integral_conj]
            refine integral_congr_ae (D.supp.mono fun k' hk' => ?_)
            simp only [T, map_mul, ← D.star k hk, ← D.star k' hk', hs₀, mul_inv_rev, inv_inv, mul_assoc]
            ring
        _ = ∫ k, ∫ k', T k' k⁻¹ ∂D.ν ∂D.ν :=
            integral_congr_ae (Eventually.of_forall fun k => inv_int D fun k' => T k' k⁻¹)
        _ = ∫ k, ∫ k', T k' k ∂D.ν ∂D.ν := inv_int D fun k => ∫ k', T k' k ∂D.ν
        _ = ∫ k', ∫ k, T k' k ∂D.ν ∂D.ν := integral_integral_swap (integ₂ D hT)
        _ = a g := (hform g).symm
    have hL : ∀ g, ∫ k, D.e k * a (k⁻¹ * g) ∂D.ν = a g := fun g => by
      rw [ha g, ← idem_int D (Φ := fun k => b (k⁻¹ * g)) (b.continuous.comp (continuous_inv.mul continuous_const))]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      beta_reduce
      rw [ha]
      simp only [mul_inv_rev, mul_assoc]
    have hR : ∀ g, ∫ k, a (g * k⁻¹) * D.e k ∂D.ν = a g := fun g => by
      have h2 := inv_int D fun k => D.e k * a (k⁻¹ * g⁻¹)
      simp only [inv_inv] at h2
      rw [hL] at h2
      rw [← key g, ← h2, ← integral_conj]
      refine integral_congr_ae (D.supp.mono fun k hk => ?_)
      simp only [map_mul, D.star k hk, Complex.conj_conj]
      rw [show k * g⁻¹ = (g * k⁻¹)⁻¹ by simp, key, mul_comm]
    refine ⟨a, fun g => ⟨hL g, hR g⟩, ?_, has (hbs hsm), hform⟩
    ext g
    rw [CuspidalProjection.ccStar_apply, key]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BumpEx
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [FirstCountableTopology G]
  [LocallyCompactSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H]

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_cont (ν : Measure H) [ν.IsHaarMeasure] {ρ : H → ℝ} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) {Φ : G → H → ℝ} (hΦ : Continuous (Function.uncurry Φ)) :
    Continuous fun x => ∫ p, ρ p * Φ x p ∂ν := by
  have e : (fun x => ∫ p, ρ p * Φ x p ∂ν) = fun x => ∫ p in tsupport ρ, ρ p * Φ x p ∂ν := by
    funext x
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport hp, zero_mul]
  rw [e]
  exact continuous_parametric_integral_of_continuous ((hρ.comp continuous_snd).mul hΦ) hρc

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_split {O : Set G} (hO : O ∈ 𝓝 (1 : G)) :
    ∃ V ∈ 𝓝 (1 : G), ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, a * b * c⁻¹ ∈ O := by
  obtain ⟨V₁, h₁, e₁⟩ := exists_nhds_split_inv hO
  obtain ⟨V₂, h₂, e₂⟩ := exists_nhds_one_split h₁
  refine ⟨V₁ ∩ V₂, inter_mem h₁ h₂, fun a ha b hb c hc => ?_⟩
  rw [← div_eq_mul_inv]
  exact e₁ _ (e₂ a ha.2 b hb.2) c hc.1

private theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bump_step (ν : Measure H) [ν.IsHaarMeasure] (π : H →* G) (hπ : Continuous π)
    {ρ : H → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ p, 0 ≤ ρ p) {p₀ : H} (hρ1 : ρ p₀ ≠ 0)
    {h : G → ℝ} (hh : Continuous h) (hh0 : ∀ x, 0 ≤ h x) (hh1 : h 1 ≠ 0) (hs : ∀ x, h x⁻¹ = h x)
    {O : Set G} (hO : ∀ p q y, ρ p ≠ 0 → ρ q ≠ 0 → h y ≠ 0 → π p * y * (π q)⁻¹ ∈ O) :
    ∃ F a : G → ℝ, Continuous F ∧ (∀ x, a x = ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν) ∧
      (∀ u, (∀ x, h (u * x) = h x) → ∀ x, F (u * x) = F x) ∧
      Continuous a ∧ (∀ x, 0 ≤ a x) ∧ a 1 ≠ 0 ∧ (∀ x, a x⁻¹ = a x) ∧ ∀ x, a x ≠ 0 → x ∈ O := by
  set F : G → ℝ := fun y => ∫ q, ρ q * h (y * π q) ∂ν with hF
  have hFc : Continuous F := bump_cont ν hρ hρc (Φ := fun y q => h (y * π q))
    (hh.comp (continuous_fst.mul (hπ.comp continuous_snd)))
  have hF0 : ∀ y, 0 ≤ F y := fun y => integral_nonneg fun q => mul_nonneg (hρ0 q) (hh0 _)
  have hF1 : 0 < F (π p₀)⁻¹ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := p₀)
      (hρ.mul (hh.comp (continuous_const.mul hπ))) hρc.mul_right
      (fun q => mul_nonneg (hρ0 q) (hh0 _)) ?_
    simpa using ⟨hρ1, hh1⟩
  have ha : ∀ x, ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν = ∫ p, ∫ q, ρ p * (ρ q * h ((π p)⁻¹ * x * π q)) ∂ν ∂ν := by
    intro x
    simp only [hF, integral_const_mul]
  refine ⟨F, fun x => ∫ p, ρ p * F ((π p)⁻¹ * x) ∂ν, hFc, fun _ => rfl, fun u hu x => ?_, ?_,
    fun x => integral_nonneg fun q => mul_nonneg (hρ0 q) (hF0 _), ne_of_gt ?_, fun x => ?_, fun x hx => ?_⟩
  · simp only [hF, mul_assoc, hu]
  · exact bump_cont ν hρ hρc (Φ := fun x p => F ((π p)⁻¹ * x))
      (hFc.comp ((hπ.comp continuous_snd).inv.mul continuous_fst))
  · refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := p₀)
      (hρ.mul (hFc.comp (hπ.inv.mul continuous_const))) hρc.mul_right
      (fun q => mul_nonneg (hρ0 q) (hF0 _)) ?_
    simpa using ⟨hρ1, hF1.ne'⟩
  · beta_reduce
    rw [ha, ha, integral_integral_swap_of_hasCompactSupport]
    · refine integral_congr_ae (Eventually.of_forall fun p => integral_congr_ae (Eventually.of_forall fun q => ?_))
      beta_reduce
      rw [← hs ((π p)⁻¹ * x * π q)]
      simp only [mul_inv_rev, inv_inv, mul_assoc]
      ring
    · exact (hρ.comp continuous_fst).mul ((hρ.comp continuous_snd).mul (hh.comp
        (((hπ.comp continuous_fst).inv.mul continuous_const).mul (hπ.comp continuous_snd))))
    · refine HasCompactSupport.intro (hρc.isCompact.prod hρc.isCompact) fun z hz => ?_
      rw [mem_prod, not_and_or] at hz
      rcases hz with hz | hz <;> simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hz]
  · by_contra hxO
    refine hx ?_
    beta_reduce
    rw [ha]
    have : ∀ p q, ρ p * (ρ q * h ((π p)⁻¹ * x * π q)) = 0 := by
      intro p q
      by_contra h0
      refine hxO ?_
      have := hO p q _ (left_ne_zero_of_mul h0) (left_ne_zero_of_mul (right_ne_zero_of_mul h0))
        (right_ne_zero_of_mul (right_ne_zero_of_mul h0))
      simpa [mul_assoc] using this
    simp [this]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.bumpEx :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (O : Set (G1 K n)), O ∈ 𝓝 (1 : G1 K n) →
      ∃ a : CC K n, tsupport a ⊆ O ∧ (∀ g, 0 ≤ (a g).re ∧ (a g).im = 0) ∧ ∫ g, a g ∂μ = 1 ∧ CuspidalProjection.ccStar a = a ∧ UpperTheory.ConvolutionTheory.C.IsLeftSmooth a := by
  intro K _ _ n μ _ O hO
  letI : FirstCountableTopology (G1 K n) := by
    set_option synthInstance.maxHeartbeats 200000 in exact inferInstance
  letI : RegularSpace (G1 K n) := by
    set_option synthInstance.maxHeartbeats 200000 in exact inferInstance
  letI : R1Space (G1 K n) := by
    set_option synthInstance.maxHeartbeats 200000 in exact inferInstance
  obtain ⟨O', hO', hO'O, hO'c⟩ := local_compact_nhds hO
  obtain ⟨V₂, hV₂, e₂⟩ := bump_split hO'
  obtain ⟨V₁, hV₁, e₁⟩ := bump_split hV₂

  obtain ⟨f, hf1, hf0, -, hf⟩ := exists_continuous_one_zero_of_isCompact (isCompact_singleton (x := (1 : G1 K n)))
    (isOpen_interior (s := V₁)).isClosed_compl
    (disjoint_singleton_left.2 fun h => h (mem_interior_iff_mem_nhds.2 hV₁))
  have hf1' : f 1 = 1 := hf1 rfl
  have hfV : ∀ y, f y ≠ 0 → y ∈ V₁ := fun y hy => by
    by_contra hn
    exact hy (hf0 fun h => hn (interior_subset h))

  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((isOpen_interior (s := V₁)).preimage (continuous_finOne (K := K) (n := n)))
    (by rw [mem_preimage, map_one]; exact mem_interior_iff_mem_nhds.2 hV₁)
  set U : Subgroup (AdelicGLn.integralFiniteGL K n) := N.toOpenSubgroup.toSubgroup
  have hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) := N.toOpenSubgroup.isOpen
  have hUV : ∀ u : U, finOne K n u ∈ V₁ := fun u => interior_subset (hN u.2)
  have := compactSpace_of_isOpen U hU
  set_option synthInstance.maxHeartbeats 200000 in
   obtain ⟨F₁, h, -, hF₁, -, hc, h0, h1, hs, hV⟩ := bump_step (haarProb U) ((finOne K n).comp U.subtype)
    (continuous_finOne.comp continuous_subtype_val) (ρ := fun _ => 1) continuous_const
    (HasCompactSupport.of_compactSpace _) (fun _ => zero_le_one) (p₀ := 1) one_ne_zero (h := fun x => f x * f x⁻¹)
    (f.continuous.mul (f.continuous.comp continuous_inv)) (fun x => mul_nonneg (hf _).1 (hf _).1)
    (by simp [hf1']) (fun x => by simp [mul_comm]) (O := V₂)
    (fun p q y _ _ hy => e₁ _ (hUV p) _ (hfV _ (left_ne_zero_of_mul hy)) _ (hUV q))
  have hinv : ∀ u ∈ U, ∀ x, h (finOne K n u * x) = h x := by
    intro u hu x
    rw [hF₁, hF₁, ← integral_mul_left_eq_self _ (⟨u, hu⟩ : U)]
    simp [mul_assoc]

  let ν : Measure (archGroup K n) := Measure.haar
  obtain ⟨ρ, hρ0, hρt, hρ1, -, -, hρN, -⟩ := exists_archBump ν (N := archP K n ⁻¹' V₂)
    (continuous_archP.continuousAt.preimage_mem_nhds (by rwa [map_one]))
  have hρc : Continuous ρ := Complex.continuous_re.comp (hρt.continuous _)
  have hρs : HasCompactSupport ρ := hρt.2.comp_left (g := Complex.re) rfl
  obtain ⟨p₀, hp₀⟩ : ∃ p, ρ p ≠ 0 := by
    by_contra hn
    push Not at hn
    simp [hn] at hρ1
  obtain ⟨F, a, hFc, hF, hFi, ac, a0, a1, as, aO⟩ := bump_step ν (archP K n) continuous_archP hρc hρs hρ0 hp₀ hc h0 h1 hs
    (O := O') (fun p q y hp hq hy => e₂ _ (hρN p hp) _ (hV y hy) _ (hρN q hq))
  have acs : HasCompactSupport a := HasCompactSupport.intro hO'c fun x hx => by
    by_contra hn
    exact hx (aO x hn)
  have hI : 0 < ∫ x, a x ∂μ := ac.integral_pos_of_hasCompactSupport_nonneg_nonzero acs a0 a1
  set I := ∫ x, a x ∂μ with hIdef
  refine ⟨⟨⟨fun x => ((a x * I⁻¹ : ℝ) : ℂ), Complex.continuous_ofReal.comp (ac.mul continuous_const)⟩,
    HasCompactSupport.comp_left (g := Complex.ofReal) (f := fun x => a x * I⁻¹) acs.mul_right Complex.ofReal_zero⟩,
    ?_, fun g => ⟨?_, Complex.ofReal_im _⟩, ?_, ?_, fun x => ?_, U, hU, fun u hu x => ?_⟩
  · refine Subset.trans (closure_minimal (fun x hx => aO x fun h0 => ?_) hO'c.isClosed) hO'O
    have hx' : ((a x * I⁻¹ : ℝ) : ℂ) ≠ 0 := hx
    simp [h0] at hx'
  · exact mul_nonneg (a0 g) (inv_nonneg.2 hI.le)
  · change ∫ x, ((a x * I⁻¹ : ℝ) : ℂ) ∂μ = 1
    rw [integral_complex_ofReal, integral_mul_const, mul_inv_cancel₀ hI.ne', Complex.ofReal_one]
  · ext g
    change conj ((a g⁻¹ * I⁻¹ : ℝ) : ℂ) = ((a g * I⁻¹ : ℝ) : ℂ)
    rw [Complex.conj_ofReal, as]
  · change (isExpLieAlgebra K n).IsSmoothFun fun A => ((a (archP K n A * x) * I⁻¹ : ℝ) : ℂ)
    have hΨ : Continuous fun y : archGroup K n => ((F ((archP K n y)⁻¹ * x) * I⁻¹ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((hFc.comp (continuous_archP.inv.mul continuous_const)).mul continuous_const)
    have hsm := IsExpLieAlgebra.isSmoothFun_comp_inv ((isExpLieAlgebra K n).isSmoothFun_integral_mul ν hΨ hρt)
    convert hsm using 2 with A
    rw [hF, ← integral_mul_const, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
    push_cast
    ring
  · change ((a (finOne K n u * x) * I⁻¹ : ℝ) : ℂ) = ((a x * I⁻¹ : ℝ) : ℂ)
    rw [hF, hF]
    simp only [archimedeanProjection_apply, ← mul_assoc, archProj_inv_mul_finOne]
    simp only [mul_assoc, hFi _ (hinv u hu)]
end

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
open scoped Pointwise

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

private theorem res_zpow_neg_mul_res_zpow_neg_eq_inv_res (μ ν : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure ν] {U C : Set G} (hU : IsCompact U)
    (hC : IsCompact C) (hν : ∀ᵐ k ∂ν, k ∈ U) (F : G → G → ℂ) (hF : Continuous (Function.uncurry F))
    (h0 : ∀ k ∈ U, ∀ g, g ∉ C → F g k = 0) : ∫ g, ∫ k, F g k ∂ν ∂μ = ∫ k, ∫ g, F g k ∂μ ∂ν := by
  apply integral_integral_swap
  have h1 : IntegrableOn (Function.uncurry F) (C ×ˢ U) (μ.prod ν) :=
    hF.continuousOn.integrableOn_compact (hC.prod hU)
  refine h1.integrable_of_ae_notMem_eq_zero ?_
  have h2 : ∀ᵐ p ∂(μ.prod ν), p.2 ∈ U := (Measure.quasiMeasurePreserving_snd).ae hν
  filter_upwards [h2] with p hp hn
  exact h0 p.2 hp p.1 fun hc => hn ⟨hc, hp⟩

private theorem cont_avg (ν : Measure G) [IsProbabilityMeasure ν] {U : Set G} (hU : IsCompact U)
    (hν : ∀ᵐ k ∂ν, k ∈ U) (F : G → G → ℂ) (hF : Continuous (Function.uncurry F)) :
    Continuous fun g => ∫ k, F g k ∂ν := by
  have h := continuous_parametric_integral_of_continuous (μ := ν) hF hU
  rwa [Measure.restrict_eq_self_of_ae_mem hν] at h

private theorem convolution_hecke_identity (μ ν : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [IsProbabilityMeasure ν]
    {U : Set G} (hU : IsCompact U) (hν : ∀ᵐ k ∂ν, k ∈ U) (e a₀ a φ : G → ℂ) (he : Continuous e) (ha₀ : Continuous a₀)
    (hc : HasCompactSupport a₀) (hφ : Continuous φ) (hfix : ∀ g, ∫ k, e k * φ (g * k) ∂ν = φ g)
    (ha : ∀ g, a g = ∫ k, ∫ k', e k * a₀ (k⁻¹ * g * k'⁻¹) * e k' ∂ν ∂ν) (x : G) :
    ∫ g, a g * φ (x * g) ∂μ = ∫ k, e k * ∫ h, a₀ h * φ (x * k * h) ∂μ ∂ν := by
  set b : G → ℂ := fun g => ∫ k', a₀ (g * k'⁻¹) * e k' ∂ν with hb
  have hbc : Continuous b := cont_avg ν hU hν (fun g k' => a₀ (g * k'⁻¹) * e k') (by
    unfold Function.uncurry; fun_prop)
  have hz : ∀ k ∈ U, ∀ g, g ∉ tsupport a₀ * U → a₀ (g * k⁻¹) = 0 := by
    intro k hk g hg
    by_contra hne
    exact hg ⟨g * k⁻¹, subset_tsupport _ hne, k, hk, by simp⟩
  have hb0 : ∀ g, g ∉ tsupport a₀ * U → b g = 0 := by
    intro g hg
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hν] with k hk
    simp [hz k hk g hg]
  have hC : IsCompact (tsupport a₀ * U) := IsCompact.mul hc hU
  have h1 : ∀ y, ∫ g, b g * φ (y * g) ∂μ = ∫ h, a₀ h * φ (y * h) ∂μ := by
    intro y
    have s1 := res_zpow_neg_mul_res_zpow_neg_eq_inv_res μ ν hU hC hν (fun g k => a₀ (g * k⁻¹) * e k * φ (y * g))
      (by unfold Function.uncurry; fun_prop) (fun k hk g hg => by simp [hz k hk g hg])
    have s2 := res_zpow_neg_mul_res_zpow_neg_eq_inv_res μ ν hU hc hν (fun g k => a₀ g * (e k * φ (y * g * k)))
      (by unfold Function.uncurry; fun_prop) (fun k hk g hg => by simp [image_eq_zero_of_notMem_tsupport hg])
    simp only [integral_mul_const, integral_const_mul, hfix] at s1 s2
    rw [s1, s2]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    rw [← integral_mul_right_eq_self (fun g => a₀ (g * k⁻¹) * e k * φ (y * g)) k]
    simp [mul_assoc]
  have s3 := res_zpow_neg_mul_res_zpow_neg_eq_inv_res μ ν hU (hU.mul hC) hν (fun g k => e k * (b (k⁻¹ * g) * φ (x * g)))
    (by unfold Function.uncurry; fun_prop) (fun k hk g hg => by
      have : k⁻¹ * g ∉ tsupport a₀ * U := fun h => hg ⟨k, hk, _, h, by simp⟩
      simp [hb0 _ this])
  have h2 : ∀ g, a g * φ (x * g) = ∫ k, e k * (b (k⁻¹ * g) * φ (x * g)) ∂ν := by
    intro g
    rw [ha, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [hb, mul_assoc (e k), integral_const_mul]
  simp only [h2]
  rw [s3]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [integral_const_mul]
  rw [← h1, ← integral_mul_left_eq_self (fun g => b (k⁻¹ * g) * φ (x * g)) k]
  simp [mul_assoc]

private theorem convolution_estimate (μ ν : Measure G) [μ.IsHaarMeasure] [IsProbabilityMeasure ν]
    {U : Set G} (hU : IsCompact U) (hν : ∀ᵐ k ∂ν, k ∈ U) (e a₀ φ : G → ℂ) (he : Continuous e) (ha₀ : Continuous a₀)
    (hc : HasCompactSupport a₀) (hφ : Continuous φ) (hfix : ∀ g, ∫ k, e k * φ (g * k) ∂ν = φ g)
    (hpos : ∀ g, 0 ≤ (a₀ g).re ∧ (a₀ g).im = 0) (hone : ∫ g, a₀ g ∂μ = 1) (x : G) (ε : ℝ)
    (hε : ∀ k ∈ U, ∀ h ∈ tsupport a₀, ‖e k‖ * ‖φ (x * k * h) - φ (x * k)‖ ≤ ε) (hε0 : 0 ≤ ε) :
    ‖(∫ k, e k * ∫ h, a₀ h * φ (x * k * h) ∂μ ∂ν) - φ x‖ ≤ ε := by
  have hI : Continuous fun k => ∫ h, a₀ h * φ (x * k * h) ∂μ := by
    have h := continuous_parametric_integral_of_continuous (μ := μ) (f := fun k h => a₀ h * φ (x * k * h))
      (by unfold Function.uncurry; fun_prop) hc
    refine h.congr fun k => ?_
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => by simp [image_eq_zero_of_notMem_tsupport hh]
  have hint : ∀ F : G → ℂ, Continuous F → Integrable F ν := fun F hF => by
    have := hF.continuousOn.integrableOn_compact (μ := ν) hU
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hν] at this
  have hai : Integrable a₀ μ := ha₀.integrable_of_hasCompactSupport hc
  have hn : ∫ g, ‖a₀ g‖ ∂μ = 1 := by
    have : ∀ g, ‖a₀ g‖ = RCLike.re (a₀ g) := fun g => by
      have h2 : a₀ g = ((a₀ g).re : ℂ) := Complex.ext (by simp) (by simp [(hpos g).2])
      rw [RCLike.re_to_complex, h2, Complex.norm_real, Real.norm_of_nonneg (hpos g).1, Complex.ofReal_re]
    simp only [this]
    rw [integral_re hai, hone]
    simp
  rw [← hfix x, ← integral_sub (hint (fun k => e k * ∫ h, a₀ h * φ (x * k * h) ∂μ) (he.mul hI))
    (hint (fun k => e k * φ (x * k)) (by fun_prop))]
  have hb : ∀ᵐ k ∂ν, ‖e k * (∫ h, a₀ h * φ (x * k * h) ∂μ) - e k * φ (x * k)‖ ≤ ε := by
    filter_upwards [hν] with k hk
    have i1 : Integrable (fun h => a₀ h * φ (x * k * h)) μ :=
      Continuous.integrable_of_hasCompactSupport (by fun_prop) hc.mul_right
    have e1 : e k * (∫ h, a₀ h * φ (x * k * h) ∂μ) - e k * φ (x * k) =
        ∫ h, e k * (a₀ h * φ (x * k * h) - a₀ h * φ (x * k)) ∂μ := by
      rw [integral_const_mul, integral_sub i1 (hai.mul_const _), integral_mul_const, hone]
      ring
    rw [e1]
    refine (norm_integral_le_of_norm_le (hai.norm.mul_const ε) (Eventually.of_forall fun h => ?_)).trans ?_
    · by_cases hh : h ∈ tsupport a₀
      · rw [← mul_sub, norm_mul, norm_mul, mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hε k hk h hh) (norm_nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport hh]
    · rw [integral_mul_const, hn, one_mul]
  simpa using norm_integral_le_of_norm_le_const hb

omit [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem exists_uniform_neighborhood {d : ℕ} (S : Eu d →ₗ[ℂ] (G → ℂ)) (hinj : Function.Injective S) (hS : ∀ v, Continuous (S v))
    (H e : G → ℂ) (hH : Continuous H) (hH0 : ∀ g, H g ≠ 0) (he : Continuous e) {U : Set G} (hU : IsCompact U) :
    ∃ O ∈ 𝓝 (1 : G), ∀ v ∈ Metric.sphere (0 : Eu d) 1, ∃ x, ∃ ε, 0 ≤ ε ∧ ε < ‖H x * S v x‖ ∧ ∀ k ∈ U, ∀ h ∈ O,
      ‖e k‖ * ‖H (x * k * h) * S v (x * k * h) - H (x * k) * S v (x * k)‖ ≤ ε := by
  have hj : Continuous fun p : Eu d × G => S p.1 p.2 := by
    have : (fun p : Eu d × G => S p.1 p.2) = fun p => ∑ i, p.1 i * S (EuclideanSpace.single i 1) p.2 := by
      funext p
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr p.1]
      simp
    rw [this]
    refine continuous_finsetSum _ fun i _ => Continuous.mul (by fun_prop) ((hS _).comp continuous_snd)
  refine (isCompact_sphere (0 : Eu d) 1).induction_on (p := fun s => ∃ O ∈ 𝓝 (1 : G), ∀ v ∈ s, ∃ x, ∃ ε, 0 ≤ ε ∧
    ε < ‖H x * S v x‖ ∧ ∀ k ∈ U, ∀ h ∈ O,
      ‖e k‖ * ‖H (x * k * h) * S v (x * k * h) - H (x * k) * S v (x * k)‖ ≤ ε) ⟨univ, univ_mem, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨O, hO, h⟩
    exact ⟨O, hO, fun v hv => h v (hst hv)⟩
  · rintro s t ⟨O, hO, h⟩ ⟨O', hO', h'⟩
    refine ⟨O ∩ O', inter_mem hO hO', ?_⟩
    rintro v (hv | hv)
    · obtain ⟨x, ε, h1, h2, h3⟩ := h v hv
      exact ⟨x, ε, h1, h2, fun k hk g hg => h3 k hk g hg.1⟩
    · obtain ⟨x, ε, h1, h2, h3⟩ := h' v hv
      exact ⟨x, ε, h1, h2, fun k hk g hg => h3 k hk g hg.2⟩
  · intro v₀ hv₀
    have hne : S v₀ ≠ 0 := by
      intro h
      have : v₀ = 0 := hinj (by rw [h, map_zero])
      simp [this] at hv₀
    obtain ⟨x, hx⟩ := Function.ne_iff.1 hne
    have hp : 0 < ‖H x * S v₀ x‖ := norm_pos_iff.2 (mul_ne_zero (hH0 x) hx)
    set ε := ‖H x * S v₀ x‖ / 2 with hε
    have c1 : Continuous fun z : (Eu d × G) × G =>
        ‖e z.2‖ * ‖H (x * z.2 * z.1.2) * S z.1.1 (x * z.2 * z.1.2) - H (x * z.2) * S z.1.1 (x * z.2)‖ := by
      have j1 : Continuous fun z : (Eu d × G) × G => S z.1.1 (x * z.2 * z.1.2) :=
        hj.comp (f := fun z : (Eu d × G) × G => (z.1.1, x * z.2 * z.1.2)) (by fun_prop)
      have j2 : Continuous fun z : (Eu d × G) × G => S z.1.1 (x * z.2) :=
        hj.comp (f := fun z : (Eu d × G) × G => (z.1.1, x * z.2)) (by fun_prop)
      exact (he.comp continuous_snd).norm.mul
        (((hH.comp (by fun_prop)).mul j1).sub ((hH.comp (by fun_prop)).mul j2)).norm
    have e1 : ∀ᶠ p : Eu d × G in 𝓝 (v₀, 1), ∀ k ∈ U,
        ‖e k‖ * ‖H (x * k * p.2) * S p.1 (x * k * p.2) - H (x * k) * S p.1 (x * k)‖ < ε := by
      refine hU.eventually_forall_of_forall_eventually fun k _ => ?_
      exact c1.continuousAt.eventually_lt continuousAt_const (by
        simp only [mul_one, sub_self, norm_zero, mul_zero]; exact half_pos hp)
    have c2 : Continuous fun v : Eu d => ‖H x * S v x‖ :=
      (continuous_const.mul (hj.comp (f := fun v : Eu d => (v, x)) (by fun_prop))).norm
    have e2 : ∀ᶠ v in 𝓝 v₀, ε < ‖H x * S v x‖ :=
      continuousAt_const.eventually_lt c2.continuousAt (half_lt_self hp)
    rw [nhds_prod_eq, eventually_prod_iff] at e1
    obtain ⟨pa, hpa, pb, hpb, h⟩ := e1
    refine ⟨{v | pa v ∧ ε < ‖H x * S v x‖}, mem_nhdsWithin_of_mem_nhds (hpa.and e2), {g | pb g}, hpb, ?_⟩
    intro v hv
    exact ⟨x, ε, (half_pos hp).le, hv.2, fun k hk g hg => (h hv.1 hg k hk).le⟩

end SlopeTestRemainingChoices

private theorem exists_positive_period_line {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure]
    {μ₂ : Measure (G1 K 2)} {τ₁ τ₂ : Submodule ℂ (L2 μ₂)} {D : TypeDat K (2 + 2)} {d : ℕ} (A : Line μ τ₁ τ₂ D d) :
    ∃ O ∈ 𝓝 (1 : G1 K (2 + 2)), ∀ a₀ a : CC K (2 + 2), tsupport a₀ ⊆ O → (∀ g, 0 ≤ (a₀ g).re ∧ (a₀ g).im = 0) →
      ∫ g, a₀ g ∂μ = 1 → (∀ g, a g = ∫ k, ∫ k', D.e k * a₀ (k⁻¹ * g * k'⁻¹) * D.e k' ∂D.ν ∂D.ν) →
      ∀ T : Eu d →L[ℂ] Eu d, (∀ v x, ∫ g, a g * flat 0 (A.sec v) (x * g) ∂μ = flat 0 (A.sec (T v)) x) → IsUnit T := by
  obtain ⟨hU, hle, -⟩ := typeFin D
  obtain ⟨-, hk, -, hc, -⟩ := hpSpec (K := K)
  have hsec : ∀ v, IsSec τ₁ τ₂ (A.sec v) ∧ D.Fix (A.sec v) := fun v => (A.onto _).1 ⟨v, rfl⟩
  have hH : Continuous fun x : G1 K (2 + 2) => Complex.exp ((0 + 2) * (HP 2 2 x : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hc))
  obtain ⟨O, hO, h⟩ := exists_uniform_neighborhood A.sec A.inj (fun v => (hsec v).1.cont) _ D.e hH (fun _ => Complex.exp_ne_zero _) D.cont hU
  refine ⟨O, hO, fun a₀ a hs hpos hone ha T hT => ?_⟩
  haveI := D.prob
  haveI := isMulRightInvariant_normOneGL μ
  have key : ∀ v ∈ Metric.sphere (0 : Eu d) 1, T v ≠ 0 := by
    intro v hv h0
    obtain ⟨x, ε, h1, h2, h3⟩ := h v hv
    have hφ : Continuous (flat 0 (A.sec v)) := hH.mul (hsec v).1.cont
    have hfix : ∀ g, ∫ k, D.e k * flat 0 (A.sec v) (g * k) ∂D.ν = flat 0 (A.sec v) g := by
      intro g
      unfold flat
      rw [← (hsec v).2 g, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [D.supp] with k hk'
      rw [show HP 2 2 (g * k) = HP 2 2 g from (hk k (hle hk')).2 g]
      ring
    have e1 := convolution_hecke_identity μ D.ν hU D.supp D.e a₀ a _ D.cont a₀.continuous a₀.hasCompactSupport hφ hfix ha x
    have e2 := convolution_estimate μ D.ν hU D.supp D.e a₀ _ D.cont a₀.continuous a₀.hasCompactSupport hφ hfix hpos hone x ε
      (fun k hk g hg => h3 k hk g (hs hg)) h1
    rw [← e1, hT, h0, map_zero] at e2
    have e3 : flat 0 (0 : G1 K (2 + 2) → ℂ) x = 0 := by simp [flat]
    rw [e3, zero_sub, norm_neg] at e2
    exact absurd e2 (not_le.2 h2)
  have hinj : Function.Injective T := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hne
    refine key (((‖v‖⁻¹ : ℝ) : ℂ) • v) ?_ (by rw [map_smul, hv, smul_zero])
    simp [norm_smul, hn]
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (T : Eu d →ₗ[ℂ] Eu d))).1 hinj⟩

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.unitB :
    UnitB := by
  intro K _ _ _ μ _ μ₂ _ τ₁ τ₂ hP D d d' A A'
  obtain ⟨O, hO, h⟩ := exists_positive_period_line μ A
  obtain ⟨O', hO', h'⟩ := exists_positive_period_line μ A'
  obtain ⟨a₀, hs, hpos, hone, hst, hsm⟩ := bumpEx μ (O ∩ O') (inter_mem hO hO')
  obtain ⟨a, hH, hst', hsm', ha⟩ := heckify μ D a₀ hst hsm
  obtain ⟨β, hβ⟩ := convR K μ μ₂ τ₁ τ₂ hP D d d' A A' a hH
  obtain ⟨β', hβ'⟩ := convR K μ μ₂ τ₂ τ₁ ⟨hP.irr₂, hP.irr₁, hP.orth.symm⟩ D d' d A' A a hH
  exact ⟨a, β, β', hsm', hH, hst', hβ, hβ',
    h a₀ a (hs.trans inter_subset_left) hpos hone ha _ (hβ.2.2 0),
    h' a₀ a (hs.trans inter_subset_right) hpos hone ha _ (hβ'.2.2 0)⟩
