module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.HeckeP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.CompLine
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.EqZeroOfSlices
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Imports

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.IntegrableAeCpt
section General

open MeasureTheory GroundTheory.Automorphic
open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private theorem integrable_ae_cpt {X H : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [NormedAddCommGroup H] {m : Measure X} [IsFiniteMeasureOnCompacts m] {S : Set X} (hS : IsCompact S) {F : X → H}
    (hF : Continuous F) (h0 : ∀ᵐ x ∂m, x ∉ S → F x = 0) : Integrable F m :=
  (hF.continuousOn.integrableOn_compact hS).integrable_of_ae_notMem_eq_zero h0

variable {ν : Measure G} [IsFiniteMeasure ν] {U : Subgroup G} {e : G → ℂ}

private theorem swap_cpt (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) {F : G → G → ℂ}
    (hF : Continuous F.uncurry) : ∫ k, ∫ h, F k h ∂ν ∂ν = ∫ h, ∫ k, F k h ∂ν ∂ν := by
  refine integral_integral_swap (integrable_ae_cpt (hU.prod hU) hF ?_)
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hs,
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae hs] with q h1 h2 h
  exact absurd ⟨h1, h2⟩ h

private theorem idem_int (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) (he : Continuous e)
    (hid : ∀ k ∈ U, ∫ h, e h * e (h⁻¹ * k) ∂ν = e k) {φ : G → ℂ} (hφ : Continuous φ) :
    ∫ k, e k * ∫ h, e h * φ (k * h) ∂ν ∂ν = ∫ h, e h * φ h ∂ν := by
  have h1 : ∫ k, e k * ∫ h, e h * φ (k * h) ∂ν ∂ν = ∫ k, ∫ h, e k * e (k⁻¹ * h) * φ h ∂ν ∂ν := by
    refine integral_congr_ae (hs.mono fun k hk => ?_)
    have := (hi k hk).integral_comp (MeasurableEquiv.mulLeft k).measurableEmbedding (fun h => e (k⁻¹ * h) * φ h)
    simp only [inv_mul_cancel_left] at this
    simp only [this, ← integral_const_mul, mul_assoc]
  rw [h1, swap_cpt hU hs (by fun_prop)]
  refine integral_congr_ae (hs.mono fun k hk => ?_)
  simp only [integral_mul_const, hid k hk]

private theorem cont_int (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) {F : G → G → ℂ}
    (hF : Continuous F.uncurry) : Continuous fun g => ∫ k, F g k ∂ν := by
  have := continuous_parametric_integral_of_continuous (μ := ν) hF hU
  rwa [Measure.restrict_eq_self_of_ae_mem hs] at this

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H)
  (μ : Measure G) [μ.IsHaarMeasure]

private theorem int_orbit (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) (he : Continuous e) (v : H) :
    Integrable (fun k => e k • π k v) ν :=
  integrable_ae_cpt hU (he.smul (π.continuous_orbit v)) (hs.mono fun _ h h' => absurd h h')

private theorem op_swap (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) {F : G → G → ℂ}
    (hF : Continuous F.uncurry) {S : Set G} (hS : IsCompact S) (h0 : ∀ x ∉ S, ∀ k ∈ U, F x k = 0) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, (∀ x, f x = ∫ k, F x k ∂ν) ∧
      ∀ v, π.integrated μ (UnitaryRep.ccToL1 μ f) v = ∫ k, ∫ x, F x k • π x v ∂μ ∂ν := by
  refine ⟨⟨⟨fun x => ∫ k, F x k ∂ν, cont_int hU hs hF⟩, HasCompactSupport.intro hS fun x hx => ?_⟩, fun _ => rfl,
    fun v => ?_⟩
  · exact integral_eq_zero_of_ae (hs.mono fun k hk => h0 x hx k hk)
  · rw [UnitaryRep.integrated_ccToL1_apply]
    change ∫ x, (∫ k, F x k ∂ν) • π x v ∂μ = _
    simp only [← integral_smul_const]
    refine integral_integral_swap (integrable_ae_cpt (hS.prod hU)
      (hF.smul ((π.continuous_orbit v).comp continuous_fst)) ?_)
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hs] with q h2 h
    have : F q.1 q.2 = 0 := h0 _ (fun h1 => h ⟨h1, h2⟩) _ h2
    change F q.1 q.2 • π q.1 v = 0
    rw [this, zero_smul]

private theorem avg_left (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) (he : Continuous e)
    (a : CompactlySupportedContinuousMap G ℂ) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, (∀ x, f x = ∫ k, e k * a (k⁻¹ * x) ∂ν) ∧
      ∀ v, π.integrated μ (UnitaryRep.ccToL1 μ f) v =
        ∫ k, e k • π k (π.integrated μ (UnitaryRep.ccToL1 μ a) v) ∂ν := by
  have ha := a.continuous
  obtain ⟨f, h1, h2⟩ := op_swap π μ hU hs (F := fun x k => e k * a (k⁻¹ * x)) (by fun_prop)
    (hU.mul a.hasCompactSupport.isCompact) fun x hx k hk => by
      by_contra hne
      exact hx ⟨k, hk, k⁻¹ * x, subset_tsupport _ (mul_ne_zero_iff.1 hne).2, mul_inv_cancel_left _ _⟩
  refine ⟨f, h1, fun v => (h2 v).trans ?_⟩
  congr 1
  funext k
  have hi : Integrable (fun z => a z • π z v) μ :=
    (a.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport a.hasCompactSupport.smul_right
  rw [UnitaryRep.integrated_ccToL1_apply, ← ContinuousLinearMap.integral_comp_comm _ hi, ← integral_smul,
    ← integral_mul_left_eq_self _ k]
  simp only [inv_mul_cancel_left, UnitaryRep.map_mul_apply, map_smul, smul_smul]

private theorem avg_right [μ.IsMulRightInvariant] (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) (he : Continuous e)
    (a : CompactlySupportedContinuousMap G ℂ) :
    ∃ f : CompactlySupportedContinuousMap G ℂ, (∀ x, f x = ∫ k, a (x * k⁻¹) * e k ∂ν) ∧
      ∀ v, π.integrated μ (UnitaryRep.ccToL1 μ f) v =
        π.integrated μ (UnitaryRep.ccToL1 μ a) (∫ k, e k • π k v ∂ν) := by
  have ha := a.continuous
  obtain ⟨f, h1, h2⟩ := op_swap π μ hU hs (F := fun x k => a (x * k⁻¹) * e k) (by fun_prop)
    (a.hasCompactSupport.isCompact.mul hU) fun x hx k hk => by
      by_contra hne
      exact hx ⟨x * k⁻¹, subset_tsupport _ (mul_ne_zero_iff.1 hne).1, k, hk, inv_mul_cancel_right _ _⟩
  refine ⟨f, h1, fun v => (h2 v).trans ?_⟩
  rw [← ContinuousLinearMap.integral_comp_comm _ (int_orbit π hU hs he v)]
  congr 1
  funext k
  rw [map_smul, UnitaryRep.integrated_ccToL1_apply, ← integral_smul, ← integral_mul_right_eq_self _ k]
  simp only [mul_inv_cancel_right, UnitaryRep.map_mul_apply, smul_smul, mul_comm]

private theorem proj_ex (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U) (he : Continuous e) :
    ∃ E : H →L[ℂ] H, ∀ v, E v = ∫ k, e k • π k v ∂ν := by
  have hi : Integrable e ν := integrable_ae_cpt hU he (hs.mono fun _ h h' => absurd h h')
  refine ⟨π.integrated ν (hi.toL1 e), fun v => ?_⟩
  rw [UnitaryRep.integrated_apply]
  exact integral_congr_ae (hi.coeFn_toL1.mono fun k hk => by simp only [hk])

private theorem two_sided [μ.IsMulRightInvariant] (hU : IsCompact (U : Set G)) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) (he : Continuous e)
    (hid : ∀ k ∈ U, ∫ h, e h * e (h⁻¹ * k) ∂ν = e k) :
    ∃ E : H →L[ℂ] H,
      (∀ a : CompactlySupportedContinuousMap G ℂ,
        (∀ g, ∫ k, e k * a (k⁻¹ * g) ∂ν = a g ∧ ∫ k, a (g * k⁻¹) * e k ∂ν = a g) →
        E ∘L π.integrated μ (UnitaryRep.ccToL1 μ a) = π.integrated μ (UnitaryRep.ccToL1 μ a) ∧
        π.integrated μ (UnitaryRep.ccToL1 μ a) ∘L E = π.integrated μ (UnitaryRep.ccToL1 μ a)) ∧
      ∀ a : CompactlySupportedContinuousMap G ℂ, ∃ f : CompactlySupportedContinuousMap G ℂ,
        (∀ g, ∫ k, e k * f (k⁻¹ * g) ∂ν = f g ∧ ∫ k, f (g * k⁻¹) * e k ∂ν = f g) ∧
        π.integrated μ (UnitaryRep.ccToL1 μ f) = E ∘L π.integrated μ (UnitaryRep.ccToL1 μ a) ∘L E := by
  obtain ⟨E, hE⟩ := proj_ex π hU hs he
  refine ⟨E, fun a h => ?_, fun a => ?_⟩
  · obtain ⟨f, h1, h2⟩ := avg_left π μ hU hs he a
    obtain ⟨f', h1', h2'⟩ := avg_right π μ hU hs he a
    obtain rfl : f = a := CompactlySupportedContinuousMap.ext fun x => (h1 x).trans (h x).1
    obtain rfl : f' = f := CompactlySupportedContinuousMap.ext fun x => (h1' x).trans (h x).2
    exact ⟨ContinuousLinearMap.ext fun v => (hE _).trans (h2 v).symm,
      ContinuousLinearMap.ext fun v => by rw [ContinuousLinearMap.comp_apply, hE, ← h2']⟩
  · obtain ⟨b, h1, h2⟩ := avg_right π μ hU hs he a
    obtain ⟨f, h3, h4⟩ := avg_left π μ hU hs he b
    have ha := a.continuous
    have hb := b.continuous
    have hbr : ∀ g, ∫ k, b (g * k⁻¹) * e k ∂ν = b g := fun g => by
      have := idem_int hU hs hi he hid (φ := fun h => a (g * h⁻¹)) (by fun_prop)
      simp only [← integral_const_mul] at this
      rw [swap_cpt hU hs (by fun_prop)] at this
      simp only [h1, ← integral_mul_const]
      refine Eq.trans ?_ (this.trans ?_)
      · simp only [mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
      · simp only [mul_comm]
    refine ⟨f, fun g => ⟨?_, ?_⟩, ContinuousLinearMap.ext fun v => ?_⟩
    · have := idem_int hU hs hi he hid (φ := fun h => b (h⁻¹ * g)) (by fun_prop)
      simp only [h3]
      simpa only [mul_inv_rev, mul_assoc] using this
    · simp only [h3, ← integral_mul_const]
      rw [swap_cpt hU hs (by fun_prop)]
      congr 1
      funext k
      rw [← hbr, ← integral_const_mul]
      simp only [mul_assoc]
    · rw [h4, h2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hE, hE]

end General

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section Amp

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]

private theorem star_test (β : TI K n) (hβ : SmoothT β) :
    ∃ β' : TI K n, SmoothT β' ∧ ∀ x, β x = starRingEnd ℂ (β' x⁻¹) := by
  have hs : (isExpLieAlgebra K n).IsSmoothFun fun g => β g⁻¹ :=
    (UpperTheory.ConvolutionTheory.Tf.invSmooth K n (fun g => β g) ((isExpLieAlgebra K n).mem_smoothFuns.2 hβ)).1
  have hs' : (isExpLieAlgebra K n).IsSmoothFun fun g => starRingEnd ℂ (β g⁻¹) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact Complex.conjCLE.contDiff.comp_contMDiff hs
  have hc : HasCompactSupport fun g : archGroup K n => starRingEnd ℂ (β g⁻¹) :=
    (β.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := starRingEnd ℂ) (map_zero _)
  refine ⟨⟨⟨_, Complex.continuous_conj.comp (β.continuous.comp continuous_inv)⟩, hc⟩, hs', fun x => ?_⟩
  change β x = starRingEnd ℂ (starRingEnd ℂ (β x⁻¹⁻¹))
  rw [Complex.conj_conj, inv_inv]

private theorem sep_left (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (T : LL μ →L[ℂ] LL μ)
    (h : ∀ β : TI K n, SmoothT β → Oinf μ ν β ∘L T = 0) : T = 0 :=
  ContinuousLinearMap.ext fun v => UpperTheory.ConvolutionTheory.Dp.diracSep K n μ ν (T v) fun β hβ => DFunLike.congr_fun (h β hβ) v

private theorem sep_right (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n))
    [m.IsHaarMeasure] (T : LL μ →L[ℂ] LL μ) (h : ∀ β : TI K n, SmoothT β → T ∘L Oinf μ ν β = 0) : T = 0 := by
  have : ContinuousLinearMap.adjoint T = 0 := sep_left ν _ fun β hβ => by
    obtain ⟨β', h1, h2⟩ := star_test β hβ
    rw [← (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.2.1 β' β h2, ← ContinuousLinearMap.adjoint_comp, h β' h1, map_zero]
  simpa using congrArg ContinuousLinearMap.adjoint this

private theorem amp_move [_root_.NumberField.IsTotallyComplex K] (𝔞 : Amp μ) (m : Measure (AdelicGLn.FiniteAdelicGL K n))
    [m.IsHaarMeasure] (y : Ix K n) (β : TI K n) (hβ : SmoothT β) :
    𝔞.Z y * Oinf μ 𝔞.ν β = 𝔞.A * Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) ∧
      Oinf μ 𝔞.ν β * 𝔞.Z y = Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) * 𝔞.A := by
  obtain ⟨hc, -, -, -, -, -, -, -, hr⟩ := UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m
  have hP : ∀ γ, prj (fixF μ 𝔞.U) * Oinf μ 𝔞.ν γ = Oinf μ 𝔞.ν γ * prj (fixF μ 𝔞.U) := fun γ =>
    ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ 𝔞.U).2.2.2.2.2.2.2.2 _ fun u _ => hr γ u).symm.eq
  have hz := (UpperTheory.ConvolutionTheory.Dp.capZc K n y.1).1 y.2
  have h1 : Oinf μ 𝔞.ν (lact (zc y.1 y.2) 𝔞.a₀) * Oinf μ 𝔞.ν β = Oinf μ 𝔞.ν 𝔞.a₀ * Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) :=
    (hc _ _).1.symm.trans ((congrArg _ ((UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν _ _ 𝔞.smooth).2.2 ‹_› hβ _ hz)).trans (hc _ _).1)
  have h2 : Oinf μ 𝔞.ν (lact (zc y.1 y.2) β) * Oinf μ 𝔞.ν 𝔞.a₀ = Oinf μ 𝔞.ν β * Oinf μ 𝔞.ν (lact (zc y.1 y.2) 𝔞.a₀) :=
    (hc _ _).1.symm.trans ((congrArg _ ((UpperTheory.ConvolutionTheory.Tf.lactConv K n 𝔞.ν _ _ hβ).2.2 ‹_› 𝔞.smooth _ hz)).trans (hc _ _).1)
  constructor
  · change Oinf μ 𝔞.ν _ * prj _ * _ = Oinf μ 𝔞.ν _ * prj _ * _
    rw [mul_assoc, hP, ← mul_assoc, h1, mul_assoc, ← hP, mul_assoc]
  · change _ * (Oinf μ 𝔞.ν _ * prj _) = _ * (Oinf μ 𝔞.ν _ * prj _)
    rw [← mul_assoc, ← h2, mul_assoc]

private theorem amp_fix [_root_.NumberField.IsTotallyComplex K] (𝔞 : Amp μ) (m : Measure (AdelicGLn.FiniteAdelicGL K n))
    [m.IsHaarMeasure] (y : Ix K n) (P : LL μ →L[ℂ] LL μ) (h1 : P * 𝔞.A = 𝔞.A) (h2 : 𝔞.A * P = 𝔞.A) :
    P * (𝔞.Z y * P) = 𝔞.Z y := by
  have e1 : P * 𝔞.Z y - 𝔞.Z y = 0 := sep_right 𝔞.ν m _ fun β hβ => by
    change (P * 𝔞.Z y - 𝔞.Z y) * _ = 0
    rw [sub_mul, mul_assoc, (amp_move 𝔞 m y β hβ).1, ← mul_assoc, h1, sub_self]
  have e2 : 𝔞.Z y * P - 𝔞.Z y = 0 := sep_left 𝔞.ν _ fun β hβ => by
    change _ * (𝔞.Z y * P - 𝔞.Z y) = 0
    rw [mul_sub, ← mul_assoc, (amp_move 𝔞 m y β hβ).2, mul_assoc, h2, sub_self]
  rw [sub_eq_zero.1 e2, sub_eq_zero.1 e1]

end Amp

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.genZk :
    ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (y : Ix E (2 + 2)), ∃ f : CC E (2 + 2), 𝔵.D.Hecke f ∧ Rop μ f = 𝔢.toAmp.Z y := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 y
  haveI := 𝔵.D.prob
  obtain ⟨P, hP, hf⟩ := two_sided (rightRegularRep (Gam E (2 + 2)) μ) μ (typeFin 𝔵.D).1 𝔵.D.supp 𝔵.D.inv 𝔵.D.cont 𝔵.D.idem
  obtain ⟨m, hm, hc⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx E (2 + 2) (by norm_num)).2.1 μ 𝔢.ν
  obtain ⟨e, -, he⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix E (2 + 2) μ m 𝔢.U 𝔢.isOpen
    (UpperTheory.ConvolutionTheory.Tf.ampComm E (2 + 2) μ 𝔢.toAmp fun τ i => (UpperTheory.ConvolutionTheory.Dp.capZc E (2 + 2) τ).1 i).2.2.2.1
  have h0 : Rop μ (UpperTheory.ConvolutionTheory.tens (lact (zc y.1 y.2) 𝔢.a₀) e) = 𝔢.toAmp.Z y :=
    (UpperTheory.ConvolutionTheory.Tf.rrTens E (2 + 2) (by norm_num) μ 𝔢.ν m hc _ e).trans (by rw [he]; rfl)
  obtain ⟨f, h1, h2⟩ := hf (UpperTheory.ConvolutionTheory.tens (lact (zc y.1 y.2) 𝔢.a₀) e)
  have h3 : P ∘L Rop μ 𝔢.a = Rop μ 𝔢.a ∧ Rop μ 𝔢.a ∘L P = Rop μ 𝔢.a := hP 𝔢.a 𝔵.a_hecke
  rw [𝔢.a_op] at h3
  have h4 : Rop μ f = P ∘L Rop μ (UpperTheory.ConvolutionTheory.tens (lact (zc y.1 y.2) 𝔢.a₀) e) ∘L P := h2
  exact ⟨f, h1, by rw [h4, h0]; exact amp_fix 𝔢.toAmp m y P h3.1 h3.2⟩
end

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.BumpConvolutionOperators

private theorem conv_bump {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    (κ : ℝ → V →L[ℂ] V) (hκ : Ker κ) (R : ℝ) (hR : ∀ t, R < |t| → κ t = 0) (w : ℝ → V) (hw : Continuous w) (hc : HasCompactSupport w)
    (e : V) (he : ∀ x, |x| ≤ R + 1 → w x = e) (U : L V) (hU : ∀ᵐ x : ℝ, U x = w x) :
    ∃ u : ℝ → V, Continuous u ∧ HasCompactSupport u ∧ (∀ᵐ x : ℝ, conv κ U x = u x) ∧ ∀ x, |x| ≤ 1 → u x = symb κ 0 e := by
  refine ⟨fun x => ∫ t, κ t (w (x + t)), ?_, ?_, ?_, fun x hx => ?_⟩
  · have h1 : ∀ x, ∫ t, κ t (w (x + t)) = ∫ t in Set.Icc (-R) R, κ t (w (x + t)) := fun x => by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
      rw [hR t (lt_of_not_ge fun h => ht (abs_le.1 h)), ContinuousLinearMap.zero_apply]
    simp only [h1]
    exact continuous_parametric_integral_of_continuous (f := fun x t => κ t (w (x + t)))
      ((hκ.1.comp continuous_snd).clm_apply (hw.comp (continuous_fst.add continuous_snd))) isCompact_Icc
  · obtain ⟨M, hM⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine HasCompactSupport.intro (isCompact_Icc (a := -(M + R)) (b := M + R)) fun x hx => ?_
    have hx' : M + R < |x| := lt_of_not_ge fun h => hx (abs_le.1 h)
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : R < |t|
    · simp [hR t ht]
    · have : w (x + t) = 0 := by
        by_contra h
        have h2 := hM (subset_tsupport _ h)
        rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
        have h3 := abs_sub (x + t) t
        rw [add_sub_cancel_right] at h3
        linarith [not_lt.1 ht]
      simp [this]
  · filter_upwards [(convSpec κ hκ U).1] with x hx
    rw [hx]
    refine integral_congr_ae ?_
    filter_upwards [(measurePreserving_add_left volume x).quasiMeasurePreserving.ae hU] with t ht
    rw [ht]
  · have hi : Integrable (fun t : ℝ => Complex.exp ((0 : ℂ) * t) • κ t) := by
      simpa using hκ.1.integrable_of_hasCompactSupport hκ.2
    rw [symb, ContinuousLinearMap.integral_apply hi]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : R < |t|
    · simp [hR t ht]
    · have : |x + t| ≤ R + 1 := (abs_add_le x t).trans (by linarith [not_lt.1 ht])
      simp [he _ this]

private theorem ker_bd {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (κ : ℝ → V →L[ℂ] V) (hκ : Ker κ) :
    ∃ R : ℝ, ∀ t, R < |t| → κ t = 0 := by
  obtain ⟨M, hM⟩ := hκ.2.isCompact.isBounded.subset_closedBall 0
  refine ⟨M, fun t ht => ?_⟩
  by_contra h
  have h2 := hM (subset_tsupport _ h)
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
  linarith

private theorem bump_ex {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e : V) (R : ℝ) :
    ∃ (w : ℝ → V) (U : L V), Continuous w ∧ HasCompactSupport w ∧ (∀ x, |x| ≤ R → w x = e) ∧ ∀ᵐ x : ℝ, U x = w x := by
  let w : ℝ → V := fun x => ((max 0 (min 1 (R + 1 - |x|)) : ℝ) : ℂ) • e
  have hw : Continuous w := by fun_prop
  have hc : HasCompactSupport w := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun x hx => ?_
    have hx' : R + 1 < |x| := lt_of_not_ge fun h => hx (abs_le.1 h)
    have : max 0 (min 1 (R + 1 - |x|)) = 0 := max_eq_left (min_le_of_right_le (by linarith))
    simp only [w, this, Complex.ofReal_zero, zero_smul]
  refine ⟨w, (hw.memLp_of_hasCompactSupport hc).toLp w, hw, hc, fun x hx => ?_, MemLp.coeFn_toLp _⟩
  have : max 0 (min 1 (R + 1 - |x|)) = 1 := by rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  simp only [w, this, Complex.ofReal_one, one_smul]

private theorem der_loc (F : (Fin 2 → ℝ) → ℂ) (a : ℂ) (hF : ∀ t, |t 0 - t 1| < 1 → F t = a * Complex.exp ((t 0 - t 1 : ℝ) : ℂ))
    (j : Fin 2) (t : Fin 2 → ℝ) (ht : |t 0 - t 1| < 1) (G : ℂ) (hG : HasDerivAt (fun x : ℝ => F (t + Pi.single j x)) G 0) :
    G = (![1, -1] j : ℝ) * a * Complex.exp ((t 0 - t 1 : ℝ) : ℂ) := by
  set ε : ℝ := ![1, -1] j with hε
  have h1 : ∀ x : ℝ, (t + Pi.single j x : Fin 2 → ℝ) 0 - (t + Pi.single j x : Fin 2 → ℝ) 1 = t 0 - t 1 + ε * x := fun x => by
    fin_cases j <;> simp [hε] <;> ring
  have h2 : ∀ᶠ x : ℝ in 𝓝 0, |t 0 - t 1 + ε * x| < 1 := by
    have : Continuous fun x : ℝ => |t 0 - t 1 + ε * x| := by fun_prop
    exact this.continuousAt.eventually_lt continuousAt_const (by simpa using ht)
  have h3 : HasDerivAt (fun x : ℝ => a * Complex.exp ((t 0 - t 1 + ε * x : ℝ) : ℂ))
      (a * (Complex.exp ((t 0 - t 1 + ε * 0 : ℝ) : ℂ) * ((ε * 1 : ℝ) : ℂ))) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul ε).const_add (t 0 - t 1)).ofReal_comp.cexp).const_mul a
  have h4 := hG.unique (h3.congr_of_eventuallyEq (h2.mono fun x hx => by
    show F _ = _
    rw [hF _ (by rwa [h1]), h1]))
  rw [h4]
  simp only [mul_zero, add_zero, mul_one]
  ring

private theorem coef (n i : ℕ) (hi : i ≤ n) (m : Multiset ℂ) (hm : m.card = n) :
    ∑ j : Fin (n + 1), (Lagrange.basis Finset.univ (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) j).coeff (n - i) *
      (m.map fun x => ((j : ℕ) : ℂ) + x).prod = m.esymm i := by
  set p : Polynomial ℂ := (m.map fun r => Polynomial.X + Polynomial.C r).prod with hp
  have hd : p.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    have : p.natDegree = n := by
      rw [hp, Polynomial.natDegree_multiset_prod_of_monic]
      · simp [Multiset.map_map, hm]
      · intro q hq
        obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 hq
        exact Polynomial.monic_X_add_C r
    refine Polynomial.degree_le_natDegree.trans_lt ?_
    rw [this, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_self n
  have hinj : Set.InjOn (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) (Finset.univ : Finset (Fin (n + 1))) := fun a _ b _ h =>
    Fin.ext (Nat.cast_injective h)
  have h1 := congrArg (fun q : Polynomial ℂ => q.coeff (n - i)) (Lagrange.eq_interpolate hinj hd)
  simp only [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at h1
  have h2 : p.coeff (n - i) = m.esymm i := by
    rw [hp, Multiset.prod_X_add_C_coeff m (by omega), hm, Nat.sub_sub_self hi]
  rw [← h2, h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm, hp, Polynomial.eval_multiset_prod, Multiset.map_map]
  simp

open GlobalTheory.CuspRep UpperTheory.V.Cm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)} (b b' : BW.Blo S 2)

private def Loc (ψ : Sm E (2 + 2)) (a : ℂ) : Prop :=
  BW.Umg ψ ∧ ∀ t : Fin 2 → ℝ, |t 0 - t 1| < 1 → (dat2 b b').comp ψ.1 t = a * Complex.exp ((t 0 - t 1 : ℝ) : ℂ)

variable {b b'}

private theorem Loc.lin {ψ χ : Sm E (2 + 2)} {a a' : ℂ} (h : Loc b b' ψ a) (h' : Loc b b' χ a') (c : ℂ) :
    Loc b b' (c • ψ + χ) (c * a + a') := by
  have hu := (BW.umgOps E (2 + 2)).2
  refine ⟨(hu _ ((hu _ h.1).2.2.1 c)).2.1 _ h'.1, fun t ht => ?_⟩
  rw [(BW.compBound E S _ (dat2 b b')).2 ψ χ c h.1 h'.1 t, h.2 t ht, h'.2 t ht]
  ring

private theorem Loc.zero : Loc b b' 0 0 := by
  have h0 := (BW.umgOps E (2 + 2)).1
  refine ⟨h0, fun t _ => ?_⟩
  have := (BW.compBound E S _ (dat2 b b')).2 0 0 1 h0 h0 t
  rw [smul_zero, add_zero, one_mul] at this
  rw [zero_mul]
  linear_combination -this

private theorem Loc.sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (ψ : ι → Sm E (2 + 2)) (a : ι → ℂ) (h : ∀ i, Loc b b' (ψ i) (a i)) :
    Loc b b' (∑ i ∈ s, c i • ψ i) (∑ i ∈ s, c i * a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Loc.zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi]; exact (h i).lin ih _

private theorem Loc.der {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (j : Fin 2) :
    Loc b b' ((dat2 b b').J j ψ) ((![1, -1] j : ℝ) * a) := by
  refine ⟨?_, fun t ht => der_loc ((dat2 b b').comp ψ.1) a h.2 j t ht _ ((BW.compShift E S _ (dat2 b b') ψ t h.1).2 j)⟩
  have : ∃ u, (dat2 b b').J j = uC E (2 + 2) u := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [BW.Dat.J, ← uC_genC, ← map_sum, ← map_smul]
    exact ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := this
  rw [hu]
  exact ((BW.umgOps E (2 + 2)).2 _ h.1).2.2.2.1 u

private theorem size_eq (j : Fin 2) : (dat2 b b').size j = 2 := by
  have : (dat2 b b').idx = (![0, 0, 1, 1] : Fin 4 → Fin 2) := by
    funext i; fin_cases i <;> rfl
  unfold BW.Dat.size
  rw [this]
  fin_cases j <;> rfl

private theorem rho_eq (j : Fin 2) : (dat2 b b').rho j = -(![1, -1] j : ℝ) := by
  have h : (dat2 b b').rho j = ((∑ l ∈ Finset.Iio j, ((dat2 b b').size l : ℝ)) - ∑ l ∈ Finset.Ioi j, ((dat2 b b').size l : ℝ)) / 2 := rfl
  rw [h]
  simp only [size_eq]
  fin_cases j <;> simp

private theorem Loc.fac {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (j : Fin 2) (x : ℂ) :
    Loc b b' ((algebraMap ℂ (Module.End ℂ (Sm E (2 + 2))) (x + ((dat2 b b').rho j : ℂ)) + (dat2 b b').J j) ψ) (x * a) := by
  have := h.lin (h.der j) (x + ((dat2 b b').rho j : ℂ))
  rw [LinearMap.add_apply, Module.algebraMap_end_apply]
  convert this using 1
  rw [rho_eq]
  push_cast
  ring

private theorem Loc.prod {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (x : Fin (2 + 2) → ℂ) (l : List (Fin (2 + 2))) :
    Loc b b' ((l.map fun i => algebraMap ℂ (Module.End ℂ (Sm E (2 + 2))) (x i + ((dat2 b b').rho ((dat2 b b').idx i) : ℂ)) +
      (dat2 b b').J ((dat2 b b').idx i)).prod ψ) ((l.map x).prod * a) := by
  induction l with
  | nil => simpa using h
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, List.map_cons, List.prod_cons, mul_assoc]
    exact ih.fac _ _

private theorem Loc.capelli {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (τ : E →+* ℂ) (u : ℂ) :
    Loc b b' (cap τ u ψ) (((Finset.univ.val.map ((dat2 b b').lam τ)).map fun x => u + x).prod * a) := by
  refine ⟨?_, fun t ht => ?_⟩
  · rw [← uC_capC]
    exact ((BW.umgOps E (2 + 2)).2 _ h.1).2.2.2.1 _
  · rw [BW.compCap E S _ (dat2 b b') ψ τ u h.1, List.ofFn_eq_map,
      (h.prod (fun i => u + (dat2 b b').lam τ i) (List.finRange (2 + 2))).2 t ht, Multiset.map_map, ← List.ofFn_eq_map,
      List.prod_ofFn]
    rfl

private theorem zop_X {n : ℕ} (y : Ix E n) : BW.zop (X y) = ∑ j : Fin (n + 1),
    (Lagrange.basis Finset.univ (fun j : Fin (n + 1) => ((j : ℕ) : ℂ)) j).coeff (n - (y.2 + 1)) •
      (cap y.1 ((j : ℕ) : ℂ) : Module.End ℂ (Sm E n)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [BW.zop, BW.evZ, aeval_X, BW.zC, map_sum, map_smul, uC_capC]

private theorem Loc.z {ψ : Sm E (2 + 2)} {a : ℂ} (h : Loc b b' ψ a) (y : Ix E (2 + 2)) :
    Loc b b' (BW.zop (X y) ψ) ((Finset.univ.val.map ((dat2 b b').lam y.1)).esymm (y.2 + 1) * a) := by
  rw [zop_X, ← coef (2 + 2) (y.2 + 1) y.2.2 _ (by simp), Finset.sum_mul, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, mul_assoc]
  exact Loc.sum _ _ _ _ fun j => h.capelli _ _

private theorem rt_zop {n : ℕ} (y : Ix E n) (g : GA E n) (ψ : Sm E n) :
    rt E n g (BW.zop (X y) ψ) = BW.zop (X y) (rt E n g ψ) := by
  have h : ∀ u : ℂ, Commute (cap y.1 u) (rt E n g) := fun u => by
    rw [← infGL_mul_finGL g, map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E n y.1 u _).mul_right (commute_cap_finRep y.1 u _)
  have : Commute (BW.zop (X y)) (rt E n g) := by
    rw [zop_X]
    exact Commute.sum_left _ _ _ fun j _ => (h _).smul_left _
  exact (LinearMap.congr_fun this.eq ψ).symm

private theorem lam_eq (τ : E →+* ℂ) : Finset.univ.val.map ((dat2 b b').lam τ) =
    (Finset.univ.val.map fun i => b'.Λ τ i) + Finset.univ.val.map fun i => b.Λ τ i := by
  refine Eq.trans ?_ (add_comm _ _)
  rfl

private theorem Loc.kill {ψ : Sm E (2 + 2)} {a : ℂ} {g : GA E (2 + 2)} (h : Loc b b' (rt E (2 + 2) g ψ) a) (y : Ix E (2 + 2)) (m : Multiset ℂ)
    (hm : ((Finset.univ.val.map fun i => b'.Λ y.1 i) + Finset.univ.val.map fun i => b.Λ y.1 i) = m) :
    (dat2 b b').comp (rt E (2 + 2) g ((-m.esymm (y.2 + 1)) • ψ + BW.zop (X y) ψ)).1 (0 : Fin 2 → ℝ) = 0 := by
  have l₂ := h.z y
  rw [lam_eq, hm] at l₂
  have l₃ := (h.lin l₂ (-m.esymm (y.2 + 1))).2 0 (by simp)
  rw [map_add (f := _), map_smul, rt_zop, l₃]
  ring

private theorem comb {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (c : ℂ) {u v : ℝ → V} {U W : L V}
    (hu : Continuous u) (hv : Continuous v) (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (hua : ∀ᵐ x : ℝ, U x = u x) (hva : ∀ᵐ x : ℝ, W x = v x) :
    Continuous (fun x => c • u x + v x) ∧ HasCompactSupport (fun x => c • u x + v x) ∧
      ∀ᵐ x : ℝ, (c • U + W : L V) x = c • u x + v x := by
  have h : HasCompactSupport (fun x => c • u x) := huc.comp_left (g := fun z => c • z) (smul_zero c)
  refine ⟨(hu.const_smul _).add hv, h.add hvc, ?_⟩
  filter_upwards [Lp.coeFn_add (c • U) W, Lp.coeFn_smul c U, hua, hva] with x h1 h2 h3 h4
  rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.BumpConvolutionOperators

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.BumpConvolutionOperators in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.genZ :
    ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : _root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.Fam 𝔢) (y : Ix E (2 + 2)),
      (∃ β, Ker β ∧ Conv 𝔵.A'.J 𝔵.A'.J (𝔢.toAmp.Z y) β ∧ symb β 0 = (𝔵.Λ y.1).esymm (y.2 + 1) • 𝔵.a₀) ∧
        𝔢.toAmp.Z y ∘L 𝔵.P = 𝔵.P ∘L 𝔢.toAmp.Z y := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 y
  obtain ⟨f, hf, hZ⟩ := genZk 𝔵 y
  refine ⟨?_, hZ ▸ (Hecke₃ E μ _ _ _ 𝔵.pair 𝔵.D _ _ 𝔵.A 𝔵.A' 𝔵.P 𝔵.isP).2 f hf⟩
  obtain ⟨β, hβ, hc, -⟩ := convR E μ _ _ _ ⟨𝔵.pair.irr₂, 𝔵.pair.irr₁, 𝔵.pair.orth.symm⟩ 𝔵.D _ _ 𝔵.A' 𝔵.A f hf
  rw [hZ] at hc
  refine ⟨β, hβ, hc, ContinuousLinearMap.ext fun e => ?_⟩
  obtain ⟨hα, ha, -⟩ := 𝔵.a_acts
  rw [𝔢.a_op] at ha
  obtain ⟨R₁, h₁⟩ := ker_bd β hβ
  obtain ⟨R₂, h₂⟩ := ker_bd _ hα
  obtain ⟨w, U, hw, hwc, hwe, hU⟩ := bump_ex e (max R₁ R₂ + 1)
  obtain ⟨u, hu, huc, hua, hu0⟩ := conv_bump _ hα _ (fun t ht => h₂ t ((le_max_right R₁ R₂).trans_lt ht)) w hw hwc e hwe U hU
  obtain ⟨v, hv, hvc, hva, hv0⟩ := conv_bump _ hβ _ (fun t ht => h₁ t ((le_max_left R₁ R₂).trans_lt ht)) w hw hwc e hwe U hU
  obtain ⟨ρ, N, Lm, hL, -, hLZ⟩ := BW.ampRep E (2 + 2) μ 𝔢.toAmp (by norm_num)
  have r₁ := (hL (𝔵.A'.J U)).1
  have r₂ := hLZ y (𝔵.A'.J U)
  rw [ha U _ (convSpec _ hα U).1] at r₁
  rw [hc U _ (convSpec _ hβ U).1] at r₂
  set φ := Lm (𝔵.A'.J U)
  set s := (𝔵.Λ y.1).esymm (y.2 + 1) with hs
  have r₃ := (BW.repOps E (2 + 2) μ (by norm_num) _ _ r₁).2.1 _ _ (-s) r₂
  rw [← map_smul, ← map_add (f := _)] at r₃
  have key : (-s) • 𝔵.a₀ e + symb β 0 e = 0 := by
    refine bloEx 𝔵 _ fun b b' hb hb' k hk => ?_
    obtain ⟨c, hc0, hcl⟩ := compLine 𝔵 b b' hb hb'
    have l₁ : Loc b b' (GlobalTheory.CuspRep.rt E (2 + 2) (k : GlobalTheory.CuspRep.GA E (2 + 2)) φ) (c * ell b b' k (𝔵.A'.sec (𝔵.a₀ e))) := by
      refine ⟨((BW.umgOps E (2 + 2)).2 _ r₁.umg).2.2.2.2.1 _, fun t ht => ?_⟩
      refine (hcl k hk u _ φ hu huc hua r₁ t).trans ?_
      rw [hu0 _ (by rw [abs_div, abs_two]; linarith [abs_nonneg (t 0 - t 1)]), mul_right_comm]
      rfl
    have l₃ := l₁.kill y (𝔵.Λ y.1) (by rw [hb.inf, hb'.inf]; rfl)
    obtain ⟨c₁, c₂, c₃⟩ := comb (-s) hu hv huc hvc hua hva
    have l₅ := (hcl k hk _ _ _ c₁ c₂ c₃ r₃ (0 : Fin 2 → ℝ)).symm.trans l₃
    rw [hu0 _ (by simp), hv0 _ (by simp)] at l₅
    exact (mul_eq_zero.1 l₅).resolve_left (mul_ne_zero hc0 (Complex.exp_ne_zero _))
  rw [ContinuousLinearMap.smul_apply]
  rw [neg_smul, neg_add_eq_zero] at key
  exact key.symm
