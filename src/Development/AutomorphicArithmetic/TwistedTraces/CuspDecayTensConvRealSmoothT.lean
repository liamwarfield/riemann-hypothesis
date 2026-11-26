module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.SliceAct
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LactConv

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.TensConvEqArchConv
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem parts_archP (a : archGroup K n) :
    ∃ s, infPart K n (archP K n a : AdelicGLn.AdelicGL K n) = a * zInf K n s ∧
      CuspidalSpectrum.finPart K n (archP K n a : AdelicGLn.AdelicGL K n) = 1 := by
  refine ⟨(detModule K n (infEmb K n a))⁻¹, ?_, ?_⟩
  · rw [← retract_infEmb, coe_retractOne, map_mul, infPart_infEmb, ← map_inv, map_inv (zInf K n)]
    rw [map_inv (centralSection K n), map_inv (infPart K n)]
    rfl
  · rw [← retract_infEmb, coe_retractOne, map_mul, finPart_infEmb, map_inv, finPart_centralSection]
    simp

private theorem tensFun_shift (β : TI K n) (e : TF K n) (a : archGroup K n) (g : normOneGL (K := K) (n := n)) :
    tensFun β e ((archP K n a)⁻¹ * g) =
      kbar β (a⁻¹ * infPart K n (g : AdelicGLn.AdelicGL K n)) *
        e (CuspidalSpectrum.finPart K n (g : AdelicGLn.AdelicGL K n)) := by
  obtain ⟨s, h1, h2⟩ := parts_archP a
  rw [tensFun, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, map_inv, h1, h2, inv_one, one_mul,
    mul_inv_rev, ← map_inv, mul_assoc, zInf_mul_comm, kbar_mul_zInf]

private theorem kbar_conv (hn : 0 < n) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : TI K n)
    (x : archGroup K n) :
    kbar (conv ν β₁ β₂) x = ∫ a, β₁ a * kbar β₂ (a⁻¹ * x) ∂ν := by
  have hc : Continuous (Function.uncurry fun (s : {r : ℝ // 0 < r}) (a : archGroup K n) =>
      β₁ a * β₂ (a⁻¹ * (x * zInf K n s))) := by
    refine (β₁.continuous.comp continuous_snd).mul (β₂.continuous.comp ?_)
    exact (continuous_snd.inv).mul (continuous_const.mul (continuous_zInf.comp continuous_fst))
  have hs : HasCompactSupport (Function.uncurry fun (s : {r : ℝ // 0 < r}) (a : archGroup K n) =>
      β₁ a * β₂ (a⁻¹ * (x * zInf K n s))) := by
    have hC : IsCompact ((fun p : {r : ℝ // 0 < r} × archGroup K n => (p.1 * detA K n (x⁻¹ * p.2), p.2)) ''
        ((detA K n '' tsupport β₂) ×ˢ tsupport β₁)) :=
      ((β₂.hasCompactSupport.isCompact.image continuous_detA).prod β₁.hasCompactSupport.isCompact).image
        ((continuous_fst.mul (continuous_detA.comp (continuous_const.mul continuous_snd))).prodMk continuous_snd)
    refine HasCompactSupport.intro hC fun p hp => ?_
    by_contra hne
    apply hp
    obtain ⟨s, a⟩ := p
    have h1 : β₁ a ≠ 0 := left_ne_zero_of_mul hne
    have h2 : β₂ (a⁻¹ * (x * zInf K n s)) ≠ 0 := right_ne_zero_of_mul hne
    have h3 := mem_of_kernel_ne_zero hn (κ := β₂) (a := a⁻¹ * x) (s := s) (by rwa [mul_assoc])
    refine ⟨(s * detA K n (a⁻¹ * x), a), ⟨h3, subset_tsupport _ h1⟩, ?_⟩
    have h4 : detA K n (a⁻¹ * x) * detA K n (x⁻¹ * a) = 1 := by
      rw [← map_mul]
      simp [mul_assoc]
    simp only [mul_assoc, h4, mul_one]
  have hsw := integral_integral_swap_of_hasCompactSupport hc hs (μ := GroundTheory.Global.posRealMeasure) (ν := ν)
  simp only [kbar, conv_apply]
  rw [hsw]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_assoc]
  exact integral_const_mul _ _

private theorem tens_conv (hn : 0 < n) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β₁ β₂ : TI K n) (e : TF K n)
    (g : normOneGL (K := K) (n := n)) :
    tens (conv ν β₁ β₂) e g = ∫ a, β₁ a * tens β₂ e ((archP K n a)⁻¹ * g) ∂ν := by
  simp only [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn _ e).1, tensFun_shift]
  rw [tensFun, kbar_conv hn, ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_assoc]

end SlopeTestRemainingChoices

theorem UpperTheory.tens_conv_eq_archConv :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
        ∀ (ν' : Measure (ArchUnits K n)) [ν'.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure],
        (∀ f : archGroup K n → ℂ, ∫ A, f A ∂ν = ∫ A : ArchUnits K n, f ⟨A, Subgroup.mem_top A⟩ ∂ν') →
        ∀ (β : ArchMatrix K n → ℝ) (hβ : Continuous β) (hβc : HasCompactSupport β)
          (hβu : tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n)) (κ γ : TI K n) (e : TF K n),
          (∀ A : archGroup K n, κ A = (β ((A : ArchUnits K n) : ArchMatrix K n) : ℂ)) →
          tens (conv ν κ γ) e = archConv ν' hβ hβc hβu (tens γ e) := by
  intro K _ _ n hn ν' _ ν _ hint β hβ hβc hβu κ γ e hκ
  ext g
  rw [tens_conv hn, archConv_apply, archConvFun, hint (fun a => κ a * tens γ e ((archP K n a)⁻¹ * g))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun A => ?_)
  simp only [hκ]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.CuspDecayArchConvFinAvg
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.cuspDecay_archConv_finAvg :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
        (ν : Measure (ArchUnits K n)) [ν.IsHaarMeasure] (β : ArchMatrix K n → ℝ)
        (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
        (hβu : tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n))
        (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
        (g : CC K n), CuspDecay μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) := by
  intro K _ _ n μ _ ν _ β hβ hβc hβu U hU g N'
  obtain ⟨Sg, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  obtain ⟨f, hf⟩ : ∃ f, f = archConv ν hβ.continuous hβc hβu (finAvg U hU g) := ⟨_, rfl⟩
  rw [← hf]
  have exists_norm_rconv_le_siegel_basic (f : CC K n)
      {S : Set (AdelicGLn.AdelicGL K n)} (hSg : IsCompact S) {t : ℝ} (ht : 0 < t) :
      ∃ (C : ℝ) (N : ℕ), ∀ φ : Lp ℂ 2 (quotientMeasure (Gam K n) μ), ∀ b ∈ S, ∀ (ρ : Fin n → ℝ)
        (hρ : ∀ i, 0 < ρ i), (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
        ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL (K := K) (n := n),
        (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
        ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) →
        ‖rconv (Gam K n) μ f φ x‖ ≤ C * √(R ^ N) * ‖φ‖ := by
    obtain ⟨Cc, N, hCc⟩ := exists_encard_le_siegel hSg ht f.hasCompactSupport
    have hf2 : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
      have := (f.continuous.memLp_of_hasCompactSupport (μ := μ) (p := 2) f.hasCompactSupport)
      rw [← L2Kernel.eLpNorm_two_sq]
      have hnorm := this.eLpNorm_lt_top
      rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp) this.aestronglyMeasurable] at hnorm
      exact (ENNReal.pow_lt_top hnorm).ne
    set A := (∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ).toReal
    have hA : 0 ≤ A := ENNReal.toReal_nonneg
    refine ⟨√(A * max Cc 0), N, ?_⟩
    intro φ b hb ρ hρ hsieg kk hkk x hx R hR1 hR
    obtain ⟨m, hmC, hm⟩ := hCc b hb ρ hρ hsieg kk hkk x hx R hR1 hR
    have hS : MeasurableSet ((fun y => x * y) '' tsupport (f : normOneGL (K := K) (n := n) → ℂ)) :=
      (f.hasCompactSupport.image (continuous_const_mul x)).measurableSet
    set_option synthInstance.maxHeartbeats 200000 in
    have h1 := enorm_rconv_sq_le (Gam K n) μ f φ x hS (fun y hy => image_eq_zero_of_notMem_tsupport
      fun h' => hy ⟨x⁻¹ * y, h', by simp⟩) hm
    rw [← mul_assoc] at h1
    have h2 := norm_le_of_enorm_sq_le (ENNReal.mul_ne_top hf2 (by simp)) h1
    refine h2.trans ?_
    gcongr
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ← Real.sqrt_mul (mul_nonneg hA
      (le_max_right _ _))]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (by linarith) _))) hA
  obtain ⟨C₀, N₀, hC₀⟩ := exists_norm_rconv_le_siegel_basic f hω ht
  obtain ⟨Ch, hCh0, hCh⟩ := exists_height_le_normOne (K := K) (n := n) hω
  obtain ⟨e, he⟩ : ∃ e, e = 2 * Fintype.card (InfinitePlace K) := ⟨_, rfl⟩
  rw [← he] at hCh
  have exists_le_max_pow (hn : 2 ≤ n) (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i) :
      ∃ (r : ℕ) (hr : 0 < r) (hrn : r < n), ∀ i j : Fin n, i < j →
        ρ i / ρ j ≤ max 1 (ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩) ^ n := by
    have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
    obtain ⟨l₀, hl₀⟩ := Finite.exists_max fun l : Fin (n - 1) =>
      ρ ⟨l, by omega⟩ / ρ ⟨l + 1, by omega⟩
    refine ⟨l₀ + 1, by omega, by omega, fun i j hij => ?_⟩
    set M := max 1 (ρ ⟨l₀ + 1 - 1, by omega⟩ / ρ ⟨l₀ + 1, by omega⟩)
    have hM1 : 1 ≤ M := le_max_left _ _
    have hstep : ∀ l : ℕ, ∀ (hl : l + 1 < n), ρ ⟨l, by omega⟩ ≤ M * ρ ⟨l + 1, hl⟩ := by
      intro l hl
      have h1 := hl₀ ⟨l, by omega⟩
      rw [← div_le_iff₀ (hρ _)]
      exact h1.trans (le_max_right _ _)
    have hchain : ∀ d : ℕ, ∀ (a : ℕ) (ha : a + d < n), ρ ⟨a, by omega⟩ ≤ M ^ d * ρ ⟨a + d, ha⟩ := by
      intro d
      induction d with
      | zero => intro a ha; simp
      | succ d ih =>
        intro a ha
        calc ρ ⟨a, by omega⟩ ≤ M ^ d * ρ ⟨a + d, by omega⟩ := ih a (by omega)
          _ ≤ M ^ d * (M * ρ ⟨a + d + 1, by omega⟩) :=
              mul_le_mul_of_nonneg_left (hstep (a + d) (by omega)) (pow_nonneg (by linarith) _)
          _ = M ^ (d + 1) * ρ ⟨a + (d + 1), ha⟩ := by rw [pow_succ]; ring_nf
    have hij' : (i : ℕ) < j := hij
    have h1 := hchain (j - i) i (by omega)
    have hj : (⟨(i : ℕ) + (j - i), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
    rw [hj] at h1
    rw [div_le_iff₀ (hρ _)]
    calc ρ i = ρ ⟨i, by omega⟩ := rfl
      _ ≤ M ^ ((j : ℕ) - i) * ρ j := h1
      _ ≤ M ^ n * ρ j := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM1 (by omega)) (hρ _).le
  
  
  have exists_norm_rconv_le_decay {β : ArchMatrix K n → ℝ}
      (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β) (hβc : HasCompactSupport β)
      (hβu : tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n))
      (U : Subgroup (AdelicGLn.integralFiniteGL K n))
      (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
      (g : CompactlySupportedContinuousMap (normOneGL (K := K) (n := n)) ℂ)
      {S : Set (AdelicGLn.AdelicGL K n)} (hSg : IsCompact S)
      (hSB : S ⊆ ((adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)))
      {t : ℝ} (ht : 0 < t) (N' : ℕ) :
      ∃ C : ℝ, ∀ φ ∈ cuspidalL2 μ, ∀ b ∈ S, ∀ (ρ : Fin n → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) →
        ∀ kk ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)), ∀ x : normOneGL (K := K) (n := n),
        (x : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk →
        ∀ R : ℝ, 1 ≤ R → (∃ i j : Fin n, i < j ∧ R ≤ ρ i / ρ j) →
        ‖rconv (Gam K n) μ (archConv ν hβ.continuous hβc hβu (finAvg U hU g)) φ x‖ ≤
          C * (R ^ N')⁻¹ * ‖φ‖ := by
    set f := archConv ν hβ.continuous hβc hβu (finAvg U hU g)
    obtain ⟨C₀, N₀, hC₀⟩ := exists_norm_rconv_le_siegel_basic f hSg ht
    have hdec := fun (r : ℕ) (hr : 0 < r) (hrn : r < n) =>
      exists_norm_rconv_le_siegel μ ν hβ hβc hβu U hU g hSg hSB ht hr hrn
    choose Nf hNf using hdec
    have hdec2 := fun (r : ℕ) (hr : 0 < r) (hrn : r < n) =>
      hNf r hr hrn (n * Nf r hr hrn + n * N')
    choose Cf hCf using hdec2
    set Cmax := max C₀ 0 + ∑ r : Fin n, if h : 0 < (r : ℕ) then max (Cf r h r.2) 0 else 0
    have hsum0 : 0 ≤ ∑ r : Fin n, if h : 0 < (r : ℕ) then max (Cf r h r.2) 0 else 0 :=
      Finset.sum_nonneg fun r _ => by split_ifs <;> simp
    have hCf_le : ∀ (r : ℕ) (hr : 0 < r) (hrn : r < n), Cf r hr hrn ≤ Cmax := by
      intro r hr hrn
      have h1 := Finset.single_le_sum (f := fun r : Fin n =>
        if h : 0 < (r : ℕ) then max (Cf r h r.2) 0 else 0)
        (fun r _ => by split_ifs <;> simp) (Finset.mem_univ ⟨r, hrn⟩)
      simp only [hr, dif_pos] at h1
      exact (le_max_left _ _).trans (h1.trans (le_add_of_nonneg_left (le_max_right _ _)))
    have hC₀_le : C₀ ≤ Cmax := (le_max_left _ _).trans (le_add_of_nonneg_right hsum0)
    have hCmax0 : 0 ≤ Cmax := (le_max_right _ _).trans (le_add_of_nonneg_right hsum0)
    refine ⟨Cmax, ?_⟩
    intro φ hφ b hb ρ hρ hsieg kk hkk x hx R hR1 ⟨i₀, j₀, hij₀, hRij⟩
    have hn : 2 ≤ n := by
      have : (i₀ : ℕ) < j₀ := hij₀
      omega
    obtain ⟨r, hr, hrn, hratio⟩ := exists_le_max_pow hn ρ hρ
    set α := ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩
    have hα0 : 0 < α := div_pos (hρ _) (hρ _)
    rcases le_or_gt α 1 with hα1 | hα1
    · have hM : max 1 α = 1 := max_eq_left hα1
      have hR1' : R = 1 := le_antisymm (hRij.trans ((hratio i₀ j₀ hij₀).trans
        (by rw [hM, one_pow]))) hR1
      have h := hC₀ φ b hb ρ hρ hsieg kk hkk x hx 1 le_rfl fun i j hij =>
        (hratio i j hij).trans (by rw [hM, one_pow])
      rw [one_pow, Real.sqrt_one, mul_one] at h
      rw [hR1', one_pow, inv_one, mul_one]
      exact h.trans (mul_le_mul_of_nonneg_right hC₀_le (norm_nonneg _))
    · have hM : max 1 α = α := max_eq_right hα1.le
      have h := hCf r hr hrn φ hφ b hb ρ hρ hsieg kk hkk x hx (α ^ n) (one_le_pow₀ hα1.le)
        fun i j hij => (hratio i j hij).trans (by rw [hM])
      have hgain : ρ ⟨r, hrn⟩ / ρ ⟨r - 1, by omega⟩ = α⁻¹ := by rw [inv_div]
      rw [hgain] at h
      set a := n * Nf r hr hrn
      set c := n * N'
      have hy1 : 1 ≤ α ^ a := one_le_pow₀ hα1.le
      have hsq : √((α ^ n) ^ Nf r hr hrn) ≤ α ^ a := by
        rw [← pow_mul]
        calc √(α ^ a) ≤ √((α ^ a) ^ 2) := Real.sqrt_le_sqrt (le_self_pow₀ hy1 two_ne_zero)
          _ = α ^ a := Real.sqrt_sq (by positivity)
      have hpow : (α⁻¹) ^ (a + c) * α ^ a = (α ^ c)⁻¹ := by
        rw [inv_pow, pow_add]
        field_simp
      have hRc : (α ^ c)⁻¹ ≤ (R ^ N')⁻¹ := by
        have hRα : R ≤ α ^ n := hRij.trans ((hratio i₀ j₀ hij₀).trans (by rw [hM]))
        rw [show c = n * N' from rfl, pow_mul]
        exact inv_anti₀ (pow_pos (by linarith) _) (pow_le_pow_left₀ (by linarith) hRα _)
      have hX : 0 ≤ (α⁻¹) ^ (a + c) * √((α ^ n) ^ Nf r hr hrn) := by positivity
      calc ‖rconv (Gam K n) μ f φ x‖
          ≤ Cf r hr hrn * (α⁻¹) ^ (a + c) * √((α ^ n) ^ Nf r hr hrn) * ‖φ‖ := h
        _ ≤ Cmax * ((α⁻¹) ^ (a + c) * α ^ a) * ‖φ‖ := by
            rw [mul_assoc (Cf r hr hrn)]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            calc Cf r hr hrn * ((α⁻¹) ^ (a + c) * √((α ^ n) ^ Nf r hr hrn))
                ≤ Cmax * ((α⁻¹) ^ (a + c) * √((α ^ n) ^ Nf r hr hrn)) :=
                  mul_le_mul_of_nonneg_right (hCf_le r hr hrn) hX
              _ ≤ Cmax * ((α⁻¹) ^ (a + c) * α ^ a) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (by positivity)) hCmax0
        _ = Cmax * (α ^ c)⁻¹ * ‖φ‖ := by rw [hpow]
        _ ≤ Cmax * (R ^ N')⁻¹ * ‖φ‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRc hCmax0) (norm_nonneg _)
  
  
  obtain ⟨C₁, hC₁⟩ := exists_norm_rconv_le_decay hβ hβc hβu U hU g hω hωB ht (n * e * N')
  rw [← hf] at hC₁
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = (max 1 t⁻¹) ^ n := ⟨_, rfl⟩
  have hτ1 : 1 ≤ τ := hτdef ▸ one_le_pow₀ (le_max_left _ _)
  obtain ⟨D, hDdef⟩ : ∃ D, D = max (Ch * τ ^ e) 1 := ⟨_, rfl⟩
  have hD1 : 1 ≤ D := hDdef ▸ le_max_right _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD1
  obtain ⟨B, hBdef⟩ : ∃ B, B = max C₀ 0 + max C₁ 0 := ⟨_, rfl⟩
  have hC₀B : C₀ ≤ B := hBdef ▸ (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hC₁B : C₁ ≤ B := hBdef ▸ (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  have hB0 : 0 ≤ B := hBdef ▸ add_nonneg (le_max_right _ _) (le_max_right _ _)
  refine ⟨B * D ^ N', fun φ hφ x => ?_⟩
  have hq1 : 1 ≤ qht x := le_ciInf fun γ => one_le_height _
  have hq0 : 0 < qht x := zero_lt_one.trans_le hq1
  have hqN : 0 < qht x ^ N' := pow_pos hq0 _
  obtain ⟨γ, hγ⟩ := hsieg (x : AdelicGLn.AdelicGL K n)
  have hγ1 : AdelicGLn.diagonal K n γ ∈ normOneGL (K := K) (n := n) := rationalGL_le_normOneGL ⟨γ, rfl⟩
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : normOneGL (K := K) (n := n), γ₁ = ⟨AdelicGLn.diagonal K n γ, hγ1⟩ := ⟨_, rfl⟩
  have hγΓ : γ₁ ∈ Gam K n := ⟨γ, by rw [hγ₁]; rfl⟩
  have hqle : qht x ≤ AutomorphicForm.height ((γ₁ * x : G1 K n) : AdelicGLn.AdelicGL K n) := by
    refine ciInf_le ⟨0, ?_⟩ (⟨γ₁, hγΓ⟩ : Gam K n)
    rintro _ ⟨δ, rfl⟩
    exact (height_pos _).le
  rw [← rconv_mul_left (Gam K n) μ f φ hγΓ x]
  obtain ⟨b, hb, _, ⟨ρ, hρ, hs, rfl⟩, kk, hkk, hx⟩ := hγ
  have hx' : ((γ₁ * x : normOneGL (K := K) (n := n)) : AdelicGLn.AdelicGL K n) =
      b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * kk := by
    rw [hγ₁]; exact hx

  have hheight : ∀ R : ℝ, 1 ≤ R → (∀ i j : Fin n, i < j → ρ i / ρ j ≤ R) → qht x ≤ D * R ^ e := by
    intro R hR1 hR
    have hall : ∀ i j : Fin n, ρ i / ρ j ≤ τ * R := fun i j => by
      rw [hτdef]; exact siegel_div_le_mul ht hρ hs hR1 hR i j
    have h1 := hCh b hb ρ hρ kk hkk _ (γ₁ * x).2 hx' (τ * R)
      (one_le_mul_of_one_le_of_one_le hτ1 hR1) hall
    calc qht x ≤ _ := hqle
      _ ≤ Ch * (τ * R) ^ e := h1
      _ = Ch * τ ^ e * R ^ e := by rw [mul_pow]; ring
      _ ≤ D * R ^ e := mul_le_mul_of_nonneg_right (hDdef ▸ le_max_left _ _)
          (pow_nonneg (zero_le_one.trans hR1) _)

  have hsmall : (∀ i j : Fin n, i < j → ρ i / ρ j ≤ 1) →
      ‖rconv (Gam K n) μ f φ (γ₁ * x)‖ ≤ B * D ^ N' * (qht x ^ N')⁻¹ * ‖φ‖ := by
    intro hall
    have h := hC₀ φ b hb ρ hρ hs kk hkk (γ₁ * x) hx' 1 le_rfl hall
    rw [one_pow, Real.sqrt_one, mul_one] at h
    have hqD : qht x ≤ D := by simpa using hheight 1 le_rfl hall
    have h1 : 1 ≤ D ^ N' * (qht x ^ N')⁻¹ := by
      rw [le_mul_inv_iff₀ hqN, one_mul]
      exact pow_le_pow_left₀ hq0.le hqD _
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    calc C₀ ≤ B := hC₀B
      _ ≤ B * (D ^ N' * (qht x ^ N')⁻¹) := le_mul_of_one_le_right hB0 h1
      _ = B * D ^ N' * (qht x ^ N')⁻¹ := by ring
  by_cases hn : 2 ≤ n
  · obtain ⟨r, hr, hrn, hratio⟩ := exists_le_max_pow hn ρ hρ
    obtain ⟨α, hαdef⟩ : ∃ α, α = ρ ⟨r - 1, by omega⟩ / ρ ⟨r, hrn⟩ := ⟨_, rfl⟩
    rw [← hαdef] at hratio
    rcases le_or_gt α 1 with hα1 | hα1
    · exact hsmall fun i j hij => (hratio i j hij).trans (by rw [max_eq_left hα1, one_pow])
    · have hM : max 1 α = α := max_eq_right hα1.le
      have hαn1 : 1 ≤ α ^ n := one_le_pow₀ hα1.le
      have hlt : (⟨r - 1, by omega⟩ : Fin n) < ⟨r, hrn⟩ := by
        rw [Fin.mk_lt_mk]; omega
      have h := hC₁ φ hφ b hb ρ hρ hs kk hkk (γ₁ * x) hx' α hα1.le
        ⟨_, _, hlt, hαdef.le⟩
      have hqA : qht x ≤ D * α ^ (n * e) := by
        have := hheight (α ^ n) hαn1 fun i j hij => (hratio i j hij).trans (by rw [hM])
        rwa [← pow_mul] at this
      have hAN : 0 < α ^ (n * e * N') := pow_pos (zero_lt_one.trans hα1) _
      have h1 : (α ^ (n * e * N'))⁻¹ ≤ D ^ N' * (qht x ^ N')⁻¹ := by
        rw [le_mul_inv_iff₀ hqN, inv_mul_le_iff₀ hAN, pow_mul α (n * e) N', ← mul_pow]
        refine pow_le_pow_left₀ hq0.le ?_ _
        linarith [mul_comm (α ^ (n * e)) D]
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      calc C₁ * (α ^ (n * e * N'))⁻¹ ≤ B * (D ^ N' * (qht x ^ N')⁻¹) :=
            mul_le_mul hC₁B h1 (inv_nonneg.2 hAN.le) hB0
        _ = B * D ^ N' * (qht x ^ N')⁻¹ := by ring
  · refine hsmall fun i j hij => ?_
    have : (i : ℕ) < j := hij
    omega
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.FinAvgTensOfLeftInvariant
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.finAvg_tens_of_leftInvariant :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
        ∀ (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
          (γ : TI K n) (e : TF K n),
          (∀ u ∈ U, ∀ h, e ((u : AdelicGLn.FiniteAdelicGL K n) * h) = e h) → finAvg U hU (tens γ e) = tens γ e := by
  intro K _ _ n hn U hU γ e he
  have happ : ∀ x, tens γ e x = tensFun γ e x := (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn γ e).1
  have hc : ∀ (u : U) (x : normOneGL (K := K) (n := n)), tens γ e ((finOne K n u)⁻¹ * x) = tens γ e x := by
    intro u x
    rw [happ, happ]
    unfold tensFun
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_finOne, map_mul, map_mul, map_inv, map_inv, infPart_finEmb,
      finPart_finEmb, inv_one, one_mul]
    have h := he (u⁻¹ : U) (u⁻¹ : U).2 (CuspidalSpectrum.finPart K n (x : AdelicGLn.AdelicGL K n))
    exact congrArg _ h
  ext x
  rw [finAvg_apply]
  haveI := compactSpace_of_isOpen U hU
  change ∫ u : U, tens γ e ((finOne K n u)⁻¹ * x) ∂haarProb U = _
  simp only [hc]
  simp
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsContDiffArchMatrixExtensionOfSmooth
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

private theorem UpperTheory.exists_smooth_bump_units {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] (h : IsExpLieAlgebra (⊤ : Subgroup 𝔸ˣ) (⊤ : Submodule ℝ 𝔸))
    (κ : (⊤ : Subgroup 𝔸ˣ) → ℝ) (hs : h.IsSmoothFun (fun A => (κ A : ℂ)))
    (hc : HasCompactSupport κ) :
    ∃ β : 𝔸 → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Set.range (Units.val : 𝔸ˣ → 𝔸) ∧
      ∀ A : (⊤ : Subgroup 𝔸ˣ), β ((A : 𝔸ˣ) : 𝔸) = κ A := by
  classical
  let ι : (⊤ : Subgroup 𝔸ˣ) → 𝔸 := fun A => ((A : 𝔸ˣ) : 𝔸)
  have hemb : Topology.IsOpenEmbedding ι :=
    Units.isOpenEmbedding_val.comp (IsOpen.isOpenEmbedding_subtypeVal (by simp))
  have hinj := hemb.injective
  let β : 𝔸 → ℝ := Function.extend ι κ 0
  have hβ : ∀ A, β (ι A) = κ A := fun A => hinj.extend_apply _ _ A
  have hβ0 : ∀ x, x ∉ Set.range ι → β x = 0 := fun x hx =>
    Function.extend_apply' _ _ _ (by simpa using hx)
  have hCc : IsCompact (ι '' tsupport κ) := IsCompact.image hc hemb.continuous
  have hCcl := hCc.isClosed
  have hsupp : Function.support β ⊆ ι '' tsupport κ := by
    intro x hx
    by_cases hr : x ∈ Set.range ι
    · obtain ⟨A, rfl⟩ := hr
      refine ⟨A, subset_tsupport _ ?_, rfl⟩
      rw [Function.mem_support, ← hβ]
      exact hx
    · exact absurd (hβ0 x hr) hx
  have hts : tsupport β ⊆ ι '' tsupport κ := closure_minimal hsupp hCcl
  refine ⟨β, ?_, hCc.of_isClosed_subset (isClosed_tsupport β) hts, ?_, hβ⟩
  · rw [contDiff_iff_contDiffAt]
    intro X
    by_cases hX : X ∈ ι '' tsupport κ
    · obtain ⟨g, -, rfl⟩ := hX
      let e := expPartialHomeomorph ℝ 𝔸
      have hF := (h.isSmoothFun_iff.1 hs) g
      have hF' : ContDiff ℝ ∞ fun Y : (⊤ : Submodule ℝ 𝔸) => κ (g * h.expG Y) :=
        Complex.reCLM.contDiff.comp hF
      let gi : 𝔸 := (((g : 𝔸ˣ)⁻¹ : 𝔸ˣ) : 𝔸)
      have hm : ContDiff ℝ ∞ (fun x : 𝔸 => gi * x) := contDiff_const.mul contDiff_id
      have h1 : gi * ι g = 1 := Units.inv_mul _
      have hn : e.target ∈ nhds (gi * ι g) := by
        rw [h1]; exact e.open_target.mem_nhds (one_mem_expPartialHomeomorph_target ℝ _)
      have hl : ContDiffAt ℝ ∞
          (fun x => subspaceProj (⊤ : Submodule ℝ 𝔸) (e.symm (gi * x))) (ι g) :=
        (subspaceProj (⊤ : Submodule ℝ 𝔸)).contDiff.contDiffAt.comp _
          (((contDiffOn_expPartialHomeomorph_symm ℝ _).contDiffAt hn).comp _ hm.contDiffAt)
      refine (hF'.contDiffAt.comp _ hl).congr_of_eventuallyEq ?_
      filter_upwards [hm.continuous.continuousAt.preimage_mem_nhds hn] with x hx
      have hexp : NormedSpace.exp (e.symm (gi * x)) = gi * x := e.right_inv hx
      have key : ι (g * h.expG (subspaceProj (⊤ : Submodule ℝ 𝔸) (e.symm (gi * x)))) = x := by
        simp only [ι, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
        rw [subspaceProj_of_mem Submodule.mem_top, hexp, ← mul_assoc]
        simp [gi]
      rw [Function.comp_apply, ← hβ, key]
    · have hz : β =ᶠ[nhds X] fun _ => (0 : ℝ) := by
        filter_upwards [hCcl.isOpen_compl.mem_nhds hX] with x hx
        by_contra hne
        exact hx (hsupp hne)
      exact contDiffAt_const.congr_of_eventuallyEq hz
  · intro x hx
    obtain ⟨A, -, rfl⟩ := hts hx
    exact ⟨(A : 𝔸ˣ), rfl⟩

theorem UpperTheory.exists_contDiff_archMatrix_extension_of_smooth :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (κ : archGroup K n → ℝ),
        (isExpLieAlgebra K n).IsSmoothFun (fun A => (κ A : ℂ)) → HasCompactSupport κ →
        ∃ β : ArchMatrix K n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β ∧ HasCompactSupport β ∧
          tsupport β ⊆ Set.range (Units.val : ArchUnits K n → ArchMatrix K n) ∧
          ∀ A : archGroup K n, β ((A : ArchUnits K n) : ArchMatrix K n) = κ A := by
  intro K _ _ n κ hs hc
  exact UpperTheory.exists_smooth_bump_units (isExpLieAlgebra K n) κ hs hc
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

theorem UpperTheory.cuspDecay_tens_conv_real_smoothT :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (G1 K n)) [μ.IsHaarMeasure]
        (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (κ γ : TI K n) (e : TF K n)
        (U : Subgroup (AdelicGLn.integralFiniteGL K n)), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) →
        SmoothT κ → (∀ g, (κ g).im = 0) →
        (∀ u ∈ U, ∀ h, e ((u : AdelicGLn.FiniteAdelicGL K n) * h) = e h) → CuspDecay μ (tens (conv ν κ γ) e) := by
  intro K _ _ n hn μ _ ν _ κ γ e U hU hκ him he
  have hκeq : ∀ g, (((κ g).re : ℝ) : ℂ) = κ g := fun g => by
    apply Complex.ext <;> simp [him g]
  have hsm : (isExpLieAlgebra K n).IsSmoothFun (fun A => (((κ A).re : ℝ) : ℂ)) := by
    have h : (fun A => (((κ A).re : ℝ) : ℂ)) = fun g => κ g := funext hκeq
    rw [h]
    exact hκ
  have hcs : HasCompactSupport (fun g => (κ g).re) :=
    κ.hasCompactSupport.comp_left (g := Complex.re) rfl
  obtain ⟨β, hβ, hβc, hβu, hβκ⟩ := UpperTheory.exists_contDiff_archMatrix_extension_of_smooth K n (fun g => (κ g).re) hsm hcs
  let φ : archGroup K n ≃ₜ* ArchUnits K n :=
    { Subgroup.topEquiv (G := ArchUnits K n) with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let m : archGroup K n ≃ᵐ ArchUnits K n := φ.toHomeomorph.toMeasurableEquiv
  have hmφ : (m : archGroup K n → ArchUnits K n) = φ.toFun := rfl
  haveI hH : (Measure.map m ν).IsHaarMeasure := by
    rw [hmφ]
    exact φ.isHaarMeasure_map ν
  have hint : ∀ f : archGroup K n → ℂ,
      ∫ A, f A ∂ν = ∫ A : ArchUnits K n, f ⟨A, Subgroup.mem_top A⟩ ∂(Measure.map m ν) := by
    intro f
    rw [integral_map_equiv m (fun A : ArchUnits K n => f ⟨A, Subgroup.mem_top A⟩)]
    rfl
  have hkey := UpperTheory.tens_conv_eq_archConv K n hn (Measure.map m ν) ν hint β hβ.continuous hβc hβu κ γ e
    (fun A => by rw [hβκ A]; exact (hκeq A).symm)
  rw [hkey, ← UpperTheory.finAvg_tens_of_leftInvariant K n hn U hU γ e he]
  exact UpperTheory.cuspDecay_archConv_finAvg K n μ (Measure.map m ν) β hβ hβc hβu U hU (tens γ e)
