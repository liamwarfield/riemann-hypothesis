module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistExAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.NormLeOfSq
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

private theorem norm_le_of_sq {t B : ℝ} (ht : 0 ≤ t) (hB : 0 ≤ B) (h : t ^ 2 ≤ B * t) : t ≤ B := by
  rcases ht.eq_or_lt with h0 | h0
  · rw [← h0]; exact hB
  · exact le_of_mul_le_mul_right (by nlinarith) h0

theorem UpperTheory.ConvolutionTheory.K.kvBd :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n),
      (PolyBd μ a → ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ x, ‖kv μ a x‖ ≤ C * qht x ^ N) ∧
      (CuspDecay μ a → ∀ N' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Pc μ (kv μ a x)‖ ≤ C * (qht x ^ N')⁻¹) := by
  intro K _ _ n μ _ a
  have hq : ∀ x : G1 K n, 0 ≤ qht x := fun x => zero_le_one.trans ((qhtBasic K n).1 x)
  refine ⟨?_, ?_⟩
  · rintro ⟨C, N, h⟩
    refine ⟨max C 0, N, le_max_right _ _, fun x => ?_⟩
    have hp : 0 ≤ qht x ^ N := pow_nonneg (hq x) N
    refine norm_le_of_sq (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp) ?_
    have h1 := h (kv μ a x) x
    rw [← inner_kv, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖kv μ a x‖ ^ 2 ≤ C * qht x ^ N * ‖kv μ a x‖ := by simpa using h1
    refine h2.trans ?_
    gcongr
    exact le_max_left _ _
  · intro hc N'
    obtain ⟨C, h⟩ := hc N'
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    have hp : 0 ≤ (qht x ^ N')⁻¹ := inv_nonneg.2 (pow_nonneg (hq x) N')
    refine norm_le_of_sq (norm_nonneg _) (mul_nonneg (le_max_right _ _) hp) ?_
    have hm : Pc μ (kv μ a x) ∈ cuspidalL2 μ := Submodule.starProjection_apply_mem _ _
    have h1 := h (Pc μ (kv μ a x)) hm x
    have h0 : ⟪kv μ a x - Pc μ (kv μ a x), Pc μ (kv μ a x)⟫_ℂ = 0 :=
      Submodule.starProjection_inner_eq_zero _ _ hm
    rw [inner_sub_left, sub_eq_zero] at h0
    rw [← inner_kv, h0, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖Pc μ (kv μ a x)‖ ^ 2 ≤ C * (qht x ^ N')⁻¹ * ‖Pc μ (kv μ a x)‖ := by simpa using h1
    refine h2.trans ?_
    gcongr
    exact le_max_left _ _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KerId
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RconvEqIntegralKernel
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

section Kernel

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ]

private theorem hasCompactSupport_kernel (f : CompactlySupportedContinuousMap G ℂ) (a : G) :
    HasCompactSupport fun q => quotientKernel Γ f (mk Γ a, q) := by
  have hT : T2Space (RightCosetSpace Γ) := RightCosetSpace.t2Space Γ
  have hC : IsCompact (mk Γ '' ((a * ·) '' tsupport (f : G → ℂ))) :=
    (f.hasCompactSupport.isCompact.image (continuous_const_mul a)).image (continuous_mk Γ)
  refine HasCompactSupport.intro hC fun q hq => ?_
  obtain ⟨b, rfl⟩ := mk_surjective Γ q
  rw [quotientKernel_mk]
  refine finsum_eq_zero_of_forall_eq_zero fun γ => ?_
  by_contra h
  refine hq ⟨(γ : G) * b, ⟨a⁻¹ * γ * b, subset_tsupport _ h, ?_⟩, mk_mul_of_mem γ.2 b⟩
  simp [mul_assoc]

private theorem rconv_eq_integral_kernel (μ : Measure G) [μ.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts μ] (f : CompactlySupportedContinuousMap G ℂ)
    (φ : Lp ℂ 2 (quotientMeasure Γ μ)) (a : G) :
    rconv Γ μ f φ a = ∫ q, φ q * quotientKernel Γ f (mk Γ a, q) ∂quotientMeasure Γ μ := by
  have hint : Integrable (fun y => φ (mk Γ y) * f (a⁻¹ * y)) μ := by
    simpa only [mul_comm] using integrable_rconv Γ μ f φ a
  have h1 : rconv Γ μ f φ a = ∫ y, φ (mk Γ y) * f (a⁻¹ * y) ∂μ := by
    unfold rconv
    simp only [mul_comm]
  rw [h1, integral_mul_eq_integral_mul_automorphize μ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  obtain ⟨b, rfl⟩ := mk_surjective Γ y
  dsimp only
  rw [quotientKernel_mk]
  congr 1
  change ∑' γ : Γ, f (a⁻¹ * (γ • b)) = _
  simp_rw [Subgroup.smul_def, smul_eq_mul, ← mul_assoc]
  exact tsum_eq_finsum (finite_support_automorphicKernel Γ f (a, b))

end Kernel

theorem UpperTheory.ConvolutionTheory.K.kvAe :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n) (x : G1 K n),
      (kv μ f x : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => (starRingEnd ℂ) (quotientKernel (Gam K n) f (mk (Gam K n) x, y)) := by
  intro K _ _ n μ _ f x
  have hc : Continuous fun q => quotientKernel (Gam K n) f (mk (Gam K n) x, q) :=
    (continuous_quotientKernel (Gam K n) f).comp (continuous_const.prodMk continuous_id)
  have hcs := hasCompactSupport_kernel (Gam K n) f x
  have hm : MemLp (fun q => (starRingEnd ℂ) (quotientKernel (Gam K n) f (mk (Gam K n) x, q))) 2
      (quotientMeasure (Gam K n) μ) :=
    (Complex.continuous_conj.comp hc).memLp_of_hasCompactSupport
      (hcs.comp_left (g := starRingEnd ℂ) (map_zero _))
  have hkw : kv μ f x = hm.toLp _ := by
    refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, rconv_eq_integral_kernel, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with q hq
    rw [hq, RCLike.inner_apply', Complex.conj_conj, mul_comm]
  rw [hkw]
  exact hm.coeFn_toLp
end

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.kerId :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f a g : CC K n) (M : L2 μ →L[ℂ] L2 μ),
      Rop μ f = Rop μ a ∘L M ∘L Rop μ g → ∀ x y : G1 K n,
        ∑ᶠ γ : Gam K n, f (x⁻¹ * (γ : G1 K n) * y) = ⟪kv μ a x, M (kv μ (ccStar g) y)⟫_ℂ := by
  intro K _ _ n μ _ f a g M hf x y
  haveI := Reduction.isFiniteMeasure_quotientMeasure (K := K) (n := n) μ
  have ext : ∀ u w : RightCosetSpace (Gam K n) → ℂ, Continuous u → Continuous w →
      u =ᵐ[quotientMeasure (Gam K n) μ] w → ∀ z : G1 K n, u (mk _ z) = w (mk _ z) := by
    intro u w hu hw h z
    have h1 := MeasureTheory.QuasiMeasurePreserving.ae (quasiMeasurePreserving_mk (Gam K n) μ) h
    exact congrFun ((hu.comp (continuous_mk _)).ae_eq_iff_eq μ (hw.comp (continuous_mk _)) |>.1 h1) z
  have s1 : ∀ φ : L2 μ, rconv (Gam K n) μ f φ x = rconv (Gam K n) μ a (M (Rop μ g φ)) x := by
    intro φ
    have e : Rop μ f φ = Rop μ a (M (Rop μ g φ)) := by rw [hf]; rfl
    refine ext _ _ (continuous_rconvQ _ μ f φ) (continuous_rconvQ _ μ a _) ?_ x
    have a1 := integrated_ae_eq_rconvQ (Gam K n) μ f φ
    have a2 := integrated_ae_eq_rconvQ (Gam K n) μ a (M (Rop μ g φ))
    change (Rop μ f φ : _ → ℂ) =ᵐ[_] _ at a1
    change (Rop μ a (M (Rop μ g φ)) : _ → ℂ) =ᵐ[_] _ at a2
    rw [e] at a1
    exact a1.symm.trans a2
  have s2 : kv μ f x = Rop μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x)) := by
    refine ext_inner_right ℂ fun φ => ?_
    rw [inner_kv, s1, ← ropAdj, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, inner_kv]
  have a3 := integrated_ae_eq_rconvQ (Gam K n) μ (ccStar g) (ContinuousLinearMap.adjoint M (kv μ a x))
  change (Rop μ (ccStar g) _ : _ → ℂ) =ᵐ[_] _ at a3
  rw [← s2] at a3
  have s3 := ext _ _ (Complex.continuous_conj.comp ((continuous_quotientKernel (Gam K n) f).comp (Continuous.prodMk_right (mk _ x))))
    (continuous_rconvQ _ μ (ccStar g) _) ((kvAe K n μ f x).symm.trans a3) y
  simp only [Function.comp_apply, quotientKernel_mk, rconvQ_mk] at s3
  rw [← inner_kv, ContinuousLinearMap.adjoint_inner_right] at s3
  rw [← inner_conj_symm, ← s3, starRingEnd_self_apply]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Imports
open MeasureTheory NumberField PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.K

theorem UpperTheory.ConvolutionTheory.K.g0 :
    G0 := by
  refine ⟨fun F E _ _ _ _ _ _ σ _ n _ μ _ => ?_, fun F _ _ n μ _ g => ?_⟩
  · obtain ⟨θ, h⟩ := galTwistEx E n μ σ.toRingEquiv
    exact ⟨θ, fun g => by rw [galAdEq]; exact h g⟩
  · rw [galAdEq]
    ext i j : 2
    exact ((adBasic F).2.1 _).symm
end
