module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import GroundTheory.AutomorphicForms.TraceNormComp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.AvSpec
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.avSpec :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (F : Flow H), (∀ t, ContinuousLinearMap.adjoint (F.U t) = F.U (-t)) ∧ Integrable wR ∧ (∫ t, ‖wR t‖ = 1) ∧ ∀ ψ : ℝ → ℂ, Integrable ψ →
      (∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h) ∧ ‖F.av ψ‖ ≤ ∫ t, ‖ψ t‖ ∧
      ContinuousLinearMap.adjoint (F.av ψ) = F.av (fun t => conj (ψ (-t))) ∧ F.rev.av ψ = F.av (fun t => ψ (-t)) ∧
      ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F' : Flow G) (Y : H →L[ℂ] G), (∀ t h, Y (F.U t h) = F'.U t (Y h)) → Y ∘L F.av ψ = F'.av ψ ∘L Y := by
  intro H _ _ _ F
  have hin : ∀ t x y, ⟪F.U t x, F.U t y⟫_ℂ = ⟪x, y⟫_ℂ := fun t x y =>
    (⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y
  have hadj : ∀ t x y, ⟪F.U t x, y⟫_ℂ = ⟪x, F.U (-t) y⟫_ℂ := fun t x y => by
    rw [← hin t x, ← F.add, add_neg_cancel, F.zero]
  have hw : Integrable wR := by
    refine (integrable_indicator_iff measurableSet_Iic).2 ?_
    exact (integrableOn_exp_Iic 0).ofReal
  have spec : ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (F : Flow G) (ψ : ℝ → ℂ), Integrable ψ →
      ∀ h, Integrable (fun t => ψ t • F.U t h) ∧ F.av ψ h = ∫ t, ψ t • F.U t h := by
    intro G _ _ _ F ψ hψ
    have hi : ∀ h, Integrable (fun t => ψ t • F.U t h) := fun h =>
      hψ.smul_bdd ‖h‖ (F.cont h).aestronglyMeasurable (Eventually.of_forall fun t => (F.norm t h).le)
    let A : G →ₗ[ℂ] G :=
      { toFun := fun h => ∫ t, ψ t • F.U t h
        map_add' := fun x y => by simp only [map_add (f := _), smul_add]; exact integral_add (hi x) (hi y)
        map_smul' := fun c x => by simp only [map_smul, RingHom.id_apply, smul_comm _ c]; exact integral_smul c _ }
    have hb : ∀ h, ‖A h‖ ≤ (∫ t, ‖ψ t‖) * ‖h‖ := fun h => by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      simp only [norm_smul, F.norm]
      exact integral_mul_const _ _
    exact fun h => ⟨hi h, Classical.epsilon_spec (p := fun A : G →L[ℂ] G => ∀ h, A h = ∫ t, ψ t • F.U t h)
      ⟨A.mkContinuous _ hb, fun _ => rfl⟩ h⟩
  refine ⟨fun t => ?_, hw, ?_, fun ψ hψ => ⟨spec F ψ hψ, ?_, ?_, ?_, ?_⟩⟩
  · exact ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => by rw [hadj, neg_neg]).symm
  · have : (fun t => ‖wR t‖) = (Iic (0 : ℝ)).indicator Real.exp := by
      funext t
      by_cases h : t ∈ Iic (0 : ℝ) <;> simp [wR, h]
    rw [this, integral_indicator measurableSet_Iic, integral_exp_Iic_zero]
  · refine ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _) fun h => ?_
    rw [(spec F ψ hψ h).2]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_smul, F.norm]
    exact integral_mul_const _ _
  · have hψ' : Integrable fun t => conj (ψ (-t)) := (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hψ.comp_neg
    refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_).symm
    rw [(spec F ψ hψ y).2, (spec F _ hψ' x).2, ← integral_inner (spec F ψ hψ y).1, ← inner_conj_symm,
      ← integral_inner (spec F _ hψ' x).1, ← integral_conj, ← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_neg, inner_smul_right, map_mul, Complex.conj_conj, inner_conj_symm, hadj]
  · ext h
    rw [(spec F.rev ψ hψ h).2, (spec F _ hψ.comp_neg h).2, ← integral_neg_eq_self]
    simp [Flow.rev]
  · intro G _ _ _ F' Y hY
    ext h
    simp only [ContinuousLinearMap.comp_apply]
    rw [(spec F ψ hψ h).2, (spec F' ψ hψ _).2, ← Y.integral_comp_comm (spec F ψ hψ h).1]
    simp only [map_smul, hY]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutSpec
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutSpec :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (s : Set ℝ), MeasurableSet s → ∀ u : L V, ∀ᵐ x : ℝ, cut V s u x = s.indicator u x := by
  intro V _ _ _ _ s hs
  have hm : ∀ u : L V, MemLp (s.indicator (u : ℝ → V)) 2 volume := fun u => (Lp.memLp u).indicator hs.nullMeasurableSet
  let A : L V →ₗ[ℂ] L V :=
    { toFun := fun u => (hm u).toLp _
      map_add' := fun u v => Lp.ext (by
        filter_upwards [(hm (u + v)).coeFn_toLp, (hm u).coeFn_toLp, (hm v).coeFn_toLp, Lp.coeFn_add u v,
          Lp.coeFn_add ((hm u).toLp _) ((hm v).toLp _)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [indicator_of_mem hx]; exact h4
        · simp [hx])
      map_smul' := fun c u => Lp.ext (by
        filter_upwards [(hm (c • u)).coeFn_toLp, (hm u).coeFn_toLp, Lp.coeFn_smul c u,
          Lp.coeFn_smul c ((hm u).toLp _)] with x h1 h2 h4 h5
        rw [h1, RingHom.id_apply, h5, Pi.smul_apply, h2]
        by_cases hx : x ∈ s <;> simp [hx, h4]) }
  have hb : ∀ u, ‖A u‖ ≤ 1 * ‖u‖ := fun u => by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [(hm u).coeFn_toLp] with x h
    show ‖((hm u).toLp _ : ℝ → V) x‖ ≤ _
    rw [h]
    exact norm_indicator_le_norm_self _ _
  exact Classical.epsilon_spec (p := fun C : L V →L[ℂ] L V => ∀ u, ∀ᵐ x : ℝ, C u x = s.indicator u x)
    ⟨A.mkContinuous 1 hb, fun u => (hm u).coeFn_toLp⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TrWeak
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.trWeak :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type} (l : Filter ι) (A : ι → H →L[ℂ] H) (A₀ Z : H →L[ℂ] H), IsTraceClass Z → (∀ i, ‖A i‖ ≤ 1) →
      (∀ x y, Tendsto (fun i => ⟪x, A i y⟫_ℂ) l (𝓝 ⟪x, A₀ y⟫_ℂ)) → Tendsto (fun i => trace (A i ∘L Z)) l (𝓝 (trace (A₀ ∘L Z))) := by
  intro H _ _ _ ι l A A₀ Z hZ hA hw
  obtain ⟨S, T, hS, hT, rfl⟩ := hZ.exists_comp
  let b := stdHilbertBasis ℂ H
  have e : ∀ B : H →L[ℂ] H, trace (B ∘L S ∘L T) = ∑' m, ⟪ContinuousLinearMap.adjoint T (b m), B (S (b m))⟫_ℂ := fun B => by
    have h1 : trace ((B ∘L S) ∘L T) = trace (T ∘L (B ∘L S)) := trace_comp_comm_of_isHilbertSchmidt (hS.comp_left B) hT
    have h2 := ((isTraceClass_comp hT (hS.comp_left B)).hasSum_trace b).tsum_eq
    simp only [ContinuousLinearMap.adjoint_inner_left]
    exact h1.trans h2.symm
  simp only [e]
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖ContinuousLinearMap.adjoint T (b m)‖ ^ 2 + ‖S (b m)‖ ^ 2)
    ((hT.adjoint.hasSum_norm_sq b).summable.add (hS.hasSum_norm_sq b).summable) (fun m => hw _ _) (Eventually.of_forall fun i m => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  have h3 : ‖A i (S (b m))‖ ≤ ‖S (b m)‖ := by simpa using (A i).le_of_opNorm_le (hA i) (S (b m))
  nlinarith [sq_nonneg (‖ContinuousLinearMap.adjoint T (b m)‖ - ‖S (b m)‖), norm_nonneg (ContinuousLinearMap.adjoint T (b m)),
    norm_nonneg (S (b m)), mul_le_mul_of_nonneg_left h3 (norm_nonneg (ContinuousLinearMap.adjoint T (b m)))]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.FourAe
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.fourAe :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (u : L V), Integrable (u : ℝ → V) → ∀ᵐ ξ : ℝ, Lp.fourierTransformₗᵢ ℝ V u ξ = 𝓕 (u : ℝ → V) ξ := by
  intro V _ _ _ _ u hu
  have hc : Continuous (𝓕 (u : ℝ → V)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hu
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hc.locallyIntegrable ?_
  intro g hg hgc
  have hs : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) := hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let φ : SchwartzMap ℝ ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  have hφ : ∀ x, φ x = (g x : ℂ) := fun x => rfl
  have h1 := congrArg (fun T : TemperedDistribution ℝ V => T φ) (Lp.fourier_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h1
  have h2 := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar) (L := innerₗ ℝ) (μ := volume) (ν := volume) (f := (φ : ℝ → ℂ)) (g := (u : ℝ → V))
    Real.continuous_fourierChar (by fun_prop) φ.integrable hu
  have h3 : (innerₗ ℝ).flip = innerₗ ℝ := by ext; simp
  rw [h3] at h2
  have e : ∀ (x : ℝ) (v : V), g x • v = φ x • v := fun x v => by rw [hφ, Complex.coe_smul]
  simp only [e]
  exact h1.symm.trans h2
end
