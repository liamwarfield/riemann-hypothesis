module

public import Development.AutomorphicArithmetic.WhittakerHecke.LiftOneRconvMemArchSmoothAndEnvelopingActionEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
public import Development.AutomorphicArithmetic.WhittakerHecke.LocGLEqLocalEmbeddingAndKGLEqIntegralGL

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ZCSuccEqAndEnvelopingActionCompatible
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem UpperTheory.polynomial_identity_coefficients_zero {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (v : Fin n → M)
    (h : ∀ u : ℂ, ∑ i : Fin n, u ^ (n - (i + 1)) • v i = 0) (i : Fin n) : v i = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have hp : (∑ j : Fin n, Polynomial.monomial (n - (j + 1)) (f (v j)) : Polynomial ℂ) = 0 := by
    apply Polynomial.funext
    intro u
    have := congrArg f (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, smul_eq_mul] at this
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, Polynomial.eval_zero]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p (n - (i + 1))) hp
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single i] at this
  · simpa using this
  · intro j _ hj
    rw [Finsupp.single_apply, if_neg]
    intro e
    apply hj
    have := j.2
    have := i.2
    exact Fin.ext (by omega)
  · simp

private theorem UpperTheory.polynomial_coefficients_compare {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (a : ℕ → M) (b : Fin n → M)
    (h : ∀ u : ℂ, ∑ i ∈ Finset.range (n + 1), u ^ (n - i) • a i = u ^ n • a 0 + ∑ i : Fin n, u ^ (n - (i + 1)) • b i)
    (i : Fin n) : a (i + 1) = b i := by
  rw [← sub_eq_zero]
  refine UpperTheory.polynomial_identity_coefficients_zero (fun i : Fin n => a (i + 1) - b i) (fun u => ?_) i
  have := h u
  rw [Finset.sum_range_succ', add_comm, Nat.sub_zero, add_right_inj,
    ← Fin.sum_univ_eq_sum_range (fun i => u ^ (n - (i + 1)) • a (i + 1)) n] at this
  simp only [smul_sub, Finset.sum_sub_distrib, this, sub_self]

theorem UpperTheory.zC_succ_eq_and_envelopingAction_compatible :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ),
          (∀ (τ : E →+* ℂ) (i : Fin n), UpperTheory.ConvolutionTheory.BW.zC E n τ (i + 1) = zc τ i) ∧
          ∀ (u : UC E n) (φ : GlobalTheory.CuspRep.Sm E n), (UpperTheory.V.Cm.uC E n u φ).1 = (uAct u (UpperTheory.V.Cm.smEq E n φ)).1 := by
  intro E _ _ _ n
  refine ⟨fun τ i => ?_, fun u φ => ?_⟩
  · obtain ⟨h0, h1⟩ := UpperTheory.ConvolutionTheory.BW.zSpec E n τ
    refine UpperTheory.polynomial_coefficients_compare (M := UC E n) (UpperTheory.ConvolutionTheory.BW.zC E n τ) (zc τ) (fun u => ?_) i
    rw [h0]
    exact (h1 u).symm.trans ((UpperTheory.ConvolutionTheory.Dp.capZc E n τ).2 u)
  · induction u using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; rfl
    | tmul c x =>
      have e : uAct (TensorProduct.tmul ℝ c x : UC E n) = c • uAction x :=
        (Algebra.TensorProduct.lift_tmul _ _ _ c x).trans (Algebra.smul_def c (uAction x)).symm
      rw [UpperTheory.V.Cm.uC_tmul, e]
      rfl
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, Submodule.coe_add, ha, hb]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.LiftOneRconvTensorModerateGrowthUniform
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HtProj
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

private theorem UpperTheory.ConvolutionTheory.Tf.height_centralSection_le (K : Type) [Field K] [NumberField K] (n : ℕ)
    (s : {r : ℝ // 0 < r}) {L : ℝ} (hL : 1 ≤ L) (h1 : (s : ℝ) ≤ L) (h2 : (s : ℝ)⁻¹ ≤ L) :
    AutomorphicForm.height (centralSection K n s) ≤ L ^ (2 * Fintype.card (InfinitePlace K)) := by
  set e : ℝ := ((n * Module.finrank ℚ K : ℝ))⁻¹ with he
  have he0 : 0 ≤ e := by positivity
  have he1 : e ≤ 1 := by
    rw [he, ← Nat.cast_mul]
    exact Nat.cast_inv_le_one _
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ L → x ^ e ≤ L := fun x hx hxL =>
    calc x ^ e ≤ L ^ e := Real.rpow_le_rpow hx hxL he0
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL he1
      _ = L := Real.rpow_one L
  refine height_diagUnits_posIdele_le (K := K) (n := n) (ρ := fun _ => (s : ℝ) ^ e)
    (fun _ => Real.rpow_pos_of_pos s.2 e) hL fun _ => ⟨key _ s.2.le h1, ?_⟩
  rw [← Real.inv_rpow s.2.le]
  exact key _ (inv_pos.2 s.2).le h2

theorem UpperTheory.ConvolutionTheory.Tf.htProj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ (C : ℝ) (c : ℕ), 1 ≤ C ∧ ∀ g : AdelicGLn.AdelicGL K n,
      AutomorphicForm.height (retractOne g : AdelicGLn.AdelicGL K n) ≤ C * AutomorphicForm.height g ^ c := by
  intro K _ _ n
  obtain ⟨D, N, -, hD⟩ := UpperTheory.adelicNorm_det_le_height_pow K n
  set m := 2 * Fintype.card (InfinitePlace K) with hm
  have hC : 1 ≤ heightConst K n := one_le_heightConst
  have hD1 : (1 : ℝ) ≤ max 1 D := le_max_left _ _
  refine ⟨heightConst K n * max 1 D ^ m, N * m + 1,
    one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hD1), fun g => ?_⟩
  have hg := one_le_height g
  have hb : ∀ x : AdelicGLn.AdelicGL K n, AutomorphicForm.height x = AutomorphicForm.height g →
      (detModule K n x : ℝ) ≤ max 1 D * AutomorphicForm.height g ^ N := fun x hx => by
    refine (hD x).trans ?_
    rw [hx]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have h2 : (detModule K n g : ℝ)⁻¹ ≤ max 1 D * AutomorphicForm.height g ^ N := by
    have := hb g⁻¹ (height_inv g)
    rwa [map_inv, Positive.coe_inv] at this
  have hz := UpperTheory.ConvolutionTheory.Tf.height_centralSection_le K n (detModule K n g)
    (one_le_mul_of_one_le_of_one_le hD1 (one_le_pow₀ hg)) (hb g rfl) h2
  rw [coe_retractOne]
  refine (height_mul_le _ _).trans ?_
  rw [height_inv]
  calc heightConst K n * AutomorphicForm.height g *
        AutomorphicForm.height (centralSection K n (detModule K n g))
      ≤ heightConst K n * AutomorphicForm.height g * (max 1 D * AutomorphicForm.height g ^ N) ^ m :=
        mul_le_mul_of_nonneg_left hz (by positivity)
    _ = _ := by ring
end

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem dm_induction {K : Type} [Field K] [NumberField K] {n : ℕ}
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (P : TI K n → Prop) (h0 : P 0)
    (hc : ∀ β₁ β₂ : TI K n, SmoothT β₁ → P (conv ν β₁ β₂))
    (ha : ∀ β β' : TI K n, SmoothT β → SmoothT β' → P β → P β' → P (β + β'))
    (β : TI K n) (hβ : SmoothT β) : P β := by
  obtain ⟨N, φ, ψ, h, e⟩ := dixmierMalliavin (isExpLieAlgebra K n) ν (fun g => β g) hβ β.hasCompactSupport
  let _ := (isExpLieAlgebra K n).chartedSpace
  let a : Fin N → TI K n := fun i => ⟨⟨φ i, (h i).1.continuous⟩, (h i).2.1⟩
  let b : Fin N → TI K n := fun i => ⟨⟨ψ i, (h i).2.2.1.continuous⟩, (h i).2.2.2⟩
  have has : ∀ i, SmoothT (a i) := fun i => (h i).1
  have h0s : SmoothT (0 : TI K n) :=
    (isExpLieAlgebra K n).mem_smoothFuns.1 (Submodule.zero_mem _)
  have key : ∀ s : Finset (Fin N), SmoothT (∑ i ∈ s, conv ν (a i) (b i)) ∧ P (∑ i ∈ s, conv ν (a i) (b i)) ∧
      ∀ x, (∑ i ∈ s, conv ν (a i) (b i)) x = ∑ i ∈ s, groupConv ν (φ i) (ψ i) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨by simpa using h0s, by simpa using h0, fun x => by simp⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hs := (UpperTheory.ConvolutionTheory.Tf.lactConv K n ν (a i) (b i) (has i)).1
      obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ hs
      refine ⟨(h6 _ ih.1).1, ha _ _ hs ih.1 (hc _ _ (has i)) ih.2.1, fun x => ?_⟩
      rw [Finset.sum_insert hi, CompactlySupportedContinuousMap.add_apply, ih.2.2, conv_apply]
      rfl
  have eβ : β = ∑ i, conv ν (a i) (b i) := by
    ext x
    rw [(key Finset.univ).2.2 x, ← Finset.sum_apply, ← e]
  rw [eβ]
  exact (key Finset.univ).2.1

private theorem lift_add {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (β β' : TI K n) (e : TF K n) (φ : LL μ) :
    liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens (β + β') e) φ) =
      liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens β e) φ) + liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens β' e) φ) := by
  funext g
  rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).2.2.1 β']
  simp only [liftOne, Pi.add_apply, rconv]
  rw [← integral_add (integrable_rconv _ μ _ φ _) (integrable_rconv _ μ _ φ _)]
  simp only [CompactlySupportedContinuousMap.add_apply, add_mul]

private theorem lift_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (e : TF K n) (φ : LL μ) :
    liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens (0 : TI K n) e) φ) = 0 := by
  have := lift_add hn μ 0 0 e φ
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem UpperTheory.liftOne_rconv_tensor_moderateGrowth_uniform :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure], Compat μ ν m →
          ∀ (β : TI K n) (e : TF K n), SmoothT β → ∃ N : ℕ, ∀ u : UC K n, ∃ B : ℝ, ∀ (φ : LL μ) (g : AdelicGLn.AdelicGL K n),
            ‖liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens (lact u β) e) φ) g‖ ≤ B * ‖φ‖ * AutomorphicForm.height g ^ N := by
  intro K _ _ n hn μ _ ν _ m _ hC β e hβ
  refine dm_induction ν (fun γ => ∃ N : ℕ, ∀ u : UC K n, ∃ B : ℝ, ∀ (φ : LL μ) (g : AdelicGLn.AdelicGL K n),
    ‖liftOne (rconv (rationalGLOne (K := K) (n := n)) μ (tens (lact u γ) e) φ) g‖ ≤ B * ‖φ‖ * AutomorphicForm.height g ^ N) ?_ ?_ ?_ β hβ
  · refine ⟨0, fun u => ⟨0, fun φ g => ?_⟩⟩
    have h0s : SmoothT (0 : TI K n) :=
      (isExpLieAlgebra K n).mem_smoothFuns.1 (Submodule.zero_mem _)
    obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ h0s
    have h := (h6 0 h0s).2 u
    rw [add_zero] at h
    rw [left_eq_add.1 h, lift_zero hn]
    simp
  · intro β₁ β₂ h₁
    obtain ⟨C, N, hCN⟩ := UpperTheory.ConvolutionTheory.C.polyBdAll K n μ (tens β₂ e)
    obtain ⟨D, c, hD, hDc⟩ := UpperTheory.ConvolutionTheory.Tf.htProj K n
    refine ⟨c * N, fun u => ?_⟩
    obtain ⟨_, -, hs, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ h₁
    obtain ⟨Y, hY, hYb, -⟩ := UpperTheory.ConvolutionTheory.Tf.htCompact K n
      ((fun a => (archP K n a : AdelicGLn.AdelicGL K n)) '' tsupport (lact u β₁))
      ((lact u β₁).hasCompactSupport.isCompact.image (continuous_subtype_val.comp continuous_archP))
    refine ⟨(∫ a, ‖lact u β₁ a‖ ∂ν) * (|C| * (heightConst K n * D * Y) ^ N), fun φ g => ?_⟩
    rw [(UpperTheory.ConvolutionTheory.Tf.lactConv K n ν β₁ β₂ h₁).2.1 u, liftOne,
      (UpperTheory.ConvolutionTheory.Tf.rconvSlice K n hn μ ν m hC (lact u β₁) β₂ e φ (hs u).1).1]
    have hint : Integrable (fun a => ‖lact u β₁ a‖) ν :=
      ((lact u β₁).continuous.integrable_of_hasCompactSupport (lact u β₁).hasCompactSupport).norm
    have hc1 : (1 : ℝ) ≤ heightConst K n := one_le_heightConst
    have hg := one_le_height g
    refine (norm_integral_le_of_norm_le (hint.mul_const
      (|C| * (heightConst K n * D * Y) ^ N * ‖φ‖ * AutomorphicForm.height g ^ (c * N)))
      (Filter.Eventually.of_forall fun a => ?_)).trans (by rw [integral_mul_const]; exact le_of_eq (by ring))
    rw [norm_mul]
    by_cases ha : lact u β₁ a = 0
    · simp [ha]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    set x : normOneGL (K := K) (n := n) := retractOne g * archP K n a with hx
    have hq0 : 0 ≤ PositivityTheory.Rg.Tf.Core.qht x := le_ciInf fun γ => (height_pos _).le
    have hq1 : PositivityTheory.Rg.Tf.Core.qht x ≤ AutomorphicForm.height (x : AdelicGLn.AdelicGL K n) := by
      refine (ciInf_le ⟨0, ?_⟩ 1).trans (le_of_eq (by simp))
      rintro _ ⟨γ, rfl⟩
      exact (height_pos _).le
    have hq2 : AutomorphicForm.height (x : AdelicGLn.AdelicGL K n) ≤
        heightConst K n * D * Y * AutomorphicForm.height g ^ c := by
      have h1 := height_mul_le (retractOne g : AdelicGLn.AdelicGL K n) (archP K n a : AdelicGLn.AdelicGL K n)
      have h2 := hYb _ ⟨a, subset_tsupport _ ha, rfl⟩
      refine h1.trans ((mul_le_mul (mul_le_mul_of_nonneg_left (hDc g) (by linarith)) h2 (height_pos _).le
        (by positivity)).trans (le_of_eq (by ring)))
    have h3 := pow_le_pow_left₀ hq0 (hq1.trans hq2) N
    rw [mul_pow, ← pow_mul] at h3
    refine (hCN φ x).trans ?_
    calc _ ≤ |C| * PositivityTheory.Rg.Tf.Core.qht x ^ N * ‖φ‖ := by
          first
            | exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hq0 N)) (norm_nonneg _)
            | (have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hq0 N)) (norm_nonneg φ); linarith)
      _ ≤ |C| * ((heightConst K n * D * Y) ^ N * AutomorphicForm.height g ^ (c * N)) * ‖φ‖ := by gcongr
      _ = _ := by ring
  · rintro γ γ' hγ hγ' ⟨N, hN⟩ ⟨N', hN'⟩
    refine ⟨max N N', fun u => ?_⟩
    obtain ⟨B, hB⟩ := hN u
    obtain ⟨B', hB'⟩ := hN' u
    refine ⟨|B| + |B'|, fun φ g => ?_⟩
    obtain ⟨_, -, -, -, -, -, h6, -⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n _ hγ
    rw [(h6 γ' hγ').2 u, lift_add hn, Pi.add_apply]
    have hg := one_le_height g
    have k : ∀ (b : ℝ) (M : ℕ), M ≤ max N N' → b * ‖φ‖ * AutomorphicForm.height g ^ M ≤
        |b| * ‖φ‖ * AutomorphicForm.height g ^ max N N' := fun b M hM =>
      mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self b) (norm_nonneg _)) (pow_le_pow_right₀ hg hM)
        (by positivity) (by positivity)
    refine (norm_add_le _ _).trans ((add_le_add ((hB φ g).trans (k B N (le_max_left _ _)))
      ((hB' φ g).trans (k B' N' (le_max_right _ _)))).trans (le_of_eq (by ring)))
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.TensorTestFunctionInvariantAndFiniteDimensionalS
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C

private theorem trEx {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (f : CompactlySupportedContinuousMap G ℂ) (a : G) :
    ∃ f' : CompactlySupportedContinuousMap G ℂ, ∀ g, f' g = f (a * g) :=
  ⟨⟨⟨fun g => f (a * g), f.continuous.comp (continuous_const.mul continuous_id)⟩,
    f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft a)⟩, fun _ => rfl⟩

theorem UpperTheory.tensorTestFunction_invariant_and_finiteDimensional_span :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (β : TI K n) (e : TF K n) (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)),
          U ≤ AdelicGLn.integralFiniteGL K n → IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)) → (∀ u ∈ U, ∀ h, e (u * h) = e h) →
          (∀ u ∈ U, ∀ z, tens β e ((MultiplicityOne.finProj K n u)⁻¹ * z) = tens β e z) ∧ (LeftFin β →
          FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) =>
            fun z : normOneGL (K := K) (n := n) => tens β e ((Subgroup.inclusion maxCompact_le_normOneGL k)⁻¹ * z)))) := by
  intro K _ _ n hn β e U hU hUo he
  have happ : ∀ (β : TI K n) (e : TF K n) x, tens β e x = tensFun β e x :=
    fun β e => (UpperTheory.ConvolutionTheory.Tf.tensApply K n hn β e).1
  refine ⟨fun u hu z => ?_, fun hβ => ?_⟩
  · have h1 : (MultiplicityOne.finProj K n u : AdelicGLn.AdelicGL K n) = finEmb K n u :=
      congrArg Subtype.val (MultiplicityOne.finProj_eq_finOne ⟨u, hU hu⟩)
    rw [happ, happ]
    unfold tensFun
    rw [Subgroup.coe_mul, Subgroup.coe_inv, h1, map_mul, map_mul, map_inv, map_inv, infPart_finEmb,
      finPart_finEmb, inv_one, one_mul, he _ (U.inv_mem hu)]
  · choose tb htb using trEx β
    choose te hte using trEx e
    let Kf := AdelicGLn.integralFiniteGL K n
    let V : Subgroup Kf := U.subgroupOf Kf
    have hV : IsOpen (V : Set Kf) := hUo.preimage continuous_subtype_val
    haveI : CompactSpace Kf := isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL K n)
    haveI : Finite (Kf ⧸ V) := Subgroup.quotient_finite_of_isOpen V hV
    let c : TI K n →ₗ[ℂ] (archGroup K n → ℂ) :=
      { toFun := fun f => f, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have hc : Function.Injective c := DFunLike.coe_injective
    let T : Submodule ℂ (TI K n) := Submodule.span ℂ (Set.range fun k : archCompact K n => tb k)
    haveI : FiniteDimensional ℂ T := by
      unfold LeftFin at hβ
      have hle : T.map c ≤ Submodule.span ℂ (Set.range fun k : archCompact K n =>
          fun g : archGroup K n => β ((k : archGroup K n) * g)) :=
        (Submodule.map_span _ _).le.trans (Submodule.span_mono (by
          rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, funext fun g => (htb k g).symm⟩))
      have := Submodule.finiteDimensional_of_le hle
      exact Module.Finite.equiv (Submodule.equivMapOfInjective _ hc _).symm
    let L : TF K n → TI K n →ₗ[ℂ] (normOneGL (K := K) (n := n) → ℂ) := fun e' =>
      { toFun := fun f => tens f e'
        map_add' := fun f g => by rw [(UpperTheory.ConvolutionTheory.Tf.tensApply K n hn f e').2.2.1]; rfl
        map_smul' := fun a f => by rw [((UpperTheory.ConvolutionTheory.Tf.tensApply K n hn f e').2.2.2.2 a).1]; rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := ⨆ q : Kf ⧸ V, T.map (L (te (q.out.1)⁻¹)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    let kf : Kf := ⟨finPart K n k.1, finPart_mem_integralFiniteGL k.2⟩
    let ka : archCompact K n := ⟨infPart K n k.1, archPart_mem_archCompact k.2⟩
    obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V kf
    refine Submodule.mem_iSup_of_mem (QuotientGroup.mk kf) ⟨_, Submodule.subset_span ⟨ka⁻¹, rfl⟩, ?_⟩
    rw [hv]
    funext z
    change tens (tb (infPart K n k.1)⁻¹) (te (finPart K n k.1 * v.1.1)⁻¹) z = tens β e _
    rw [happ, happ]
    unfold tensFun
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, map_mul, map_mul, map_inv, map_inv, hte,
      mul_inv_rev, mul_assoc, he _ (U.inv_mem (show v.1.1 ∈ U from v.2))]
    congr 1
    simp only [kbar, htb, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.FiniteTranslatesMatrixCoefficient
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ShiftMap
private def UpperTheory.Reformulated.B.ShiftMap.shift {G H : Type} [Group G] [Group H] (p : G →* H) :
    G →* ((H → ℂ) →ₗ[ℂ] (H → ℂ)) where
  toFun g := LinearMap.funLeft ℂ ℂ (fun z => (p g)⁻¹ * z)
  map_one' := by
    ext φ z
    simp [LinearMap.funLeft]
  map_mul' g h := by
    ext φ z
    simp [LinearMap.funLeft, mul_assoc]

private lemma UpperTheory.Reformulated.B.ShiftMap.shift_apply {G H : Type} [Group G] [Group H] (p : G →* H)
    (g : G) (φ : H → ℂ) (z : H) : UpperTheory.Reformulated.B.ShiftMap.shift p g φ z = φ ((p g)⁻¹ * z) := rfl

theorem UpperTheory.Reformulated.B.ShiftMap.finite_translates_matrix_coefficient :
    ∀ (G H : Type) [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
    [inst_3 : Group H] [inst_4 : TopologicalSpace H] [IsTopologicalGroup H] (p : G →* H),
    Continuous (⇑p : G → H) →
      ∀ (f : H → ℂ),
        Continuous f →
          FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f (((p : G → H) k)⁻¹ * z))) →
            ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ),
              Continuous (⇑ρ : G → Matrix (Fin d) (Fin d) ℂ) ∧
                ∀ (x : G →₀ ℂ),
                  (x.sum fun (k : G) (c : ℂ) ↦ c • (ρ : G → Matrix (Fin d) (Fin d) ℂ) k) =
                      (0 : Matrix (Fin d) (Fin d) ℂ) →
                    ∀ (z : H), (x.sum fun (k : G) (c : ℂ) ↦ c * f (((p : G → H) k)⁻¹ * z)) = (0 : ℂ) := by
  intro G H _ _ _ _ _ _ p hp f hf hfd
  set V : Submodule ℂ (H → ℂ) :=
    Submodule.span ℂ (Set.range fun (k : G) (z : H) ↦ f ((p k)⁻¹ * z)) with hV
  have hinv : ∀ g : G, ∀ φ ∈ V, UpperTheory.Reformulated.B.ShiftMap.shift p g φ ∈ V := by
    intro g
    have h : V ≤ V.comap (UpperTheory.Reformulated.B.ShiftMap.shift p g) := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨g * k, ?_⟩
      funext z
      simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc]
    exact fun φ hφ => h hφ
  have hcont : ∀ φ ∈ V, Continuous φ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨k, rfl⟩ := h
      exact hf.comp (continuous_const.mul continuous_id)
    | zero => exact continuous_zero
    | add a b _ _ ha hb => exact ha.add hb
    | smul c a _ ha => exact ha.const_smul c
  have hfV : f ∈ V := Submodule.subset_span ⟨1, by funext z; simp⟩
  let σ : G →* (V →ₗ[ℂ] V) :=
    { toFun := fun g => (UpperTheory.Reformulated.B.ShiftMap.shift p g).restrict (hinv g)
      map_one' := by
        ext φ z
        simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply]
      map_mul' := by
        intro g h
        ext φ z
        simp [UpperTheory.Reformulated.B.ShiftMap.shift_apply, mul_assoc] }
  have hσ : ∀ (g : G) (φ : V) (z : H), (σ g φ : H → ℂ) z = (φ : H → ℂ) ((p g)⁻¹ * z) :=
    fun _ _ _ => rfl
  let b := Module.finBasis ℂ V
  let e := LinearMap.toMatrixAlgEquiv b
  refine ⟨Module.finrank ℂ V, (e.toAlgHom.toRingHom.toMonoidHom).comp σ, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    have h1 : Continuous fun g : G => σ g (b j) := by
      refine Continuous.subtype_mk (continuous_pi fun z => ?_) _
      exact (hcont _ (b j).2).comp (hp.inv.mul continuous_const)
    have h2 : Continuous (b.coord i) := LinearMap.continuous_of_finiteDimensional _
    refine (h2.comp h1).congr fun g => ?_
    change _ = LinearMap.toMatrixAlgEquiv b (σ g) i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    rfl
  · intro x hx z
    have h1 : (x.sum fun k c => c • σ k) = 0 := by
      apply e.injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, ← hx, Finsupp.sum, Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul]
      rfl
    have h2 := congrArg (fun T : V →ₗ[ℂ] V => (T ⟨f, hfV⟩ : H → ℂ) z) h1
    simpa [Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply, hσ] using h2
end

theorem UpperTheory.finite_translates_matrix_coefficient :
    ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
          (p : G →* H), Continuous p → ∀ f : H → ℂ, Continuous f →
          FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : G => fun z : H => f ((p k)⁻¹ * z))) →
          ∃ (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), Continuous ρ ∧
            ∀ x : G →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 → ∀ z, (x.sum fun k c => c * f ((p k)⁻¹ * z)) = 0 :=
  _root_.UpperTheory.Reformulated.B.ShiftMap.finite_translates_matrix_coefficient
end

open NumberField

section SlopeTestRemainingChoices

open MeasureTheory IsDedekindDomain GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.BW UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
  {μ : Measure (normOneGL (K := E) (n := n))} [μ.IsHaarMeasure]

private theorem ampRep_open {φ : Sm E n} {U : Subgroup (AdelicGLn.FiniteAdelicGL E n)}
    (hU : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL E n))) (h : ∀ u ∈ U, GlobalTheory.CuspRep.finRep E n u φ = φ) :
    IsOpen {k | GlobalTheory.CuspRep.finRep E n k φ = φ} := by
  let S : Subgroup (GL (Fin n) (Af E)) :=
    { carrier := {k | GlobalTheory.CuspRep.finRep E n k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {k l} hk hl => by
        change GlobalTheory.CuspRep.finRep E n (k * l) φ = φ
        rw [map_mul, Module.End.mul_apply, hl, hk]
      inv_mem' := fun {k} hk => by
        change GlobalTheory.CuspRep.finRep E n k⁻¹ φ = φ
        conv_lhs => rw [← show GlobalTheory.CuspRep.finRep E n k φ = φ from hk, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel, map_one]
        rfl }
  exact Subgroup.isOpen_mono (H₁ := U) (H₂ := S) h hU

private theorem ampRep_fix {f : TG E n} {v : LL μ} {φ : Sm E n}
    (hφ : φ.1 = liftOne (rconv (rationalGLOne (K := E) (n := n)) μ f v)) {u : AdelicGLn.FiniteAdelicGL E n}
    (h : ∀ z, f ((MultiplicityOne.finProj E n u)⁻¹ * z) = f z) : GlobalTheory.CuspRep.finRep E n u φ = φ := by
  refine Subtype.ext (funext fun g => ?_)
  change φ.1 (g * finGL E n u) = φ.1 g
  have e : retractOne (finGL E n u) = MultiplicityOne.finProj E n u := by
    rw [← Fb.finEmb_eq]; rfl
  simp only [hφ, liftOne, retractOne_mul, e, rconv, mul_inv_rev, mul_assoc, h]

set_option synthInstance.maxHeartbeats 200000 in
private theorem ampRep_rep {f : TG E n} {v : LL μ} {φ : Sm E n}
    (hφ : φ.1 = liftOne (rconv (rationalGLOne (K := E) (n := n)) μ f v)) (hl : IsOpen {k | GlobalTheory.CuspRep.finRep E n k φ = φ})
    (hg : ∃ N : ℕ, ∀ u : Cm.UC E n, ∃ B : ℝ, ∀ g, ‖(Cm.uC E n u φ).1 g‖ ≤ B * AutomorphicForm.height g ^ N) :
    Rep μ (RR μ f v) φ := by
  refine ⟨⟨fun γ g => ?_, hl, hg⟩, fun t g => ?_, ?_⟩
  · rw [hφ]
    have hγ1 : AdelicGLn.diagonal E n γ ∈ normOneGL (K := E) (n := n) := rationalGL_le_normOneGL ⟨γ, rfl⟩
    have hγΓ : (⟨AdelicGLn.diagonal E n γ, hγ1⟩ : normOneGL (K := E) (n := n)) ∈ rationalGLOne (K := E) (n := n) := ⟨γ, rfl⟩
    exact (congrArg (rconv (rationalGLOne (K := E) (n := n)) μ f v) (retractOne_coe_mul ⟨_, hγ1⟩ g)).trans (rconv_mul_left _ μ f v hγΓ _)
  · rw [hφ]
    exact liftOne_centralSection_mul _ _ g
  · have := isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
    filter_upwards [integrated_ae_eq_rconvQ (rationalGLOne (K := E) (n := n)) μ f v] with y hy
    exact hy.trans (((congrFun hφ _).trans (liftOne_coe _ _)).trans
      ((rconvQ_mk _ μ f v _).symm.trans (congrArg (rconvQ _ μ f v) (Quotient.out_eq y)))).symm

private theorem ampRep_killed {f : TG E n} {v : LL μ} {d : ℕ} {ρ : KA E n → Matrix (Fin d) (Fin d) ℂ}
    (h : ∀ x : KA E n →₀ ℂ, (x.sum fun k c => c • ρ k) = 0 →
      ∀ z, (x.sum fun k c => c * f ((Subgroup.inclusion maxCompact_le_normOneGL k)⁻¹ * z)) = 0) :
    Killed ρ (liftOne (rconv (rationalGLOne (K := E) (n := n)) μ f v)) := by
  intro x hx g
  have e : ∀ k : KA E n, retractOne (g * (k : GA E n)) =
      retractOne g * Subgroup.inclusion maxCompact_le_normOneGL k :=
    fun k => retractOne_mul_coe g (Subgroup.inclusion maxCompact_le_normOneGL k)
  simp only [Finsupp.sum, liftOne, e, rconv, ← integral_const_mul]
  rw [← integral_finsetSum _ fun k _ => (integrable_rconv _ μ f v _).const_mul _]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  have := h x hx ((retractOne g)⁻¹ * y)
  simp only [Finsupp.sum] at this
  simp only [mul_inv_rev, mul_assoc (Subgroup.inclusion maxCompact_le_normOneGL _)⁻¹, ← mul_assoc (x _),
    ← Finset.sum_mul, this, zero_mul, Pi.zero_apply]

end SlopeTestRemainingChoices

open MeasureTheory IsDedekindDomain GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.V in
theorem UpperTheory.ConvolutionTheory.BW.ampRep :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.AmpRep E := by
  intro E _ _ _ n μ _ 𝔞 hn
  obtain ⟨m, _, hm⟩ := (Tf.compatEx E n hn).2.1 μ 𝔞.ν
  have hUc : IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL E n)) :=
    (AdelicGLn.isCompact_integralFiniteGL E n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen) 𝔞.le
  obtain ⟨e, he, heP⟩ := Tf.prjFix E n μ m 𝔞.U 𝔞.isOpen hUc
  have heU : ∀ u ∈ 𝔞.U, ∀ h, e (u * h) = e h := fun u hu h => by
    rw [he, he]
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    exact if_congr (𝔞.U.mul_mem_cancel_left hu) rfl rfl
  have hR : ∀ β, Oinf μ 𝔞.ν β ∘L prj (fixF μ 𝔞.U) = RR μ (tens β e) := fun β => by
    rw [Tf.rrTens E n hn μ 𝔞.ν m hm, heP]
  have hder := UpperTheory.liftOne_rconv_mem_archSmooth_and_envelopingAction_eq E n hn μ 𝔞.ν m hm
  have huC : ∀ β, SmoothT β → ∀ (v : LL μ) (φ : Sm E n), φ.1 = liftOne (rconv (rationalGLOne (K := E) (n := n)) μ (tens β e) v) →
      ∀ u, (Cm.uC E n u φ).1 = liftOne (rconv (rationalGLOne (K := E) (n := n)) μ (tens (lact u β) e) v) := fun β hβ v φ hφ u => by
    obtain ⟨h, hh⟩ := hder β e hβ v
    rw [(UpperTheory.zC_succ_eq_and_envelopingAction_compatible E n).2, ← hh u]
    exact congrArg (fun ψ => (uAct u ψ).1) (Subtype.ext hφ)
  have hfix : ∀ β (v : LL μ) (φ : Sm E n), φ.1 = liftOne (rconv (rationalGLOne (K := E) (n := n)) μ (tens β e) v) →
      ∀ u ∈ 𝔞.U, GlobalTheory.CuspRep.finRep E n u φ = φ := fun β v φ hφ u hu =>
    ampRep_fix hφ ((UpperTheory.tensorTestFunction_invariant_and_finiteDimensional_span E n hn β e 𝔞.U 𝔞.le 𝔞.isOpen heU).1 u hu)
  have hrep : ∀ β, SmoothT β → ∀ (v : LL μ) (φ : Sm E n), φ.1 = liftOne (rconv (rationalGLOne (K := E) (n := n)) μ (tens β e) v) →
      Rep μ ((Oinf μ 𝔞.ν β ∘L prj (fixF μ 𝔞.U)) v) φ := fun β hβ v φ hφ => by
    rw [hR]
    obtain ⟨N, hN⟩ := UpperTheory.liftOne_rconv_tensor_moderateGrowth_uniform E n hn μ 𝔞.ν m hm β e hβ
    refine ampRep_rep hφ (ampRep_open 𝔞.isOpen (hfix β v φ hφ)) ⟨N, fun u => ?_⟩
    obtain ⟨B, hB⟩ := hN u
    exact ⟨B * ‖v‖, fun g => by rw [huC β hβ v φ hφ]; exact hB v g⟩
  let L : LL μ →ₗ[ℂ] Sm E n :=
    { toFun := fun v => ⟨liftOne (rconv (rationalGLOne (K := E) (n := n)) μ (tens 𝔞.a₀ e) v),
        (Cm.sm_eq E n).ge (hder 𝔞.a₀ e 𝔞.smooth v).1⟩
      map_add' := fun v w => Subtype.ext (funext fun g => rconv_add _ μ _ v w _)
      map_smul' := fun c v => Subtype.ext (funext fun g => rconv_smul _ μ _ c v _) }
  obtain ⟨d, ρ, hρ, hk⟩ := UpperTheory.finite_translates_matrix_coefficient (KA E n) (normOneGL (K := E) (n := n)) (Subgroup.inclusion maxCompact_le_normOneGL)
    (continuous_subtype_val.subtype_mk _) (tens 𝔞.a₀ e) (tens 𝔞.a₀ e).continuous
    ((UpperTheory.tensorTestFunction_invariant_and_finiteDimensional_span E n hn 𝔞.a₀ e 𝔞.U 𝔞.le 𝔞.isOpen heU).2 𝔞.fin)
  obtain ⟨N, hN⟩ := UpperTheory.liftOne_rconv_tensor_moderateGrowth_uniform E n hn μ 𝔞.ν m hm 𝔞.a₀ e 𝔞.smooth
  refine ⟨⟨d, ρ, hρ⟩, N, L, fun v => ⟨hrep _ 𝔞.smooth v _ rfl, ampRep_killed hk, fun w hw k hk => ?_⟩,
    fun u => ?_, fun x v => ?_⟩
  · refine hfix _ v _ rfl (locGL E n w k) (𝔞.max w hw ⟨k, ?_, ((UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL E n w).1 k).symm⟩)
    rw [← (UpperTheory.locGL_eq_localEmbedding_and_KGL_eq_integralGL E n w).2]
    exact hk
  · obtain ⟨B, hB⟩ := hN u
    exact ⟨B, fun v g => by rw [huC _ 𝔞.smooth v (L v) rfl]; exact hB v g⟩
  · obtain ⟨_, -, hs, -⟩ := Tf.lactSpec E n 𝔞.a₀ 𝔞.smooth
    refine hrep _ (hs _).1 v _ ?_
    rw [← huC _ 𝔞.smooth v (L v) rfl, ← (UpperTheory.zC_succ_eq_and_envelopingAction_compatible E n).1, zop, evZ, MvPolynomial.aeval_X]
