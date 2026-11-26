module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.KillEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpecAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TrOnBot
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwInt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SmoothDecay
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClass
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspTrBand

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.OneSide
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

section SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem cheb_cont (η : ℝ) (m : ℕ) : Continuous (cheb η m) := by
  unfold cheb
  exact (Polynomial.continuous _).comp (by fun_prop)

private theorem ev_cheb {K : Type} [Field K] [NumberField K] {n : ℕ} (ψ : PR K n →+* (H →L[ℂ] H))
    (hc : ∀ c : ℂ, ψ (C (C c)) = c • 1) (A : H →L[ℂ] H) (hA : ψ (C (X none)) = A) (hsa : IsSelfAdjoint A)
    (η : ℝ) (m : ℕ) : ψ (chebP η m) = fcalc (cheb η m) A := by
  have e1 : fcalc (fun x : ℝ => 2 * x / η - 1) A = ((2 / η : ℝ) : ℂ) • A - 1 := by
    unfold fcalc
    have : (fun x : ℝ => 2 * x / η - 1) = fun x : ℝ => (2 / η) • x - 1 := by
      funext x; simp only [smul_eq_mul]; ring
    rw [this, cfc_sub _ _ A, cfc_smul (2 / η) (fun x : ℝ => x) A, cfc_id' ℝ A, cfc_const_one ℝ A]
    rfl
  have e2 : fcalc (cheb η m) A =
      Polynomial.aeval (((2 / η : ℝ) : ℂ) • A - 1) (Polynomial.Chebyshev.T ℝ m) := by
    rw [← e1]
    unfold fcalc
    rw [← cfc_polynomial (R := ℝ) (Polynomial.Chebyshev.T ℝ m) (cfc (fun x : ℝ => 2 * x / η - 1) A),
      ← cfc_comp' (fun y => (Polynomial.Chebyshev.T ℝ m).eval y) (fun x : ℝ => 2 * x / η - 1) A]
    rfl
  let φ : MvPolynomial (Option (Ix K n)) ℂ →ₐ[ℤ] (H →L[ℂ] H) := (ψ.comp C).toIntAlgHom
  have e3 : ψ (chebP η m) = φ (Polynomial.aeval (C ((2 / η : ℝ) : ℂ) * X none - 1 : MvPolynomial (Option (Ix K n)) ℂ)
      (Polynomial.Chebyshev.T ℤ m)) := by
    unfold chebP
    rw [← Polynomial.Chebyshev.map_T (algebraMap ℤ ℂ), Polynomial.aeval_map_algebraMap]
    rfl
  have e4 : φ (C ((2 / η : ℝ) : ℂ) * X none - 1) = ((2 / η : ℝ) : ℂ) • A - 1 := by
    rw [map_sub, map_mul, map_one]
    show ψ (C (C _)) * ψ (C (X none)) - 1 = _
    rw [hc, hA, smul_mul_assoc, one_mul]
  rw [e3, ← Polynomial.aeval_algHom_apply, e4, e2, ← Polynomial.Chebyshev.map_T (algebraMap ℤ ℝ),
    Polynomial.aeval_map_algebraMap]

private theorem fcalc_norm_le (A : H →L[ℂ] H) (h0 : 0 ≤ A) (h1 : ‖A‖ ≤ 1) (φ : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ x ∈ Set.Icc (0 : ℝ) 1, |φ x| ≤ c) : ‖fcalc φ A‖ ≤ c := by
  unfold fcalc
  refine norm_cfc_le hc fun x hx => h x ⟨spectrum_nonneg_of_nonneg h0 hx, ?_⟩
  rcases subsingleton_or_nontrivial (H →L[ℂ] H) with hs | hs
  · simp [spectrum.of_subsingleton] at hx
  · exact (le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans h1)

private theorem off_est (A Q W P : H →L[ℂ] H) (h0 : 0 ≤ A) (h1 : ‖A‖ ≤ 1) (hQ : Commute A Q) (hW : Commute W P)
    (hP : ‖1 - P‖ ≤ 1) (η c : ℝ) (hc : 0 ≤ c) (t χ : ℝ → ℝ) (ht : Continuous t) (hχ : Continuous χ)
    (ht1 : ∀ x ∈ Set.Icc 0 η, |t x| ≤ 1) (ht2 : ∀ x ∈ Set.Icc (0 : ℝ) 1, |t x| ≤ c)
    (hχ1 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχ2 : ∀ x ≥ η, χ x = 1) :
    ‖fcalc t A * Q * W * (1 - P)‖ ≤ ‖W‖ * (‖Q‖ + c * ‖Q * (fcalc χ A * (1 - P))‖) := by
  have hsa : IsSelfAdjoint A := isSelfAdjoint_of_nonneg h0
  have hcm : Commute (fcalc χ A) Q := hQ.cfc_real χ
  have e1 : fcalc t A = fcalc (fun x => t x * (1 - χ x)) A + fcalc t A * fcalc χ A := by
    unfold fcalc
    rw [← cfc_mul t χ A, ← cfc_add A _ _]
    congr 1
    funext x; ring
  have n1 : ‖fcalc (fun x => t x * (1 - χ x)) A‖ ≤ 1 := by
    refine fcalc_norm_le A h0 h1 _ 1 zero_le_one fun x hx => ?_
    rcases le_total x η with h | h
    · rw [abs_mul]
      have : |1 - χ x| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hχ1 x]
      exact mul_le_one₀ (ht1 x ⟨hx.1, h⟩) (abs_nonneg _) this
    · simp [hχ2 x h]
  have n2 := fcalc_norm_le A h0 h1 t c hc ht2
  have hW' : W * (1 - P) = (1 - P) * W := ((Commute.one_right W).sub_right hW).eq
  have e2 : fcalc t A * Q * W * (1 - P) =
      (fcalc (fun x => t x * (1 - χ x)) A * (Q * (1 - P)) + fcalc t A * (Q * (fcalc χ A * (1 - P)))) * W := by
    rw [mul_assoc _ W, hW', ← mul_assoc]
    congr 1
    conv_lhs => rw [e1]
    rw [add_mul, add_mul, mul_assoc (fcalc t A), hcm.eq]
    simp only [mul_assoc]
  rw [e2, mul_comm ‖W‖]
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (norm_nonneg _))
  · calc _ ≤ 1 * (‖Q‖ * 1) := (norm_mul_le _ _).trans
          (mul_le_mul n1 ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hP (norm_nonneg _))) (norm_nonneg _) zero_le_one)
      _ = ‖Q‖ := by ring
  · exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right n2 (norm_nonneg _))

omit [CompleteSpace H] in
private theorem norm_pow_le_clm (U : H →L[ℂ] H) (j : ℕ) : ‖U ^ j‖ ≤ ‖U‖ ^ j := by
  rcases j with _ | j
  · rw [pow_zero, pow_zero]
    exact ContinuousLinearMap.norm_id_le
  · exact norm_pow_le' U j.succ_pos

private theorem prj_facts (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) :
    (∀ v, prj V v ∈ V) ∧ (∀ v ∈ V, prj V v = v) ∧ IsSelfAdjoint (prj V) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  exact ⟨fun v => (hm _).1 (Submodule.starProjection_apply_mem _ v),
    fun v hv => Submodule.starProjection_eq_self_iff.2 ((hm _).2 hv), isSelfAdjoint_starProjection _⟩

private theorem pres_of_comm (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H)
    (h : T * prj V = prj V * T) : ∀ v ∈ V, T v ∈ V := by
  intro v hv
  obtain ⟨a1, a2, -⟩ := prj_facts V hV
  have := congrArg (fun S : H →L[ℂ] H => S v) h
  simp only [ContinuousLinearMap.mul_apply, a2 v hv] at this
  rw [this]; exact a1 _

private theorem eig_pres (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (A T : H →L[ℂ] H) (x : ℝ)
    (h : Commute T (prj V)) (hA : Commute T A) : ∀ v ∈ eigIn V A x, T v ∈ eigIn V A x := by
  intro v hv
  refine ⟨pres_of_comm V hV T h.eq v hv.1, ?_⟩
  have h2 : A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv.2
  refine Module.End.mem_eigenspace_iff.2 ?_
  have := congrArg (fun S : H →L[ℂ] H => S v) hA.eq
  simp only [ContinuousLinearMap.mul_apply, h2, map_smul] at this
  exact this.symm

private theorem trOn_scalar (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (A Q B : H →L[ℂ] H) (x : ℝ) (a : ℂ)
    (hsa : IsSelfAdjoint A) (hAV : Commute A (prj V)) (hQV : Commute Q (prj V)) (hQA : Commute Q A)
    [FiniteDimensional ℂ (eigIn V A x)] (hQ : ∀ v ∈ eigIn V A x, Q v = a • v) :
    trOn (eigIn V A x) (A * Q * B) = x * a * trOn (eigIn V A x) B := by
  have hE : IsClosed (eigIn V A x : Set H) := (eigIn V A x).closed_of_finiteDimensional
  obtain ⟨a1, a2, a3⟩ := prj_facts _ hE
  obtain ⟨-, -, b3⟩ := prj_facts _ hV
  have hc : (eigIn V A x).topologicalClosure = eigIn V A x := hE.submodule_topologicalClosure_eq
  have hT1 : Commute (A * Q) (prj V) := hAV.mul_left hQV
  have hT2 : Commute (A * Q) A := (Commute.refl A).mul_left hQA
  have hcomm : (A * Q) ∘L prj (eigIn V A x) = prj (eigIn V A x) ∘L (A * Q) := by
    refine K.commProj _ _ ?_ ?_
    · rw [hc]; exact eig_pres V hV A _ x hT1 hT2
    · rw [hc]
      refine eig_pres V hV A _ x ?_ ?_
      · have := hT1.star_star
        rwa [b3.star_eq] at this
      · have := hT2.star_star
        rwa [hsa.star_eq] at this
  have e : prj (eigIn V A x) ∘L (A * Q * B) ∘L prj (eigIn V A x) =
      ((x : ℂ) * a) • (prj (eigIn V A x) ∘L B ∘L prj (eigIn V A x)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    have h1 := congrArg (fun S : H →L[ℂ] H => S (B (prj (eigIn V A x) v))) hcomm
    have hm := a1 (B (prj (eigIn V A x) v))
    have h2 : A (prj (eigIn V A x) (B (prj (eigIn V A x) v))) = (x : ℂ) • _ := Module.End.mem_eigenspace_iff.1 hm.2
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply] at h1 ⊢
    rw [← h1, hQ _ hm, map_smul, h2, smul_smul, mul_comm]
  unfold trOn
  rw [e]
  unfold trace
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right]
  exact tsum_mul_left

private theorem final_arith (C τ u q r k zN zN' x y : ℝ) (hτ : 0 ≤ τ) (hu : 0 ≤ u) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hk : 0 ≤ k) (hz : 1 ≤ zN) (hz' : 0 ≤ zN') (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hx : x ≤ u * (q + k * r)) (hy : y ≤ k * q * u) :
    C * zN * x + C * zN' * y + 1 * (q * u * τ) ≤ (|C| + τ) * u * (zN * (q + k * r) + k * zN' * q) := by
  have hz0 : 0 ≤ zN := zero_le_one.trans hz
  have h1 : C * zN * x ≤ |C| * zN * (u * (q + k * r)) := by
    have := le_abs_self C
    gcongr
  have h2 : C * zN' * y ≤ |C| * zN' * (k * q * u) := by
    have := le_abs_self C
    gcongr
  have h3 : q ≤ zN * (q + k * r) + k * zN' * q := by
    have a : 0 ≤ k * r := by positivity
    have b : 0 ≤ k * zN' * q := by positivity
    nlinarith
  have h4 : τ * u * q ≤ τ * u * (zN * (q + k * r) + k * zN' * q) := by gcongr
  nlinarith

end SlopeTestRemainingChoices

set_option maxHeartbeats 1600000 in
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Fx PositivityTheory.Rg.Tf.Core in
theorem UpperTheory.ConvolutionTheory.Ci.oneSide :
    K.Kern2 → PolyBdAll → SmoothDecay → DecayTraceClass → CuspTrBand → CuspidalMultiplicityOneTotallyComplex → EvEx → OneSide := by
  intro hK hPB hSD hDT hCB hMO hEv K _ _ _ n l hn μ _ θ 𝔰 ev hev hin
  obtain ⟨h0, h1, -, -⟩ := hEv K n hn μ 𝔰.toAmp
  have da := hSD K n μ 𝔰.a 𝔰.a_smooth
  have dg := hSD K n μ _ 𝔰.g_smooth
  obtain ⟨N, hN⟩ := hK K n μ θ 𝔰.a 𝔰.g (hPB K n μ _) da (hPB K n μ _) dg
  refine ⟨N, fun η hη hη1 χ hχ hχ1 hχ2 => ?_⟩
  have hsa : IsSelfAdjoint 𝔰.toAmp.A := isSelfAdjoint_of_nonneg h0
  have hPc : prj (cuspidalL2 μ) = Pc μ := by
    unfold prj Pc
    congr 1
    exact (isClosed_cuspidalL2 μ).submodule_topologicalClosure_eq
  have hcP : ∀ T, Inner μ T → Commute T (Pc μ) := fun T hT => by
    rw [← hPc]; exact hT _ (isClosed_cuspidalL2 μ) (isInvariant_cuspidalL2 μ)
  have hcV : ∀ T, Inner μ T → ∀ V, IsSummand μ V → Commute T (prj V) := fun T hT V hV => hT _ hV.closed hV.inv
  have hAin : Inner μ 𝔰.toAmp.A := hev.amp ▸ hin _
  have hQA : ∀ Q, Commute (ev Q) 𝔰.toAmp.A := fun Q => hev.amp ▸ (Commute.all Q _).map ev
  have hcomp : IsCompactOperator (𝔰.toAmp.A ∘L Pc μ) := by
    rw [← hPc, ← 𝔰.a_op]; exact (opBasics K n μ 𝔰.a).2.2
  obtain ⟨s, hs1, hs2, hs3⟩ := hCB K n μ θ (hMO K n μ) 𝔰.toAmp.A h0
    (fun V hV => pres_of_comm V hV.closed _ (hcV _ hAin V hV).eq) hcomp η hη
  refine ⟨s, hs1, hs2, fun N' => ?_⟩
  obtain ⟨C₀, hC⟩ := hN N'
  have htc : IsTraceClass (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ) := by
    have := hDT K n μ 𝔰.a 𝔰.g 1 da dg (Commute.one_left (Pc μ)).eq
    rw [𝔰.a_op] at this
    exact this
  refine ⟨|C₀| + (traceNorm (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)).toReal, fun Q a ha m j Z f hZ hf => ?_⟩
  obtain ⟨hb1, hb2, -⟩ := FX.cheb_bound η m hη hη1
  have hk : 0 ≤ (4 / η) ^ m := by positivity
  have hch : ev (chebP η m * Q) = fcalc (cheb η m) 𝔰.toAmp.A * ev Q := by
    rw [map_mul, ev_cheb ev hev.const _ hev.amp hsa]
  have hUP : Commute (𝔰.Uq 0 ^ j) (Pc μ) := (hcP _ (𝔰.Uq_inner 0)).pow_left j
  have hUA : Commute (𝔰.Uq 0 ^ j) 𝔰.toAmp.A := (𝔰.Uq_amp 0).pow_left j
  have hMP : Commute (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) (Pc μ) := (hcP _ (hin _)).mul_left hUP
  have k1 := hC f (ev (chebP η m * Q) * 𝔰.Uq 0 ^ j) Z hZ hMP.eq (by rw [𝔰.a_op]; exact hf.1) hf.2
  have hP : ‖1 - Pc μ‖ ≤ 1 := by
    have : 1 - Pc μ = (cuspidalL2 μ)ᗮ.starProjection := by
      unfold Pc
      exact (Submodule.starProjection_orthogonal' (cuspidalL2 μ)).symm
    rw [this]
    exact Submodule.starProjection_norm_le _
  have hu := norm_pow_le_clm (𝔰.Uq 0) j
  have k2 := off_est 𝔰.toAmp.A (ev Q) (𝔰.Uq 0 ^ j) (Pc μ) h0 h1 (hQA Q).symm hUP hP η _ hk (cheb η m) χ (cheb_cont η m) hχ
    hb1 hb2 hχ1 hχ2
  have k2' := k2.trans (mul_le_mul_of_nonneg_right hu (by positivity))
  rw [← hch] at k2'
  have k3 : ‖ev (chebP η m * Q) * 𝔰.Uq 0 ^ j‖ ≤ (4 / η) ^ m * ‖ev Q‖ * ‖𝔰.Uq 0‖ ^ j := by
    rw [hch]
    refine (norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans ?_) hu (norm_nonneg _) (by positivity))
    exact mul_le_mul_of_nonneg_right (fcalc_norm_le _ h0 h1 _ _ hk hb2) (norm_nonneg _)
  have eT : Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ =
      (ev Q * 𝔰.Uq 0 ^ j) * (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ) := by
    have c1 : Commute (ev Q * 𝔰.Uq 0 ^ j) (Pc μ * 𝔰.toAmp.A) :=
      ((hcP _ (hin Q)).mul_left hUP).mul_right ((hQA Q).mul_left hUA)
    calc _ = (Pc μ * 𝔰.toAmp.A) * (ev Q * 𝔰.Uq 0 ^ j) * (Rop μ 𝔰.g * Pc μ) := by simp only [mul_assoc]
      _ = _ := by rw [← c1.eq]; simp only [mul_assoc]
  have hTt : IsTraceClass (Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ) := by
    rw [eT]; exact htc.comp_left _
  have hTn : (traceNorm (Pc μ * (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) * Pc μ)).toReal ≤
      ‖ev Q‖ * ‖𝔰.Uq 0‖ ^ j * (traceNorm (Pc μ * (𝔰.toAmp.A * Rop μ 𝔰.g) * Pc μ)).toReal := by
    rw [eT]
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top htc.ne) (traceNorm_comp_left_le _ _)).trans ?_
    rw [ENNReal.toReal_mul, toReal_enorm]
    exact mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _)))
      ENNReal.toReal_nonneg
  have k4 := hs3 (cheb η m) 1 (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) (cheb_cont η m) zero_le_one hb1
    (fun V hV v hv => pres_of_comm V hV.closed (𝔰.toAmp.A * ev Q * 𝔰.Uq 0 ^ j)
      (((hcV _ hAin V hV).mul_left (hcV _ (hin Q) V hV)).mul_left ((hcV _ (𝔰.Uq_inner 0) V hV).pow_left j)).eq _
      ((opBasics K n μ 𝔰.g).1 V hV v hv)) hTt
  have e1 : cuspTr μ θ f = trace (Pc μ ∘L fcalc (cheb η m) 𝔰.toAmp.A ∘L
      (𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) ∘L θ.U ∘L Pc μ) := by
    have c : Commute (fcalc (cheb η m) 𝔰.toAmp.A) 𝔰.toAmp.A := (Commute.refl _).cfc_real _
    unfold cuspTr
    rw [hf.1, hch]
    simp only [← ContinuousLinearMap.mul_def, mul_assoc]
    rw [← mul_assoc 𝔰.toAmp.A, ← c.eq, mul_assoc]
  have e2 : ∑ p ∈ s, (cheb η m p.1 : ℂ) * (p.1 * a p *
      trOn (eigIn p.2 𝔰.toAmp.A p.1) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)) =
      ∑ p ∈ s, (cheb η m p.1 : ℂ) * trOn (eigIn p.2 𝔰.toAmp.A p.1)
        ((𝔰.toAmp.A * ev Q * (𝔰.Uq 0 ^ j * Rop μ 𝔰.g)) ∘L θ.U) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hV := ((hs1 p).1 hp).2.1
    haveI := hs2 p hp
    rw [← trOn_scalar p.2 hV.closed 𝔰.toAmp.A (ev Q) _ p.1 (a p) hsa (hcV _ hAin _ hV) (hcV _ (hin Q) _ hV) (hQA Q) (ha p hp)]
    rfl
  rw [e2]
  rw [← e1] at k4
  refine (norm_sub_le_norm_sub_add_norm_sub _ (cuspTr μ θ f) _).trans
    ((add_le_add k1 (k4.trans (mul_le_mul_of_nonneg_left hTn zero_le_one))).trans ?_)
  exact final_arith _ _ _ _ _ _ _ _ _ _ ENNReal.toReal_nonneg (by positivity) (norm_nonneg _) (norm_nonneg _) hk
    (one_le_pow₀ hZ) (by have := zero_le_one.trans hZ; positivity) (norm_nonneg _) (norm_nonneg _) k2' k3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.HomogMonomial
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open PositivityTheory.Rg.Fx

private noncomputable def cm {κ R R' : Type} [CommRing R] [CommRing R'] (φ : R → R') (P : MvPolynomial κ R) :
    MvPolynomial κ R' := ∑ β ∈ P.support, monomial β (φ (P.coeff β))

private theorem coeff_cm {κ R R' : Type} [CommRing R] [CommRing R'] {φ : R → R'} (h0 : φ 0 = 0)
    (P : MvPolynomial κ R) (β : κ →₀ ℕ) : (cm φ P).coeff β = φ (P.coeff β) := by
  classical
  rw [cm, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, h0]

private noncomputable def sb {κ κ' R T : Type} [CommRing R] [CommRing T] (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T)
    (ψ : R →+* T) : MvPolynomial κ R →+* MvPolynomial κ' T :=
  eval₂Hom (C.comp ψ) fun x => map a (h x)

private theorem sb_monomial {κ κ' R T : Type} [CommRing R] [CommRing T] (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T)
    (ψ : R →+* T) (β : κ →₀ ℕ) (r : R) :
    sb h a ψ (monomial β r) = C (ψ r) * map a (β.prod fun i k => h i ^ k) := by
  rw [sb, eval₂Hom_monomial, map_finsuppProd]
  simp only [map_pow, RingHom.comp_apply]

private theorem cm_sb {κ κ' R R' T T' : Type} [CommRing R] [CommRing R'] [CommRing T] [CommRing T']
    (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T) (a' : ℂ →+* T') (ψ : R →+* T) (ψ' : R' →+* T')
    (φ : R → R') (φ' : T → T') (h0 : φ 0 = 0) (h0' : φ' 0 = 0) (ha : ∀ x y, φ (x + y) = φ x + φ y)
    (ha' : ∀ x y, φ' (x + y) = φ' x + φ' y) (hl : ∀ x c, φ' (x * a c) = φ' x * a' c)
    (hc : ∀ r, φ' (ψ r) = ψ' (φ r)) (P : MvPolynomial κ R) :
    cm φ' (sb h a ψ P) = sb h a' ψ' (cm φ P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial β r =>
    have e : cm φ (monomial β r) = monomial β (φ r) := by
      ext γ
      rw [coeff_cm h0, coeff_monomial, coeff_monomial]
      split_ifs
      · rfl
      · exact h0
    rw [e, sb_monomial, sb_monomial]
    ext γ
    rw [coeff_cm h0', coeff_C_mul, coeff_C_mul, coeff_map, coeff_map, hl, hc]
  | add p q hp hq =>
    have e : cm φ (p + q) = cm φ p + cm φ q := by
      ext γ
      rw [MvPolynomial.coeff_add, coeff_cm h0, coeff_cm h0, coeff_cm h0, MvPolynomial.coeff_add, ha]
    rw [e, map_add (f := _), map_add (f := _), ← hp, ← hq]
    ext γ
    rw [MvPolynomial.coeff_add, coeff_cm h0', coeff_cm h0', coeff_cm h0', MvPolynomial.coeff_add, ha']

private theorem homog_eq {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) (s : Finset (ι →₀ ℕ)) (hs : p.support ⊆ s) :
    homog d p = ∑ α ∈ s, X none ^ (d - α.degree) * rename some (monomial α (p.coeff α)) := by
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [notMem_support_iff.mp hα]
  simp

private theorem homog_add {ι : Type} (d : ℕ) (p q : MvPolynomial ι ℂ) : homog d (p + q) = homog d p + homog d q := by
  classical
  rw [homog_eq d _ _ support_add, homog_eq d p _ Finset.subset_union_left, homog_eq d q _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add, map_add (f := _), map_add (f := _), mul_add]

private theorem homog_monomial {ι : Type} (d : ℕ) (α : ι →₀ ℕ) (c : ℂ) :
    homog d (monomial α c) = X none ^ (d - α.degree) * rename some (monomial α c) := by
  classical
  rw [homog_eq d _ _ support_monomial_subset, Finset.sum_singleton, coeff_monomial, if_pos rfl]

private theorem homog_mul {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) (c : ℂ) : homog d (p * C c) = homog d p * C c := by
  induction p using MvPolynomial.induction_on' with
  | monomial α r =>
    rw [homog_monomial, mul_comm, C_mul_monomial, homog_monomial, ← C_mul_monomial, map_mul, rename_C]
    ring
  | add p q hp hq => rw [add_mul, homog_add, homog_add, hp, hq, add_mul]

private theorem homog_rename {ι ι' : Type} (δ : ι → ι') (d : ℕ) (p : MvPolynomial ι ℂ) :
    homog d (rename δ p) = rename (Option.map δ) (homog d p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α r =>
    rw [homog_monomial, map_mul, map_pow, rename_X, rename_rename]
    conv_lhs => rw [rename_monomial, homog_monomial, ← rename_monomial, rename_rename, Finsupp.degree_mapDomain]
    rfl
  | add p q hp hq => rw [map_add (f := _), homog_add, homog_add, hp, hq, map_add (f := _)]

private theorem piece_mul {ι : Type} [Fintype ι] (k : ℕ) (f : EP ι) (c : ℂ) :
    piece k (f * algebraMap ℂ (EP ι) c) = piece k f * C c := by
  obtain ⟨ha, h0, hs⟩ := UpperTheory.ConvolutionTheory.FX.piece_add ι k
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => rw [zero_mul, h0, zero_mul]
  | add f g hf hg => rw [add_mul, ha, ha, hf, hg, add_mul]
  | single v p =>
    have e : algebraMap ℂ (EP ι) c = AddMonoidAlgebra.single 0 (C c) := rfl
    rw [e, AddMonoidAlgebra.single_mul_single, add_zero, hs, hs, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm p, homogeneousComponent_C_mul]
    ring

private theorem lift_alg {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (c : ℂ) :
    lift x τ (algebraMap ℂ (EP ι) c) = algebraMap ℂ A c := by
  have e : algebraMap ℂ (EP ι) c = AddMonoidAlgebra.single 0 (C c) := rfl
  rw [e]
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem ren_ren {ι ι' ι'' : Type} [Fintype ι] [Fintype ι'] [Fintype ι''] [DecidableEq ι'] [DecidableEq ι'']
    (δ : ι → ι') (δ' : ι' → ι'') (f : EP ι) : ren δ' (ren δ f) = ren (δ' ∘ δ) f := by
  unfold ren
  rw [(UpperTheory.ConvolutionTheory.FX.subst ι ι' _ _ f).2]
  congr 2
  · funext i
    simp
  · ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (δ i)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

private theorem ev_ren {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι']
    (δ : ι → ι') (L : ι' → ℂ) (f : EP ι) : ev L (ren δ f) = ev (fun i => L (δ i)) f := by
  unfold ren
  rw [(UpperTheory.ConvolutionTheory.FX.subst ι ι' _ _ f).1]
  congr 2
  funext i
  simp [apply_ite]

private theorem eval_powE {n : ℕ} (f : ℕ) (i : Fin n) (s : Multiset ℂ) (hs : s.card = n) :
    eval (fun j : Fin n => s.esymm (j + 1)) (powE f i) = (s.map (· ^ f)).esymm (i + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hs
      subst hl
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i)
      = expand f (esymm (Fin n) ℂ (i + 1)) := by
    rw [← esymmAlgHom_apply]
    have := congrArg Subtype.val
      ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
        ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)
    exact this
  have h2 := congrArg (aeval a) h1
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply] at h2
  have h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f := by
    apply MvPolynomial.algHom_ext
    intro r
    simp
  rw [h3] at h2
  simp only [aeval_esymm_eq_multiset_esymm] at h2
  rw [Multiset.map_map, ← coe_aeval_eq_eval]
  exact h2

private theorem map_eq_cm {κ R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (P : MvPolynomial κ R) :
    map φ P = cm φ P := by
  ext γ
  rw [coeff_map, coeff_cm (map_zero φ)]

private theorem map_sb {κ κ' R R' T T' : Type} [CommRing R] [CommRing R'] [CommRing T] [CommRing T']
    (h : κ → MvPolynomial κ' ℂ) (a : ℂ →+* T) (a' : ℂ →+* T') (ψ : R →+* T) (ψ' : R' →+* T')
    (φ : R →+* R') (φ' : T →+* T') (hl : ∀ c, φ' (a c) = a' c)
    (hc : ∀ r, φ' (ψ r) = ψ' (φ r)) (P : MvPolynomial κ R) :
    map φ' (sb h a ψ P) = sb h a' ψ' (map φ P) := by
  rw [map_eq_cm, map_eq_cm]
  exact cm_sb h a a' ψ ψ' φ φ' (map_zero _) (map_zero _) (map_add _) (map_add _)
    (fun x c => by rw [map_mul, hl]) hc P

theorem UpperTheory.ConvolutionTheory.Ci.kfBc :
    KfBc := by
  classical
  intro F E _ _ _ _ _ n SE SF hS Φ G hΦ hG
  let res : Ix E n → Ix F n := fun x => (x.1.comp (algebraMap F E), x.2)
  let h : Pl E × Fin n → MvPolynomial (Pl F × Fin n) ℂ := fun x =>
    rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)
  refine ⟨sb h (algebraMap ℂ _) (ren res) Φ, fun k => sb h C (rename res).toRingHom (G k), ⟨fun w => ?_, ?_⟩,
    fun k => ?_, fun d => ?_, fun L' t' ht => ?_⟩
  · have h1 := hΦ.1 fun τ => w (τ.comp (algebraMap F E))
    refine (map_sb h (algebraMap ℂ _) (algebraMap ℂ _) (ren res) (ren res)
      (ren fun x : Ix E n => (x.1, w (x.1.comp (algebraMap F E)) x.2)) _ ?_ ?_ Φ).trans (by rw [h1])
    · intro c
      exact lift_alg _ _ c
    · intro r
      rw [ren_ren, ren_ren]
      rfl
  · intro y hy
    have e : sb h (algebraMap ℂ _) (ren res) Φ =
        bind₁ (fun x => map (algebraMap ℂ (EP (Ix F n))) (h x)) (map (ren res) Φ) := by
      rw [bind₁, aeval_def, eval₂_map]
      rfl
    rw [e] at hy
    obtain ⟨y', hy', hy2⟩ := mem_vars_bind₁ _ _ hy
    obtain ⟨i, -, rfl⟩ := mem_vars_rename _ _ (vars_map _ _ hy2)
    exact fun hh => hΦ.2 y' (vars_map _ _ hy') ((hS _).2 hh)
  · obtain ⟨ha, h0, -⟩ := UpperTheory.ConvolutionTheory.FX.piece_add (Ix E n) k
    obtain ⟨ha', h0', -⟩ := UpperTheory.ConvolutionTheory.FX.piece_add (Ix F n) k
    have h1 := hG k
    refine Eq.trans ?_ (cm_sb h (algebraMap ℂ _) C (ren res) (rename res).toRingHom (piece k) (piece k) h0 h0' ha ha'
      (piece_mul k) (fun r => UpperTheory.ConvolutionTheory.FX.piece_ren _ r _ res k) Φ).symm
    refine (map_sb h C C (rename res).toRingHom (rename res).toRingHom (aeval blockE).toRingHom _ ?_ ?_ _).trans
      (by rw [h1]; rfl)
    · intro c
      simp
    · intro r
      have e : (aeval (blockE (τ := F →+* ℂ) (n := n))).comp (rename res) =
          (rename res).comp (aeval (blockE (τ := E →+* ℂ) (n := n))) := by
        apply MvPolynomial.algHom_ext
        intro y
        simp only [AlgHom.comp_apply, rename_X, aeval_X, blockE, rename_rename]
        rfl
      exact DFunLike.congr_fun e r
  · unfold trunc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact cm_sb h C C (rename res).toRingHom (rename (Option.map res)).toRingHom (homog d) (homog d)
      (by simp [homog]) (by simp [homog]) (homog_add d) (homog_add d) (homog_mul d) (homog_rename res d) (G k)
  · rw [← RingHom.comp_apply]
    refine hom_congr_vars (p₁ := Φ) (p₂ := Φ) ?_ ?_ rfl
    · refine RingHom.ext fun f => ?_
      simp only [evK, sb, RingHom.comp_apply, eval₂Hom_C]
      exact ev_ren res L' f
    · intro y hy _
      have h1 := eval_powE (resDeg F y.1) y.2 _ (ht _ fun hh => hΦ.2 y hy ((hS _).2 hh))
      simp only [evK, sb, h, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]
      rw [hval, bcSat, ← h1]
      have hc : (ev L').comp (algebraMap ℂ (EP (Ix F n))) = RingHom.id ℂ :=
        RingHom.ext fun c => lift_alg _ _ c
      rw [hc]
      rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SepPoly
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

private theorem exists_esymm_ne {s t : Multiset ℂ} {n : ℕ} (hs : s.card = n) (ht : t.card = n) (h : s ≠ t) :
    ∃ k : Fin n, s.esymm (k + 1) ≠ t.esymm (k + 1) := by
  by_contra hc
  push Not at hc
  apply h
  have hp : (s.map fun a => Polynomial.X - Polynomial.C a).prod = (t.map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, Multiset.prod_X_sub_X_eq_sum_esymm, hs, ht]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < n + 1 := Finset.mem_range.mp hj
    have : s.esymm j = t.esymm j := by
      rcases j with _ | j
      · simp [Multiset.esymm]
      · exact hc ⟨j, by omega⟩
    rw [this]
  rw [← Polynomial.roots_multiset_prod_X_sub_C s, hp, Polynomial.roots_multiset_prod_X_sub_C]

private theorem one_factor (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Set (Pl K))
    (Λ : (K →+* ℂ) → Multiset ℂ) (t : Pl K → Multiset ℂ) (Λ' : (K →+* ℂ) → Multiset ℂ) (t' : Pl K → Multiset ℂ)
    (h1 : ∀ τ, (Λ τ).card = n) (h2 : ∀ w ∉ S, (t w).card = n) (h3 : ∀ τ, (Λ' τ).card = n)
    (h4 : ∀ w ∉ S, (t' w).card = n) (h : ¬ (Λ = Λ' ∧ ∀ w ∉ S, t w = t' w)) :
    ∃ P : PR K n, (∀ y ∈ P.vars, y.1 ∉ S) ∧ (∀ x : ℝ, x ≠ 0 → val x Λ t P ≠ 0) ∧ ∀ x : ℝ, val x Λ' t' P = 0 := by
  classical
  by_cases hΛ : Λ = Λ'
  · have : ∃ w, w ∉ S ∧ t w ≠ t' w := by
      by_contra hc
      push Not at hc
      exact h ⟨hΛ, hc⟩
    obtain ⟨w, hw, hne⟩ := this
    obtain ⟨k, hk⟩ := exists_esymm_ne (h2 w hw) (h4 w hw) hne
    refine ⟨X (w, k) - C (C ((t' w).esymm (k + 1))), ?_, ?_, ?_⟩
    · intro y hy
      have := vars_sub_subset _ hy
      rw [vars_C, vars_X, Finset.union_empty, Finset.mem_singleton] at this
      rw [this]; exact hw
    · intro x _
      simpa [val, hval, sub_eq_zero] using hk
    · intro x
      simp [val, hval]
  · obtain ⟨τ, hne⟩ := Function.ne_iff.mp hΛ
    obtain ⟨k, hk⟩ := exists_esymm_ne (h1 τ) (h3 τ) hne
    refine ⟨C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none), ?_, ?_, ?_⟩
    · intro y hy
      rw [vars_C] at hy
      exact absurd hy (Finset.notMem_empty _)
    · intro x hx
      have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      have e : val x Λ t (C (X (some (τ, k)) - C ((Λ' τ).esymm (k + 1)) * X none) : PR K n) =
          x * ((Λ τ).esymm (k + 1) - (Λ' τ).esymm (k + 1)) := by
        rw [val, eval₂Hom_C]
        simp
        ring
      rw [e]
      exact mul_ne_zero hx' (sub_ne_zero.mpr hk)
    · intro x
      rw [val, eval₂Hom_C]
      simp
      ring

theorem UpperTheory.ConvolutionTheory.Ci.sepPoly :
    SepPoly := by
  classical
  intro K _ _ n S Λ t I _ Λ' t' h1 h2 h3 h4 h
  choose P hP1 hP2 hP3 using fun i => one_factor K n S Λ t (Λ' i) (t' i) h1 h2 (h3 i) (h4 i) (h i)
  set Q : PR K n := ∏ i, P i with hQ
  refine ⟨Q, Q.vars.image Prod.fst, max Q.totalDegree (Q.support.sup fun β => (Q.coeff β).totalDegree), ?_,
    ⟨?_, le_max_left _ _, ?_⟩, ?_, ?_⟩
  · intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (vars_prod P hy)
    exact hP1 i y hi
  · intro y hy
    exact Finset.mem_image_of_mem _ hy
  · intro β
    by_cases hβ : β ∈ Q.support
    · exact le_max_of_le_right (Finset.le_sup (f := fun β => (Q.coeff β).totalDegree) hβ)
    · rw [notMem_support_iff.mp hβ, totalDegree_zero]
      exact Nat.zero_le _
  · intro x hx
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hP2 i x hx
  · intro i x
    rw [hQ, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (hP3 i x)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.FixFAnti
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

private theorem prj_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule ℂ H) {v : H} (hv : v ∈ W) : prj W v = v := by
  unfold prj
  exact Submodule.starProjection_eq_self_iff.2 (W.le_topologicalClosure hv)

private theorem fixF_anti {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]
    {U U' : Subgroup (AdelicGLn.FiniteAdelicGL K n)} (h : U' ≤ U) : fixF μ U ≤ fixF μ U' := by
  unfold fixF
  exact biInf_mono fun u hu => h hu

private theorem eig_fix {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : v ∈ V ∧ 𝔞.A v = (x : ℂ) • v ∧ v ∈ fixF μ 𝔞.U := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
  have h3 : 𝔞.A v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 h2
  refine ⟨h1, h3, ?_⟩
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h4 := hA v
  rw [h3] at h4
  exact (Submodule.smul_mem_iff _ hx').1 h4

private theorem poly_ind {H σ ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ev : MvPolynomial σ (MvPolynomial ι ℂ) →+* (H →L[ℂ] H)) (f : MvPolynomial σ (MvPolynomial ι ℂ) →+* ℂ)
    (v : H) (s : Set σ) (h0 : ∀ c : ℂ, ev (C (C c)) v = f (C (C c)) • v)
    (h1 : ∀ i, ev (C (X i)) v = f (C (X i)) • v) (h2 : ∀ y ∈ s, ev (X y) v = f (X y) • v)
    (P : MvPolynomial σ (MvPolynomial ι ℂ)) (hP : ∀ y ∈ P.vars, y ∈ s) : ev P v = f P • v := by
  have hadd : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P + Q) v = f (P + Q) • v := by
    intro P Q hP hQ
    rw [map_add (f := _), map_add (f := _), ContinuousLinearMap.add_apply, hP, hQ, add_smul]
  have hmul : ∀ P Q, ev P v = f P • v → ev Q v = f Q • v → ev (P * Q) v = f (P * Q) • v := by
    intro P Q hP hQ
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hQ, map_smul, hP, smul_smul, mul_comm]
  have hC : ∀ c : MvPolynomial ι ℂ, ev (C c) v = f (C c) • v := by
    intro c
    induction c using MvPolynomial.induction_on with
    | C a => exact h0 a
    | add p q hp hq => rw [C_add]; exact hadd _ _ hp hq
    | mul_X p i hp => rw [C_mul]; exact hmul _ _ hp (h1 i)
  have hm : P ∈ supported (MvPolynomial ι ℂ) s := mem_supported.2 fun y hy => hP y hy
  clear hP
  rw [supported_eq_adjoin_X] at hm
  induction hm using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨y, hy, rfl⟩ := hp
    exact h2 y hy
  | algebraMap r => exact hC r
  | add p q _ _ hp hq => exact hadd _ _ hp hq
  | mul p q _ _ hp hq => exact hmul _ _ hp hq

private theorem eig_fixL {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) {w : Pl K} (hw : w ∉ 𝔞.S) :
    v ∈ V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n) := by
  obtain ⟨h1, -, h2⟩ := eig_fix 𝔞 hA hx hv
  rw [Submodule.mem_inf, fixL]
  exact ⟨h1, fixF_anti μ (𝔞.max w hw) h2⟩

private theorem val_CC {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (c : ℂ) : val (n := n) x Λ t (C (C c)) = c := by simp [val]

private theorem val_none {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) : val (n := n) x Λ t (C (X none)) = x := by simp [val]

private theorem val_some {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (y : Ix K n) :
    val (n := n) x Λ t (C (X (some y))) = x * (Λ y.1).esymm (y.2 + 1) := by simp [val]

private theorem val_X {K : Type} [Field K] [NumberField K] {n : ℕ} (x : ℝ) (Λ : (K →+* ℂ) → Multiset ℂ)
    (t : Pl K → Multiset ℂ) (w : Pl K) (i : Fin n) :
    val (n := n) x Λ t (X (w, i)) = (t w).esymm (i + 1) := by simp [val, hval]

private theorem ev_val {K : Type} [Field K] [NumberField K] {n : ℕ} {μ : Measure (normOneGL (K := K) (n := n))} [μ.IsHaarMeasure]
    (𝔞 : Amp μ) (hA : ∀ v, 𝔞.A v ∈ fixF μ 𝔞.U) {V : Submodule ℂ (LL μ)} {x : ℝ} (hx : 0 < x)
    {ev : PR K n →+* (LL μ →L[ℂ] LL μ)} (hev : 𝔞.IsEv ev) {Λ : (K →+* ℂ) → Multiset ℂ} {t : Pl K → Multiset ℂ}
    (h : At μ 𝔞.S V Λ t) (P : PR K n) (hPv : ∀ y ∈ P.vars, y.1 ∉ 𝔞.S) {v : LL μ}
    (hv : v ∈ eigIn V 𝔞.A x) : ev P v = val x Λ t P • v := by
  obtain ⟨hvV, hAv, hvU⟩ := eig_fix 𝔞 hA hx hv
  obtain ⟨hI, hS⟩ := h
  have hO : Oinf μ 𝔞.ν 𝔞.a₀ v = (x : ℂ) • v := by
    rw [← hAv, Amp.A, ContinuousLinearMap.comp_apply, prj_self _ hvU]
  refine poly_ind ev (val x Λ t) v {y | y.1 ∉ 𝔞.S} (fun c => ?_) (fun o => ?_) (fun y hy => ?_) P hPv
  · rw [hev.const, val_CC, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  · cases o with
    | none => rw [hev.amp, hAv, val_none]
    | some y =>
      obtain ⟨-, h1⟩ := hI y.1
      rw [hev.cen, Amp.Z, ContinuousLinearMap.comp_apply, prj_self _ hvU,
        h1 𝔞.ν 𝔞.a₀ 𝔞.smooth y.2 v hvV, hO, smul_smul, mul_comm, val_some]
  · obtain ⟨w, i⟩ := y
    obtain ⟨-, -, h1⟩ := hS w hy
    rw [hev.hecke w hy i, h1 i v (eig_fixL 𝔞 hA hx hv hy), val_X]

theorem UpperTheory.ConvolutionTheory.Ci.evVal :
    EvEx → ParEx → EvVal := by
  intro hE hP K _ _ _ n hn μ _ 𝔞 V x hx hV
  obtain ⟨-, -, hA, -⟩ := hE K n hn μ 𝔞
  obtain ⟨p1, p2, -⟩ := hP K n hn μ V hV
  refine ⟨fun hne => ?_, fun Λ t Λ' t' h h' => ?_, fun ev hev Λ t h P hPv v hv => ev_val 𝔞 hA hx hev h P hPv hv⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
    have hB : ∀ w, ∃ B, w ∉ 𝔞.S → SSat μ V w B := by
      intro w
      by_cases hw : w ∈ 𝔞.S
      · exact ⟨0, fun h => absurd hw h⟩
      · obtain ⟨B, hB⟩ := (p2 w ((Submodule.ne_bot_iff _).2 ⟨v, eig_fixL 𝔞 hA hx hv hw, hv0⟩)).exists
        exact ⟨B, fun _ => hB⟩
    choose t ht using hB
    choose Λ hΛ using fun τ => (p1 τ).exists
    exact ⟨Λ, t, And.intro hΛ ht⟩
  · refine ⟨funext fun τ => (p1 τ).unique (h.1 τ) (h'.1 τ), fun w hw => ?_⟩
    have hs := h.2 w hw
    exact (p2 w hs.2.1).unique hs (h'.2 w hw)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.CprsMulRight
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

section SlopeTestRemainingChoices

open scoped InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem prj_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] : prj E = E.starProjection := by
  have h : E.topologicalClosure = E := E.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  unfold prj
  congr 1

private theorem prj_mem_iff {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v = v ↔ v ∈ V := by
  unfold prj
  rw [Submodule.starProjection_eq_self_iff, hV.submodule_topologicalClosure_eq]

private noncomputable def cprs (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) : Module.End ℂ E :=
  (E.orthogonalProjectionOnto : H →ₗ[ℂ] E) ∘ₗ (T : H →ₗ[ℂ] H) ∘ₗ E.subtype

private theorem cprs_coe (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) (v : E) :
    (cprs E T v : H) = E.starProjection (T v) := rfl

private theorem trOn_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    trOn E T = LinearMap.trace ℂ E (cprs E T) := by
  let b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_sum_inner _ b, trOn, prj_eq, GroundTheory.Automorphic.trace]
  set S : H →L[ℂ] H := T ∘L E.starProjection with hS
  refine HasSum.tsum_eq ?_
  have h := hasSum_sum (s := Finset.univ) fun k _ =>
    (GroundTheory.Automorphic.stdHilbertBasis ℂ H).hasSum_inner_mul_inner (ContinuousLinearMap.adjoint S (b k : H)) (b k : H)
  convert (preTransparency := .reducible) h using 1
  · rfl
  · funext i
    rw [ContinuousLinearMap.comp_apply, b.starProjection_eq_sum_rankOne]
    simp only [ContinuousLinearMap.sum_apply, inner_sum, InnerProductSpace.rankOne_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, Submodule.coe_inner, cprs_coe, hS, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 (b k).2, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (b k).2]

private theorem comm_proj (E : Submodule ℂ H) [FiniteDimensional ℂ E] (U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E)
    (h' : ∀ v ∈ E, ContinuousLinearMap.adjoint U v ∈ E) (v : H) :
    E.starProjection (U v) = U (E.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (E.starProjection_apply_mem v)) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact E.starProjection_inner_eq_zero v _ (h' w hw)

private theorem cprs_mul_right (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E) :
    cprs E T * cprs E U = cprs E (T * U) := by
  ext v
  rw [mul_apply_eq_comp, cprs_coe, cprs_coe, cprs_coe, Submodule.starProjection_eq_self_iff.2 (h _ v.2)]
  rfl

private theorem cprs_mul_left (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H)
    (h : ∀ v, E.starProjection (U v) = U (E.starProjection v)) :
    cprs E U * cprs E T = cprs E (U * T) := by
  ext v
  rw [mul_apply_eq_comp, cprs_coe, cprs_coe, cprs_coe, mul_apply_eq_comp, h, h,
    Submodule.starProjection_eq_self_iff.2 (E.starProjection_apply_mem _)]

private theorem mem_eig {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (A U : H →L[ℂ] H) (x : ℝ)
    (h1 : Commute U (prj V)) (h2 : Commute U A) : ∀ v ∈ eigIn V A x, U v ∈ eigIn V A x := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [← prj_mem_iff hV] at hv1 ⊢
    have := congrArg (fun L : H →L[ℂ] H => L v) h1.eq
    simp only [mul_apply_eq_comp, hv1] at this
    exact this.symm
  · rw [Module.End.mem_eigenspace_iff] at hv2 ⊢
    have := congrArg (fun L : H →L[ℂ] H => L v) h2.eq
    simp only [mul_apply_eq_comp] at this
    simp only [ContinuousLinearMap.coe_coe] at hv2 ⊢
    rw [← this, hv2, map_smul]

private theorem abs_form (hE : ExpForm) (l : ℕ) (hl : 0 < l) (V : Submodule ℂ H) (hV : IsClosed (V : Set H))
    (A T : H →L[ℂ] H) (hA : 0 ≤ A) (x : ℝ) [FiniteDimensional ℂ (eigIn V A x)] (U : ZMod l → H →L[ℂ] H)
    (h1 : ∀ i, Commute (U i) (prj V)) (h2 : ∀ i, Commute (U i) A) (h3 : ∀ i k, Commute (U i) (U k))
    (h4 : ∀ i, T * U i = U (i + 1) * T) :
    ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop,
      trOn (eigIn V A x) ((U 0 ^ j) ∘L T) = ∑ ζ ∈ s, c ζ * ζ ^ j := by
  have hAs : IsSelfAdjoint A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA
  have hPs : IsSelfAdjoint (prj V) := isSelfAdjoint_starProjection _
  have hm : ∀ i, ∀ v ∈ eigIn V A x, U i v ∈ eigIn V A x := fun i => mem_eig hV A _ x (h1 i) (h2 i)
  have hm' : ∀ i, ∀ v ∈ eigIn V A x, ContinuousLinearMap.adjoint (U i) v ∈ eigIn V A x := fun i => by
    refine mem_eig hV A _ x ?_ ?_
    · have := (h1 i).star_star
      rwa [hPs.star_eq] at this
    · have := (h2 i).star_star
      rwa [hAs.star_eq] at this
  have hc := fun i => comm_proj _ (U i) (hm i) (hm' i)
  obtain ⟨s, c, hs, h⟩ := hE (eigIn V A x) l hl (fun i => cprs _ (U i)) (cprs _ T)
    (fun i k => by
      show _ * _ = _ * _
      rw [cprs_mul_right _ _ _ (hm k), cprs_mul_right _ _ _ (hm i), (h3 i k).eq])
    (fun i => by rw [cprs_mul_right _ _ _ (hm i), cprs_mul_left _ _ _ (hc (i + 1)), h4])
  refine ⟨s, c, hs, (eventually_ge_atTop (Module.finrank ℂ (eigIn V A x))).mono fun j hj => ?_⟩
  rw [← h j hj, trOn_eq]
  congr 1
  clear hj
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ j ih => rw [pow_succ', pow_succ', mul_assoc, ← ih, cprs_mul_left _ _ _ (hc 0)]; rfl

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.Ci.trExp :
    ExpForm → TrExp := by
  intro hE K _ _ n l hl μ _ θ 𝔰 V x hA hV hfin
  exact abs_form hE l hl V hV.closed _ _ hA x 𝔰.Uq (fun i => 𝔰.Uq_inner i V hV.closed hV.inv) 𝔰.Uq_amp 𝔰.Uq_comm
    𝔰.Uq_perm
end

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.Ci in
theorem UpperTheory.ConvolutionTheory.ci : UpperTheory.ConvolutionTheory.CI :=
  ciOf (trExp expForm) (evVal evEx Dp.parEx) valBc (killEx Dp.parEx) kfBc truncSpec sepPoly
    (oneSide K.kern2 C.polyBdAll C.smoothDecay C.decayTraceClass C.cuspTrBand Dp.multiplicity_one_cuspidal_spectrum_normOneGL evEx) evEx kill
